package main

import (
	"database/sql"
	"encoding/csv"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"io/ioutil"
	"net/mail"
	"os"
	"sort"
	"strconv"
	"strings"
	"text/template"
	"time"

	"github.com/jmhodges/clock"
	"github.com/letsencrypt/boulder/cmd"
	"github.com/letsencrypt/boulder/db"
	blog "github.com/letsencrypt/boulder/log"
	bmail "github.com/letsencrypt/boulder/mail"
	"github.com/letsencrypt/boulder/metrics"
	"github.com/letsencrypt/boulder/policy"
	"github.com/letsencrypt/boulder/sa"
)

type mailer struct {
	clk           clock.Clock
	log           blog.Logger
	dbMap         dbSelector
	mailer        bmail.Mailer
	subject       string
	emailTemplate *template.Template
	recipients    []recipient
	targetRange   interval
	sleepInterval time.Duration
}

// interval defines a range of email addresses to send to, alphabetically. The
// "start" field is inclusive and the "end" field is exclusive. To include
// everything, set "end" to "\xFF".
type interval struct {
	start string
	end   string
}

// queryResult is a gorp selectable holder for database query results.
type queryResult struct {
	// ID is exported for gorp.
	ID int64

	// Contact is exported for gorp.
	Contact []byte
}

func (i *interval) ok() error {
	if i.start > i.end {
		return fmt.Errorf(
			"interval start value (%s) is greater than end value (%s)",
			i.start, i.end)
	}
	return nil
}

func (i *interval) includes(s string) bool {
	return s >= i.start && s < i.end
}

func (m *mailer) ok() error {
	// Ensure the checkpoint range is valid.
	if err := m.targetRange.ok(); err != nil {
		return err
	}

	// Error if sleep interval is negative.
	if m.sleepInterval < 0 {
		return fmt.Errorf("sleep interval (%d) is < 0", m.sleepInterval)
	}
	return nil
}

func (m *mailer) printStatus(to string, current, total int, start time.Time) {
	// Should never happen.
	if total <= 0 || current < 1 || current > total {
		m.log.AuditErrf("Invalid current: %d or total: %d", current, total)
	}

	completion := (float32(current) / float32(total)) * 100
	now := m.clk.Now()
	elapsed := now.Sub(start)
	m.log.Infof("Sending to address: %q message: %d of %d [%.2f%%] time elapsed: %s",
		to, current, total, completion, elapsed)
}

func sortEmailAddresses(input addressesToRecipientsMap) []string {
	var addresses []string
	for k := range input {
		addresses = append(addresses, k)
	}
	sort.Strings(addresses)
	return addresses
}

func (m *mailer) run() error {
	if err := m.ok(); err != nil {
		return err
	}

	m.log.Infof("Resolving %d recipient addresses", len(m.recipients))
	addressesToRecipients, err := m.resolveEmailAddresses()
	if err != nil {
		return err
	}

	totalAddresses := len(addressesToRecipients)
	if totalAddresses == 0 {
		return errors.New("0 recipients remained after resolving addresses")
	}

	m.log.Infof(
		"%d recipients were resolved to %d addresses",
		len(m.recipients), totalAddresses)

	var mostRecipientsLengh int
	var mostRecipientsAddress string
	for emailAddress, recipients := range addressesToRecipients {
		if len(recipients) > mostRecipientsLengh {
			mostRecipientsLengh = len(recipients)
			mostRecipientsAddress = emailAddress
		}
	}
	m.log.Infof(
		"The address with the most recipients: %q had: %d associated recipients",
		mostRecipientsAddress, mostRecipientsLengh)

	err = m.mailer.Connect()
	if err != nil {
		return err
	}

	defer func() {
		_ = m.mailer.Close()
	}()

	startTime := m.clk.Now()
	sortedAddresses := sortEmailAddresses(addressesToRecipients)
	var sent int
	for pos, address := range sortedAddresses {
		if !m.targetRange.includes(address) {
			m.log.Debugf("Address: %q is outside of target range, skipping", address)
			continue
		}

		if err := policy.ValidEmail(address); err != nil {
			m.log.Infof("Skipping: %q due to policy violation: %s", address, err)
			continue
		}

		recipients := addressesToRecipients[address]
		m.printStatus(address, pos+1, totalAddresses, startTime)

		var mailBody strings.Builder
		err = m.emailTemplate.Execute(&mailBody, recipients)
		if err != nil {
			return err
		}

		if mailBody.Len() == 0 {
			return errors.New("message body was empty after interpolation")
		}

		err := m.mailer.SendMail([]string{address}, m.subject, mailBody.String())
		if err != nil {
			var recoverableSMTPErr bmail.RecoverableSMTPError
			if errors.As(err, &recoverableSMTPErr) {
				m.log.Errf("Address: %q was rejected by server due to: %s", address, err)
				continue
			}
			return fmt.Errorf(
				"while sending mail: %d of %d to: %q: %s", pos, len(sortedAddresses), address, err)
		}

		sent++
		m.clk.Sleep(m.sleepInterval)
	}

	if sent == 0 {
		return errors.New("0 messages sent, configured recipients or interval may be invalid")
	}
	return nil
}

// resolveEmailAddresses fetches the contact row of each recipient by
// registration ID then creates a map of email addresses to (a list of)
// `recipient`s that resolve to that email address.
func (m *mailer) resolveEmailAddresses() (addressesToRecipientsMap, error) {
	result := make(addressesToRecipientsMap, len(m.recipients))
	for _, r := range m.recipients {
		contact, err := getContactForID(r.id, m.dbMap)
		if err != nil {
			return nil, err
		}

		for _, address := range contact {
			parsedAddress, err := mail.ParseAddress(address)
			if err != nil {
				m.log.Errf("While parsing address: %q for ID: %d: %s", address, r.id, err)
				continue
			}
			result[parsedAddress.Address] = append(result[parsedAddress.Address], r)
		}
	}
	return result, nil
}

// dbSelector since the only methods we use from the `gorp.DbMap` object are
// `SelectOne` and `Execute` the we just define an interface with those methods
// instead of importing all of gorp. This facilitates mock implementations for
// unit tests.
type dbSelector interface {
	SelectOne(holder interface{}, query string, args ...interface{}) error
	Exec(query string, args ...interface{}) (sql.Result, error)
}

// getContactForID queries the database for the contact field associated with
// the provided registration ID.
func getContactForID(id int64, dbMap dbSelector) ([]string, error) {
	// Transaction isolation level READ UNCOMMITTED trades consistency for
	// performance.
	_, err := dbMap.Exec(
		"SET SESSION TRANSACTION ISOLATION LEVEL READ UNCOMMITTED;",
	)
	if err != nil {
		return nil, fmt.Errorf(
			"while setting transaction isolation level: %s", err)
	}

	var result queryResult
	err = dbMap.SelectOne(&result,
		`SELECT id,
			contact 
	 	FROM registrations 
	 	WHERE contact NOT IN ('[]', 'null')
			AND id = :id;`,
		map[string]interface{}{
			"id": id,
		})
	if err != nil {
		if db.IsNoRows(err) {
			return []string{}, nil
		}
		return nil, err
	}

	var contactContents []string
	err = json.Unmarshal(result.Contact, &contactContents)
	if err != nil {
		return nil, err
	}

	var addresses []string
	for _, entry := range contactContents {
		if strings.HasPrefix(entry, "mailto:") {
			addresses = append(addresses, strings.TrimPrefix(entry, "mailto:"))
		}
	}
	return addresses, nil
}

// recipient represents one entry of recipient list file.
type recipient struct {
	id int64

	// Extra is exported so the contents can be accessed to fill template
	// variables referenced in the email body.
	Extra map[string]string
}

// addressesToRecipientsMap maps from an email address to a list of `recipient`s
// with the same email address.
type addressesToRecipientsMap map[string][]recipient

// parseRecipientList parses the contents of a recipient list file into a list
// of `recipient` objects. All columns after `id` into a per-recipient map from
// column name -> value.
func parseRecipientList(recipientList *csv.Reader) ([]recipient, error) {
	entries, err := recipientList.Read()
	if err != nil {
		return nil, err
	}

	if len(entries) == 0 {
		return nil, errors.New("no entries in the recipient list")
	}

	if entries[0] != "id" {
		return nil, fmt.Errorf(
			"the first column of the header row must be \"id\", got: %q", entries[0])
	}

	var columnNames []string
	for _, columnName := range entries[1:] {
		columnNames = append(columnNames, strings.TrimSpace(columnName))
	}

	headerColsTotal := len(columnNames)
	var recipients []recipient
	for {
		entry, err := recipientList.Read()
		if err != nil {
			if errors.Is(err, io.EOF) {
				break
			}
			return nil, err
		}

		entryColsTotal := len(entry)
		if entryColsTotal == 0 {
			return nil, errors.New("recipient list contains an empty line")
		}

		if entryColsTotal != headerColsTotal {
			return nil, fmt.Errorf(
				`line: %q contains: %d columns, expected: %d columns`,
				entry, entryColsTotal, headerColsTotal)
		}

		entryID := entry[0]
		id, err := strconv.ParseInt(entryID, 10, 64)
		if err != nil {
			return nil, fmt.Errorf(
				"%q could not be parsed as a registration ID: %s", entryID, err)
		}

		extra := make(map[string]string)
		for num, columnName := range entry[1:] {
			extra[columnNames[num]] = columnName
		}

		recipients = append(recipients, recipient{id, extra})
	}

	if len(recipients) == 0 {
		return nil, errors.New("recipient list contained 0 entries after the header")
	}
	return recipients, nil
}

// makeRecipientList determines the format of the recipient list file,
// constructs a reader, and returns the result of parsing with that reader.
func makeRecipientList(csvFilename, tsvFilename string) ([]recipient, error) {
	var filename string
	var delimiter rune

	if csvFilename != "" {
		filename = csvFilename
	} else if tsvFilename != "" {
		// We can use a `*csv.Reader` to parse a TSV file, we just have to
		// supply a custom delimiter in rune form.
		filename = tsvFilename
		delimiter = '\t'
	}

	contents, err := os.Open(filename)
	if err != nil {
		return nil, err
	}

	reader := csv.NewReader(contents)
	if delimiter != 0 {
		reader.Comma = delimiter
	}
	return parseRecipientList(reader)
}

const usageIntro = `
Introduction:

The notification mailer exists to send a message to the contact associated
with a list of registration IDs. The attributes of the message (from address,
subject, and message content) are provided by the command line arguments. The
message content is provided as a path to a template file via the -body argument.

Provide a list of recipient user ids in a CSV file passed with the -recipientList
flag. The CSV file must have "id" as the first column and may have additional
fields to be interpolated into the email template:

	id, lastIssuance
	1234, "from example.com 2018-12-01"
	5678, "from example.net 2018-12-13"

The additional fields will be interpolated with Golang templating, e.g.:

  Your last issuance on each account was:
		{{ range . }} {{ .Extra.lastIssuance }}
		{{ end }}

To help the operator gain confidence in the mailing run before committing fully
three safety features are supported: dry runs, intervals and a sleep between emails.

The -dry-run=true flag will use a mock mailer that prints message content to
stdout instead of performing an SMTP transaction with a real mailserver. This
can be used when the initial parameters are being tweaked to ensure no real
emails are sent. Using -dry-run=false will send real email.

Intervals supported via the -start and -end arguments. Only email addresses that
are alphabetically between the -start and -end strings will be sent. This can be used
to break up sending into batches, or more likely to resume sending if a batch is killed,
without resending messages that have already been sent. The -start flag is inclusive and
the -end flag is exclusive.

Notify-mailer de-duplicates email addresses and groups together the resulting recipient
structs, so a person who has multiple accounts using the same address will only receive
one email.

During mailing the -sleep argument is used to space out individual messages.
This can be used to ensure that the mailing happens at a steady pace with ample
opportunity for the operator to terminate early in the event of error. The
-sleep flag honours durations with a unit suffix (e.g. 1m for 1 minute, 10s for
10 seconds, etc). Using -sleep=0 will disable the sleep and send at full speed.

Examples:
  Send an email with subject "Hello!" from the email "hello@goodbye.com" with
  the contents read from "test_msg_body.txt" to every email associated with the
  registration IDs listed in "test_reg_recipients.json", sleeping 10 seconds
  between each message:

  notify-mailer -config test/config/notify-mailer.json -body
    cmd/notify-mailer/testdata/test_msg_body.txt -from hello@goodbye.com
    -recipient-list cmd/notify-mailer/testdata/test_msg_recipients.csv -subject "Hello!"
    -sleep 10s -dry-run=false

  Do the same, but only to example@example.com:

  notify-mailer -config test/config/notify-mailer.json
    -body cmd/notify-mailer/testdata/test_msg_body.txt -from hello@goodbye.com
    -recipient-list cmd/notify-mailer/testdata/test_msg_recipients.csv -subject "Hello!"
    -start example@example.com -end example@example.comX

  Send the message starting with example@example.com and emailing every address that's
	alphabetically higher:

  notify-mailer -config test/config/notify-mailer.json 
    -body cmd/notify-mailer/testdata/test_msg_body.txt -from hello@goodbye.com 
    -recipient-list cmd/notify-mailer/testdata/test_msg_recipients.csv -subject "Hello!"
    -start example@example.com

Required arguments:
- body
- config
- from
- subject
- recipient-list-csv OR recipient-list-tsv`

func main() {
	from := flag.String("from", "", "From header for emails. Must be a bare email address.")
	subject := flag.String("subject", "", "Subject of emails")
	recipientListCSV := flag.String("recipient-list-csv", "", "File containing a CSV list of registration IDs and extra info.")
	recipientListTSV := flag.String("recipient-list-tsv", "", "File containing a TSV list of registration IDs and extra info.")
	bodyFile := flag.String("body", "", "File containing the email body in Golang template format.")
	dryRun := flag.Bool("dry-run", true, "Whether to do a dry run.")
	sleep := flag.Duration("sleep", 500*time.Millisecond, "How long to sleep between emails.")
	start := flag.String("start", "", "Alphabetically lowest email address to include.")
	end := flag.String("end", "\xFF", "Alphabetically highest email address (exclusive).")
	reconnBase := flag.Duration("retry-base", 1*time.Second, "Base sleep duration between retry attempts")
	reconnMax := flag.Duration("retry-max", 5*60*time.Second, "Max sleep duration between retry attempts after exponential backoff")
	configFile := flag.String("config", "", "File containing a JSON config.")

	flag.Usage = func() {
		fmt.Fprintf(os.Stderr, "%s\n\n", usageIntro)
		fmt.Fprintf(os.Stderr, "Usage of %s:\n", os.Args[0])
		flag.PrintDefaults()
	}

	flag.Parse()
	if *from == "" || *subject == "" || *bodyFile == "" || *configFile == "" ||
		(*recipientListCSV == "" && *recipientListTSV == "") || (*recipientListCSV != "" && *recipientListTSV != "") {
		flag.Usage()
		os.Exit(1)
	}

	configData, err := ioutil.ReadFile(*configFile)
	cmd.FailOnError(err, fmt.Sprintf("Reading %q", *configFile))

	// Parse JSON config.
	var cfg struct {
		NotifyMailer struct {
			DB cmd.DBConfig
			cmd.SMTPConfig
		}
		Syslog cmd.SyslogConfig
	}
	err = json.Unmarshal(configData, &cfg)
	cmd.FailOnError(err, "Unmarshaling config")

	log := cmd.NewLogger(cfg.Syslog)
	defer log.AuditPanic()

	// Setup database client.
	dbSettings := sa.DbSettings{
		MaxOpenConns:    cfg.NotifyMailer.DB.MaxOpenConns,
		MaxIdleConns:    cfg.NotifyMailer.DB.MaxIdleConns,
		ConnMaxLifetime: cfg.NotifyMailer.DB.ConnMaxLifetime.Duration,
		ConnMaxIdleTime: cfg.NotifyMailer.DB.ConnMaxIdleTime.Duration,
	}
	dbURL, err := cfg.NotifyMailer.DB.URL()
	cmd.FailOnError(err, "Couldn't load DB URL")

	dbMap, err := sa.NewDbMap(dbURL, dbSettings)
	cmd.FailOnError(err, "Couldn't connect to database")

	// Load message body.
	body, err := ioutil.ReadFile(*bodyFile)
	cmd.FailOnError(err, fmt.Sprintf("Reading %q", *bodyFile))

	template, err := template.New("email").Parse(string(body))
	cmd.FailOnError(err, fmt.Sprintf("Parsing template %q", *bodyFile))

	address, err := mail.ParseAddress(*from)
	cmd.FailOnError(err, fmt.Sprintf("Parsing %q", *from))

	recipients, err := makeRecipientList(*recipientListCSV, *recipientListTSV)
	cmd.FailOnError(err, "While making the recipient list")

	targetRange := interval{
		start: *start,
		end:   *end,
	}

	var mailClient bmail.Mailer
	if *dryRun {
		log.Infof("Doing a dry run")
		mailClient = bmail.NewDryRun(*address, log)
	} else {
		smtpPassword, err := cfg.NotifyMailer.SMTPConfig.PasswordConfig.Pass()
		cmd.FailOnError(err, "Failed to load SMTP password")

		mailClient = bmail.New(
			cfg.NotifyMailer.Server,
			cfg.NotifyMailer.Port,
			cfg.NotifyMailer.Username,
			smtpPassword,
			nil,
			*address,
			log,
			metrics.NoopRegisterer,
			*reconnBase,
			*reconnMax)
	}

	m := mailer{
		clk:           cmd.Clock(),
		log:           log,
		dbMap:         dbMap,
		mailer:        mailClient,
		subject:       *subject,
		recipients:    recipients,
		emailTemplate: template,
		targetRange:   targetRange,
		sleepInterval: *sleep,
	}

	err = m.run()
	cmd.FailOnError(err, "mailer.send returned error")
}
