/*
 * Copyright 1991-2016 Mentor Graphics Corporation
 *
 * All Rights Reserved.
 *
 * THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
 * MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
 */

#include <ctype.h>
#include <stdlib.h>
#if defined(unix)
#   include <unistd.h>
#endif
#include <stdio.h>
#include <string.h>

#define PGM "tssi2mti"

/* The TSSI document "ASCII I/O Interface" specifies a maximum of
 *   16384 state characters in an input row.  Using hexadecimal
 *   data, this could result in 65536 bits of data, which is more
 *   than a 640K DOS program could handle, but this situation is
 *   unlikely.
 */
#define MAX_POS 16384

/*
 * TSSI allows 18 time digits. The limit in a 63-bit time value is
 *   9.223E18 or almost 19 digits, so we'll allow that.
 */
#define MAX_TIME_DIGITS 19

#define NEWLINE(fd) while ((! feof(fd)) && (getc(fd) != '\n'))

#define FORCES_PER_RUN 100

struct bit_defn {
	char *name;
	char dir;
	char prev_val;
};

static struct signal_defn {
	char nbits;		/* Only values used are 1 and 4. */
	struct bit_defn bits[4];
} *signals[MAX_POS];

static void Exit_usage();
static int  Parse_deffile();
static int  Write_forces();
static int  New_signal();
static int  New_bit();

static int lineno = 1;
static int forces_since_last_run = 0;
static int last_col = 0;

int main(argc, argv)
	int argc;
	char **argv;
{
	FILE *deffile;
	FILE *vectors;
	FILE *forces;
	int exit_code;

	if ((argc < 2) 
	||  (argc > 3)) {
		Exit_usage(NULL);
	}
	if ((deffile = fopen(argv[1], "r")) == NULL) {
		Exit_usage(argv[1]);
	}
	if (argc == 2) {
		vectors = fdopen(STDIN_FILENO, "r");
	} else {
		if ((vectors = fopen(argv[2], "r")) == NULL) {
			Exit_usage(argv[2]);
		}
	}
	forces = fdopen(STDOUT_FILENO, "w");
	exit_code = Parse_deffile(deffile);
	if (exit_code == 0) {
		int i, last_in_col;

		for (last_in_col = i = 0; i < last_col; i++) {
			if (signals[i]) {
				int j;

				for (j=0; j < signals[i]->nbits; j++) {
					if (signals[i]->bits[j].name) {
						if  ((signals[i]->bits[j].dir == 'I')
						||   (signals[i]->bits[j].dir == 'B')) {
							last_in_col = i + 1;
						} else {
							free(signals[i]->bits[j].name);
							signals[i]->bits[j].name = NULL;
						}
					}
				}
				if (last_in_col != (i + 1)) {
					free(signals[i]);
					signals[i] = NULL;
				}
			}
		}
		last_col = last_in_col;
		exit_code = Write_forces(vectors, forces);
	}
	fclose(forces);

	return exit_code;
}

static int  Parse_deffile(deffile)
	FILE *deffile;
{
	char buf[1024];
	char *bufp;
	int going, ch;
	int inputs = 0;
	char *sig_name, *sig_pos, *sig_io1, *sig_io2;


	while (! feof(deffile)) {
		bufp = buf;
		for(going = 1; going; ) {
			switch (ch = getc(deffile)) {
				case '#':
					NEWLINE(deffile);
				case '\n':
				case EOF:
					*bufp = '\0';
					going = 0;
					break;
				default:
					*bufp++ = ch;
					break;
			}
		}
		sig_pos = sig_io1 = sig_io2 = NULL;
		if ((sig_name = strtok(buf, " \t"))) {
			if ((sig_pos = strtok(0, " \t"))) {
				if ((sig_io1 = strtok(0, " \t"))) {
					sig_io2 = strtok(0, " \t");
				}
			}
		}
		inputs += New_signal(sig_name, sig_pos, sig_io1, sig_io2);
		lineno++;
	}

	if (inputs == 0) {
		fprintf(stderr, "Warning: No inputs specified in signal definitions, no force vectors generated.\n");
		return 4;
	} else {
		return 0;
	}
}

static void Signal_error(char* msg, char* nm)
{
	fprintf(stderr, "Error: %s - signal \"%s\", line %d\n", msg, nm, lineno);
}

/*
 * Make a new entry in the signal pool.  Return a 1 if the signal could
 *   be an input (i.e., is an input or I/O pin), else 0.
 */

static int  New_signal(nm, pos, io1, io2)
	char *nm;
	char *pos;
	char *io1;
	char *io2;
{
	char msg_buf[256];
	struct signal_defn *sigp = NULL;
	int rv = 0;

	if (nm && pos) {
		char *bitp;
		int col = 0;
		int bit = -1;

		for(bitp=pos;*bitp;bitp++) {
			if ( ! isdigit(*bitp)) {
				if (*bitp != '.') {
					col = -1;
				}
				break;
			}
		}
		if (*bitp == '.') {
			switch (bitp[1]) {
				case '0': bit =  0; break;
				case '1': bit =  1; break;
				case '2': bit =  2; break;
				case '3': bit =  3; break;
				default:  bit = -1; break;
			}
			if ((bit == -1)
			||  (bitp[2] != '\0')) {
				sprintf(msg_buf,
					"Bit position must be a digit between 0 and 3");
				Signal_error(msg_buf, nm);

				return 0;
			} else {
				bit = -1;
			}
		}
		if (col == 0) {
			col = atoi(pos);
		}
		if ((col > 0) && (col <= MAX_POS)) {
			if ((sigp = signals[col-1]) == NULL) {
				sigp = signals[col-1] =
					(struct signal_defn *)malloc(sizeof(struct signal_defn));
				sigp->nbits = (bit >= 0) ? 4 : 1;
				rv = New_bit(sigp, col, bit, nm, io1, io2);
			} else if (sigp->nbits == 4) {
				if (sigp->bits[bit].name == NULL) {
					rv = New_bit(sigp, col, bit, nm, io1, io2);
				} else {
					sprintf(msg_buf,
						"Signal %s already defined at position %d.%d",
						sigp->bits[0].name, col, bit);
					Signal_error(msg_buf, nm);
				}
			} else {
				sprintf(msg_buf, "Signal %s already defined at position %d",
					sigp->bits[0].name, col);
				Signal_error(msg_buf, nm);
			}
		} else {
			sprintf(msg_buf, "Pin position must be an integer between 1 and %d",
				MAX_POS);
			Signal_error(msg_buf, nm);
		}
	}

	return rv;
}

/*
 * Fill in the bit position - return 1 for input or I/O ports.
 */
static int New_bit(sigp, col, bit_pos, nm, io1, io2)
	struct signal_defn *sigp;
	int col;
	int bit_pos;
	char *nm;
	char *io1;
	char *io2;
{
	int bit = (sigp->nbits == 4) ? bit_pos : 0;
	char msg_buf[256];
	char dir2;

	sigp->bits[bit].name = strdup(nm);
	sigp->bits[bit].prev_val = 0;
	if (col > last_col) {
		last_col = col;
	}
	if (io1) {
		sigp->bits[bit].dir = 'U';
		if (strlen(io1) == 1) {
			if ((*io1 == 'I') || (*io1 == 'i')) {
				sigp->bits[bit].dir = 'I';
			} else if ((*io1 == 'O') || (*io1 == 'o')) {
				sigp->bits[bit].dir = 'O';
			} else {
				sprintf(msg_buf,
					"Pin direction '%c' not recognized",
					*io1);
				Signal_error(msg_buf, nm);
			}
		}
		if (sigp->bits[bit].dir == 'U') {
			Signal_error(
				"Pin direction specification must be 'I' or 'O'",
				nm);
		}
	}
	if (io2) {
		dir2 = 'U';
		if (strlen(io2) == 1) {
			if ((*io2 == 'I') || (*io2 == 'i')) {
				dir2 = 'I';
			} else if ((*io2 == 'O') || (*io2 == 'o')) {
				dir2 = 'O';
			} else {
				sprintf(msg_buf,
					"Second pin direction '%c' not recognized",
					*io2);
				Signal_error(msg_buf, nm);
			}
		}
		if (sigp->bits[bit].dir == 'U') {
			Signal_error(
				"Pin direction specification must be 'I' or 'O'",
				nm);
		} else {
			if (dir2 == sigp->bits[bit].dir) {
				Signal_error("Pin direction specified twice", nm);
			} else {
				sigp->bits[bit].dir = 'B';
			}
		}
	}

	return (sigp->bits[bit].dir == 'I') || (sigp->bits[bit].dir == 'B');
}

/*
 * Get_time - read the time field from the input line.  Return 1 for
 *   success, 0 for various error conditions and -1 (EOF) for end-of-file.
 */
static int Get_time(fd, buf)
	FILE *fd;
	char *buf;
{
	int i = 0;
	int ch;

	for (;;) {
		ch = getc(fd);
		switch (ch) {
			case EOF:
				if (i != 0) {
					fprintf(stderr,
						"Error: End of file reading time, line %d\n",
						lineno);
					return 0;
				} else {
					return EOF;
				}

			case ' ':
			case '\t':
				if (i == 0) {
					break;
				} else {
					buf[i] = '\0';

					return 1;
				}

			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9':
				if (i <= MAX_TIME_DIGITS) {
					buf[i++] = ch;
					break;
				} else {
					fprintf(stderr,
						"Error: Too many digits in time, line %d\n", lineno);

					return 0;
				}

			case '#':
				if (i == 0) {
					NEWLINE(fd);
					lineno++;
					break;
				} else {
					fprintf(stderr,
						"Error: Comment character ends time, line %d\n",
						lineno);
					return 0;
				}

			case '\n':
			case '\r':
				if (i == 0) {
					/* Allow CR/LF for DOS. */
					if (ch == '\r') NEWLINE(fd);
					lineno++;
					break;
				} else {
					buf[i] = '\0';
					fprintf(stderr,
						"Error: No data at time %s, line %d\n",
						buf, lineno);
					return 0;
				}

			default:
				fprintf(stderr,
					"Error: Invalid character '%c' (0x%X) in time, line %d\n",
					ch, ch, lineno);
				return 0;
		}
	}
}

static void Value_error(val, nm, col, bit, time, nbits)
	char val;
	char *nm;
	int col;
	int bit;
	char *time;
	int nbits;
{
	char pos_buf[32];

	if (nbits == 4) {
		sprintf(pos_buf, "%d.%d", col, bit);
	} else {
		sprintf(pos_buf, "%d", col);
	}
	fprintf(stderr, "Error: Invalid input value '%c' on signal %s", val, nm);
	fprintf(stderr, "(column %s), time %s, line %d\n", pos_buf, time, lineno);
}

static int  Process_col(fd, col, val, time)
	FILE *fd;
	int col;
	char val;
	char *time;
{
	struct signal_defn *sigp = signals[col - 1];

	if (sigp) {
		int bit;
		char *val_str = "uuuu";

		switch (val) {
			case '0':	val_str = (sigp->nbits == 4) ? "0000" : "0uuu" ; break;
			case '1':	val_str = (sigp->nbits == 4) ? "1000" : "1uuu" ; break;
			case '2':	if (sigp->nbits == 4) val_str = "0100" ; break;
			case '3':	if (sigp->nbits == 4) val_str = "1100" ; break;
			case '4':	if (sigp->nbits == 4) val_str = "0010" ; break;
			case '5':	if (sigp->nbits == 4) val_str = "1010" ; break;
			case '6':	if (sigp->nbits == 4) val_str = "0110" ; break;
			case '7':	if (sigp->nbits == 4) val_str = "1110" ; break;
			case '8':	if (sigp->nbits == 4) val_str = "0001" ; break;
			case '9':	if (sigp->nbits == 4) val_str = "1001" ; break;
			case 'a':
			case 'A':	if (sigp->nbits == 4) val_str = "0101" ; break;
			case 'b':
			case 'B':	if (sigp->nbits == 4) val_str = "1101" ; break;
			case 'c':
			case 'C':	if (sigp->nbits == 4) val_str = "1100" ; break;
			case 'd':
			case 'D':	val_str = (sigp->nbits == 4) ? "1011" : "0uuu" ; break;
			case 'e':
			case 'E':	if (sigp->nbits == 4) val_str = "0111" ; break;
			case 'f':
			case 'F':	if (sigp->nbits == 4) val_str = "1111" ; break;

			case 'u':
			case 'U':	val_str = "1111"; break;

			case 'n':
			case 'N':	val_str = "XXXX"; break;

			case 'z':
			case 'Z':	val_str = "ZZZZ"; break;

			case 'h':
			case 'H':
			case 'l':
			case 'L':
			case 'x':
			case 'X':
			case 't':
			case 'T':
			case '?':
				for (bit = 0; bit < sigp->nbits; bit++) {
					if (sigp->bits[bit].dir == 'B') {
						val_str[bit] = 'Z';
					}
				}
		}
		for (bit = 0; bit < sigp->nbits; bit++) {
			if (sigp->bits[bit].name) {
				if (val_str[bit] == 'u') {
					Value_error(val, sigp->bits[bit].name,
						col, bit, time, sigp->nbits);
				} else if (sigp->bits[bit].prev_val != val_str[bit]) {
					fprintf(fd, "force %s %c @%s\n",
						sigp->bits[bit].name, val_str[bit], time);
					sigp->bits[0].prev_val = val_str[bit];
					forces_since_last_run++;
				}
			}
		}
	}

	return (col <= last_col);
}

static int  Write_forces(vectors, forces)
	FILE *vectors;
	FILE *forces;
{
	char time[MAX_TIME_DIGITS + 1];
	char prev_time[MAX_TIME_DIGITS + 1];
	char last_run_time[MAX_TIME_DIGITS + 1];
	int rv, col, ch, going;

	lineno = 1;
	time[0] = '\0';
	while((rv = Get_time(vectors, time)) == 1) {
		strcpy(prev_time, time);
		if (forces_since_last_run > FORCES_PER_RUN) {
			fprintf(forces, "run @%s\n", time);
			strcpy(last_run_time, time);
			forces_since_last_run = 0;
		}
		for(going = col = 1; going; ) {
			ch = getc(vectors);
			switch (ch) {
				case '\t':
				case ' ':
					break;

				case '\n':
					going = 0;
					break;

				default:
					if (ch == '\\') {
						if ((ch = getc(vectors)) == '\n') {
							lineno++;
							break;
						} else {
							ungetc(ch, vectors);
							ch = '\\';
						}
					}
					going = Process_col(forces, col++, ch, time);
					break;
			}
		}
		if (col < last_col) {
			fprintf(stderr, "Error: too few columns of signal data, line %d\n",
				lineno);
		}
		if (ch != '\n') {
			NEWLINE(vectors);
		}
		lineno++;
	}
	if (strcmp(prev_time, last_run_time)) {
		fprintf(forces, "run @%s\n", prev_time);
	}

	return (rv == EOF) ? 0 : 8;
}

static void Exit_usage(fn)
	char *fn;
{
	if (fn != NULL) {
		perror(fn);
	}
	fprintf(stderr, "Usage: %s signal_def_file [vector_file]\n", PGM);

	exit(4);
}
