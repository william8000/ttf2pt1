/*
 * True Type Font to Adobe Type 1 font converter 
 * By Mark Heath <mheath@netspace.net.au> 
 * Based on ttf2pfa by Andrew Weeks <ccsaw@bath.ac.uk> 
 * With help from Frank M. Siegert <fms@this.net> 
 *
 * see COPYRIGHT
 *
***********************************************************************
 *
 * Sergey Babkin <babkin@bellatlantic.net>, <sab123@hotmail.com>
 *
 * Added post-processing of resulting outline to correct the errors
 * both introduced during conversion and present in the original font,
 * autogeneration of hints (has yet to be improved though) and BlueValues,
 * scaling to 1000x1000 matrix, option to print the result on STDOUT,
 * support of Unicode to CP1251 conversion, optimization  of the
 * resulting font code by space (that improves the speed too). Excluded
 * the glyphs that are unaccessible through the encoding table from
 * the output file. Added the built-in Type1 assembler (taken from
 * the `t1utils' package).
 *
***********************************************************************
 *
 * Thomas Henlich <thenlich@rcs.urz.tu-dresden.de>
 *
 * Added generation of .afm file (font metrics)
 * Read encoding information from encoding description file
 * Fixed bug in error message about unknown language ('-l' option)
 * Added `:' after %%!PS-AdobeFont-1.0
 * changed unused entries in ISOLatin1Encoding[] from .notdef to c127,c128...
 *
***********************************************************************
 *
 * Thomas Henlich <thenlich@rcs.urz.tu-dresden.de>
 *
 * Added generation of .afm file (font metrics)
 *
***********************************************************************
 *
 * Bug Fixes: 
************************************************************************
 *
 * Sun, 21 Jun 1998 Thomas Henlich <thenlich@Rcs1.urz.tu-dresden.de> 
 * 1. "width" should be "short int" because otherwise: 
 *     characters with negative widths (e.g. -4) become *very* wide (65532) 
 * 2. the number of /CharStrings is numglyphs and not numglyphs+1 
 *
***********************************************************************
 *
 *
 *
 * The resultant font file produced by this program still needs to be ran
 * through t1asm (from the t1utils archive) to produce a completely valid
 * font. 
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <time.h>
#include <ctype.h>
#include <math.h>

#ifdef _GNU_SOURCE
#include <getopt.h>
#endif

#ifndef WINDOWS
#	include <unistd.h>
#	include <netinet/in.h>
#else
#	define WINDOWS_FUNCTIONS /* ask to define functions - in one file only */
#	include "windows.h"
#endif

#include "pt1.h"
#include "global.h"
#include "version.h"

/* globals */

/* table of front-ends */

extern struct frontsw ttf_sw;

struct frontsw *frontswtab[] = {
	&ttf_sw,
	NULL /* end of table */
};

struct frontsw *cursw=0; /* the active front end */
char *front_arg=""; /* optional argument */

/* options */
int      encode = 0;	/* encode the resulting file */
int      pfbflag = 0;	/* produce compressed file */
int      wantafm=0;	/* want to see .afm instead of .t1a on stdout */
int      correctvsize=0;	/* try to correct the vertical size of characters */
int      wantuid = 0;	/* user wants UniqueID entry in the font */
int      allglyphs = 0;	/* convert all glyphs, not only 256 of them */
int      warnlevel = 3;	/* the level of permitted warnings */
int      forceunicode = 0; /* consider any fonr as Unicode for mapping purposes */
/* options - maximal limits */
int      max_stemdepth = 128;	/* maximal depth of stem stack in interpreter (128 - limit from X11) */
/* options - debugging */
int      absolute = 0;	/* print out in absolute values */
int      reverse = 1;	/* reverse font to Type1 path directions */
/* options - suboptions of Outline Processing, defaults are set in table */
int      optimize;	/* enables space optimization */
int      smooth;	/* enable smoothing of outlines */
int      transform;	/* enables transformation to 1000x1000 matrix */
int      hints;	/* enables autogeneration of hints */
int      subhints;	/* enables autogeneration of substituted hints */
int      trybold;	/* try to guess whether the font is bold */
int      correctwidth;	/* try to correct the character width */

/* table of Outline Processing (may think also as Optimization) options */
static struct {
	char disbl; /* character to disable - enforced lowercase */
	char enbl;  /* character to enable - auto-set as toupper(disbl) */
	int *valp; /* pointer to the actual variable containign value */
	int  dflt; /* default value */
	char *descr; /* description */
} opotbl[] = {
	{ 'b', 0/*auto-set*/, &trybold, 1, "guessing of the ForceBold hint" },
	{ 'h', 0/*auto-set*/, &hints, 1, "autogeneration of hints" },
	{ 'u', 0/*auto-set*/, &subhints, 1, "hint substitution technique" },
	{ 'o', 0/*auto-set*/, &optimize, 1, "space optimization of font files" },
	{ 's', 0/*auto-set*/, &smooth, 1, "smoothing and repair of outlines" },
	{ 't', 0/*auto-set*/, &transform, 1, "auto-scaling to the standard matrix 1000x1000" },
	{ 'w', 0/*auto-set*/, &correctwidth, 0, "correct the glyph widths (use only for buggy fonts)" },
};

int      debug = DEBUG;	/* debugging flag */

FILE    *pfa_file, *afm_file;
int      numglyphs, long_offsets, ncurves;
struct font_metrics fontm;

/* non-globals */
static char    *strUID = 0;	/* user-supplied UniqueID */
static unsigned long numUID;	/* auto-generated UniqueID */

static int      ps_fmt_3 = 0;
static double   scale_factor, original_scale_factor;

static char	*glyph_rename[256];

/* the names assigned if the original font
 * does not specify any
 */

static char    *Fmt3Encoding[256] = {
	"c0", "c1", "c2", "c3",
	"c4", "c5", "c6", "c7",
	"c8", "c9", "c10", "c11",
	"c12", "CR", "c14", "c15",
	"c16", "c17", "c18", "c19",
	"c20", "c21", "c22", "c23",
	"c24", "c25", "c26", "c27",
	"c28", "c29", "c30", "c31",
	"space", "exclam", "quotedbl", "numbersign",
	"dollar", "percent", "ampersand", "quotesingle",
	"parenleft", "parenright", "asterisk", "plus",
	"comma", "hyphen", "period", "slash",
	"zero", "one", "two", "three",
	"four", "five", "six", "seven",
	"eight", "nine", "colon", "semicolon",
	"less", "equal", "greater", "question",
	"at", "A", "B", "C",
	"D", "E", "F", "G",
	"H", "I", "J", "K",
	"L", "M", "N", "O",
	"P", "Q", "R", "S",
	"T", "U", "V", "W",
	"X", "Y", "Z", "bracketleft",
	"backslash", "bracketright", "asciicircum", "underscore",
	"grave", "a", "b", "c",
	"d", "e", "f", "g",
	"h", "i", "j", "k",
	"l", "m", "n", "o",
	"p", "q", "r", "s",
	"t", "u", "v", "w",
	"x", "y", "z", "braceleft",
	"bar", "braceright", "asciitilde", "c127",
	"c128", "c129", "quotesinglbase", "florin",
	"quotedblbase", "ellipsis", "dagger", "daggerdbl",
	"circumflex", "perthousand", "Scaron", "guilsinglleft",
	"OE", "c141", "c142", "c143",
	"c144", "quoteleft", "quoteright", "quotedblleft",
	"quotedblright", "bullet", "endash", "emdash",
	"tilde", "trademark", "scaron", "guilsinglright",
	"oe", "c157", "c158", "Ydieresis",
	"nbspace", "exclamdown", "cent", "sterling",
	"currency", "yen", "brokenbar", "section",
	"dieresis", "copyright", "ordfeminine", "guillemotleft",
	"logicalnot", "sfthyphen", "registered", "macron",
	"degree", "plusminus", "twosuperior", "threesuperior",
	"acute", "mu", "paragraph", "periodcentered",
	"cedilla", "onesuperior", "ordmasculine", "guillemotright",
	"onequarter", "onehalf", "threequarters", "questiondown",
	"Agrave", "Aacute", "Acircumflex", "Atilde",
	"Adieresis", "Aring", "AE", "Ccedilla",
	"Egrave", "Eacute", "Ecircumflex", "Edieresis",
	"Igrave", "Iacute", "Icircumflex", "Idieresis",
	"Eth", "Ntilde", "Ograve", "Oacute",
	"Ocircumflex", "Otilde", "Odieresis", "multiply",
	"Oslash", "Ugrave", "Uacute", "Ucircumflex",
	"Udieresis", "Yacute", "Thorn", "germandbls",
	"agrave", "aacute", "acircumflex", "atilde",
	"adieresis", "aring", "ae", "ccedilla",
	"egrave", "eacute", "ecircumflex", "edieresis",
	"igrave", "iacute", "icircumflex", "idieresis",
	"eth", "ntilde", "ograve", "oacute",
	"ocircumflex", "otilde", "odieresis", "divide",
	"oslash", "ugrave", "uacute", "ucircumflex",
	"udieresis", "yacute", "thorn", "ydieresis"
};

#ifdef notdef /* { */
/* This table is not used anywhere in the code
 * so it's ifdef-ed out by default but left in
 * the source code for reference purposes (and
 * possibly for future use)
 */

static char    *ISOLatin1Encoding[256] = {
	".null", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", "CR", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	"space", "exclam", "quotedbl", "numbersign",
	"dollar", "percent", "ampersand", "quoteright",
	"parenleft", "parenright", "asterisk", "plus",
	"comma", "hyphen", "period", "slash",
	"zero", "one", "two", "three",
	"four", "five", "six", "seven",
	"eight", "nine", "colon", "semicolon",
	"less", "equal", "greater", "question",
	"at", "A", "B", "C",
	"D", "E", "F", "G",
	"H", "I", "J", "K",
	"L", "M", "N", "O",
	"P", "Q", "R", "S",
	"T", "U", "V", "W",
	"X", "Y", "Z", "bracketleft",
	"backslash", "bracketright", "asciicircum", "underscore",
	"grave", "a", "b", "c",
	"d", "e", "f", "g",
	"h", "i", "j", "k",
	"l", "m", "n", "o",
	"p", "q", "r", "s",
	"t", "u", "v", "w",
	"x", "y", "z", "braceleft",
	"bar", "braceright", "asciitilde", "c127",
	"c128", "c129", "quotesinglbase", "florin",
	"quotedblbase", "ellipsis", "dagger", "daggerdbl",
	"circumflex", "perthousand", "Scaron", "guilsinglleft",
	"OE", "c141", "c142", "c143",
	"c144", "quoteleft", "quoteright", "quotedblleft",
	"quotedblright", "bullet", "endash", "emdash",
	"tilde", "trademark", "scaron", "guilsinglright",
	"oe", "c157", "c158", "Ydieresis",
	"nbspace", "exclamdown", "cent", "sterling",
	"currency", "yen", "brokenbar", "section",
	"dieresis", "copyright", "ordfeminine", "guillemotleft",
	"logicalnot", "sfthyphen", "registered", "macron",
	"degree", "plusminus", "twosuperior", "threesuperior",
	"acute", "mu", "paragraph", "periodcentered",
	"cedilla", "onesuperior", "ordmasculine", "guillemotright",
	"onequarter", "onehalf", "threequarters", "questiondown",
	"Agrave", "Aacute", "Acircumflex", "Atilde",
	"Adieresis", "Aring", "AE", "Ccedilla",
	"Egrave", "Eacute", "Ecircumflex", "Edieresis",
	"Igrave", "Iacute", "Icircumflex", "Idieresis",
	"Eth", "Ntilde", "Ograve", "Oacute",
	"Ocircumflex", "Otilde", "Odieresis", "multiply",
	"Oslash", "Ugrave", "Uacute", "Ucircumflex",
	"Udieresis", "Yacute", "Thorn", "germandbls",
	"agrave", "aacute", "acircumflex", "atilde",
	"adieresis", "aring", "ae", "ccedilla",
	"egrave", "eacute", "ecircumflex", "edieresis",
	"igrave", "iacute", "icircumflex", "idieresis",
	"eth", "ntilde", "ograve", "oacute",
	"ocircumflex", "otilde", "odieresis", "divide",
	"oslash", "ugrave", "uacute", "ucircumflex",
	"udieresis", "yacute", "thorn", "ydieresis"
};

#endif /* } notdef */

static char    *adobe_StandardEncoding[256] = {
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	"space", "exclam", "quotedbl", "numbersign",
	"dollar", "percent", "ampersand", "quoteright",
	"parenleft", "parenright", "asterisk", "plus",
	"comma", "hyphen", "period", "slash",
	"zero", "one", "two", "three",
	"four", "five", "six", "seven",
	"eight", "nine", "colon", "semicolon",
	"less", "equal", "greater", "question",
	"at", "A", "B", "C", "D", "E", "F", "G",
	"H", "I", "J", "K", "L", "M", "N", "O",
	"P", "Q", "R", "S", "T", "U", "V", "W",
	"X", "Y", "Z", "bracketleft",
	"backslash", "bracketright", "asciicircum", "underscore",
	"quoteleft", "a", "b", "c", "d", "e", "f", "g",
	"h", "i", "j", "k", "l", "m", "n", "o",
	"p", "q", "r", "s", "t", "u", "v", "w",
	"x", "y", "z", "braceleft",
	"bar", "braceright", "asciitilde", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", "exclamdown", "cent", "sterling",
	"fraction", "yen", "florin", "section",
	"currency", "quotesingle", "quotedblleft", "guillemotleft",
	"guilsinglleft", "guilsinglright", "fi", "fl",
	".notdef", "endash", "dagger", "daggerdbl",
	"periodcentered", ".notdef", "paragraph", "bullet",
	"quotesinglbase", "quotedblbase", "quotedblright", "guillemotright",
	"ellipsis", "perthousand", ".notdef", "questiondown",
	".notdef", "grave", "acute", "circumflex",
	"tilde", "macron", "breve", "dotaccent",
	"dieresis", ".notdef", "ring", "cedilla",
	".notdef", "hungarumlaut", "ogonek", "caron",
	"emdash", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", "AE", ".notdef", "ordfeminine",
	".notdef", ".notdef", ".notdef", ".notdef",
	"Lslash", "Oslash", "OE", "ordmasculine",
	".notdef", ".notdef", ".notdef", ".notdef",
	".notdef", "ae", ".notdef", ".notdef",
	".notdef", "dotlessi", ".notdef", ".notdef",
	"lslash", "oslash", "oe", "germandbls",
	".notdef", ".notdef", ".notdef", ".notdef"
};

/*
 * Decription of the supported conversions from Unicode
 *
 * SB
 * Yes, I know that the compiled-in conversion is stupid but
 * it is simple to implement and allows not to worry about the
 * filesystem context. After all, the source is always available
 * and adding another language to it is easy.
 *
 * The language name is expected to be the same as the subdirectory name 
 * in the `encodings' directory (for possible future extensions). 
 * The primary use of the aliases is for guessing based on the current 
 * locale.
 */

#define MAXUNIALIAS 10

/* the character used as the language argument separator */
#define LANG_ARG_SEP '+'

/* type of Unicode converter function */
typedef int uni_conv_t(int unival, char *name, char *arg);
/* type of Unicode language initialization function */
typedef void uni_init_t(char *arg);

struct uni_language {
	uni_init_t	*init; /* the initialization function */
	uni_conv_t	*conv; /* the conversion function */
	char *name; /* the language name */
	char *descr; /* description */
	char *alias[MAXUNIALIAS]; /* aliases of the language name */
	int sample_upper; /* code of some uppercase character for correctvsize() */
};

/* the converter routines have an option of adding this suffix to the font name */
static char *uni_font_name_suffix = ""; /* empty by default */
/* this buffer may be used to store the suffix */
#define UNI_MAX_SUFFIX_LEN	100
static char uni_suffix_buf[UNI_MAX_SUFFIX_LEN+1];

/*
 * Prototypes of the conversion routines
 */

/*
 * unival is unicode value to translate
 * name is the glyph name
 * arg is the user-specified language-dependent argument
 *   which can for example select the subfont plane for Eastern fonts.
 *   If none is supplied by user then an empty string ("") is passed.
 *   If no language is specified by user and auto-guessing happens
 *   then NULL is passed.
 */

static uni_conv_t unicode_latin1;
static uni_conv_t unicode_latin2;
static uni_conv_t unicode_latin4;
static uni_conv_t unicode_latin5;
static uni_conv_t unicode_russian;
static uni_conv_t unicode_adobestd;

static uni_init_t unicode_init_user;
static uni_conv_t unicode_user;

/*
 * The order of descriptions is important: if we can't guess the
 * language we just call all the conversion routines in order until
 * we find one that understands this glyph.
 */
static struct uni_language uni_lang[]= {
	/* pseudo-language for all the languages using Latin1 */
	{
		0, /* no init function */
		unicode_latin1, 
		"latin1",
		"works for most of the Western languages",
		{ "en_", "de_", "fr_", "nl_", "no_", "da_", "it_" },
		'A'
	},
	{ /* by Szalay Tamas <tomek@elender.hu> */
		0, /* no init function */
		unicode_latin2, 
		"latin2",
		"works for Central European languages",
		{ "hu_","pl_","cz_","si_","sk_" },
		'A'
	},
	{ /* by Rièardas Èepas <rch@WriteMe.Com> */
		0, /* no init function */
		unicode_latin4, 
		"latin4",
		"works for Baltic languages",
		{ "lt_", "lv_" }, /* doubt about ee_ */
		'A'
	},
	{ /* by Turgut Uyar <uyar@cs.itu.edu.tr> */
		0, /* no init function */
		unicode_latin5, 
		"latin5",
		"for Turkish",
		{ "tr_" },
		'A'
	},
	{
		0, /* no init function */
		unicode_russian,
		"russian",
		"in Windows encoding",
		{ "ru_", "su_" },
		'A'
	},
	{
		0, /* no init function */
		unicode_russian, /* a hack to allow different converters */
		"bulgarian",
		"in Windows encoding",
		{ "bg_" }, /* not sure whether the Bulgarian locale is named this way */
		'A'
	},
	{
		0, /* no init function */
		unicode_adobestd,
		"adobestd",
		"Adobe Standard, expected by TeX",
		{ NULL },
		'A'
	},
#if 0 /* nonfunctional, needs a translation map - here only as example */
	{
		unicode_init_GBK,
		unicode_GBK,
		"GBK",
		"Chinese in GBK encoding",
		{ "zh_CN.GBK" }, /* not sure if it's right */
		0 /* have no idea about capital letters in Chinese */
	},
#endif
};

static uni_conv_t *uni_lang_converter=0; /* 0 means "unknown, try all" */
static int uni_sample='A'; /* sample of an uppercase character */
static char *uni_lang_arg=""; /* user-supplied language-dependent argument */

extern int      runt1asm(int);

/*
 * Bitmap control macros
 */

#define DEF_BITMAP(name, size)	unsigned char name[((size)+7)/8]
#define SET_BITMAP(name, bit)	( name[(bit)/8] |= (1<<((bit)%8)) )
#define CLR_BITMAP(name, bit)	( name[(bit)/8] &= ~(1<<((bit)%8)) )
#define IS_BITMAP(name, bit)	( name[(bit)/8] & (1<<((bit)%8)) )

/*
 * user-defined loadable maps
 */


/* The idea begind buckets is to avoid comparing every code with all 256 codes int table.
 * All the 16-bit unicode space is divided between a number of equal-sized buckets.
 * Initially all the buckets are marked with 0. Then if any code in the bucket is
 * used it's marked with 1. Later during translation we check the code's bucket first
 * and it it's 0 then return failure right away. This may be useful for
 * Chinese fonts with many thousands of glyphs.
 */

#define BUCKET_ID_BITS	11
#define MARK_UNI_BUCKET(unicode) SET_BITMAP(uni_user_buckets, (unicode)>>(16-BUCKET_ID_BITS))
#define IS_UNI_BUCKET(unicode) IS_BITMAP(uni_user_buckets, (unicode)>>(16-BUCKET_ID_BITS))

static DEF_BITMAP(uni_user_buckets, 1<<BUCKET_ID_BITS);

static unsigned short unicode_map[256]; /* font-encoding to unicode map */

static void
unicode_init_user(
		 char *path
)
{
	FILE           *unicode_map_file;
#define UNIBFSZ	256
	char            buffer[UNIBFSZ];
	unsigned        code, unicode, curpos, unicode2;
	char           *arg, *p;
	int             enabled, found;
	int             lineno, cnt, n;
	char            next;

	/* check if we have an argument (plane name) */
	arg = strrchr(path, LANG_ARG_SEP);
	if(arg != 0) {
		*arg++ = 0;
		if( *arg == 0 || strlen(arg) > UNI_MAX_SUFFIX_LEN-1) 
			arg = NULL;
		else {
			sprintf(uni_suffix_buf, "-%s", arg);
			uni_font_name_suffix = uni_suffix_buf;
		}
	} 

	/* now read in the encoding description file, if requested */
	if ((unicode_map_file = fopen(path, "r")) == NULL) {
		fprintf(stderr, "**** Cannot access map file '%s' ****\n", path);
		exit(1);
	}

	if(arg==NULL)
		enabled = found = 1;
	else
		enabled = found = 0;

	lineno=0; curpos=0;
	while (fgets (buffer, UNIBFSZ, unicode_map_file) != NULL) {
		char name[UNIBFSZ];

		lineno++;

		if(sscanf(buffer, "plane %s",&name)==1) {
			if(arg == 0) {
				fprintf(stderr, "**** map file '%s' requires plane name\n", path);
				fprintf(stderr, "for example:\n");
				fprintf(stderr, "  ttf2pt1 -L %s%c%s ...\n", path, LANG_ARG_SEP, name);
				fprintf(stderr, "to select plane '%s'\n", name);
				exit(1);
			}
			if( !strcmp(arg, name) ) {
				enabled = found = 1; 
				curpos = 0;
			} else {
				enabled = 0;
				if(found) /* no need to read further */
					break;
			}
			continue;
		}

		if( !enabled )
			continue; /* skip to the next plane */

		if( sscanf(buffer, "at %i", &curpos) == 1 ) {
			if(curpos > 255) {
				fprintf(stderr, "**** map file '%s' line %d: code over 255\n", path, lineno);
				exit(1);
			}
			if(ISDBG(EXTMAP)) fprintf(stderr, "=== at 0x%x\n", curpos);
			continue;
		}

		/* try the format of Roman Czyborra's files */
		if (sscanf (buffer, " =%x U+%4x", &code, &unicode) == 2) {
			if (code < 256) {
				MARK_UNI_BUCKET(unicode);
				unicode_map[code] = unicode;
				glyph_rename[code] = NULL;
			}
		}
		/* try the format of Linux locale charmap file */
		else if (sscanf (buffer, " <%*s /x%x <U%4x>", &code, &unicode) == 2) {
			if (code < 256) {
				MARK_UNI_BUCKET(unicode);
				unicode_map[code] = unicode;
				glyph_rename[code] = NULL;
			}
		}
		/* try the format with glyph renaming */
		else if (sscanf (buffer, " !%x U+%4x %128s", &code,
			&unicode, name) == 3) {
			if (code < 256) {
				MARK_UNI_BUCKET(unicode);
				unicode_map[code] = unicode;
				glyph_rename[code] = strdup(name);
			}
		}
		/* try the compact sequence format */
		else if( (n=sscanf(buffer, " %i%n", &unicode, &cnt)) == 1 ) {
			p = buffer;
			do {
				if(curpos > 255) {
					fprintf(stderr, "**** map file '%s' line %d: code over 255 for unicode 0x%x\n", 
						path, lineno, unicode);
					exit(1);
				}
				if(ISDBG(EXTMAP)) fprintf(stderr, "=== 0x%d -> 0x%x\n", curpos, unicode);
				MARK_UNI_BUCKET(unicode);
				unicode_map[curpos++] = unicode;
				p += cnt;
				if( sscanf(p, " %[,-]%n", &next,&cnt) == 1 ) {
					if(ISDBG(EXTMAP)) fprintf(stderr, "=== next: '%c'\n", next);
					p += cnt;
					if( next == '-' ) { /* range */
						if ( sscanf(p, " %i%n", &unicode2, &cnt) != 1 ) {
							fprintf(stderr, "**** map file '%s' line %d: missing end of range\n", path, lineno);
							exit(1);
						}
						p += cnt;
						if(ISDBG(EXTMAP)) fprintf(stderr, "=== range 0x%x to 0x%x\n", unicode, unicode2);
						for(unicode++; unicode <= unicode2; unicode++) {
							if(curpos > 255) {
								fprintf(stderr, "**** map file '%s' line %d: code over 255 in unicode range ...-0x%x\n", 
									path, lineno, unicode2);
								exit(1);
							}
							if(ISDBG(EXTMAP)) fprintf(stderr, "=== 0x%x -> 0x%x\n", curpos, unicode);
							MARK_UNI_BUCKET(unicode);
							unicode_map[curpos++] = unicode;
						}
					}
				}
			} while ( sscanf(p, " %i%n", &unicode, &cnt) == 1 );
		}

	}

	fclose (unicode_map_file);

	if( !found ) {
		fprintf(stderr, "**** map file '%s' has no plane '%s'\n", path, arg);
		exit(1);
	}

	if(unicode_map['A'] == 'A')
		uni_sample = 'A'; /* seems to be compatible with Latin */
	else
		uni_sample = 0; /* don't make any assumptions */
}

static int
unicode_user(
		 int unival,
		 char *name,
		 char *arg
)
{
	int res;

	if( ! IS_UNI_BUCKET(unival) )
		return -1;

	for (res = 0; res < 256; res++)
		if (unicode_map[res] == unival)
			return res;
	return -1;
}

static int
unicode_russian(
		 int unival,
		 char *name,
		 char *arg
)
{
	int res;
	static DEF_BITMAP(used, 256);

	if (unival <= 0x0081) {
		SET_BITMAP(used, unival);
		return unival;
	} else if (unival >= 0x0410 && unival < 0x0450) {	/* cyrillic letters */
		res = unival - 0x410 + 0xc0;
		SET_BITMAP(used, res);
		return res;
	} else if (unival >= 0x00a0 && unival <= 0x00bf
	&& unival!=0x00a3 && unival!=0x00b3) {
		SET_BITMAP(used, unival);
		return unival;
	} else {
		switch (unival) {
		case 0x0401:
			SET_BITMAP(used, 0xb3);
			return 0xb3;	/* cyrillic YO */
		case 0x0451:
			SET_BITMAP(used, 0xa3);
			return 0xa3;	/* cyrillic yo */
		}
	}

	/* there are enough broken fonts that pretend to be Latin1 */
	res=unicode_latin1(unival, name, NULL);
	if(res<256 && res>=0 && !IS_BITMAP(used, res))
		return res;
	else
		return -1;
}

static int
unicode_latin1(
		 int unival,
		 char *name,
		 char *arg
)
{
	int i, res;

	if (unival <= 0x007f) {
		return unival;
	} else if (unival >= 0x00a0 && unival <= 0x00ff) {
		return unival;
	} else {
		switch (unival) {
		case 0x008d:
			return 0x8d;
		case 0x017d:
			return 0x8e;
		case 0x008f:
			return 0x8f;
		case 0x0090:
			return 0x90;
		case 0x009d:
			return 0x9d;
		case 0x017e:
			return 0x9e;
		case 0x0152:
			return 0x8c;
		case 0x0153:
			return 0x9c;
		case 0x0160:
			return 0x8a;
		case 0x0161:
			return 0x9a;
		case 0x0178:
			return 0x9f;
		case 0x0192:
			return 0x83;
		case 0x02c6:
			return 0x88;
		case 0x02dc:
			return 0x98;
		case 0x2013:
			return 0x96;
		case 0x2014:
			return 0x97;
		case 0x2018:
			return 0x91;
		case 0x2019:
			return 0x92;
		case 0x201a:
			return 0x82;
		case 0x201c:
			return 0x93;
		case 0x201d:
			return 0x94;
		case 0x201e:
			return 0x84;
		case 0x2020:
			return 0x86;
		case 0x2021:
			return 0x87;
		case 0x2022:
			return 0x95;
		case 0x2026:
			return 0x85;
		case 0x2030:
			return 0x89;
		case 0x2039:
			return 0x8b;
		case 0x203a:
			return 0x9b;
		case 0x2122:
			return 0x99;
		case 0x20ac:
			return 0x80;
		default:
			return -1;
		}
	}
}

/*
 * Not all of the Adobe glyphs are in the Unicode
 * standard mapps, so the font creators have
 * different ideas about their codes. Because
 * of this we try to map based on the glyph
 * names instead of Unicode codes. If there are
 * no glyph names (ps_fmt_3!=0) we fall back
 * to the code-based scheme.
 */

static int
unicode_adobestd(
		 int unival,
		 char *name,
		 char *arg
)
{
	int i, res;
	static unsigned short cvttab[][2]={
		{ 0x2019,  39 }, /* quoteright */
		{ 0x00a1, 161 }, /* exclamdown */
		{ 0x00a2, 162 },
		{ 0x00a3, 163 },
		{ 0x2215, 164 },
		{ 0x00a5, 165 },
		{ 0x0192, 166 },
		{ 0x00a7, 167 },
		{ 0x00a4, 168 }, /* currency */
		{ 0x0027, 169 },
		{ 0x201c, 170 },
		{ 0x00ab, 171 },
		{ 0x2039, 172 },
		{ 0x203a, 173 },
		{ 0xfb01, 174 },
		{ 0xfb02, 175 },
		{ 0x2013, 177 },
		{ 0x2020, 178 },
		{ 0x2021, 179 }, /* daggerdbl */
		{ 0x2219, 180 },
		{ 0x00b6, 182 },
		{ 0x2022, 183 },
		{ 0x201a, 184 },
		{ 0x201e, 185 },
		{ 0x201d, 186 },
		{ 0x00bb, 187 },
		{ 0x2026, 188 },
		{ 0x2030, 189 },
		{ 0x00bf, 191 },
		{ 0x0060, 193 },
		{ 0x00b4, 194 },
		{ 0x02c6, 195 }, /* circumflex */
		{ 0x02dc, 196 },
		{ 0x02c9, 197 },
		{ 0x02d8, 198 },
		{ 0x02d9, 199 },
		{ 0x00a8, 200 },
		{ 0x02da, 202 },
		{ 0x00b8, 203 },
		{ 0x02dd, 205 },
		{ 0x02db, 206 },
		{ 0x02c7, 207 },
		{ 0x2014, 208 },
		{ 0x00c6, 225 }, /* AE */
		{ 0x00aa, 227 },
		{ 0x0141, 232 },
		{ 0x00d8, 233 },
		{ 0x0152, 234 },
		{ 0x00ba, 235 }, /* ordmasculine */
		{ 0x00e6, 241 },
		{ 0x0131, 245 },
		{ 0x0142, 248 },
		{ 0x00f8, 249 },
		{ 0x0153, 250 },
		{ 0x00df, 251 }, 
		{ 0xffff,   0 } /* end of table */
	};

	if(!ps_fmt_3) {
		for(i=32; i<256; i++) {
			if(!strcmp(name, adobe_StandardEncoding[i]))
				return i;
		}
		return -1;
	} else {
		for(i=0; cvttab[i][0]!=0xffff; i++)
			if(cvttab[i][0]==unival)
				return cvttab[i][1];

		/* must be after table check because of 0x0027 */
		if (unival <= 0x007F) {
			return unival;
		} else {
			return -1;
		}
	}
}

static int
unicode_latin2(
		 int unival,
		 char *name,
		 char *arg
)
{
	int i, res;

	if (unival <= 0x007E) {
		return unival;
	} else {
		switch (unival) {
		case 0x00A0:
			return 0xA0;
		case 0x0104:
			return 0xA1;
		case 0x02D8:
			return 0xA2;
		case 0x0141:
			return 0xA3;
		case 0x00A4:
			return 0xA4;
		case 0x013D:
			return 0xA5;
		case 0x015A:
			return 0xA6;
		case 0x00A7:
			return 0xA7;
		case 0x00A8:
			return 0xA8;
		case 0x0160:
			return 0xA9;
		case 0x015E:
			return 0xAA;
		case 0x0164:
			return 0xAB;
		case 0x0179:
			return 0xAC;
		case 0x00AD:
			return 0xAD;
		case 0x017D:
			return 0xAE;
		case 0x017B:
			return 0xAF;
		case 0x00B0:
			return 0xB0;
		case 0x0105:
			return 0xB1;
		case 0x02DB:
			return 0xB2;
		case 0x0142:
			return 0xB3;
		case 0x00B4:
			return 0xB4;
		case 0x013E:
			return 0xB5;
		case 0x015B:
			return 0xB6;
		case 0x02C7:
			return 0xB7;
		case 0x00B8:
			return 0xB8;
		case 0x0161:
			return 0xB9;
		case 0x015F:
			return 0xBA;
		case 0x0165:
			return 0xBB;
		case 0x017A:
			return 0xBC;
		case 0x02DD:
			return 0xBD;
		case 0x017E:
			return 0xBE;
		case 0x017C:
			return 0xBF;
		case 0x0154:
			return 0xC0;
		case 0x00C1:
			return 0xC1;
		case 0x00C2:
			return 0xC2;
		case 0x0102:
			return 0xC3;
		case 0x00C4:
			return 0xC4;
		case 0x0139:
			return 0xC5;
		case 0x0106:
			return 0xC6;
		case 0x00C7:
			return 0xC7;
		case 0x010C:
			return 0xC8;
		case 0x00C9:
			return 0xC9;
		case 0x0118:
			return 0xCA;
		case 0x00CB:
			return 0xCB;
		case 0x011A:
			return 0xCC;
		case 0x00CD:
			return 0xCD;
		case 0x00CE:
			return 0xCE;
		case 0x010E:
			return 0xCF;
		case 0x0110:
			return 0xD0;
		case 0x0143:
			return 0xD1;
		case 0x0147:
			return 0xD2;
		case 0x00D3:
			return 0xD3;
		case 0x00D4:
			return 0xD4;
		case 0x0150:
			return 0xD5;
		case 0x00D6:
			return 0xD6;
		case 0x00D7:
			return 0xD7;
		case 0x0158:
			return 0xD8;
		case 0x016E:
			return 0xD9;
		case 0x00DA:
			return 0xDA;
		case 0x0170:
			return 0xDB;
		case 0x00DC:
			return 0xDC;
		case 0x00DD:
			return 0xDD;
		case 0x0162:
			return 0xDE;
		case 0x00DF:
			return 0xDF;
		case 0x0155:
			return 0xE0;
		case 0x00E1:
			return 0xE1;
		case 0x00E2:
			return 0xE2;
		case 0x0103:
			return 0xE3;
		case 0x00E4:
			return 0xE4;
		case 0x013A:
			return 0xE5;
		case 0x0107:
			return 0xE6;
		case 0x00E7:
			return 0xE7;
		case 0x010D:
			return 0xE8;
		case 0x00E9:
			return 0xE9;
		case 0x0119:
			return 0xEA;
		case 0x00EB:
			return 0xEB;
		case 0x011B:
			return 0xEC;
		case 0x00ED:
			return 0xED;
		case 0x00EE:
			return 0xEE;
		case 0x010F:
			return 0xEF;
		case 0x0111:
			return 0xF0;
		case 0x0144:
			return 0xF1;
		case 0x0148:
			return 0xF2;
		case 0x00F3:
			return 0xF3;
		case 0x00F4:
			return 0xF4;
		case 0x0151:
			return 0xF5;
		case 0x00F6:
			return 0xF6;
		case 0x00F7:
			return 0xF7;
		case 0x0159:
			return 0xF8;
		case 0x016F:
			return 0xF9;
		case 0x00FA:
			return 0xFA;
		case 0x0171:
			return 0xFB;
		case 0x00FC:
			return 0xFC;
		case 0x00FD:
			return 0xFD;
		case 0x0163:
			return 0xFE;
		case 0x02D9:
			return 0xFF;
		default:
			return -1;
		}
	}
}

static int
unicode_latin4(
		 int unival,
		 char *name,
		 char *arg
)
{
	int i, res;

	if (unival <= 0x0081) {
		return unival;
	} else {
		switch (unival) {
		case 0x201e:
			return 0x90; /* these two quotes are a hack only */
		case 0x201c:
			return 0x91; /* these two quotes are a hack only */
		case 0x008d:
			return 0x8d;
		case 0x008e:
			return 0x8e;
		case 0x008f:
			return 0x8f;
		case 0x009d:
			return 0x9d;
		case 0x009e:
			return 0x9e;
		case 0x0152:
			return 0x8c;
		case 0x0153:
			return 0x9c;
		case 0x0178:
			return 0x9f;
		case 0x0192:
			return 0x83;
		case 0x02c6:
			return 0x88;
		case 0x02dc:
			return 0x98;
		case 0x2013:
			return 0x96;
		case 0x2014:
			return 0x97;
		case 0x2019:
			return 0x92;
		case 0x201a:
			return 0x82;
		case 0x201d:
			return 0x94;
		case 0x2020:
			return 0x86;
		case 0x2021:
			return 0x87;
		case 0x2022:
			return 0x95;
		case 0x2026:
			return 0x85;
		case 0x2030:
			return 0x89;
		case 0x2039:
			return 0x8b;
		case 0x203a:
			return 0x9b;
		case 0x2122:
			return 0x99;
			
		case 0x00A0: 
			return 0xA0; /*  NO-BREAK SPACE */
		case 0x0104: 
			return 0xA1; /*  LATIN CAPITAL LETTER A WITH OGONEK */
		case 0x0138: 
			return 0xA2; /*  LATIN SMALL LETTER KRA */
		case 0x0156: 
			return 0xA3; /*  LATIN CAPITAL LETTER R WITH CEDILLA */
		case 0x00A4: 
			return 0xA4; /*  CURRENCY SIGN */
		case 0x0128: 
			return 0xA5; /*  LATIN CAPITAL LETTER I WITH TILDE */
		case 0x013B: 
			return 0xA6; /*  LATIN CAPITAL LETTER L WITH CEDILLA */
		case 0x00A7: 
			return 0xA7; /*  SECTION SIGN */
		case 0x00A8: 
			return 0xA8; /*  DIAERESIS */
		case 0x0160: 
			return 0xA9; /*  LATIN CAPITAL LETTER S WITH CARON */
		case 0x0112: 
			return 0xAA; /*  LATIN CAPITAL LETTER E WITH MACRON */
		case 0x0122: 
			return 0xAB; /*  LATIN CAPITAL LETTER G WITH CEDILLA */
		case 0x0166: 
			return 0xAC; /*  LATIN CAPITAL LETTER T WITH STROKE */
		case 0x00AD: 
			return 0xAD; /*  SOFT HYPHEN */
		case 0x017D: 
			return 0xAE; /*  LATIN CAPITAL LETTER Z WITH CARON */
		case 0x00AF: 
			return 0xAF; /*  MACRON */
		case 0x00B0: 
			return 0xB0; /*  DEGREE SIGN */
		case 0x0105: 
			return 0xB1; /*  LATIN SMALL LETTER A WITH OGONEK */
		case 0x02DB: 
			return 0xB2; /*  OGONEK */
		case 0x0157: 
			return 0xB3; /*  LATIN SMALL LETTER R WITH CEDILLA */
		case 0x00B4: 
			return 0xB4; /*  ACUTE ACCENT */
		case 0x0129: 
			return 0xB5; /*  LATIN SMALL LETTER I WITH TILDE */
		case 0x013C: 
			return 0xB6; /*  LATIN SMALL LETTER L WITH CEDILLA */
		case 0x02C7: 
			return 0xB7; /*  CARON */
		case 0x00B8: 
			return 0xB8; /*  CEDILLA */
		case 0x0161: 
			return 0xB9; /*  LATIN SMALL LETTER S WITH CARON */
		case 0x0113: 
			return 0xBA; /*  LATIN SMALL LETTER E WITH MACRON */
		case 0x0123: 
			return 0xBB; /*  LATIN SMALL LETTER G WITH CEDILLA */
		case 0x0167: 
			return 0xBC; /*  LATIN SMALL LETTER T WITH STROKE */
		case 0x014A: 
			return 0xBD; /*  LATIN CAPITAL LETTER ENG */
		case 0x017E: 
			return 0xBE; /*  LATIN SMALL LETTER Z WITH CARON */
		case 0x014B: 
			return 0xBF; /*  LATIN SMALL LETTER ENG */
		case 0x0100: 
			return 0xC0; /*  LATIN CAPITAL LETTER A WITH MACRON */
		case 0x00C1: 
			return 0xC1; /*  LATIN CAPITAL LETTER A WITH ACUTE */
		case 0x00C2: 
			return 0xC2; /*  LATIN CAPITAL LETTER A WITH CIRCUMFLEX */
		case 0x00C3: 
			return 0xC3; /*  LATIN CAPITAL LETTER A WITH TILDE */
		case 0x00C4: 
			return 0xC4; /*  LATIN CAPITAL LETTER A WITH DIAERESIS */
		case 0x00C5: 
			return 0xC5; /*  LATIN CAPITAL LETTER A WITH RING ABOVE */
		case 0x00C6: 
			return 0xC6; /*  LATIN CAPITAL LIGATURE AE */
		case 0x012E: 
			return 0xC7; /*  LATIN CAPITAL LETTER I WITH OGONEK */
		case 0x010C: 
			return 0xC8; /*  LATIN CAPITAL LETTER C WITH CARON */
		case 0x00C9: 
			return 0xC9; /*  LATIN CAPITAL LETTER E WITH ACUTE */
		case 0x0118: 
			return 0xCA; /*  LATIN CAPITAL LETTER E WITH OGONEK */
		case 0x00CB: 
			return 0xCB; /*  LATIN CAPITAL LETTER E WITH DIAERESIS */
		case 0x0116: 
			return 0xCC; /*  LATIN CAPITAL LETTER E WITH DOT ABOVE */
		case 0x00CD: 
			return 0xCD; /*  LATIN CAPITAL LETTER I WITH ACUTE */
		case 0x00CE: 
			return 0xCE; /*  LATIN CAPITAL LETTER I WITH CIRCUMFLEX */
		case 0x012A: 
			return 0xCF; /*  LATIN CAPITAL LETTER I WITH MACRON */
		case 0x0110: 
			return 0xD0; /*  LATIN CAPITAL LETTER D WITH STROKE */
		case 0x0145: 
			return 0xD1; /*  LATIN CAPITAL LETTER N WITH CEDILLA */
		case 0x014C: 
			return 0xD2; /*  LATIN CAPITAL LETTER O WITH MACRON */
		case 0x0136: 
			return 0xD3; /*  LATIN CAPITAL LETTER K WITH CEDILLA */
		case 0x00D4: 
			return 0xD4; /*  LATIN CAPITAL LETTER O WITH CIRCUMFLEX */
		case 0x00D5: 
			return 0xD5; /*  LATIN CAPITAL LETTER O WITH TILDE */
		case 0x00D6: 
			return 0xD6; /*  LATIN CAPITAL LETTER O WITH DIAERESIS */
		case 0x00D7: 
			return 0xD7; /*  MULTIPLICATION SIGN */
		case 0x00D8: 
			return 0xD8; /*  LATIN CAPITAL LETTER O WITH STROKE */
		case 0x0172: 
			return 0xD9; /*  LATIN CAPITAL LETTER U WITH OGONEK */
		case 0x00DA: 
			return 0xDA; /*  LATIN CAPITAL LETTER U WITH ACUTE */
		case 0x00DB: 
			return 0xDB; /*  LATIN CAPITAL LETTER U WITH CIRCUMFLEX */
		case 0x00DC: 
			return 0xDC; /*  LATIN CAPITAL LETTER U WITH DIAERESIS */
		case 0x0168: 
			return 0xDD; /*  LATIN CAPITAL LETTER U WITH TILDE */
		case 0x016A: 
			return 0xDE; /*  LATIN CAPITAL LETTER U WITH MACRON */
		case 0x00DF: 
			return 0xDF; /*  LATIN SMALL LETTER SHARP S */
		case 0x0101: 
			return 0xE0; /*  LATIN SMALL LETTER A WITH MACRON */
		case 0x00E1: 
			return 0xE1; /*  LATIN SMALL LETTER A WITH ACUTE */
		case 0x00E2: 
			return 0xE2; /*  LATIN SMALL LETTER A WITH CIRCUMFLEX */
		case 0x00E3: 
			return 0xE3; /*  LATIN SMALL LETTER A WITH TILDE */
		case 0x00E4: 
			return 0xE4; /*  LATIN SMALL LETTER A WITH DIAERESIS */
		case 0x00E5: 
			return 0xE5; /*  LATIN SMALL LETTER A WITH RING ABOVE */
		case 0x00E6: 
			return 0xE6; /*  LATIN SMALL LIGATURE AE */
		case 0x012F: 
			return 0xE7; /*  LATIN SMALL LETTER I WITH OGONEK */
		case 0x010D: 
			return 0xE8; /*  LATIN SMALL LETTER C WITH CARON */
		case 0x00E9: 
			return 0xE9; /*  LATIN SMALL LETTER E WITH ACUTE */
		case 0x0119: 
			return 0xEA; /*  LATIN SMALL LETTER E WITH OGONEK */
		case 0x00EB: 
			return 0xEB; /*  LATIN SMALL LETTER E WITH DIAERESIS */
		case 0x0117: 
			return 0xEC; /*  LATIN SMALL LETTER E WITH DOT ABOVE */
		case 0x00ED: 
			return 0xED; /*  LATIN SMALL LETTER I WITH ACUTE */
		case 0x00EE: 
			return 0xEE; /*  LATIN SMALL LETTER I WITH CIRCUMFLEX */
		case 0x012B: 
			return 0xEF; /*  LATIN SMALL LETTER I WITH MACRON */
		case 0x0111: 
			return 0xF0; /*  LATIN SMALL LETTER D WITH STROKE */
		case 0x0146: 
			return 0xF1; /*  LATIN SMALL LETTER N WITH CEDILLA */
		case 0x014D: 
			return 0xF2; /*  LATIN SMALL LETTER O WITH MACRON */
		case 0x0137: 
			return 0xF3; /*  LATIN SMALL LETTER K WITH CEDILLA */
		case 0x00F4: 
			return 0xF4; /*  LATIN SMALL LETTER O WITH CIRCUMFLEX */
		case 0x00F5: 
			return 0xF5; /*  LATIN SMALL LETTER O WITH TILDE */
		case 0x00F6: 
			return 0xF6; /*  LATIN SMALL LETTER O WITH DIAERESIS */
		case 0x00F7: 
			return 0xF7; /*  DIVISION SIGN */
		case 0x00F8: 
			return 0xF8; /*  LATIN SMALL LETTER O WITH STROKE */
		case 0x0173: 
			return 0xF9; /*  LATIN SMALL LETTER U WITH OGONEK */
		case 0x00FA: 
			return 0xFA; /*  LATIN SMALL LETTER U WITH ACUTE */
		case 0x00FB: 
			return 0xFB; /*  LATIN SMALL LETTER U WITH CIRCUMFLEX */
		case 0x00FC: 
			return 0xFC; /*  LATIN SMALL LETTER U WITH DIAERESIS */
		case 0x0169: 
			return 0xFD; /*  LATIN SMALL LETTER U WITH TILDE */
		case 0x016B: 
			return 0xFE; /*  LATIN SMALL LETTER U WITH MACRON */
		case 0x02D9: 
			return 0xFF; /*  DOT ABOVE */
			
			
		default:
			return -1;
		}
	}
}

static int
unicode_latin5(
		 int unival,
		 char *name,
		 char *arg
)
{
	int i, res;

	if (unival <= 0x0081) {
		return unival;
	} else if (unival >= 0x00a0 && unival <= 0x00ff) {
		return unival;
	} else {
		switch (unival) {
		case 0x008d:
			return 0x8d;
		case 0x008e:
			return 0x8e;
		case 0x008f:
			return 0x8f;
		case 0x0090:
			return 0x90;
		case 0x009d:
			return 0x9d;
		case 0x009e:
			return 0x9e;
		case 0x011e:
			return 0xd0;	/* G breve */
		case 0x011f:
			return 0xf0;	/* g breve */
		case 0x0130:
			return 0xdd;	/* I dot */
		case 0x0131:
			return 0xfd;	/* dotless i */
		case 0x0152:
			return 0x8c;
		case 0x0153:
			return 0x9c;
		case 0x015e:
			return 0xde;	/* S cedilla */
		case 0x015f:
			return 0xfe;	/* s cedilla */
		case 0x0160:
			return 0x8a;
		case 0x0161:
			return 0x9a;
		case 0x0178:
			return 0x9f;
		case 0x0192:
			return 0x83;
		case 0x02c6:
			return 0x88;
		case 0x02dc:
			return 0x98;
		case 0x2013:
			return 0x96;
		case 0x2014:
			return 0x97;
		case 0x2018:
			return 0x91;
		case 0x2019:
			return 0x92;
		case 0x201a:
			return 0x82;
		case 0x201c:
			return 0x93;
		case 0x201d:
			return 0x94;
		case 0x201e:
			return 0x84;
		case 0x2020:
			return 0x86;
		case 0x2021:
			return 0x87;
		case 0x2022:
			return 0x95;
		case 0x2026:
			return 0x85;
		case 0x2030:
			return 0x89;
		case 0x2039:
			return 0x8b;
		case 0x203a:
			return 0x9b;
		case 0x2122:
			return 0x99;
		default:
			return -1;
		}
	}
}

#if 0
/* non-functional now, shown as example */
static int GBK_plane;

static void
unicode_init_GBK(
		 char *arg
)
{
	int res;

	if(sscanf(arg, "%x", &GBK_plane) < 1 || GBK_plane < 0x81 || GBK_plane > 0xFE) {
		fprintf(stderr, "**** language Chinese GBK requires argument of plane, 81 to FE (hexadecimal)\n");
		fprintf(stderr, "for example\n");
		fprintf(stderr, "  ttf2pt1 -l GBK%c81\n", LANG_ARG_SEP);
		fprintf(stderr, "to select plane 81\n");
		exit(1);
	}

	/* not snprintf() for reasons of compatibility with old systems */
	sprintf(uni_suffix_buf, "-%02x", GBK_plane);
	uni_font_name_suffix = uni_suffix_buf;

	GBK_plane <<= 8;
}

/* non-functional now, shown as example */
static int
unicode_GBK(
		 int unival,
		 char *name,
		 char *arg
)
{
	static int map[1]={0};
	int res;

	if(arg==0) /* just probing - never answer */
		return -1;

	if(unival >= sizeof map)
		return -1;

	res = map[unival];
	if((res & 0xFF00) == GBK_plane)
		return res & 0xFF;
	else
		return -1;
}
#endif /* 0 */

int
unicode_to_win31(
		 int unival,
		 char *name
)
{
	int i, res;
	static unsigned char used[256];

	if(unival<0) {
		fprintf(stderr,"**** Internal error: unicode value < 0 ****\n");
		exit(1);
	}

	/* know the language */
	if(uni_lang_converter!=0)
		return (*uni_lang_converter)(unival, name, uni_lang_arg);

	/* don't know the language, try all */
	for(i=0; i < sizeof uni_lang/sizeof(struct uni_language); i++) {
		res=(*uni_lang[i].conv)(unival, name, NULL);
		if(res == -1)
			continue;
		if(res & ~0xff) {
			fprintf(stderr,"**** Internal error: broken unicode conversion ****\n");
			fprintf(stderr,"**** language '%s' code 0x%04x ****\n", 
				uni_lang[i].name, unival);
			exit(1);
		}
		/* make sure that the priority is in the order of the language list */
		if(used[res]>i)
			return -1;
		else {
			used[res]=250-i;
			return res;
		}
	}

	return -1;
}

/*
 * Scale the values according to the scale_factor
 */

double
fscale(
      double val
)
{
	return scale_factor * val;
}

int
iscale(
      int val
)
{
	return (int) (val > 0 ? scale_factor * val + 0.5
		      : scale_factor * val - 0.5);
}

/*
 * Try to force fixed width of characters
 */

static void
alignwidths(void)
{
	int             i;
	int             n = 0, avg, max = 0, min = 3000, sum = 0, x;

	for (i = 0; i < numglyphs; i++) {
		if (glyph_list[i].flags & GF_USED) {
			x = glyph_list[i].width;

			if (x != 0) {
				if (x < min)
					min = x;
				if (x > max)
					max = x;

				sum += x;
				n++;
			}
		}
	}

	if (n == 0)
		return;

	avg = sum / n;

	WARNING_3 fprintf(stderr, "widths: max=%d avg=%d min=%d\n", max, avg, min);

	/* if less than 5% variation from average */
	/* force fixed width */
	if (20 * (avg - min) < avg && 20 * (max - avg) < avg) {
		for (i = 0; i < numglyphs; i++) {
			if (glyph_list[i].flags & GF_USED)
				glyph_list[i].width = avg;
		}
		fontm.is_fixed_pitch = 1;
	}
}

static void
convert_glyf(
	int	glyphno
)
{
	GLYPH          *g;

	g = &glyph_list[glyphno];


	g->scaledwidth = iscale(g->width);

	g->entries = 0;
	g->lastentry = 0;
	g->path = 0;
	if (g->ttf_pathlen != 0) {
		ncurves = cursw->glpath(glyphno, glyph_list);
		assertpath(g->entries, __FILE__, __LINE__, g->name);

		fclosepaths(g);
		assertpath(g->entries, __FILE__, __LINE__, g->name);

		/* float processing */
		if(smooth) {
			ffixquadrants(g);
			assertpath(g->entries, __FILE__, __LINE__, g->name);
		}

		pathtoint(g); 
		/* all processing past this point expects integer path */
		assertpath(g->entries, __FILE__, __LINE__, g->name);

#if 0
		fixcontours(g);
		testfixcvdir(g);
#endif

		/* int processing */
		if (smooth) {
			smoothjoints(g);
			assertpath(g->entries, __FILE__, __LINE__, g->name);

			straighten(g, 1);
			assertpath(g->entries, __FILE__, __LINE__, g->name);

			splitzigzags(g);
			assertpath(g->entries, __FILE__, __LINE__, g->name);

			forceconcise(g);
			assertpath(g->entries, __FILE__, __LINE__, g->name);

			straighten(g, 0);
			assertpath(g->entries, __FILE__, __LINE__, g->name);

			smoothjoints(g);
			assertpath(g->entries, __FILE__, __LINE__, g->name);

			flattencurves(g);
		}

		/* XXX we have to count curves _after_ processing, not before */
		if (ncurves > 100) {
			WARNING_2 fprintf(stderr,
			"** Glyph %s is too long, may display incorrectly\n",
				g->name);
		}
	}
}

static void
handle_gnames(void)
{
	int             i, n, found;

	/* get the names from the font file */
	ps_fmt_3 = cursw->glnames(glyph_list);

	/* check for names with wrong characters */
	for (n = 0; n < numglyphs; n++) {
		int             c;
		for (i = 0; (c = glyph_list[n].name[i]) != 0; i++) {
			if (!(isalnum(c) || c == '.' || c == '_' ) 
			|| i==0 && isdigit(c)) { /* must not start with a digit */
				WARNING_3 fprintf(stderr, "Glyph %d %s (%s), ",
					n, isdigit(c) ? "name starts with a digit" : 
						"has bad characters in name",
					glyph_list[n].name);
				glyph_list[n].name = malloc(10);
				sprintf(glyph_list[n].name, "_%d", n);
				WARNING_3 fprintf(stderr, "changing to %s\n", glyph_list[n].name);
				break;
			}
		}
	}

	if( !ps_fmt_3 ) {
		for (n = 0; n < numglyphs; n++) {
			found = 0;
			for (i = 0; i < n && !found; i++) {
				if (strcmp(glyph_list[i].name, glyph_list[n].name) == 0) {
					glyph_list[n].name = malloc(10);
					sprintf(glyph_list[n].name, "_%d", n);
					WARNING_3 fprintf(stderr,
						"Glyph %d has the same name as %d: (%s), changing to %s\n",
						n, i,
						glyph_list[i].name,
						glyph_list[n].name);
					found = 1;
				}
			}
		}
	}

	/* ignore the return code for now */
	cursw->glenc(glyph_list, encoding);

	if (ps_fmt_3 == 1) {
		for (i = 0; i < 256; i++) {
			if (encoding[i] != 0) {
				glyph_list[encoding[i]].name = Fmt3Encoding[i];
			} else {
				glyph_list[encoding[i]].name = ".notdef";
			}
		}
	}

	/* enforce two special cases defined in TTF manual */
	if(numglyphs > 0)
		glyph_list[0].name = ".notdef";
	if(numglyphs > 1)
		glyph_list[1].name = ".null";

 	for (i = 0; i < 256; i++) {
 		if ((encoding[i] != 0) && glyph_rename[i]) {
 		    glyph_list[encoding[i]].name = glyph_rename[i];
 		}
 	}
 	
}

static void
usage(void)
{
	int i;

#ifdef _GNU_SOURCE
#	define fplop(txt)	fputs(txt, stderr);
#else
#	define fplop(txt)
#endif

	fputs("Use:\n", stderr);
	fputs("ttf2pt1 [-<opts>] [-l language | -L file] <ttf-file> <fontname>\n", stderr);
	fputs("  or\n", stderr);
	fputs("ttf2pt1 [-<opts>] [-l language | -L file] <ttf-file> -\n", stderr);
	fputs("  or\n", stderr);
	fputs("ttf2pt1 [-<opts>] [-l language | -L file] <ttf-file> - | t1asm > <pfa-file>\n", stderr);

	fplop("\n");
	fplop("This build supports both short and long option names,\n");
	fplop("the long options are listed before corresponding short ones\n");

	fplop(" --afm\n");
	fputs("  -A - write the .afm file to STDOUT instead of the font itself\n", stderr);
	fplop(" --allglyphs\n");
	fputs("  -a - include all glyphs, even those  not in the encoding table\n", stderr);
	fplop(" --pfb\n");
	fputs("  -b - produce a compressed .pfb file\n", stderr);
	fplop(" --debug dbg_suboptions\n");
	fputs("  -d dbg_suboptions - debugging options, run ttf2pt1 -d? for help\n", stderr);
	fplop(" --encode\n");
	fputs("  -e - produce a fully encoded .pfa file\n", stderr);
	fplop(" --forceunicode\n");
	fputs("  -F - force use of Unicode encoding even if other MS encoding detected\n", stderr); 
	fplop(" --language language\n");
	fputs("  -l language - convert Unicode to specified language, run ttf2pt1 -l? for list\n", stderr);
	fplop(" --languagemap file\n");
	fputs("  -L file - convert Unicode according to encoding description file\n", stderr);
	fplop(" --limit <type>=<value>\n");
	fputs("  -m <type>=<value> - set maximal limit of given type to value, types:\n", stderr);
	fputs("      h - maximal hint stack depth in the PostScript interpreter\n", stderr);
	fplop(" --processing suboptions\n");
	fputs("  -O suboptions - control outline processing, run ttf2pt1 -O? for help\n", stderr);
	fplop(" --parser name\n");
	fputs("  -p name - use specific front-end parser, run ttf2pt1 -p? for list\n", stderr);
	fplop(" --uid id\n");
	fputs("  -u id - use this UniqueID, -u A means autogeneration\n", stderr);
	fplop(" --vscale size\n");
	fputs("  -v size - scale the font to make uppercase letters >size/1000 high\n", stderr);
	fplop(" --version\n");
	fputs("  -V - print ttf2pt1 version number\n", stderr);
	fplop(" --warning number\n");
	fputs("  -W number - set the level of permitted warnings (0 - disable)\n", stderr);
	fputs("Obsolete options (will be removed in future releases, use -O? instead):\n", stderr);
	fputs("  -f - don't try to guess the value of the ForceBold hint\n", stderr);
	fputs("  -h - disable autogeneration of hints\n", stderr);
	fputs("  -H - disable hint substitution\n", stderr);
	fputs("  -o - disable outline optimization\n", stderr);
	fputs("  -s - disable outline smoothing\n", stderr);
	fputs("  -t - disable auto-scaling to 1000x1000 standard matrix\n", stderr);
	fputs("  -w - correct the glyph widths (use only for buggy fonts)\n", stderr);
	fputs("The last '-' means 'use STDOUT'.\n", stderr);

#undef fplop

}

static void
printversion(void)
{
  fprintf(stderr, "ttf2pt1 %s\n", TTF2PT1_VERSION);
}
  
main(
     int argc,
     char **argv
)
{
	int             i, j;
	time_t          now;
	char            filename[256];
	int             c,nchars,nmetrics;
	int             ws;
	int             forcebold= -1; /* -1 means "don't know" */
	char           *lang;
	int             oc;
	int             subid;
#ifdef _GNU_SOURCE
#	define ttf2pt1_getopt(a, b, c, d, e)	getopt_long(a, b, c, d, e)
	static struct option longopts[] = {
		{ "afm", 0, NULL, 'A' },
		{ "allglyphs", 0, NULL, 'a' },
		{ "pfb", 0, NULL, 'b' },
		{ "debug", 1, NULL, 'd' },
		{ "encode", 0, NULL, 'e' },
		{ "forceunicode", 0, NULL, 'F' },
		{ "language", 1, NULL, 'l' },
		{ "languagemap", 1, NULL, 'L' },
		{ "limit", 1, NULL, 'm' },
		{ "processing", 1, NULL, 'O' },
		{ "parser", 1, NULL, 'p' },
		{ "uid", 1, NULL, 'u' },
		{ "vscale", 1, NULL, 'v' },
		{ "version", 0, NULL, 'V' },
		{ "warning", 1, NULL, 'W' },
		{ NULL, 0, NULL, 0 }
	};
#else
#	define ttf2pt1_getopt(a, b, c, d, e)	getopt(a, b, c)
#endif

	/* initialize sub-options of -O */
	for(i=0; i< (sizeof opotbl)/(sizeof opotbl[0]); i++) {
		opotbl[i].disbl = tolower(opotbl[i].disbl);
		opotbl[i].enbl = toupper(opotbl[i].disbl);
		*(opotbl[i].valp) = opotbl[i].dflt;
	}

	while(( oc=ttf2pt1_getopt(argc, argv, "FaoebAsthHfwVv:p:l:d:u:L:m:W:O:",
			longopts, NULL) )!= -1) {
		switch(oc) {
		case 'W':
			if(sscanf(optarg, "%d", &warnlevel) < 1 || warnlevel < 0) {
				fprintf(stderr, "**** warning level must be a positive number\n");
				exit(1);
			}
			break;
		case 'F':
			forceunicode = 1;
			break;
		case 'o':
			fputs("Warning: option -o is obsolete, use -Oo instead\n", stderr);
			optimize = 0;
			break;
		case 'e':
			encode = 1;
			break;
		case 'b':
			encode = pfbflag = 1;
			break;
		case 'A':
			wantafm = 1;
			break;
		case 'a':
			allglyphs = 1;
			break;
		case 's':
			fputs("Warning: option -s is obsolete, use -Os instead\n", stderr);
			smooth = 0;
			break;
		case 't':
			fputs("Warning: option -t is obsolete, use -Ot instead\n", stderr);
			transform = 0;
			break;
		case 'd':
			for(i=0; optarg[i]!=0; i++)
				switch(optarg[i]) {
				case 'a':
					absolute = 1;
					break;
				case 'r':
					reverse = 0;
					break;
				default:
					if (optarg[i] != '?')
					  fprintf(stderr, "**** Unknown debugging option '%c' ****\n", optarg[i]);
					fputs("The recognized debugging options are:\n", stderr);
					fputs("  a - enable absolute coordinates\n", stderr);
					fputs("  r - do not reverse font outlines directions\n", stderr);
					exit(1);
					break;
				};
			break;
		case 'm':
		{
			char subopt;
			int val;

			if(sscanf(optarg, "%c=%d", &subopt, &val) !=2) {
				fprintf(stderr, "**** Misformatted maximal limit ****\n");
				fprintf(stderr, "spaces around the equal sign are not allowed\n");
				fprintf(stderr, "good examples: -mh=100 -m h=100\n");
				fprintf(stderr, "bad examples: -mh = 100 -mh= 100\n");
				exit(1);
				break;
			}
			switch(subopt) {
			case 'h':
				max_stemdepth = val;
				break;
			default:
				if (subopt != '?')
				  fprintf(stderr, "**** Unknown limit type '%c' ****\n", subopt);
				fputs("The recognized limit types are:\n", stderr);
				fputs("  h - maximal hint stack depth in the PostScript interpreter\n", stderr);
				exit(1);
				break;
			}
			break;
		}
		case 'O':
		{
			char subopt;
			char *p;
			char dflt[20]; /* should be big enough */
			for(p=optarg; (subopt = *p) != 0; p++) {
				for(i=0; i< (sizeof opotbl)/(sizeof opotbl[0]); i++) {
					if(subopt == opotbl[i].disbl) {
						*(opotbl[i].valp) = 0;
						break;
					} else if(subopt == opotbl[i].enbl) {
						*(opotbl[i].valp) = 1;
						break;
					} 
				}
				if( i == (sizeof opotbl)/(sizeof opotbl[0]) ) { /* found no match */
					if (subopt != '?')
						fprintf(stderr, "**** Unknown outline processing suboption '%c' ****\n", subopt);
					fprintf(stderr,"The general form of the outline processing option is:\n");
					fprintf(stderr,"   -O suboptions\n");
					fprintf(stderr,"(To remember easily -O may be also thought of as \"optimization\").\n");
					fprintf(stderr,"The lowercase suboptions disable features, corresponding\n");
					fprintf(stderr,"uppercase suboptions enable them. The supported suboptions,\n");
					fprintf(stderr,"their default states and the features they control are:\n");
					p = dflt;
					for(i=0; i< (sizeof opotbl)/(sizeof opotbl[0]); i++) {
						fprintf(stderr,"   %c/%c - [%s] %s\n", opotbl[i].disbl, opotbl[i].enbl,
							opotbl[i].dflt ? "enabled" : "disabled", opotbl[i].descr);
						if(opotbl[i].dflt)
							*p++ = opotbl[i].enbl;
						else
							*p++ = opotbl[i].disbl;
					}
					*p = 0;
					fprintf(stderr, "The default state corresponds to the option -O %s\n", dflt);
					exit(1);
				}
			}
			break;
		}
		case 'h':
			fputs("Warning: option -h is obsolete, use -Oh instead\n", stderr);
			hints = 0;
			break;
		case 'H':
			fputs("Warning: meaning of option -H has been changed to its opposite\n", stderr);
			fputs("Warning: option -H is obsolete, use -Ou instead\n", stderr);
			subhints = 0;
			break;
		case 'f':
			fputs("Warning: option -f is obsolete, use -Ob instead\n", stderr);
			trybold = 0;
			break;
		case 'w':
			fputs("Warning: option -w is obsolete, use -OW instead\n", stderr);
			correctwidth = 1;
			break;
		case 'u':
			if(wantuid) {
				fprintf(stderr, "**** UniqueID may be specified only once ****\n");
				exit(1);
			}
			wantuid = 1; 
			if(optarg[0]=='A' && optarg[1]==0)
				strUID=0; /* will be generated automatically */
			else {
				strUID=optarg;
				for(i=0; optarg[i]!=0; i++)
					if( !isdigit(optarg[i]) ) {
						fprintf(stderr, "**** UniqueID must be numeric or A for automatic ****\n");
						exit(1);
					}
			}
			break;
		case 'v':
			correctvsize = atoi(optarg);
			if(correctvsize <= 0 && correctvsize > 1000) {
				fprintf(stderr, "**** wrong vsize '%d', ignored ****\n", correctvsize);
				correctvsize=0;
			}
			break;
		case 'p':
			if(cursw!=0) {
				fprintf(stderr, "**** only one front-end parser be used ****\n");
				exit(1);
			}

			{ /* separate parser from parser-specific argument */
				char *p = strchr(optarg, LANG_ARG_SEP);
				if(p != 0) {
					*p = 0;
					front_arg = p+1;
				} else
					front_arg = "";
			}
			for(i=0; frontswtab[i] != NULL; i++)
				if( !strcmp(frontswtab[i]->name, optarg) ) {
					cursw = frontswtab[i];
					break;
				}

			if(cursw==0) {
				if (strcmp(optarg, "?"))
				  fprintf(stderr, "**** unknown front-end parser '%s' ****\n", optarg);
				fputs("the following front-ends are supported now:\n", stderr);
				for(i=0; frontswtab[i] != NULL; i++) {
					fprintf(stderr,"  %s (%s)\n   file suffixes: ", 
						frontswtab[i]->name,
						frontswtab[i]->descr ? frontswtab[i]->descr : "no description"
					);
					for(j=0; j<MAXSUFFIX; j++)
						if(frontswtab[i]->suffix[j])
							fprintf(stderr, "%s ", frontswtab[i]->suffix[j]);
					fprintf(stderr, "\n");
				}
				exit(1);
			}
			break;
		case 'l':
			if(uni_lang_converter!=0) {
				fprintf(stderr, "**** only one language option may be used ****\n");
				exit(1);
			}

			{ /* separate language from language-specific argument */
				char *p = strchr(optarg, LANG_ARG_SEP);
				if(p != 0) {
					*p = 0;
					uni_lang_arg = p+1;
				} else
					uni_lang_arg = "";
			}
			for(i=0; i < sizeof uni_lang/(sizeof uni_lang[0]); i++)
				if( !strcmp(uni_lang[i].name, optarg) ) {
					uni_lang_converter=uni_lang[i].conv;
					uni_sample=uni_lang[i].sample_upper;
					if(uni_lang[i].init != 0)
						uni_lang[i].init(uni_lang_arg);
					break;
				}

			if(uni_lang_converter==0) {
				if (strcmp(optarg, "?"))
				  fprintf(stderr, "**** unknown language '%s' ****\n", optarg);
				fputs("       the following languages are supported now:\n", stderr);
				for(i=0; i < sizeof uni_lang/(sizeof uni_lang[0]); i++)
					fprintf(stderr,"         %s (%s)\n", 
						uni_lang[i].name,
						uni_lang[i].descr ? uni_lang[i].descr : "no description"
					);
				exit(1);
			}
			break;
		case 'L':
			if(uni_lang_converter!=0) {
				fprintf(stderr, "**** only one language option may be used ****\n");
				exit(1);
			}
			uni_lang_converter = unicode_user;
			unicode_init_user(optarg);
			break;
		case 'V':
			printversion();
			exit(0);
			break;
		default:
			usage();
			exit(1);
			break;
		}
	}
	argc-=optind-1; /* the rest of code counts from argv[0] */
	argv+=optind-1;

	if (absolute && encode) {
		fprintf(stderr, "**** options -a and -e are incompatible ****\n");
		exit(1);
	}
	if (argc != 3) {
		usage();
		exit(1);
	}

	/* try to guess the language by the locale used */
	if(uni_lang_converter==0 && (lang=getenv("LANG"))!=0 ) {
		for(i=0; i < sizeof uni_lang/sizeof(struct uni_language); i++) {
			if( !strncmp(uni_lang[i].name, lang, strlen(uni_lang[i].name)) ) {
				uni_lang_converter=uni_lang[i].conv;
				goto got_a_language;
			}
		}
		/* no full name ? try aliases */
		for(i=0; i < sizeof uni_lang/sizeof(struct uni_language); i++) {
			for(c=0; c<MAXUNIALIAS; c++)
				if( uni_lang[i].alias[c]!=0
				&& !strncmp(uni_lang[i].alias[c], lang, strlen(uni_lang[i].alias[c])) ) {
					uni_lang_converter=uni_lang[i].conv;
					goto got_a_language;
				}
		}
	got_a_language:
		if(uni_lang_converter!=0) 
			WARNING_1 fprintf(stderr, "Using language '%s' for Unicode fonts\n", uni_lang[i].name);
	}

	/* try to guess the front-end parser by the file name suffix */
	if(cursw==0) {
		char *p = strrchr(argv[1], '.');

		if(p!=0) {
			p++;
			for(i=0; frontswtab[i] != 0 && cursw == 0; i++) {
				for(j=0; j<MAXSUFFIX; j++)
					if(frontswtab[i]->suffix[j]
					&& !strcmp(p, frontswtab[i]->suffix[j]) ) {
						cursw = frontswtab[i];
						WARNING_1 fprintf(stderr, "Auto-detected front-end parser '%s'\n", 
							cursw->name);
						WARNING_1 fprintf(stderr, " (use ttf2pt1 -p? to get the full list of available front-ends)\n");
						break;
					}
			}
		}

		if(cursw==0) {
			cursw = frontswtab[0];
			WARNING_1 fprintf(stderr, "Can't detect front-end parser, using '%s' by default\n", 
				cursw->name);
			WARNING_1 fprintf(stderr, " (use ttf2pt1 -p? to get the full list of available front-ends)\n");
		}
	}

	/* open the input file */
	cursw->open(argv[1], front_arg);

	if (argv[2][0] == '-' && argv[2][1] == 0) {
		pfa_file = stdout;
#ifndef WINDOWS
		if ((afm_file = fopen("/dev/null", "w+")) == NULL) {
#else /* WINDOWS */
		if(encode) {
			fprintf(stderr, "**** can't write encoded file to stdout ***\n");
			exit(1);
		}
		if ((afm_file = fopen("NUL", "w+")) == NULL) {
#endif /* WINDOWS */
			fprintf(stderr, "**** Cannot open /dev/null ****\n");
			exit(1);
		}
		if(wantafm) { /* print .afm instead of .pfa */
			FILE *n;
			n=pfa_file;
			pfa_file=afm_file;
			afm_file=n;
		}
	} else {
#ifndef WINDOWS
		sprintf(filename, "%s.%s", argv[2], encode ? (pfbflag ? "pfb" : "pfa") : "t1a" );
#else /* WINDOWS */
		sprintf(filename, "%s.t1a", argv[2]);
#endif /* WINDOWS */
		if ((pfa_file = fopen(filename, "w+b")) == NULL) {
			fprintf(stderr, "**** Cannot create %s ****\n", filename);
			exit(1);
		} else {
			WARNING_2 fprintf(stderr, "Creating file %s\n", filename);
		}

		sprintf(filename, "%s.afm", argv[2]) ;
		if ((afm_file = fopen(filename, "w+")) == NULL) {
			fprintf(stderr, "**** Cannot create %s ****\n", filename);
			exit(1);
		}
	}

	/*
	 * Now check whether we want a fully encoded .pfa file
	 */
#ifndef WINDOWS
	if (encode) {
		int             p[2];
		extern FILE    *ifp, *ofp;	/* from t1asm.c */

		ifp=stdin;
		ofp=stdout;

		if (pipe(p) < 0) {
			perror("**** Cannot create pipe ****\n");
			exit(1);
		}
		ofp = pfa_file;
		ifp = fdopen(p[0], "r");
		if (ifp == NULL) {
			perror("**** Cannot use pipe for reading ****\n");
			exit(1);
		}
		pfa_file = fdopen(p[1], "w");
		if (pfa_file == NULL) {
			perror("**** Cannot use pipe for writing ****\n");
			exit(1);
		}
		switch (fork()) {
		case -1:
			perror("**** Cannot fork the assembler process ****\n");
			exit(1);
		case 0:	/* child */
			fclose(pfa_file);
			exit(runt1asm(pfbflag));
		}
	}
#endif /* WINDOWS */

	numglyphs = cursw->nglyphs();

	WARNING_3 fprintf(stderr, "numglyphs = %d\n", numglyphs);

	glyph_list = (GLYPH *) calloc(numglyphs,  sizeof(GLYPH));

	for (i = 0; i < numglyphs; i++) {
		glyph_list[i].char_no = -1;
		glyph_list[i].orig_code = -1;
		glyph_list[i].name = "UNKNOWN";
		glyph_list[i].flags = GF_FLOAT; /* we start with float representation */
	}

	handle_gnames();

	cursw->glmetrics(glyph_list);
	cursw->fnmetrics(&fontm);
 
	original_scale_factor = 1000.0 / (double) fontm.units_per_em;

	if(transform == 0)
		scale_factor = 1.0; /* don't transform */
	else
		scale_factor = original_scale_factor;

	if(correctvsize && uni_sample!=0) { /* only for known languages */
		/* try to adjust the scale factor to make a typical
		 * uppercase character of hight at least (correctvsize), this
		 * may improve the appearance of the font but also
		 * make it weird, use with caution
		 */
		int ysz;

		ysz = iscale(glyph_list[encoding[uni_sample]].yMax);
		if( ysz<correctvsize ) {
			scale_factor *= (double)correctvsize / ysz;
		}
	}

	if(allglyphs) {
		for (i = 0; i < numglyphs; i++) {
			glyph_list[i].flags |= GF_USED;
		}
	} else {
		for (i = 0; i < 256; i++) {
			glyph_list[encoding[i]].flags |= GF_USED;
		}

		/* also always include .notdef */
		for (i = 0; i < numglyphs; i++) 
			if(!strcmp(glyph_list[i].name, ".notdef")) {
				glyph_list[i].flags |= GF_USED;
				break;
			}
	}

	for (i = 0; i < numglyphs; i++) {
		if (glyph_list[i].flags & GF_USED) {
			DBG_TO_GLYPH(&glyph_list[i]);
			convert_glyf(i);
			DBG_FROM_GLYPH(&glyph_list[i]);
		}
	}

	italic_angle = fontm.italic_angle;

	if (italic_angle > 45.0 || italic_angle < -45.0)
		italic_angle = 0.0;	/* consider buggy */

	if (hints) {
		findblues();
		for (i = 0; i < numglyphs; i++) {
			if (glyph_list[i].flags & GF_USED) {
				DBG_TO_GLYPH(&glyph_list[i]);
				buildstems(&glyph_list[i]);
				assertpath(glyph_list[i].entries, __FILE__, __LINE__, glyph_list[i].name);
				DBG_FROM_GLYPH(&glyph_list[i]);
			}
		}
		stemstatistics();
	} else {
		for(i=0; i<4; i++)
			bbox[i] = iscale(fontm.bbox[i]);
	}
	/* don't touch the width of fixed width fonts */
	if( fontm.is_fixed_pitch )
		correctwidth=0;
	docorrectwidth(); /* checks correctwidth inside */
	if (reverse)
		for (i = 0; i < numglyphs; i++) {
			if (glyph_list[i].flags & GF_USED) {
				DBG_TO_GLYPH(&glyph_list[i]);
				reversepaths(&glyph_list[i]);
				assertpath(glyph_list[i].entries, __FILE__, __LINE__, glyph_list[i].name);
				DBG_FROM_GLYPH(&glyph_list[i]);
			}
		}


#if 0
	/*
	** It seems to bring troubles. The problem is that some
	** styles of the font may be recognized as fixed-width
	** while other styles of the same font as proportional.
	** So it's better to be commented out yet.
	*/
	if (tryfixed) 
		alignwidths();
#endif

	if(trybold) {
		forcebold = fontm.force_bold;
	}

	fprintf(pfa_file, "%%!PS-AdobeFont-1.0: %s %s\n", fontm.name_ps, fontm.name_copyright);
	time(&now);
	fprintf(pfa_file, "%%%%CreationDate: %s", ctime(&now));
	fprintf(pfa_file, "%% Converted from TrueType font %s by ttf2pt1 %s\n%%\n", argv[1], TTF2PT1_VERSION);
	fprintf(pfa_file, "%%%%EndComments\n");
	fprintf(pfa_file, "12 dict begin\n/FontInfo 9 dict dup begin\n");

	WARNING_3 fprintf(stderr, "FontName %s%s\n", fontm.name_ps, uni_font_name_suffix);


	fprintf(pfa_file, "/version (%s) readonly def\n", fontm.name_version);

	fprintf(pfa_file, "/Notice (%s) readonly def\n", fontm.name_copyright);

	fprintf(pfa_file, "/FullName (%s) readonly def\n", fontm.name_full);
	fprintf(pfa_file, "/FamilyName (%s) readonly def\n", fontm.name_family);

	if(wantuid) {
		if(strUID)
			fprintf(pfa_file, "/UniqueID %s def\n", strUID);
		else {
			numUID=0;
			for(i=0; fontm.name_full[i]!=0; i++) {
				numUID *= 37; /* magic number, good for hash */
				numUID += fontm.name_full[i]-' ';
				/* if the name is long the first chars
				 * may be lost forever, so re-insert
				 * them thus making kind of CRC
				 */
				numUID += (numUID>>24) & 0xFF;
			}
			/* the range for private UIDs is 4 000 000 - 4 999 999 */
			fprintf(pfa_file, "/UniqueID %lu def\n", numUID%1000000+4000000);
		}
	}

	fprintf(pfa_file, "/Weight (%s) readonly def\n", fontm.name_style);

	fprintf(pfa_file, "/ItalicAngle %f def\n", italic_angle);
	fprintf(pfa_file, "/isFixedPitch %s def\n",
		fontm.is_fixed_pitch ? "true" : "false");

	/* we don't print out the unused glyphs */
	nchars = 0;
	for (i = 0; i < numglyphs; i++) {
		if (glyph_list[i].flags & GF_USED) {
			nchars++;
		}
	}

    fprintf(afm_file, "StartFontMetrics 4.1\n");
	fprintf(afm_file, "FontName %s%s\n", fontm.name_ps, uni_font_name_suffix);
    fprintf(afm_file, "FullName %s\n", fontm.name_full);
    fprintf(afm_file, "Notice %s\n", fontm.name_copyright);
    fprintf(afm_file, "EncodingScheme FontSpecific\n");
    fprintf(afm_file, "FamilyName %s\n", fontm.name_family);
    fprintf(afm_file, "Weight %s\n", fontm.name_style);
    fprintf(afm_file, "Version %s\n", fontm.name_version);
    fprintf(afm_file, "Characters %d\n", nchars);
    fprintf(afm_file, "ItalicAngle %.1f\n", italic_angle);

    fprintf(afm_file, "Ascender %d\n", fontm.ascender);
    fprintf(afm_file, "Descender %d\n", fontm.descender);

	fprintf(pfa_file, "/UnderlinePosition %d def\n",
		iscale(fontm.underline_position));

	fprintf(pfa_file, "/UnderlineThickness %hd def\nend readonly def\n",
		iscale(fontm.underline_thickness));

	fprintf(afm_file, "UnderlineThickness %d\n",
		iscale(fontm.underline_thickness));

	fprintf(afm_file, "UnderlinePosition %d\n",
		iscale(fontm.underline_position));

    fprintf(afm_file, "IsFixedPitch %s\n",
		fontm.is_fixed_pitch ? "true" : "false");
    fprintf(afm_file, "FontBBox %d %d %d %d\n",
		bbox[0], bbox[1], bbox[2], bbox[3]);

	fprintf(pfa_file, "/FontName /%s%s def\n", fontm.name_ps, uni_font_name_suffix);
	fprintf(pfa_file, "/PaintType 0 def\n/StrokeWidth 0 def\n");
	/* I'm not sure if these are fixed */
	fprintf(pfa_file, "/FontType 1 def\n");

	if (transform) {
		fprintf(pfa_file, "/FontMatrix [0.001 0 0 0.001 0 0] def\n");
	} else {
		fprintf(pfa_file, "/FontMatrix [%9.7f 0 0 %9.7f 0 0] def\n",
			original_scale_factor / 1000.0, original_scale_factor / 1000.0);
	}

	fprintf(pfa_file, "/FontBBox {%d %d %d %d} readonly def\n",
		bbox[0], bbox[1], bbox[2], bbox[3]);

	fprintf(pfa_file, "/Encoding 256 array\n");
	/* determine number of elements for metrics table */
	nmetrics = 256;
 	for (i = 0; i < numglyphs; i++) {
		if( glyph_list[i].flags & GF_USED 
		&& glyph_list[i].char_no == -1 ) {
			nmetrics++;
		}
	}
	fprintf(afm_file, "StartCharMetrics %d\n", nmetrics);

 	for (i = 0; i < 256; i++) {
		fprintf(pfa_file,
			"dup %d /%s put\n", i, glyph_list[encoding[i]].name);
		if( glyph_list[encoding[i]].flags & GF_USED ) 
			print_glyph_metrics(i, encoding[i]);
	}

	/* print the metrics for glyphs not in encoding table */
	if(allglyphs) {
		for(i=0; i<numglyphs; i++) {
			if( (glyph_list[i].flags & GF_USED)
			&& glyph_list[i].char_no == -1 )
				print_glyph_metrics(-1, i);
		}
	}

	fprintf(pfa_file, "readonly def\ncurrentdict end\ncurrentfile eexec\n");
	fprintf(pfa_file, "dup /Private 16 dict dup begin\n");

	fprintf(pfa_file, "/RD{string currentfile exch readstring pop}executeonly def\n");
	fprintf(pfa_file, "/ND{noaccess def}executeonly def\n");
	fprintf(pfa_file, "/NP{noaccess put}executeonly def\n");

	/* UniqueID must be shown twice, in both font and Private dictionary */
	if(wantuid) {
		if(strUID)
			fprintf(pfa_file, "/UniqueID %s def\n", strUID);
		else
			fprintf(pfa_file, "/UniqueID %lu def\n", numUID);
	}

	if(forcebold==0)
		fprintf(pfa_file, "/ForceBold false def\n");
	else if(forcebold==1)
		fprintf(pfa_file, "/ForceBold true def\n");

	fprintf(pfa_file, "/BlueValues [ ");
	for (i = 0; i < nblues; i++)
		fprintf(pfa_file, "%d ", bluevalues[i]);
	fprintf(pfa_file, "] def\n");

	fprintf(pfa_file, "/OtherBlues [ ");
	for (i = 0; i < notherb; i++)
		fprintf(pfa_file, "%d ", otherblues[i]);
	fprintf(pfa_file, "] def\n");

	if (stdhw != 0)
		fprintf(pfa_file, "/StdHW [ %d ] def\n", stdhw);
	if (stdvw != 0)
		fprintf(pfa_file, "/StdVW [ %d ] def\n", stdvw);
	fprintf(pfa_file, "/StemSnapH [ ");
	for (i = 0; i < 12 && stemsnaph[i] != 0; i++)
		fprintf(pfa_file, "%d ", stemsnaph[i]);
	fprintf(pfa_file, "] def\n");
	fprintf(pfa_file, "/StemSnapV [ ");
	for (i = 0; i < 12 && stemsnapv[i] != 0; i++)
		fprintf(pfa_file, "%d ", stemsnapv[i]);
	fprintf(pfa_file, "] def\n");

	fprintf(pfa_file, "/MinFeature {16 16} def\n");
	/* Are these fixed also ? */
	fprintf(pfa_file, "/password 5839 def\n");

	/* calculate the number of subroutines */

	subid=5;
	for (i = 0; i < numglyphs; i++) {
		if (glyph_list[i].flags & GF_USED) {
			subid+=glyph_list[i].nsg;
		}
	}

	fprintf(pfa_file, "/Subrs %d array\n", subid);
	/* standard subroutines */
	fprintf(pfa_file, "dup 0 {\n\t3 0 callothersubr pop pop setcurrentpoint return\n\t} NP\n");
	fprintf(pfa_file, "dup 1 {\n\t0 1 callothersubr return\n\t} NP\n");
	fprintf(pfa_file, "dup 2 {\n\t0 2 callothersubr return\n\t} NP\n");
	fprintf(pfa_file, "dup 3 {\n\treturn\n\t} NP\n");
	/* our sub to make the hint substitution code shorter */
	fprintf(pfa_file, "dup 4 {\n\t1 3 callothersubr pop callsubr return\n\t} NP\n");

	/* print the hinting subroutines */
	subid=5;
	for (i = 0; i < numglyphs; i++) {
		if (glyph_list[i].flags & GF_USED) {
			subid+=print_glyph_subs(i, subid);
		}
	}

	fprintf(pfa_file, "ND\n");

	fprintf(pfa_file, "2 index /CharStrings %d dict dup begin\n", nchars);

	for (i = 0; i < numglyphs; i++) {
		if (glyph_list[i].flags & GF_USED) {
			print_glyph(i);
		}
	}


	fprintf(pfa_file, "end\nend\nreadonly put\n");
	fprintf(pfa_file, "noaccess put\n");
	fprintf(pfa_file, "dup/FontName get exch definefont pop\n");
	fprintf(pfa_file, "mark currentfile closefile\n");
	fprintf(pfa_file, "cleartomark\n");
	fclose(pfa_file);

    fprintf(afm_file, "EndCharMetrics\n");

	/* print the kerning data if present */
	cursw->prkern(glyph_list, afm_file);

    fprintf(afm_file, "EndFontMetrics\n");
    fclose(afm_file);

	WARNING_1 fprintf(stderr, "Finished - font files created\n");

    fclose(pfa_file);
	cursw->close();

#ifndef WINDOWS
	while (wait(&ws) > 0) {
	}
#else 
	if (encode) {
		extern FILE    *ifp, *ofp;	/* from t1asm.c */

		sprintf(filename, "%s.%s", argv[2], pfbflag ? "pfb" : "pfa" );

		if ((ofp = fopen(filename, "w+b")) == NULL) {
			fprintf(stderr, "**** Cannot create %s ****\n", filename);
			exit(1);
		} else {
			WARNING_2 fprintf(stderr, "Creating file %s\n", filename);
		}

		sprintf(filename, "%s.t1a", argv[2]);

		if ((ifp = fopen(filename, "rb")) == NULL) {
			fprintf(stderr, "**** Cannot read %s ****\n", filename);
			exit(1);
		} else {
			WARNING_2 fprintf(stderr, "Converting file %s\n", filename);
		}

		runt1asm(pfbflag);

		WARNING_2 fprintf(stderr, "Removing file %s\n", filename);
		if(unlink(filename) < 0) 
			WARNING_1 fprintf(stderr, "Unable to remove file %s\n", filename);
	}
#endif /* WINDOWS */
}
