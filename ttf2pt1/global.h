/*
 * see COPYRIGHT
 */


/* options */

extern int      optimize;	/* enables space optimization */
extern int      smooth;	/* enable smoothing of outlines */
extern int      transform;	/* enables transformation to 1000x1000 matrix */
extern int      hints;	/* enables autogeneration of hints */
extern int      subhints;	/* enables autogeneration of substituted hints */
extern int      absolute;	/* print out in absolute values */
extern int      trybold;	/* try to guess whether the font is bold */
extern int      reverse;	/* reverse font to Type1 path directions */
extern int      encode;	/* encode the resulting file */
extern int      pfbflag;	/* produce compressed file */
extern int      wantafm;	/* want to see .afm instead of .t1a on stdout */
extern int      correctwidth;	/* try to correct the character width */
extern int      correctvsize;	/* try to correct the vertical size of characters */
extern int      wantuid;	/* user wants UniqueID entry in the font */
extern int      allglyphs;	/* convert all glyphs, not only 256 of them */

/* other globals */
extern FILE    *pfa_file, *afm_file;
extern int      ttf_file, numglyphs, long_offsets, ncurves;

/* debugging */

/* debug flags */
#define DEBUG_UNICODE	0x00000001 /* unicode to 8-bit code conversion */
#define DEBUG_MAINSTEMS	0x00000002 /* glyph-wide main stem generation */
#define DEBUG_SUBSTEMS	0x00000004 /* substituted stem generation */
#define DEBUG_STEMS	(DEBUG_MAINSTEMS|DEBUG_SUBSTEMS)
#define DEBUG_REVERSAL	0x00000008 /* reversal of the paths */
#define DEBUG_FIXCVDIR	0x00000010 /* fixcvdir() */
#define DEBUG_STEMOVERLAP	0x00000020 /* stemoverlap() */
#define DEBUG_BLUESTEMS	0x00000040 /* markbluestems() */
#define DEBUG_DISABLED	0x80000000 /* special flag: temporary disable debugging */

/* at what we want to look now */
#ifndef DEBUG
#	define DEBUG (0)
#endif

/* uncomment the next line if debugging data is wanted for one glyph only */
/* #define DBG_GLYPH	"exclam"  /* */

#if DEBUG==0
#	define ISDBG(name)	(0)
#	define ENABLEDBG(condition) (0)
#	define DISABLEDBG(condition) (0)
#else
	extern int debug; /* collection of the flags */
/* this ISDBG will only work on ANSI C, not K&R */
#	define ISDBG(name)	( (debug & DEBUG_DISABLED) ? 0 : (debug & (DEBUG_##name)) )
#	define ENABLEDBG(condition) ( (condition) ? (debug&=~DEBUG_DISABLED) : 0 )
#	define DISABLEDBG(condition) ( (condition) ? (debug|=DEBUG_DISABLED) : 0 )
#endif

#ifdef DBG_GLYPH
#	define DBG_TO_GLYPH(g) DISABLEDBG( strcmp( (g)->name, DBG_GLYPH ) )
#	define DBG_FROM_GLYPH(g) ENABLEDBG(1)
#else
#	define DBG_TO_GLYPH(g) (0)
#	define DBG_FROM_GLYPH(g) (0)
#endif

/* prototypes */
void get_glyf_table( int glyphno, TTF_GLYF **tab, int *len);
int scale( int val);
