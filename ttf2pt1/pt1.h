/*
 * see COPYRIGHT
 */


/* glyph entry, one drawing command */
typedef struct gentry {
	struct gentry  *next;	/* double linked list */
	struct gentry  *prev;
	struct gentry  *first;	/* first entry in path */
	int             x1, y1, x2, y2, x3, y3;	/* absolute values, NOT
						 * deltas */
	signed char     stemid; /* connection to the substituted stem group */
	char            type;
#define GE_HSBW	'B'
#define GE_MOVE 'M'
#define GE_LINE 'L'
#define GE_CURVE 'C'
#define GE_PATH 'P'
	char            flags; /* not used yet, for future development */
}               GENTRY;

/* stem structure, describes one [hv]stem  */
/* acually, it describes one border of a stem */
/* the whole stem is a pair of these structures */

typedef struct stem {
	short           value;	/* value of X or Y coordinate */
	short           origin;	/* point of origin for curve stems */
		/* also for all the stems the tuple (value, origin, flags & ST_UP)
		 * is used to determine whether a stem is relevant for a
		 * line, it's considered revelant if this tuple is
		 * equal to any of the ends of the line
		 */
	short           from, to;	/* values of other coordinate between
					 * which this stem is valid */

	short           flags;
	/* ordering of ST_END, ST_FLAT, ST_ZONE is IMPORTANT for sorting */
#define ST_END		0x01	/* end of line, lowest priority */
#define ST_FLAT		0x02	/* stem is defined by a flat line, not a
				 * curve */
#define ST_ZONE		0x04	/* pseudo-stem, the limit of a blue zone */
#define ST_UP		0x08	/* the black area is to up or right from
				 * value */
#define ST_3		0x20	/* first stem of [hv]stem3 */
#define ST_BLUE		0x40	/* stem is in blue zone */
#define ST_TOPZONE	0x80	/* 1 - top zone, 0 - bottom zone */
#define ST_VERT     0x100	/* vertical stem (used in substitutions) */
}               STEM;

#define MAX_STEMS	2000	/* we can't have more stems than path
				 * elements (or hope so) */
#define NSTEMGRP	50	/* maximal number of the substituted stem groups */

/* structure for economical representation of the
 * substituted stems
 */

typedef struct stembounds {
	short low; /* low bound */
	short high; /* high bound */
	char isvert; /* 1 - vertical, 0 - horizontal */
	char already; /* temp. flag: is aleready included */
} STEMBOUNDS;

typedef struct contour {
	short           ymin, xofmin;
	short           inside;	/* inside which contour */
	char            direction;
#define DIR_OUTER 1
#define DIR_INNER 0
}               CONTOUR;

typedef struct glyph {
	int             char_no;/* Encoding of glyph */
	int             unicode;/* Unicode value of glyph */
	char           *name;	/* Postscript name of glyph */
	int             xMin, yMin, xMax, yMax;	/* values from TTF dictionary */
	int             lsb;
	short int       width;
	short           flags;
#define GF_USED	0x0001		/* whether is this glyph used in T1 font */

	GENTRY         *entries;/* doube linked list of entries */
	GENTRY         *lastentry;	/* the last inserted entry */
	GENTRY         *path;	/* beggining of the last path */
	int             oldwidth; /* actually also scaled */
	int             scaledwidth;
#define	MAXLEGALWIDTH	10000 

	STEM           *hstems; /* global horiz. and vert. stems */
	STEM           *vstems;
	int             nhs, nvs;	/* numbers of stems */

	STEMBOUNDS     *sbstems; /* substituted stems for all the groups */
	short          *nsbs; /* indexes of the group ends in the common array */
	int             nsg; /* actual number of the stem groups */
	int             firstsubr; /* first substistuted stems subroutine number */

	CONTOUR        *contours;	/* it is not used now */
	int             ncontours;

	int             rymin, rymax;	/* real values */
	/* do we have flat surfaces on top/bottom */
	char            flatymin, flatymax;

}               GLYPH;

extern int      stdhw, stdvw;	/* dominant stems widths */
extern int      stemsnaph[12], stemsnapv[12];	/* most typical stem width */

extern int      bluevalues[14];
extern int      nblues;
extern int      otherblues[10];
extern int      notherb;
extern int      bbox[4];	/* the FontBBox array */
extern double   italic_angle;

extern GLYPH   *glyph_list;
extern short    encoding[256];	/* inverse of glyph[].char_no */

/* prototypes of functions */
int sign( int x);
void rmoveto( int dx, int dy);
void rlineto( int dx, int dy);
void rrcurveto( int dx1, int dy1, int dx2, int dy2, int dx3, int dy3);
void assertpath( GENTRY * from, int line, char *name);
void g_closepath( GLYPH * g);
void fixcvends( GENTRY * ge);
void flattencurves( GLYPH * g);
void fixcvdir( GENTRY * ge, int dir);
int getcvdir( GENTRY * ge);
int checkcv( GENTRY * ge, int dx, int dy);
void closepaths( GLYPH * g);
void smoothjoints( GLYPH * g);
void debugstems( char *name, STEM * hstems, int nhs, STEM * vstems, int nvs);
int addbluestems( STEM *s, int n);
void sortstems( STEM * s, int n);
int stemoverlap( STEM * s1, STEM * s2);
int steminblue( STEM *s);
void markbluestems( STEM *s, int nold);
void joinsubstems( STEM * s, short *pairs, int nold, int useblues);
int joinmainstems( STEM * s, int nold, int useblues);
void buildstems( GLYPH * g);
void straighten( GLYPH * g, int zigonly);
double curvelen( int x0, int y0, int x1, int y1,
	 int x2, int y2, int x3, int y3);
void splitzigzags( GLYPH * g);
void forceconcise( GLYPH * g);
void reversepathsfromto( GENTRY * from, GENTRY * to);
void reversepaths( GLYPH * g);
void print_glyf( int glyphno);
int print_glyf_subs( int glyphno, int startid);
void print_glyf_metrics( int code, int glyphno);
