#include <stdio.h>

typedef struct par *par; /* 0 means "cover" */
typedef struct item *item;

struct par {
  char *id;
  par super, sub, prev;
  item first, last;
};

#define ONE 1
#define DEF 2
#define CON 3
#define TERM 4
#define APP 5
#define ABST 6
#define VAR 7

typedef struct exp *exp;
typedef struct one *one;
typedef struct def *def;
typedef struct con *con;
typedef struct term *term;
typedef struct args *args;
typedef struct app *app;
typedef struct abst *abst;
typedef struct var *var;

struct exp {
  short kind;
};

struct one {
  short kind; /* 1 */
  char *id;
  short code;
};

struct item {
  short kind; /* 2 or 3 */
  char *id;
  exp type;
  short deg, code;
  con back;
  par where;
  item prev, next, forth;
  short echo;
};

struct def {
  short kind; /* 2 */
  char *id;
  exp type;
  short deg, code;
  con back;
  par where;
  item prev, next, forth;
  short echo;
  exp body; /* 0 means "PN" */
  int seq;
};

struct con {
  short kind; /* 3 */
  char *id;
  exp type;
  short deg, code;
  con back;
  par where;
  item prev, next, forth;
  short echo;
  exp ref;
  args implicit;
};

struct term {
  short kind; /* 4 */
  def fun;
  args arglist;
};

struct args {
  exp arg;
  args prev;
};

struct app {
  short kind; /* 5 */
  exp fun, arg;
};

struct abst {
  short kind; /* 6 */
  char *id;
  exp type, body;
  abst ref;
  var clone;
};

struct var {
  short kind; /* 7 */
  abst lambda;
};

/* */

typedef union {
  int asint;
  char *asid;
  par aspar;
  exp asexp;
  args asargs;
} YYSTYPE;

extern YYSTYPE yylval;

int yylex(void);
int yyparse(void);
#undef yywrap
int yywrap(void);
int yyerror(char *message);

extern int line, cdepth;
extern int flag[], parameter[];
#define FLAG(x) flag[(unsigned)x]
#define PARAMETER(x) parameter[(unsigned)x]
#define HASPROP() FLAG('p')

char *ident(char *s);
extern par curpar;
par superpar(char *id);
par subpar(par p, char *id);
void yield(void);
void openpar(char *id, int re);
void closepar(char *id);
void setcon(exp c);
void newcon(char *id, exp type);
void newdef(char *id, exp body, exp type, int noexpand);
void opencon(void);
void closecon(void);
void finalclosecon(void);
void recover(void);
exp oneexp(int code);
exp call(exp fun, args arglist, int iscall);
exp appl(exp arg, exp fun);
exp openabs(char *id, exp type);
exp closeabs(exp d, exp body);
exp findsym(char *id);
exp findexp(par p, char *id);
args newlist(args prev, exp e);

/* */

typedef struct value *value;
struct value {
  char *id, *oldvalue;
  value prev;
};

#ifdef NOCHECK
#define WRONG()
#define CHECK(condition)
#else
#define WRONG()                                                                \
  (error(),                                                                    \
   (void)fprintf(stderr, "\nfile \"%s\"; line %d # program error\n", __FILE__, \
                 __LINE__),                                                    \
   exit(2))
#define CHECK(condition) ((condition) || (WRONG(), 1))
#endif

#define ALLOC(x) (x) alloc(sizeof(struct x))
#define STDSUM (FLAG('z') ? stdout : stderr)

extern char *
    yytext; /* with the original lex this should be: "extern char yytext[];"! */

extern int mayrestore;
void outofmem(void);
void savemem(void);
void restoremem(void);
void initalloc(void);
void exitalloc(void);
char *alloc(int n);
void initident(void);
char *getidvalue(char *s);
void setidvalue(char *s, char *x);
char *other(char *s);
void error(void);
extern par toplist;
int fprintpar(FILE *F, par p);
int fprintrelpar(FILE *F, par p, par q);
void initpar(void);
void exitpar(void);
void inititem(void);
void exititem(void);
extern int inbody;
extern con curcon;
extern item firstitem;
void savevalue(char *id, char *newvalue);
void mark(char *markvalue);
void restorevalue(void);
char *restoretomark(void);
void initexp(void);
term newterm(def fun, args arglist);
var absframe(char *id, exp type);
int occurs(exp e, abst l);
int fprintexp(FILE *F, exp e);
int fprintsym(FILE *F, exp e);
exp substvar(exp d, abst l, exp e);
exp substcon(args a, con c, exp e);
exp auttype(exp e);
int degree(exp e);
int flavor(exp e);
extern int mayeta;
extern int limitreductions, reductionsleft;
void initsame(void);
void exitsame(void);
int beta(exp *xe);
int delta(exp *xe);
int same(exp d, exp e);
int checktype(exp body, exp type);
int checkdegree(exp e, int from, int to);
int check(exp e);
exp domain(exp e);
void excerpt(void);
void everything(void);
void deltalambda(void);
