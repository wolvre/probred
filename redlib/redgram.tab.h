/* A Bison parser, made by GNU Bison 3.0.2.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2013 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

#ifndef YY_REDLIB_REDGRAM_TAB_H_INCLUDED
# define YY_REDLIB_REDGRAM_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int redlibdebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    PS_IDENTIFIER = 258,
    PS_INLINE_ARGUMENT = 259,
    PS_PROCESS = 260,
    PS_ROLE = 261,
    PS_URGENT = 262,
    PS_PROCESS_COUNT = 263,
    PS_MODE_COUNT = 264,
    PS_XTION_COUNT = 265,
    PS_ASSIGNMENT = 266,
    PS_GUARD = 267,
    PS_ERASE = 268,
    PS_GLOBALLY = 269,
    PS_MODE = 270,
    PS_XTIONS = 271,
    PS_ADDRESSES = 272,
    PS_RATE = 273,
    PS_WHEN = 274,
    PS_MAY = 275,
    PS_GOTO = 276,
    PS_IN = 277,
    PS_WHILE = 278,
    PS_IF = 279,
    PS_ELSE = 280,
    PS_LOCAL = 281,
    PS_GLOBAL = 282,
    PS_STACK = 283,
    PS_MEMORY = 284,
    PS_BIRD = 285,
    PS_BIRD_PLUS = 286,
    PS_BIRD_MINUS = 287,
    PS_PARAMETER = 288,
    PS_FORMULA = 289,
    PS_QUANTIFY = 290,
    PS_SYSTEM = 291,
    PS_INFO = 292,
    PS_CALL = 293,
    PS_RETURN = 294,
    PS_CPLUG = 295,
    PS_CLOCK = 296,
    PS_DENSE = 297,
    PS_DISCRETE = 298,
    PS_FLOAT = 299,
    PS_DOUBLE = 300,
    PS_STREAM = 301,
    PS_ORDERED = 302,
    PS_UNORDERED = 303,
    PS_OPEN = 304,
    PS_CLOSE = 305,
    PS_INPUT = 306,
    PS_OUTPUT = 307,
    PS_FROM_STREAM = 308,
    PS_TO_STREAM = 309,
    PS_FREE = 310,
    PS_MALLOC = 311,
    PS_BOOLEAN = 312,
    PS_SYNCHRONIZER = 313,
    PS_INLINE = 314,
    PS_TCTL = 315,
    PS_DEBUG = 316,
    PS_RISK = 317,
    PS_GOAL = 318,
    PS_MATRIX = 319,
    PS_CHECK = 320,
    PS_DIRTY = 321,
    PS_LEAKS = 322,
    PS_REDLIB = 323,
    PS_SESSION = 324,
    PS_PARAMETRIC = 325,
    PS_SAFETY = 326,
    PS_BRANCHING = 327,
    PS_BISIMULATION = 328,
    PS_SIMULATION = 329,
    PS_P = 330,
    PS_INFINITY = 331,
    PS_BIT_AND = 332,
    PS_BIT_OR = 333,
    PS_AND = 334,
    PS_OR = 335,
    PS_NOT = 336,
    PS_BIT_NOT = 337,
    PS_TRUE = 338,
    PS_FALSE = 339,
    PS_IMPLY = 340,
    PS_RIGHTARROW = 341,
    PS_UNTIL = 342,
    PS_ALWAYS = 343,
    PS_EVENTUALLY = 344,
    PS_EVENT = 345,
    PS_WITH = 346,
    PS_ON = 347,
    PS_RESET = 348,
    PS_THROUGH = 349,
    PS_EVENTS = 350,
    PS_FORALL = 351,
    PS_EXISTS = 352,
    PS_ALMOST = 353,
    PS_OFTEN = 354,
    PS_ASSUME = 355,
    PS_STRONG = 356,
    PS_WEAK = 357,
    PS_EQ = 358,
    PS_NEQ = 359,
    PS_LESS = 360,
    PS_LEQ = 361,
    PS_GREATER = 362,
    PS_GEQ = 363,
    PS_INC = 364,
    PS_DEC = 365,
    PS_CLEAR = 366,
    PS_PLUS = 367,
    PS_MINUS = 368,
    PS_MULTIPLY = 369,
    PS_DIVIDE = 370,
    PS_MODULO = 371,
    PS_SUM = 372,
    PS_LPAR = 373,
    PS_RPAR = 374,
    PS_LBRAC = 375,
    PS_RBRAC = 376,
    PS_LCURLY = 377,
    PS_RCURLY = 378,
    PS_NUMBER = 379,
    PS_HEX_NUMBER = 380,
    PS_FLOAT_NUMBER = 381,
    PS_NULL = 382,
    PS_INITIAL = 383,
    PS_CHANGE = 384,
    PS_SIMULATE = 385,
    PS_DEADLOCK = 386,
    PS_ZENO = 387,
    PS_INDEX = 388,
    PS_PRIMED = 389,
    PS_COMMA = 390,
    PS_DDOTS = 391,
    PS_COLON = 392,
    PS_SEMICOLON = 393,
    PS_EXCLAMATION = 394,
    PS_QUESTION = 395,
    PS_VARIABLE = 396,
    PS_BDD = 397,
    PS_SYNC = 398,
    PS_QFD = 399,
    PS_CONSTRUCT = 400,
    PS_WINDOW = 401,
    PS_POSITION = 402,
    PS_RECTANGLE = 403,
    PS_SHAPE = 404,
    PS_SQUARE = 405,
    PS_OVAL = 406,
    PS_CIRCLE = 407,
    PS_TRIANGLE = 408,
    PS_LEFTWARD = 409,
    PS_RIGHTWARD = 410,
    PS_UPWARD = 411,
    PS_DOWNWARD = 412,
    PS_COLOR = 413,
    PS_RED = 414,
    PS_WHITE = 415,
    PS_BLACK = 416,
    PS_BLUE = 417,
    PS_YELLOW = 418,
    PS_GREEN = 419,
    PS_POINT = 420,
    PS_DISCRETE_INLINE_CALL = 421,
    PS_BOOLEAN_INLINE_CALL = 422,
    PS_MACRO_CONSTANT = 423
  };
#endif
/* Tokens.  */
#define PS_IDENTIFIER 258
#define PS_INLINE_ARGUMENT 259
#define PS_PROCESS 260
#define PS_ROLE 261
#define PS_URGENT 262
#define PS_PROCESS_COUNT 263
#define PS_MODE_COUNT 264
#define PS_XTION_COUNT 265
#define PS_ASSIGNMENT 266
#define PS_GUARD 267
#define PS_ERASE 268
#define PS_GLOBALLY 269
#define PS_MODE 270
#define PS_XTIONS 271
#define PS_ADDRESSES 272
#define PS_RATE 273
#define PS_WHEN 274
#define PS_MAY 275
#define PS_GOTO 276
#define PS_IN 277
#define PS_WHILE 278
#define PS_IF 279
#define PS_ELSE 280
#define PS_LOCAL 281
#define PS_GLOBAL 282
#define PS_STACK 283
#define PS_MEMORY 284
#define PS_BIRD 285
#define PS_BIRD_PLUS 286
#define PS_BIRD_MINUS 287
#define PS_PARAMETER 288
#define PS_FORMULA 289
#define PS_QUANTIFY 290
#define PS_SYSTEM 291
#define PS_INFO 292
#define PS_CALL 293
#define PS_RETURN 294
#define PS_CPLUG 295
#define PS_CLOCK 296
#define PS_DENSE 297
#define PS_DISCRETE 298
#define PS_FLOAT 299
#define PS_DOUBLE 300
#define PS_STREAM 301
#define PS_ORDERED 302
#define PS_UNORDERED 303
#define PS_OPEN 304
#define PS_CLOSE 305
#define PS_INPUT 306
#define PS_OUTPUT 307
#define PS_FROM_STREAM 308
#define PS_TO_STREAM 309
#define PS_FREE 310
#define PS_MALLOC 311
#define PS_BOOLEAN 312
#define PS_SYNCHRONIZER 313
#define PS_INLINE 314
#define PS_TCTL 315
#define PS_DEBUG 316
#define PS_RISK 317
#define PS_GOAL 318
#define PS_MATRIX 319
#define PS_CHECK 320
#define PS_DIRTY 321
#define PS_LEAKS 322
#define PS_REDLIB 323
#define PS_SESSION 324
#define PS_PARAMETRIC 325
#define PS_SAFETY 326
#define PS_BRANCHING 327
#define PS_BISIMULATION 328
#define PS_SIMULATION 329
#define PS_P 330
#define PS_INFINITY 331
#define PS_BIT_AND 332
#define PS_BIT_OR 333
#define PS_AND 334
#define PS_OR 335
#define PS_NOT 336
#define PS_BIT_NOT 337
#define PS_TRUE 338
#define PS_FALSE 339
#define PS_IMPLY 340
#define PS_RIGHTARROW 341
#define PS_UNTIL 342
#define PS_ALWAYS 343
#define PS_EVENTUALLY 344
#define PS_EVENT 345
#define PS_WITH 346
#define PS_ON 347
#define PS_RESET 348
#define PS_THROUGH 349
#define PS_EVENTS 350
#define PS_FORALL 351
#define PS_EXISTS 352
#define PS_ALMOST 353
#define PS_OFTEN 354
#define PS_ASSUME 355
#define PS_STRONG 356
#define PS_WEAK 357
#define PS_EQ 358
#define PS_NEQ 359
#define PS_LESS 360
#define PS_LEQ 361
#define PS_GREATER 362
#define PS_GEQ 363
#define PS_INC 364
#define PS_DEC 365
#define PS_CLEAR 366
#define PS_PLUS 367
#define PS_MINUS 368
#define PS_MULTIPLY 369
#define PS_DIVIDE 370
#define PS_MODULO 371
#define PS_SUM 372
#define PS_LPAR 373
#define PS_RPAR 374
#define PS_LBRAC 375
#define PS_RBRAC 376
#define PS_LCURLY 377
#define PS_RCURLY 378
#define PS_NUMBER 379
#define PS_HEX_NUMBER 380
#define PS_FLOAT_NUMBER 381
#define PS_NULL 382
#define PS_INITIAL 383
#define PS_CHANGE 384
#define PS_SIMULATE 385
#define PS_DEADLOCK 386
#define PS_ZENO 387
#define PS_INDEX 388
#define PS_PRIMED 389
#define PS_COMMA 390
#define PS_DDOTS 391
#define PS_COLON 392
#define PS_SEMICOLON 393
#define PS_EXCLAMATION 394
#define PS_QUESTION 395
#define PS_VARIABLE 396
#define PS_BDD 397
#define PS_SYNC 398
#define PS_QFD 399
#define PS_CONSTRUCT 400
#define PS_WINDOW 401
#define PS_POSITION 402
#define PS_RECTANGLE 403
#define PS_SHAPE 404
#define PS_SQUARE 405
#define PS_OVAL 406
#define PS_CIRCLE 407
#define PS_TRIANGLE 408
#define PS_LEFTWARD 409
#define PS_RIGHTWARD 410
#define PS_UPWARD 411
#define PS_DOWNWARD 412
#define PS_COLOR 413
#define PS_RED 414
#define PS_WHITE 415
#define PS_BLACK 416
#define PS_BLUE 417
#define PS_YELLOW 418
#define PS_GREEN 419
#define PS_POINT 420
#define PS_DISCRETE_INLINE_CALL 421
#define PS_BOOLEAN_INLINE_CALL 422
#define PS_MACRO_CONSTANT 423

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE YYSTYPE;
union YYSTYPE
{
#line 8435 "redgram.y" /* yacc.c:1909  */

  int 					number;
  float					float_number; 
  char					*string;
  struct name_link_type			*nlist; 
  struct index_pair_link_type		*iplist; 
  struct parse_xtion_link_type		*xlist;
  struct parse_xtion_type		*xtion;
  struct parse_statement_type		*st; 
  struct ps_exp_type			*sp;
  struct ps_bunit_type			*splist; 
  struct gram_interval_type		*gint;
  struct gram_fairness_type		*gfair;
  struct gram_optional_address_type	*addr;
  struct ps_fairness_link_type		*gseq;
  struct parse_module_type		*module; 
  struct parse_mode_type		*mode; 
  struct parse_operand_type		*opn;
  struct parse_variable_type		*pvar; 
//  struct parse_indirect_type		*pind; 
  struct pnp_var_type			*pnp; 
  struct parse_stream_operation_type	*pso; 

#line 414 "redgram.tab.h" /* yacc.c:1909  */
};
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE redliblval;

int redlibparse (void);

#endif /* !YY_REDLIB_REDGRAM_TAB_H_INCLUDED  */
