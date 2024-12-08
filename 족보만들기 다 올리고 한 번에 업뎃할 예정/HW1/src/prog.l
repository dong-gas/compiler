%option noyywrap

%{
#include "prog.tab.h"
%}

dig [0-9]
let [A-Za-z]

%%
"+"                         { return PLUS; }
"*"                         { return MULT; }
"-"                         { return MINUS; }
"/"                         { return DIV; }
"("                         { return OPENB; }
")"                         { return CLOSEB; }
"="                         { return ASSIGN; }
";"                         { return SEMICOLON; }
","                         { return COMMA; }
{dig}+                      { yylval.n = atoi(yytext); return NUM; }
({let}|_)({let}|{dig}|_)*   { yylval.s = strdup(yytext); return ID; }
[ \t\n]+                    { /* Skip whitespaces. */ }
.                           { /* Wildcard '.' that matches anything. */
                              printf("Invalid token: %s\n", yytext);
                              exit(1);
                            }

%%
