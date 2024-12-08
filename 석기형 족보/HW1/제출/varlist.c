#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "varlist.h"

// TODO: Fill in
VarNode* make_varlist(char *var, int val, VarNode *next) {
    VarNode* varnode = (VarNode*)malloc(sizeof(VarNode));
    varnode->var = var;
    varnode->val = val;
    varnode->next = next;
    return varnode;
}

// TODO: Fill in
int lookup_var(VarNode *head, char *var) {
    VarNode* cur = head;
    while(cur != NULL){
        if(!strcmp(cur->var, var)) return cur->val;
        cur = cur->next;
    }
    if(cur == NULL){
        return 0;
    }
}

// TODO: Fill in
void free_varlist(VarNode *head) {
    VarNode* cur = head;
    while(cur != NULL){
        head = cur->next;
        free(cur);
        cur = head;
    }
    return;
}
