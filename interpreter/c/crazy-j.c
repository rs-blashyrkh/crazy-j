// Blashyrkh.maniac.coding
// BTC:1Maniaccv5vSQVuwrmRtfazhf2WsUJ1KyD DOGE:DManiac9Gk31A4vLw9fLN9jVDFAQZc2zPj

// Copyright (c) 2025 Blashyrkh
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to
// deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
// THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
// IN THE SOFTWARE.

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <ctype.h>


struct Node
{
    struct Node   *next;
    struct Node   *left;
    struct Node   *right;
    unsigned int   opcode:31;
    unsigned int   mark:1;
};

#define DECLARE_OPCODE(name, value, apply_fn) \
    enum enum_ ## name {OP_ ## name=value}; \
    static void apply_fn(struct Node *a); \
    static struct Node name={NULL, NULL, NULL, OP_ ## name, 0};


// Application nodes. Dynamically allocated on heap
static const unsigned int OP_APPLY = 0x00;
// Special opcodes - IN_C (input continuation) and IN_V (input value). All special nodes
// are chained using 'left' pointer into single list. All special nodes with particular
// opcode (either OP_IN_C or OP_IN_V) are resolved and replaced en masse.
static const unsigned int OP_IN_C  = 0x01;
static const unsigned int OP_IN_V  = 0x03;
static void apply_IN_C(struct Node *a);
static void apply_IN_V(struct Node *a);

DECLARE_OPCODE(STOPPER,    0x02,    NO_APPLY);
DECLARE_OPCODE(SWAPPER,    0x05,    apply_SWAPPER);
DECLARE_OPCODE(OUT_C,      0x07,    apply_OUT_C);

// Basic combinators. Shift is arity-1
DECLARE_OPCODE(I,          0x09<<0, apply_I);  // I = lambda x . x
DECLARE_OPCODE(J,          0x0B<<3, apply_J);  // J = lambda xyzw = xy(xwz)

// Combinators needed to implement IO
DECLARE_OPCODE(T,          0x0D<<1, apply_T);  // T = lambda xy . yx
DECLARE_OPCODE(KI,         0x09<<1, apply_I);  // KI = lambda xy . y         = Church zero
DECLARE_OPCODE(V,          0x0F<<2, apply_V);  // V = lambda xyz . zxy
DECLARE_OPCODE(SB,         0x11<<2, apply_SB); // SB = lambda xyz = y(xyz)   = Church increment


static inline int is_special(unsigned int opcode)
{
    return (opcode&~2)==1;
}

typedef void (*apply_fn)(struct Node *);

// Not just a list. (idx*2+1) must be equal to the opcode with right zeroes stripped
static const apply_fn apply_functions[]=
{
    apply_IN_C,
    apply_IN_V,
    apply_SWAPPER,
    apply_OUT_C,
    apply_I,
    apply_J,
    apply_T,
    apply_V,
    apply_SB,
};


#ifndef GC_THRESHOLD
# define GC_THRESHOLD (1024*1024*1024)
#endif

struct ProtectedNode
{
    struct ProtectedNode *next;
    struct Node *node;
};

// Global variables
// {
struct ProtectedNode *protected_nodes=NULL;
static struct Node *special_node_list=NULL; // IN_CONT and IN_VAL nodes, ".left" is used for chaining
static struct Node *all_node_list=NULL;     // All nodes (including special ones), ".next" is used for chaining
static struct Node *free_node_list=NULL;
static unsigned int num_allocations=0;
// }

static void reduce(struct Node *expr);


static void mark_node(struct Node *node)
{
    if(node && !node->mark)
    {
        node->mark=1;
        if(!is_special(node->opcode)) // 'left' has different meaning for special nodes
        {
            mark_node(node->left);
            mark_node(node->right);
        }
    }
}

static void gc(void)
{
    // Mark all protected nodes and their children
    for(struct ProtectedNode *pn=protected_nodes; pn!=NULL; pn=pn->next)
        mark_node(pn->node);

    struct Node **pp;

    // Unchain all unmarked special nodes
    pp=&special_node_list;
    while(*pp)
    {
        struct Node *p=*pp;
        if(!p->mark)
        {
            *pp=p->left;
        }
        else
        {
            pp=&p->left;
        }
    }

    unsigned int freed=0;
    unsigned int kept=0;

    // Unchain and free all unmarked nodes, unmark all marked nodes
    pp=&all_node_list;
    while(*pp)
    {
        struct Node *p=*pp;
        if(!p->mark)
        {
            *pp=p->next;

            p->next=free_node_list;
            free_node_list=p;

            ++freed;
        }
        else
        {
            p->mark=0;
            pp=&p->next;
            ++kept;
        }
    }
    num_allocations-=freed;
}

static inline struct Node *new_node(struct Node *left, struct Node *right, unsigned int opcode)
{
    struct Node *p;
    if(!free_node_list)
    {
        p=(struct Node *)malloc(sizeof(struct Node));
    }
    else
    {
        p=free_node_list;
        free_node_list=p->next;
    }

    p->next=all_node_list;
    p->left=left;
    p->right=right;
    p->opcode=opcode;
    p->mark=0;
    all_node_list=p;

    if(is_special(opcode))
    {
        p->left=special_node_list;
        special_node_list=p;
    }

    ++num_allocations;

    return p;
}

static inline struct Node *new_combinator(char ch)
{
    ch=tolower(ch);
    if(ch=='i')
        return &I;
    else if(ch=='j')
        return &J;
    else
        return NULL;
}

static inline struct Node *new_application(struct Node *left, struct Node *right)
{
    return new_node(left, right, OP_APPLY);
}

static inline void replace_application(struct Node *a, struct Node *left, struct Node *right)
{
    a->left=left;
    a->right=right;
}

static inline void replace_node(struct Node *a, const struct Node *source)
{
    a->left=source->left;
    a->right=source->right;
    a->opcode=source->opcode;
    if(is_special(a->opcode))
    {
        a->left=special_node_list;
        special_node_list=a;
    }
}

static inline struct Node *new_input_cont(void)
{
    return new_node(NULL, NULL, OP_IN_C);
}

static inline struct Node *new_input_value(void)
{
    return new_node(NULL, NULL, OP_IN_V);
}

// Find all nodes, remove them from the hash table, chain together into single-linked list
// and return the head of the list (and in the darkness bind them, of course)
static struct Node *find_special_nodes(unsigned int opcode)
{
    struct Node *res=NULL;

    struct Node **pp=&special_node_list;
    while(*pp!=NULL)
    {
        struct Node *p=*pp;
        if(p->opcode==opcode)
        {
            *pp=p->left;
            p->left=res;
            res=p;
        }
        else
        {
            pp=&p->left;
        }
    }
    return res;
}

static void apply_IN_C(struct Node *a)
{
    struct Node *node=find_special_nodes(OP_IN_C);
    if(!node)
        return;

    struct Node *left=new_application(&V, new_input_value());
    struct Node *right=new_input_cont();

    while(node)
    {
        struct Node *next=node->left;

        node->left=left;
        node->right=right;
        node->opcode=OP_APPLY;

        node=next;
    }
}

static void apply_IN_V(struct Node *a)
{
    struct Node *node=find_special_nodes(OP_IN_V);
    if(!node)
        return;

    int code=fgetc(stdin);
    if(code<0 || code>255)
        code=256;

    struct Node *donor=&KI;
    for(int i=0; i<code; ++i)
    {
        donor=new_application(&SB, donor);
    }

    while(node)
    {
        struct Node *next=node->left;
        replace_node(node, donor);

        node=next;
    }
}

static void apply_SWAPPER(struct Node *a)
{
    replace_application(a, a->right, a->left);
}

static void apply_OUT_C(struct Node *a)
{
    struct Node *n=new_application(new_application(a->right, &SWAPPER), &STOPPER);
    reduce(n);

    unsigned int code=0;
    while(n->opcode==OP_APPLY && n->right->opcode==OP_SWAPPER && code<256+126)
    {
        ++code;
        n=n->left;
    }
    if(n->opcode!=OP_STOPPER)
        code=256+126;

    if(code<256)
    {
        fputc(code, stdout);
        fflush(stdout);
    }
    else
    {
        exit(code-256);
    }

    // Should return `T<OUT> to continue. Being applied to the rest of the program, it gives `<PROG><OUT>
    replace_application(a, &T, &OUT_C);
}

static void apply_I(struct Node *a)
{
    replace_node(a, a->right);
}

static void apply_J(struct Node *a)
{
    replace_application(
        a,
        new_application(a->left->left->left->right, a->left->left->right),
        new_application(new_application(a->left->left->left->right, a->right), a->left->right));
}

static void apply_T(struct Node *a)
{
    replace_application(a, a->right, a->left->right);
}

static void apply_V(struct Node *a)
{
    replace_application(a, new_application(a->right, a->left->left->right), a->left->right);
}

static void apply_SB(struct Node *a)
{
    replace_application(
        a,
        a->left->right,
        new_application(new_application(a->left->left->right, a->left->right), a->right));
}

static struct Node *new_application_load(struct Node *left, struct Node *right)
{
/*
    struct OptimizeRule
    {
        unsigned int  op_left;
        unsigned int  op_right;
        struct Node  *node;
    };
    static const struct OptimizeRule rules[]=
    {
    };

    for(unsigned int i=0; i<sizeof(rules)/sizeof(rules[0]); ++i)
    {
        if(left->opcode==rules[i].op_left && right->opcode==rules[i].op_right)
            return rules[i].node;
    }
*/
    return new_application(left, right);
}

// TODO: return parsing error info (line, col, message)
// TODO: support CC syntax 
static struct Node *parse_program(FILE *f)
{
    unsigned int line=1;
    unsigned int col=0;
    int ignore_rest_of_line=0;

    unsigned int op_stack_size=0;
    unsigned int op_stack_cap=0;
    struct Node **op_stack=NULL;

    unsigned int n_stack_size=0;
    unsigned int n_stack_cap=10;
    unsigned int *n_stack=(unsigned int *)malloc(n_stack_cap*sizeof(unsigned int));
    n_stack[n_stack_size++]=0;

    int ch;
    while((ch=fgetc(f))!=EOF)
    {
        if(ch=='\n')
        {
            ++line;
            col=0;
            ignore_rest_of_line=0;
            continue;
        }

        ++col;
        if(ignore_rest_of_line)
            continue;

        if(ch=='#')
            ignore_rest_of_line=1;
        else if(ch=='`')
        {
            if(n_stack_size>=n_stack_cap)
            {
                n_stack_cap+=10;
                n_stack=(unsigned int *)realloc(n_stack, n_stack_cap*sizeof(unsigned int));
                if(!n_stack)
                    abort();
            }
            n_stack[n_stack_size++]=0;
        }
        else if(ch=='i' || ch=='j')
        {
            if(op_stack_size>=op_stack_cap)
            {
                op_stack_cap+=20;
                op_stack=(struct Node **)realloc(op_stack, op_stack_cap*sizeof(struct Node *));
                if(!op_stack)
                    abort();
            }
            op_stack[op_stack_size++]=new_combinator(ch);
            ++n_stack[n_stack_size-1];

            while(n_stack_size>0 && n_stack[n_stack_size-1]==2)
            {
                struct Node *left=op_stack[op_stack_size-2];
                struct Node *right=op_stack[op_stack_size-1];

                --n_stack_size;
                ++n_stack[n_stack_size-1];
                --op_stack_size;

                op_stack[op_stack_size-1]=new_application_load(left, right);
            }
        }
    }
    // TODO: checks

    struct Node *res=NULL;
    if(op_stack_size==1)
        res=op_stack[0];

    free(op_stack);
    free(n_stack);

    return res;
}

static inline int get_non_ws_char(FILE *f)
{
    for(;;)
    {
        int ch=fgetc(f);
        if(ch==EOF || !isspace(ch))
            return ch;
    }
}

static void reduce(struct Node *p)
{
    // If the expression's root node is not Application then there's nothing we can do
    // to reduce it
    if(p->opcode!=OP_APPLY)
        return;

    struct ProtectedNode prot;
    prot.node=p;
    prot.next=protected_nodes;
    protected_nodes=&prot;

    unsigned int stack_cap=1000;
    unsigned int stack_size=0;
    struct Node **stack=(struct Node **)malloc(stack_cap*sizeof(struct Node *));

    while(p->opcode==OP_APPLY)
    {
        unsigned int op=p->left->opcode;
        // Left subtree is an application as well - we need to go deeper
        if(op==OP_APPLY)
        {
            if(stack_size==stack_cap)
            {
                stack_cap*=2;
                stack=(struct Node **)realloc(stack, stack_cap*sizeof(struct Node *));
            }
            stack[stack_size]=p;
            ++stack_size;

            p=p->left;
        }
        // Stopper atoms
        else if(op==OP_STOPPER)
        {
            break;
        }
        else
        {
            // Trivial opcode
            if((op&0x01)==0)
            {
                p->opcode=op>>1;
            }
            // Non-trivial opcode with handler function
            else
            {
                apply_functions[(op>>1)](p);
            }

            if(p->opcode!=OP_APPLY && stack_size>0)
            {
                --stack_size;
                p=stack[stack_size];
            }
        }

        if(num_allocations>=GC_THRESHOLD/48)
        {
            gc();
        }
    }

    free(stack);

    protected_nodes=prot.next;
}

int main(int argc, char *argv[])
{
    struct Node *program=new_input_cont();
    for(int i=1; i<argc; ++i)
    {
        FILE *f=fopen(argv[i], "rt");
        if(!f)
        {
            perror("Failed to open source file");
            return 1;
        }

        struct Node *node=parse_program(f);
        fclose(f);

        if(!node)
        {
            fprintf(stderr, "Failed to parse source file\n");
            return 1;
        }

        program=new_application(node, program);
    }

    program=new_application(program, &OUT_C);
    reduce(program);

    return 126;
}
