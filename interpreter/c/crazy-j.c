// Blashyrkh.maniac.coding
// BTC:1Maniaccv5vSQVuwrmRtfazhf2WsUJ1KyD DOGE:DManiac9Gk31A4vLw9fLN9jVDFAQZc2zPj

// Copyright (c) 2025-2026 Blashyrkh
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
// Special opcodes - IN (input). No other special opcodes in current implementation, but they
// may be added in the future. All special nodes are chained using 'left' pointer into single
// list. All special nodes with particular opcode are resolved and replaced en masse.
static const unsigned int OP_IN  = 0x01;
static void apply_IN(struct Node *a);

DECLARE_OPCODE(STOPPER,    0x02,    NO_APPLY);
DECLARE_OPCODE(SWAPPER,    0x03,    apply_SWAPPER);
DECLARE_OPCODE(OUT_C,      0x05,    apply_OUT_C);

// Basic combinators. Shift is arity-1
DECLARE_OPCODE(I,          0x07<<0, apply_I);  // I = lambda x . x
DECLARE_OPCODE(J,          0x09<<3, apply_J);  // J = lambda xyzw = xy(xwz)

// Combinators needed to implement IO
DECLARE_OPCODE(T,          0x0B<<1, apply_T);  // T = lambda xy . yx
DECLARE_OPCODE(V,          0x0D<<2, apply_V);  // V = lambda xyz . zxy
DECLARE_OPCODE(SB,         0x0F<<2, apply_SB); // SB = lambda xyz . y(xyz)   = Church increment

// Combinators used in program pre-processing
DECLARE_OPCODE(Q1,         0x11<<2, apply_Q1);
DECLARE_OPCODE(R,          0x13<<2, apply_R);
DECLARE_OPCODE(Q4,         0x15<<2, apply_Q4);
DECLARE_OPCODE(JR,         0x17<<3, apply_JR);  // JR = lambda xyzw . ywzx

static inline int is_special(unsigned int opcode)
{
    return opcode==OP_IN;
}

typedef void (*apply_fn)(struct Node *);

// Not just a list. (idx*2+1) must be equal to the opcode with right zeroes stripped
static const apply_fn apply_functions[]=
{
    apply_IN,
    apply_SWAPPER,
    apply_OUT_C,
    apply_I,
    apply_J,
    apply_T,
    apply_V,
    apply_SB,
    apply_Q1,
    apply_R,
    apply_Q4,
    apply_JR
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
    if(ch=='i' || ch=='I' || ch=='+')
        return &I;
    else if(ch=='j' || ch=='J' || ch=='-')
        return &J;
    else if(ch==',')
        return &Q1;
    else if(ch=='.')
        return &T;
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

static inline struct Node *new_input(void)
{
    return new_node(NULL, NULL, OP_IN);
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

static void apply_IN(struct Node *a)
{
    struct Node *node=find_special_nodes(OP_IN);
    if(!node)
        return;

    int code=fgetc(stdin);
    if(code<0 || code>255)
        code=256;

    struct Node *numeral=&I;
    for(int i=0; i<code; ++i)
    {
        numeral=new_application(&SB, numeral);
    }

    struct Node *left=new_application(&V, numeral);
    struct Node *right=new_input();

    while(node)
    {
        struct Node *next=node->left;

        node->left=left;
        node->right=right;
        node->opcode=OP_APPLY;

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
    while(n->opcode==OP_APPLY && n->right->opcode==OP_SWAPPER && code<257+126)
    {
        ++code;
        n=n->left;
    }
    if(n->opcode!=OP_STOPPER)
        code=257+126;

    if(code>0 && code<257)
    {
        fputc(code-1, stdout);
        fflush(stdout);
    }
    else
    {
        exit(code-257);
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

static void apply_Q1(struct Node *a)
{
    replace_application(
        a,
        a->left->left->right,
        new_application(a->right, a->left->right));
}

static void apply_R(struct Node *a)
{
    replace_application(
        a,
        new_application(a->left->right, a->right),
        a->left->left->right);
}

static void apply_Q4(struct Node *a)
{
    replace_application(
        a,
        a->right,
        new_application(a->left->right, a->left->left->right));
}

static void apply_JR(struct Node *a)
{
    replace_application(a,
        new_application(
            new_application(a->left->left->right, a->right),
            a->left->right),
        a->left->left->left->right);
}

static struct Node *new_application_load(struct Node *left, struct Node *right)
{
    struct OptimizeRule
    {
        unsigned int  op_left;
        unsigned int  op_right;
        struct Node  *node;
    };
    static const struct OptimizeRule rules[]=
    {
        {OP_J,  OP_I,  &Q1 },
        {OP_Q1, OP_I,  &T  },
        {OP_J,  OP_T,  &R  },
        {OP_Q1, OP_T,  &Q4 },
        {OP_J,  OP_R,  &JR },
    };

    for(unsigned int i=0; i<sizeof(rules)/sizeof(rules[0]); ++i)
    {
        if(left->opcode==rules[i].op_left && right->opcode==rules[i].op_right)
            return rules[i].node;
    }

    return new_application(left, right);
}

struct ParseErrorInfo
{
    unsigned int line;
    unsigned int col;
    int ch;
    const char *message;
};

static struct Node *parse_program(FILE *f, struct ParseErrorInfo *error)
{
    enum Syntax
    {
        Unknown,
        Unlambda,
        CC,
        BFMimic
    } syntax=Unknown;

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

    unsigned int ltr_stack_size=0;
    unsigned int ltr_stack_cap=0;
    char *ltr_stack=(char *)malloc(ltr_stack_cap*sizeof(char));

    char left_to_right=1;

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
        {
            ignore_rest_of_line=1;
            continue;
        }
        if(isspace(ch))
            continue;

        if(
            ((ch=='`' || ch=='i' || ch=='j') && (syntax!=Unlambda && syntax!=Unknown)) ||
            ((ch=='(' || ch==')' || ch=='I' || ch=='J') && (syntax!=CC && syntax!=Unknown)) ||
            ((ch=='[' || ch==']' || ch=='>' || ch=='<' || ch=='.' || ch==',' || ch=='+' || ch=='-') && (syntax!=BFMimic && syntax!=Unknown)))
        {
            error->message="Unexpected character";
            goto err;
        }

        if(ch=='`' || ch=='(' || ch=='[')
        {
            syntax=(ch=='`')?Unlambda
                  :(ch=='(')?CC
                            :BFMimic;

            if(n_stack_size>=n_stack_cap)
            {
                n_stack_cap+=10;
                n_stack=(unsigned int *)realloc(n_stack, n_stack_cap*sizeof(unsigned int));
                if(!n_stack)
                    abort();
            }
            n_stack[n_stack_size++]=0;

            if(syntax==BFMimic)
            {
                if(ltr_stack_size>=ltr_stack_cap)
                {
                    ltr_stack_cap+=10;
                    ltr_stack=(char *)realloc(ltr_stack, ltr_stack_cap*sizeof(char));
                    if(!ltr_stack)
                        abort();
                }
                ltr_stack[ltr_stack_size++]=left_to_right;
            }
        }
        else if(ch=='i' || ch=='j' || ch=='I' || ch=='J' || ch=='+' || ch=='-' || ch=='.' || ch==',')
        {
            syntax=(ch=='i' || ch=='j')?Unlambda
                  :(ch=='I' || ch=='J')?CC
                                       :BFMimic;

            if(op_stack_size>=op_stack_cap)
            {
                op_stack_cap+=20;
                op_stack=(struct Node **)realloc(op_stack, op_stack_cap*sizeof(struct Node *));
                if(!op_stack)
                    abort();
            }
            op_stack[op_stack_size++]=new_combinator(ch);
            ++n_stack[n_stack_size-1];
        }
        else if(ch==')' || ch==']')
        {
            syntax=(ch==')')?CC
                            :BFMimic;

            if(n_stack_size==1)
            {
                error->message="Unbalanced";
                goto err;
            }

            if(n_stack[n_stack_size-1]==0)
            {
                error->message="Unexpected character";
                goto err;
            }

            --n_stack_size;
            ++n_stack[n_stack_size-1];

            if(syntax==BFMimic)
            {
                left_to_right=ltr_stack[--ltr_stack_size];
            }
        }
        else if(ch=='>' || ch=='<')
        {
            syntax=BFMimic;
            left_to_right=(ch=='>');
        }
        else
        {
            error->message="Unexpected character";
            goto err;
        }

        while(n_stack_size>=1 && n_stack[n_stack_size-1]==2)
        {
            struct Node *left=op_stack[op_stack_size-2];
            struct Node *right=op_stack[op_stack_size-1];

            --op_stack_size;
            op_stack[op_stack_size-1]=left_to_right?new_application_load(left, right)
                                                   :new_application_load(right, left);

            if(syntax==CC || syntax==BFMimic)
            {
                --n_stack[n_stack_size-1];
            }
            else
            {
                if(n_stack_size==1)
                {
                    error->message="EOF expected instead of";
                    goto err;
                }
                --n_stack_size;
                ++n_stack[n_stack_size-1];
            }
        }
    }

    struct Node *res;
    if(n_stack_size==1 && n_stack[0]==0)
    {
        res=new_combinator('i');
    }
    else if(n_stack_size>1)
    {
        ++col;
        error->message="Unexpected";
        goto err;
    }
    else
    {
        res=op_stack[0];
    }

    free(op_stack);
    free(n_stack);
    free(ltr_stack);

    return res;

err:
    error->line=line;
    error->col=col;
    error->ch=ch;
    free(op_stack);
    free(n_stack);
    free(ltr_stack);
    return NULL;
}

static void dump_node(FILE *f, const struct Node *p)
{
    if(p->opcode==OP_APPLY)
    {
        fputc('`', f);
        dump_node(f, p->left);
        dump_node(f, p->right);
    }
    else
    {
        static const char *names[]=
        {
            "{IN}",  "{SW}", "{OUT}", "I",   "J",  "T", "V", "{SB}",
            "Q1",    "R",    "Q4",    "Jr",
        };

        unsigned int opcode=p->opcode;
        while(!(opcode&1))
            opcode>>=1;

        opcode>>=1;
        if(opcode<sizeof(names)/sizeof(names[0]))
            fputs(names[opcode], f);
        else
            fputs("{?}", f);
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
    int dump_mode=0;
    int allow_options=1;

    struct Node *program=new_input();
    for(int i=1; i<argc; ++i)
    {
        if(allow_options && strcmp(argv[i], "--")==0)
        {
            allow_options=0;
            continue;
        }

        if(allow_options && strcmp(argv[i], "--dump")==0)
        {
            dump_mode=1;
            continue;
        }

        FILE *f=fopen(argv[i], "rt");
        if(!f)
        {
            perror("Failed to open source file");
            return 1;
        }

        struct ParseErrorInfo error;
        struct Node *node=parse_program(f, &error);
        fclose(f);

        if(!node)
        {
            if(error.ch==EOF)
                fprintf(stderr, "%s:%u:%u: %s EOF\n", argv[i], error.line, error.col, error.message);
            else
                fprintf(stderr, "%s:%u:%u: %s '%c'\n", argv[i], error.line, error.col, error.message, error.ch);
            return 1;
        }
        if(dump_mode)
        {
            dump_node(stderr, node);
            fputc('\n', stderr);
        }

        program=new_application(node, program);
    }

    program=new_application(program, &OUT_C);
    reduce(program);

    return 126;
}
