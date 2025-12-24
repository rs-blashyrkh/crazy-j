// Blashyrkh.maniac.coding
// BTC:1Maniaccv5vSQVuwrmRtfazhf2WsUJ1KyD DOGE:DManiac9Gk31A4vLw9fLN9jVDFAQZc2zPj

#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <string.h>


struct Enumerator
{
    unsigned int n;
    int *counters;
    int *sums;
    char *strbuf;
};

static int allocate_k_points(struct Enumerator *e, unsigned int from_pos, unsigned int k)
{
    while(from_pos<e->n)
    {
        const int mx=e->n-1-from_pos;
        const int pt=k>mx?mx:k;

        if(e->sums[from_pos]<from_pos)
            return 0;

        e->counters[from_pos]=pt;
        e->sums[from_pos+1]=e->sums[from_pos]+pt;

        ++from_pos;
        k-=pt;
    }
    return k==0;
}

static int next_scheme(struct Enumerator *e)
{
    for(unsigned int pos=e->n; pos>0; )
    {
        --pos;

        if(e->counters[pos]>0)
        {
            --e->counters[pos];
            --e->sums[pos+1];
            if(allocate_k_points(e, pos+1, e->n-1-e->sums[pos+1]))
                return 1;
        }
    }
    return 0;
}

static void init_pattern(struct Enumerator *e)
{
    unsigned int j=0;
    for(unsigned int i=0; i<e->n; ++i)
    {
        for(int k=0; k<e->counters[i]; ++k)
            e->strbuf[j++]='`';
        e->strbuf[j++]=e->counters[i]>0?'j':'i';
    }
    e->strbuf[j]='\0';
}

static int next_pattern(struct Enumerator *e)
{
    int carry=1;
    for(unsigned int i=e->n; i>0 && carry>0; )
    {
        --i;

        if(e->counters[i]==0)
        {
            char *p=e->strbuf+i+e->sums[i+1];
            if(*p=='i')
            {
                *p='j';
                carry=0;
            }
            else
            {
                *p='i';
            }
        }
    }
    return !carry;
}

void enumerator_init(struct Enumerator *e, unsigned int n)
{
    e->n=n;
    e->counters=(int *)malloc(sizeof(int)*n);
    e->sums=(int *)malloc(sizeof(int)*(n+1));
    e->strbuf=(char *)malloc(2*n);

    e->sums[0]=0;
    allocate_k_points(e, 0, n-1);
    init_pattern(e);
}

int enumerator_free(struct Enumerator *e)
{
    free(e->counters);
    free(e->sums);
    free(e->strbuf);
}

int enumerator_next(struct Enumerator *e)
{
    if(next_pattern(e))
        return 1;
    if(next_scheme(e))
    {
        init_pattern(e);
        return 1;
    }
    return 0;
}

static int parse_n_specification(char *arg, unsigned int *n_min, unsigned int *n_max)
{
    char *endp;

    char *hyph=strchr(arg, '-');
    if(!hyph)
    {
        *n_min=*n_max=strtoul(arg, &endp, 10);
        if(endp==arg || *endp!='\0')
        {
            return 0;
        }
    }
    else
    {
        *hyph='\0';
        if(*arg=='\0')
        {
            *n_min=1;
        }
        else
        {
            *n_min=strtoul(arg, &endp, 10);
            if(endp==arg || *endp!='\0')
            {
                return 0;
            }
        }

        arg=hyph+1;
        if(*arg=='\0')
        {
            *n_max=INT_MAX;
        }
        else
        {
            *n_max=strtoul(arg, &endp, 10);
            if(endp==arg || *endp!='\0')
            {
                return 0;
            }
        }
    }
    return 1;
}

int main(int argc, char *argv[])
{
    unsigned int n_min;
    unsigned int n_max;

    if(argc==1)
    {
        n_min=1;
        n_max=INT_MAX;
    }
    else if(argc==2)
    {
        if(!parse_n_specification(argv[1], &n_min, &n_max))
        {
            fprintf(stderr, "Failed to parse N\n");
            return 1;
        }
    }
    else
    {
        fprintf(stderr, "Too many arguments. Sorry, I don't know what to do\n");
        return 1;
    }

    if(n_min<1)
        n_min=1;

    for(unsigned int n=n_min; n<=n_max; ++n)
    {
        struct Enumerator e;
        enumerator_init(&e, n);

        for(;;)
        {
            printf("%s\n", e.strbuf);
            if(!enumerator_next(&e))
                break;
        }

        enumerator_free(&e);
    }
    return 0;
}
