/* Passive reverse-KL evaluation on a positive forest.
 * Please keep every use of the hidden graph inside this evaluator.
 * Removing unselected components gives an acyclic hypergraph with singleton
 * separators. Please orient each factor from its unique parent separator.
 * Arbitrary positive product rows require conditional factor KLs and root KLs.
 * Small boundary factors are enumerated; large ones use independent product
 * draws and the nonnegative integrand exp(log(p/q))-1-log(p/q).
 */
#include <math.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static const double phi[3] = {1., -1., 0.};

typedef struct {
    const int64_t *parent;
    const double *strength, *rows, *down, *up;
} Context;

static void transition(const Context *c, int64_t u, int64_t v, double *out) {
    int forward = c->parent[v] == u;
    double theta = c->strength[forward ? v : u];
    double incoming = forward ? c->up[v] : c->down[u];
    double cavity[3], z=0.;
    for (int b=0; b<3; ++b) {
        cavity[b] = c->rows[3*v+b]/(1.+theta*phi[b]*incoming);
        z += cavity[b];
    }
    for (int b=0; b<3; ++b) cavity[b] /= z;
    for (int a=0; a<3; ++a) {
        z=0.;
        for (int b=0; b<3; ++b) {
            out[3*a+b] = cavity[b]*(1.+theta*phi[a]*phi[b]);
            z += out[3*a+b];
        }
        for (int b=0; b<3; ++b) out[3*a+b] /= z;
    }
}

static void multiply(double *left, const double *right) {
    double result[9]={0.};
    for (int a=0; a<3; ++a) for (int b=0; b<3; ++b)
        for (int k=0; k<3; ++k) result[3*a+b] += left[3*a+k]*right[3*k+b];
    for (int a=0; a<3; ++a) {
        double z=result[3*a]+result[3*a+1]+result[3*a+2];
        for (int b=0; b<3; ++b) left[3*a+b]=result[3*a+b]/z;
    }
}

static double integrand(double x) {
    if (fabs(x)<1e-4)
        return x*x*(.5+x*(1./6.+x*(1./24.+x*(1./120.+x/720.))));
    return expm1(x)-x;
}

static double log_ratio(double p, double q) {
    return fabs(p-q)<.5*q ? log1p((p-q)/q) : log(p)-log(q);
}

static double pair_kl(const double *left, const double *right, const double *matrix) {
    double total=0.;
    for (int a=0; a<3; ++a) for (int b=0; b<3; ++b)
        total += left[a]*right[b]*integrand(log_ratio(matrix[3*a+b],right[b]));
    return total;
}

static uint64_t next_random(uint64_t *state) {
    uint64_t z=(*state += UINT64_C(0x9e3779b97f4a7c15));
    z=(z^(z>>30))*UINT64_C(0xbf58476d1ce4e5b9);
    z=(z^(z>>27))*UINT64_C(0x94d049bb133111eb);
    return z^(z>>31);
}

static double uniform(uint64_t *state) {
    return ((next_random(state)>>11)+.5)*(1./9007199254740992.);
}

/* Please normalize each upward message before multiplying at its parent.
 * This computes the boundary probability without underflow for large factors.
 * Boundary vertices occupy the first k positions; the first is the root.
 */
static double boundary_log_conditional_mass(int64_t count, int64_t k, const int64_t *labels,
        const int64_t *parent, const int64_t *order, const double *matrix,
        double *work) {
    for (int64_t i=0; i<3*count; ++i) work[i]=1.;
    double scale=0.;
    for (int64_t pos=count; pos-- > 0;) {
        int64_t u=order[pos];
        if (u<k) for (int a=0; a<3; ++a)
            if (a!=labels[u]) work[3*u+a]=0.;
        if (parent[u]<0) {
            /* The root label is fixed, so please omit its marginal probability. */
            return log(work[3*u+labels[u]])+scale;
        }
        double message[3]={0.};
        for (int a=0; a<3; ++a) for (int b=0; b<3; ++b)
            message[a] += matrix[9*u+3*a+b]*work[3*u+b];
        double maximum=fmax(message[0], fmax(message[1],message[2]));
        scale += log(maximum);
        for (int a=0; a<3; ++a) work[3*parent[u]+a] *= message[a]/maximum;
    }
    return NAN;
}

int forest_batch_product_kl(int64_t n, const double *prior, const double *strength,
        const int64_t *parent, const int64_t *order, const int64_t *offsets,
        const int64_t *neighbors, const int64_t *history, const int64_t *selected,
        const double *sampling_rows,
        int64_t exact_arity, int64_t samples, uint64_t seed,
        double *rows, double *pair_cost, double *total, double *variance, int64_t *stats) {
    double *real=calloc((size_t)(16*n),sizeof(double));
    int64_t *integer=calloc((size_t)(12*n),sizeof(int64_t));
    if (!real || !integer) { free(real); free(integer); return 1; }
    double *down=real, *up=real+n, *head0=real+2*n, *head1=real+3*n;
    double *matrix=real+4*n, *work=real+13*n;
    int64_t *seen=integer, *core=integer+n, *degree=integer+2*n;
    int64_t *hidden=integer+3*n, *boundary=integer+4*n, *queue=integer+5*n;
    int64_t *anchors=integer+6*n, *index=integer+7*n;
    int64_t *cparent=integer+8*n, *corder=integer+9*n;
    int64_t *rank=integer+10*n, *has_parent=integer+11*n;
    for (int64_t i=0; i<n; ++i) rank[order[i]]=i;
    int result=0;
    *total=0.; *variance=0.;
    for (int j=0; j<6; ++j) stats[j]=0;
    for (int64_t u=0; u<n; ++u) { index[u]=-1; pair_cost[u]=0.; }
    /* Please compute exact current-history marginal and cavity messages first. */
    for (int64_t pos=n; pos-- > 0;) {
        int64_t u=order[pos];
        double a=prior[3*u], b=prior[3*u+1], c=prior[3*u+2];
        for (int64_t e=offsets[u]; e<offsets[u+1]; ++e) {
            int64_t v=neighbors[e];
            if (parent[v]==u) { a*=1.+strength[v]*down[v]; b*=1.-strength[v]*down[v]; }
        }
        head0[u]=a; head1[u]=b;
        down[u]=history[u]<0 ? (a-b)/(a+b+c) : (history[u]==0 ? 1. : (history[u]==1 ? -1. : 0.));
    }
    for (int64_t pos=0; pos<n; ++pos) {
        int64_t u=order[pos];
        if (history[u]>=0) {
            for (int a=0; a<3; ++a) rows[3*u+a]=(history[u]<2 ? history[u] : 2)==a;
            for (int64_t e=offsets[u]; e<offsets[u+1]; ++e)
                if (parent[neighbors[e]]==u) up[neighbors[e]]=down[u];
            continue;
        }
        double incoming=parent[u]<0 ? 0. : up[u];
        double a=head0[u]*(1.+strength[u]*incoming), b=head1[u]*(1.-strength[u]*incoming), c=prior[3*u+2];
        double z=a+b+c;
        rows[3*u]=a/z; rows[3*u+1]=b/z; rows[3*u+2]=c/z;
        for (int64_t e=offsets[u]; e<offsets[u+1]; ++e) {
            int64_t v=neighbors[e];
            if (parent[v]==u) {
                double ca=a/(1.+strength[v]*down[v]), cb=b/(1.-strength[v]*down[v]);
                up[v]=(ca-cb)/(ca+cb+c);
            }
        }
    }
    Context context={parent,strength,rows,down,up};
    for (int64_t v=0; v<n; ++v) {
        int64_t u=parent[v];
        if (u>=0 && selected[u] && selected[v]) {
            double t[9]; transition(&context,u,v,t);
            if (has_parent[v]++) { result=6; goto cleanup; }
            pair_cost[v]=pair_kl(sampling_rows+3*u,sampling_rows+3*v,t);
            *total += pair_cost[v]; ++stats[0];
            if (stats[2]<2) stats[2]=2;
        }
    }
    for (int64_t start=0; start<n; ++start) {
        if (history[start]>=0 || selected[start] || seen[start]) continue;
        int64_t nh=0, nb=0, pending=1;
        queue[0]=start; seen[start]=1;
        while (pending) {
            int64_t u=queue[--pending]; hidden[nh++]=u;
            for (int64_t e=offsets[u]; e<offsets[u+1]; ++e) {
                int64_t v=neighbors[e];
                if (history[v]>=0) continue;
                if (selected[v]) boundary[nb++]=v;
                else if (!seen[v]) { seen[v]=1; queue[pending++]=v; }
            }
        }
        ++stats[4];
        if (nb<2) continue;
        /* Please choose the ancestor separator before building compressed indices.
         * In a topmost hidden component, the earliest boundary is a valid root.
         */
        int64_t first=0;
        for (int64_t i=1; i<nb; ++i)
            if (rank[boundary[i]]<rank[boundary[first]]) first=i;
        int64_t swap=boundary[0]; boundary[0]=boundary[first]; boundary[first]=swap;
        for (int64_t i=1; i<nb; ++i)
            if (has_parent[boundary[i]]++) { result=6; goto cleanup; }
        if (nb>stats[2]) stats[2]=nb;
        /* Please prune side branches before contracting hidden degree-two paths. */
        for (int64_t i=0; i<nh; ++i) core[hidden[i]]=1;
        for (int64_t i=0; i<nb; ++i) { core[boundary[i]]=1; degree[boundary[i]]=1; }
        int64_t front=0, back=0;
        for (int64_t i=0; i<nh; ++i) {
            int64_t u=hidden[i]; degree[u]=0;
            for (int64_t e=offsets[u]; e<offsets[u+1]; ++e) degree[u]+=core[neighbors[e]];
            if (degree[u]<2) queue[back++]=u;
        }
        while (front<back) {
            int64_t u=queue[front++];
            if (!core[u]) continue;
            core[u]=0;
            for (int64_t e=offsets[u]; e<offsets[u+1]; ++e) {
                int64_t v=neighbors[e];
                if (core[v] && --degree[v]==1 && !selected[v]) queue[back++]=v;
            }
        }
        int64_t na=0;
        for (int64_t i=0; i<nb; ++i) anchors[na++]=boundary[i];
        for (int64_t i=0; i<nh; ++i) {
            int64_t u=hidden[i];
            if (core[u] && degree[u]!=2) anchors[na++]=u;
        }
        if (na>stats[5]) stats[5]=na;
        for (int64_t i=0; i<na; ++i) { index[anchors[i]]=i; cparent[i]=-2; }
        cparent[0]=-1; corder[0]=0; front=0; back=1;
        while (front<back) {
            int64_t ai=corder[front++], u=anchors[ai];
            for (int64_t e=offsets[u]; e<offsets[u+1]; ++e) {
                int64_t v=neighbors[e];
                if (!core[v]) continue;
                double bridge[9]; transition(&context,u,v,bridge);
                int64_t previous=u;
                while (index[v]<0) {
                    int64_t next=-1;
                    for (int64_t f=offsets[v]; f<offsets[v+1]; ++f)
                        if (core[neighbors[f]] && neighbors[f]!=previous) { next=neighbors[f]; break; }
                    if (next<0) { result=2; goto cleanup; }
                    double step[9]; transition(&context,v,next,step); multiply(bridge,step);
                    previous=v; v=next;
                }
                int64_t bi=index[v];
                if (cparent[bi]!=-2) continue;
                cparent[bi]=ai; corder[back++]=bi;
                memcpy(matrix+9*bi,bridge,9*sizeof(double));
            }
        }
        if (back!=na) { result=3; goto cleanup; }
        if (nb==2) {
            *total += pair_kl(sampling_rows+3*boundary[0],sampling_rows+3*boundary[1],matrix+9);
            ++stats[0];
        } else {
            int exact=nb<=exact_arity;
            int64_t draws=samples;
            if (exact) { draws=1; for (int64_t i=0; i<nb; ++i) draws*=3; }
            double average=0., m2=0., exact_sum=0.;
            for (int64_t draw=0; draw<draws; ++draw) {
                int64_t encoded=draw;
                double logq_joint=0., logq_children=0.;
                for (int64_t i=0; i<nb; ++i) {
                    const double *p=sampling_rows+3*boundary[i];
                    if (exact) { queue[i]=encoded%3; encoded/=3; }
                    else { double u=uniform(&seed); queue[i]=u<p[0] ? 0 : (u<p[0]+p[1] ? 1 : 2); }
                    double term=log(p[queue[i]]);
                    logq_joint += term;
                    if (i) logq_children += term;
                }
                double logp=boundary_log_conditional_mass(na,nb,queue,cparent,corder,matrix,work);
                double value=integrand(logp-logq_children);
                if (!isfinite(value) || value<0.) { result=4; goto cleanup; }
                if (exact) exact_sum += exp(logq_joint)*value;
                else { double delta=value-average; average+=delta/(draw+1); m2+=delta*(value-average); }
            }
            if (exact) { *total += exact_sum; ++stats[0]; }
            else { *total += average; *variance += m2/(samples-1)/samples; ++stats[1]; stats[3]+=samples; }
        }
        for (int64_t i=0; i<nh; ++i) core[hidden[i]]=0;
        for (int64_t i=0; i<nb; ++i) core[boundary[i]]=0;
        for (int64_t i=0; i<na; ++i) index[anchors[i]]=-1;
    }
    /* Every selected vertex is a root or a child of exactly one factor. */
    for (int64_t u=0; u<n; ++u) if (selected[u] && !has_parent[u]) {
        for (int a=0; a<3; ++a)
            *total += sampling_rows[3*u+a]*integrand(log_ratio(rows[3*u+a],sampling_rows[3*u+a]));
    }
    if (!isfinite(*total) || !isfinite(*variance) || *total<0. || *variance<0.) result=5;
cleanup:
    free(real); free(integer);
    return result;
}
