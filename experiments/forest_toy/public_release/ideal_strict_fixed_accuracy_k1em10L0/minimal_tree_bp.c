/* Exact positive forest inference and passive path-batch KL evaluation.
 * Please keep true topology and coefficients inside the oracle and evaluator.
 * Sampling controllers receive only the conditional rows they requested.
 */
#include <math.h>
#include <stdint.h>
#include <stdlib.h>

int field_forest_rows(int64_t n, int64_t count, const double *strength,
                      const double *prior, const int64_t *parent,
                      const int64_t *order, const int64_t *offsets,
                      const int64_t *neighbors, const int64_t *states,
                      int64_t width, const int64_t *readouts, double *out,
                      int compute_z, int64_t vocab, double *log_z) {
    double *work = malloc((size_t)(4*n)*sizeof(double));
    if (!work) return 1;
    double *down=work, *up=work+n, *head0=work+2*n, *head1=work+3*n;
    for (int64_t q=0; q<count; ++q) {
        const int64_t *state=states+q*n;
        double total_z=0.0, compensation=0.0;
        for (int64_t k=n; k-- > 0;) {
            int64_t u=order[k];
            double a=prior[3*u], b=prior[3*u+1], c=prior[3*u+2];
            for (int64_t e=offsets[u]; e<offsets[u+1]; ++e) {
                int64_t v=neighbors[e];
                if (parent[v]==u) {
                    a *= 1.0+strength[v]*down[v];
                    b *= 1.0-strength[v]*down[v];
                }
            }
            head0[u]=a; head1[u]=b;
            double z=a+b+c;
            if (state[u]>=0) {
                down[u]=state[u]==0 ? 1.0 : (state[u]==1 ? -1.0 : 0.0);
                z=state[u]==0 ? a : (state[u]==1 ? b : c/(vocab-2));
            } else down[u]=(a-b)/z;
            if (compute_z) {
                double increment=log(z)-compensation;
                double next=total_z+increment;
                compensation=(next-total_z)-increment;
                total_z=next;
            }
        }
        if (compute_z) log_z[q]=total_z;
        for (int64_t k=0; k<n; ++k) {
            int64_t u=order[k];
            if (state[u]>=0) {
                for (int64_t e=offsets[u]; e<offsets[u+1]; ++e)
                    if (parent[neighbors[e]]==u) up[neighbors[e]]=down[u];
                continue;
            }
            double incoming=parent[u]<0 ? 0.0 : up[u];
            double a=head0[u]*(1.0+strength[u]*incoming);
            double b=head1[u]*(1.0-strength[u]*incoming);
            double c=prior[3*u+2];
            head0[u]=a; head1[u]=b;
            for (int64_t e=offsets[u]; e<offsets[u+1]; ++e) {
                int64_t v=neighbors[e];
                if (parent[v]==u) {
                    double ca=a/(1.0+strength[v]*down[v]);
                    double cb=b/(1.0-strength[v]*down[v]);
                    up[v]=(ca-cb)/(ca+cb+c);
                }
            }
        }
        for (int64_t j=0; j<width; ++j) {
            int64_t u=readouts[j], dest=3*(q*width+j);
            double z=head0[u]+head1[u]+prior[3*u+2];
            out[dest]=head0[u]/z;
            out[dest+1]=head1[u]/z;
            out[dest+2]=prior[3*u+2]/z;
        }
    }
    free(work);
    return 0;
}

/* Please use this stable f-divergence expression for small dependencies.
 * q*(p/q-1-log(p/q)) sums to KL(q||p) for normalized p and q.
 * The series avoids subtracting nearly equal logarithms, without clipping KL.
 */
static double divergence(double ratio) {
    double x=ratio-1.0;
    if (fabs(x)<1e-4)
        return x*x*(0.5+x*(-1.0/3.0+x*(0.25+x*(-0.2+x/6.0))));
    return x-log(ratio);
}

/* A collection of paths is concatenated with zero-strength separator edges.
 * Committed positions separate the remaining intervals. The true selected-batch
 * marginal is a chain in each interval; integrate every gap, including unaries.
 */
int field_chain_kl(int64_t n, const double *prior, const double *strength,
                   const int64_t *history, const int64_t *selected,
                   double *rows, double *pair_cost, double *total) {
    double *suffix=malloc((size_t)(3*n)*sizeof(double));
    if (!suffix) return 1;
    const double phi[3]={1.0,-1.0,0.0};
    double moment=0.0;
    for (int64_t i=n; i-- > 0;) {
        double z=0.0;
        for (int a=0; a<3; ++a) {
            double v=prior[3*i+a]*(1.0+strength[i]*phi[a]*moment);
            if (history[i]>=0) v=(history[i]<2 ? history[i] : 2)==a ? v : 0.0;
            suffix[3*i+a]=v; z+=v;
        }
        for (int a=0; a<3; ++a) suffix[3*i+a]/=z;
        moment=suffix[3*i]-suffix[3*i+1];
    }
    double marginal[3]={0}, bridge[9]={0}, left_marginal[3]={0};
    int have_left=0;
    double sum=0.0, compensation=0.0;
    for (int64_t i=0; i<n; ++i) {
        pair_cost[i]=0.0;
        if (i==0 || strength[i-1]==0.0) {
            for (int a=0; a<3; ++a) marginal[a]=suffix[3*i+a];
            have_left=0;
        } else {
            double transition[9], next[3]={0}, next_bridge[9]={0};
            for (int a=0; a<3; ++a) {
                double z=0.0;
                for (int b=0; b<3; ++b) {
                    transition[3*a+b]=suffix[3*i+b]*(1.0+strength[i-1]*phi[a]*phi[b]);
                    z+=transition[3*a+b];
                }
                for (int b=0; b<3; ++b) {
                    transition[3*a+b]/=z;
                    next[b]+=marginal[a]*transition[3*a+b];
                }
            }
            for (int a=0; a<3; ++a) marginal[a]=next[a];
            if (have_left) {
                for (int a=0; a<3; ++a) for (int b=0; b<3; ++b)
                    for (int c=0; c<3; ++c)
                        next_bridge[3*a+b]+=bridge[3*a+c]*transition[3*c+b];
                for (int j=0; j<9; ++j) bridge[j]=next_bridge[j];
            }
        }
        for (int a=0; a<3; ++a) rows[3*i+a]=marginal[a];
        if (history[i]>=0) { have_left=0; continue; }
        if (!selected[i]) continue;
        if (have_left) {
            double value=0.0;
            for (int a=0; a<3; ++a) for (int b=0; b<3; ++b)
                value+=left_marginal[a]*marginal[b]*divergence(bridge[3*a+b]/marginal[b]);
            if (!isfinite(value) || value<0.0) { free(suffix); return 2; }
            pair_cost[i]=value;
            double increment=value-compensation, next=sum+increment;
            compensation=(next-sum)-increment; sum=next;
        }
        have_left=1;
        for (int a=0; a<3; ++a) {
            left_marginal[a]=marginal[a];
            for (int b=0; b<3; ++b) bridge[3*a+b]=a==b ? 1.0 : 0.0;
        }
    }
    *total=sum;
    free(suffix);
    return 0;
}
