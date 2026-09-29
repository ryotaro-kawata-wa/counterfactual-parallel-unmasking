/* Exact sum-product for a forest with one positive coefficient per edge.
 * Please keep the coefficients inside the oracle. Sampling decisions receive
 * only the requested conditional rows, never this graph or its weights.
 */
#include <stdint.h>
#include <stdlib.h>

int weighted_forest_rows(int64_t n, int64_t count, const double *strength,
                         const int64_t *parent, const int64_t *order,
                         const int64_t *offsets, const int64_t *neighbors,
                         const int64_t *states, int64_t width,
                         const int64_t *readouts, double *out) {
    double *work = malloc((size_t)(4*n)*sizeof(double));
    if (!work) return 1;
    double *down = work, *up = work+n, *head0 = work+2*n, *head1 = work+3*n;
    for (int64_t q=0; q<count; ++q) {
        const int64_t *state = states+q*n;
        for (int64_t k=n; k-- > 0;) {
            int64_t u=order[k];
            if (state[u]>=0) {
                down[u] = state[u]==0 ? 1.0 : (state[u]==1 ? -1.0 : 0.0);
                continue;
            }
            double a=0.4, b=0.4;
            for (int64_t e=offsets[u]; e<offsets[u+1]; ++e) {
                int64_t v=neighbors[e];
                if (parent[v]==u) {
                    a *= 1.0+strength[v]*down[v];
                    b *= 1.0-strength[v]*down[v];
                }
            }
            head0[u]=a; head1[u]=b;
            down[u]=(a-b)/(a+b+0.2);
        }
        for (int64_t k=0; k<n; ++k) {
            int64_t u=order[k];
            if (state[u]>=0) {
                for (int64_t e=offsets[u]; e<offsets[u+1]; ++e) {
                    int64_t v=neighbors[e];
                    if (parent[v]==u) up[v]=down[u];
                }
                continue;
            }
            double incoming=parent[u]<0 ? 0.0 : up[u];
            double a=head0[u]*(1.0+strength[u]*incoming);
            double b=head1[u]*(1.0-strength[u]*incoming);
            head0[u]=a; head1[u]=b;
            for (int64_t e=offsets[u]; e<offsets[u+1]; ++e) {
                int64_t v=neighbors[e];
                if (parent[v]==u) {
                    /* Please remove the same child-edge factor used above. */
                    double ca=a/(1.0+strength[v]*down[v]);
                    double cb=b/(1.0-strength[v]*down[v]);
                    up[v]=(ca-cb)/(ca+cb+0.2);
                }
            }
        }
        for (int64_t j=0; j<width; ++j) {
            int64_t u=readouts[j], destination=3*(q*width+j);
            double z=head0[u]+head1[u]+0.2;
            out[destination]=head0[u]/z;
            out[destination+1]=head1[u]/z;
            out[destination+2]=0.2/z;
        }
    }
    free(work);
    return 0;
}
