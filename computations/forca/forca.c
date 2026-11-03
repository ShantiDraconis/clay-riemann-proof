/*
 * Z(t) e derivadas com aritmética intervalar (FLINT 3 / Arb): a altura da lombada entre dois zeros, certificada.
 *
 *   forca T LEN PREC     imprime Z(T), Z'(T), Z''(T)/2, … (LEN coeficientes de Taylor) como bolas [meio ± raio]
 *
 * acb_dirichlet_hardy_z usa a fórmula de Riemann–Siegel com cota rigorosa do resto em alturas grandes.
 */
#include <stdio.h>
#include <stdlib.h>
#include <flint/flint.h>
#include <flint/arb.h>
#include <flint/acb.h>
#include <flint/acb_dirichlet.h>

int main(int argc, char **argv)
{
    if (argc < 2) { fprintf(stderr, "uso: forca T [LEN] [PREC]\n"); return 2; }
    slong len = argc > 2 ? atol(argv[2]) : 3;
    slong prec = argc > 3 ? atol(argv[3]) : 256;
    acb_t t; acb_init(t);
    arb_set_str(acb_realref(t), argv[1], prec);
    acb_ptr z = _acb_vec_init(len);
    acb_dirichlet_hardy_z(z, t, NULL, NULL, len, prec);
    printf("{\"T\": \"%s\", \"prec\": %ld, \"Z\": [", argv[1], prec);
    for (slong i = 0; i < len; i++)
    {
        char *s = arb_get_str(acb_realref(z + i), 30, 0);
        printf("%s\"%s\"", i ? ", " : "", s);
        flint_free(s);
    }
    printf("]}\n");
    _acb_vec_clear(z, len);
    acb_clear(t);
    flint_cleanup();
    return 0;
}
