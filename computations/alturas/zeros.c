/*
 * Zeros de ζ(s) acima da altura já verificada, com aritmética intervalar (FLINT 3 / Arb).
 *
 *   zeros nzeros T PREC        imprime N(T): o número exato de zeros com 0 < Im s ≤ T (contagem de Turing)
 *   zeros platt N LEN PREC     LEN zeros consecutivos de Z(t) a partir do N-ésimo zero não trivial de ζ
 *                              (método local de Platt; índice certificado pela contagem de Turing)
 *   zeros hardy N LEN PREC     o mesmo pelo método geral (Gram/Rosser/Turing), para conferir em alturas menores
 *
 * O N-ésimo zero de Z(t) devolvido com o índice N certificado é o N-ésimo zero de ζ contado com todos os zeros
 * (na reta ou fora dela): se houvesse um zero fora da reta Re s = 1/2 nessa faixa, a contagem não fecharia e a
 * função não devolveria esse índice. A saída é JSON com cada ordenada como bola [meio ± raio].
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/arb.h>
#include <flint/acb.h>
#include <flint/acb_dirichlet.h>

static void imprime_vec(arb_srcptr v, slong k)
{
    for (slong i = 0; i < k; i++)
    {
        char *s = arb_get_str(v + i, 48, 0);
        printf("%s\"%s\"", i ? ", " : "", s);
        flint_free(s);
    }
}

int main(int argc, char **argv)
{
    if (argc < 3) { fprintf(stderr, "uso: zeros nzeros T PREC | zeros platt|hardy N LEN PREC\n"); return 2; }
    if (strcmp(argv[1], "nzeros") == 0)
    {
        slong prec = argc > 3 ? atol(argv[3]) : 128;
        arb_t t, r; arb_init(t); arb_init(r);
        arb_set_str(t, argv[2], prec);
        acb_dirichlet_zeta_nzeros(r, t, prec);
        char *s = arb_get_str(r, 40, 0);
        printf("{\"T\": \"%s\", \"N\": \"%s\", \"prec\": %ld}\n", argv[2], s, prec);
        flint_free(s); arb_clear(t); arb_clear(r);
        flint_cleanup();
        return 0;
    }
    if (argc < 4) return 2;
    fmpz_t n; fmpz_init(n);
    if (fmpz_set_str(n, argv[2], 10)) { fprintf(stderr, "N inválido\n"); return 2; }
    slong len = atol(argv[3]);
    slong prec = argc > 4 ? atol(argv[4]) : 128;
    arb_ptr res = _arb_vec_init(len);
    slong achados = len;
    if (strcmp(argv[1], "platt") == 0)
        achados = acb_dirichlet_platt_local_hardy_z_zeros(res, n, len, prec);
    else
        acb_dirichlet_hardy_z_zeros(res, n, len, prec);
    printf("{\"metodo\": \"%s\", \"n\": \"%s\", \"len\": %ld, \"achados\": %ld, \"prec\": %ld, \"zeros\": [",
           argv[1], argv[2], len, achados, prec);
    imprime_vec(res, achados);
    printf("]}\n");
    _arb_vec_clear(res, len);
    fmpz_clear(n);
    flint_cleanup();
    return 0;
}
