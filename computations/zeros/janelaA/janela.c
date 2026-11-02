/* Verificação rigorosa de RH numa janela de alturas, pelo método de Platt (FLINT/Arb 3.6.0).
   Uso: janela n len prec
   Devolve as alturas dos zeros n, n+1, ..., n+len-1 da função Z de Hardy, como bolas da Arb.
   A Arb só devolve um bloco depois de fixar N(t) por Turing nos pontos de Gram âncora e de
   achar entre eles exatamente esse número de trocas de sinal de Z: logo todos os zeros de
   zeta na faixa com altura no bloco (qualquer sigma) estão na reta e são simples. */
#include <stdlib.h>
#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/arb.h>
#include <flint/acb_dirichlet.h>
#include <flint/profiler.h>

int main(int argc, char *argv[])
{
    fmpz_t n, k;
    slong len, prec, found, i;
    arb_ptr p;
    timeit_t timer;
    if (argc < 4) { flint_printf("uso: janela n len prec\n"); return 1; }
    fmpz_init(n); fmpz_init(k);
    fmpz_set_str(n, argv[1], 10);
    len = atol(argv[2]);
    prec = atol(argv[3]);
    flint_set_num_threads(argc > 4 ? atoi(argv[4]) : 1);
    p = _arb_vec_init(len);
    timeit_start(timer);
    found = acb_dirichlet_platt_hardy_z_zeros(p, n, len, prec);
    timeit_stop(timer);
    flint_printf("# FLINT %s, prec %wd bits, inicio n = ", FLINT_VERSION, prec);
    fmpz_print(n);
    flint_printf(", pedidos %wd, achados %wd, tempo %wd ms\n", len, found, timer->wall);
    fmpz_set(k, n);
    for (i = 0; i < found; i++)
    {
        fmpz_print(k);
        flint_printf("\t");
        arb_printn(p + i, 30, 0);
        flint_printf("\n");
        fmpz_add_ui(k, k, 1);
    }
    _arb_vec_clear(p, len);
    fmpz_clear(n); fmpz_clear(k);
    flint_cleanup();
    return found == len ? 0 : 2;
}
