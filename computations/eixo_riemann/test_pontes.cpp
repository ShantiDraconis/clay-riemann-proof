// Pontes em C++: a ponte só tem duas pontas (e -> 0, e -> 1) e o quarteto age em C^4 permutando coordenadas.
// Compilar: g++ -std=c++17 -O2 -Wall
#include <array>
#include <cmath>
#include <complex>
#include <cstdio>
#include <random>

using C = std::complex<double>;
static int falhas = 0;
static void confere(const char* nome, bool ok) {
  std::printf("%s %s\n", ok ? "ok   " : "FALHA", nome);
  if (!ok) ++falhas;
}

struct Idem { C z, w; };
static Idem mul(Idem x, Idem y) { return {x.z * y.z, x.z * y.w + x.w * y.z + x.w * y.w}; }
static C avalia(C c, Idem x) { return x.z + c * x.w; }

// qualquer função serve: a permutação vem só da geometria do quarteto
static C f(C s) { return std::exp(s) + s * s * s - C(0.3, 1.7) * s; }
static std::array<C, 4> Q(C s) { return {f(s), f(1.0 - s), f(std::conj(s)), f(1.0 - std::conj(s))}; }

int main() {
  std::mt19937_64 rng(11);
  std::uniform_real_distribution<double> u(-2, 2);
  auto rc = [&] { return C(u(rng), u(rng)); };

  double erro[5] = {0, 0, 0, 0, 0};
  const double cs[5] = {0, 1, 0.25, 0.5, 0.75};
  for (int k = 0; k < 5; ++k)
    for (int it = 0; it < 500; ++it) {
      Idem x{rc(), rc()}, y{rc(), rc()};
      erro[k] = std::fmax(erro[k], std::abs(avalia(cs[k], mul(x, y)) - avalia(cs[k], x) * avalia(cs[k], y)));
    }
  std::printf("      erro do homomorfismo: c=0 %.1e, c=1 %.1e, c=0.25 %.2f, c=0.5 %.2f, c=0.75 %.2f\n",
              erro[0], erro[1], erro[2], erro[3], erro[4]);
  confere("e -> c respeita o produto de Idem so em c = 0 e c = 1", erro[0] < 1e-12 && erro[1] < 1e-12 &&
                                                                     erro[2] > 0.1 && erro[3] > 0.1 && erro[4] > 0.1);

  bool perm = true;
  const int pe[4] = {2, 3, 0, 1}, pt[4] = {1, 0, 3, 2}, pr[4] = {3, 2, 1, 0};
  for (int it = 0; it < 1000; ++it) {
    C s = rc();
    auto q = Q(s), qe = Q(std::conj(s)), qt = Q(1.0 - s), qr = Q(1.0 - std::conj(s));
    for (int k = 0; k < 4; ++k)
      perm &= std::abs(qe[k] - q[pe[k]]) + std::abs(qt[k] - q[pt[k]]) + std::abs(qr[k] - q[pr[k]]) < 1e-9;
  }
  confere("quarteto como operador: Klein age em C^4 permutando coordenadas (1000 pontos)", perm);

  unsigned long long n = 4, seq[5];
  for (int k = 0; k < 5; ++k) { seq[k] = n; n = n * n; }
  confere("4 -> 16 -> 256 -> 65536 -> 4294967296 (|Z0|^(2^k))",
          seq[0] == 4 && seq[1] == 16 && seq[2] == 256 && seq[3] == 65536 && seq[4] == 4294967296ULL);

  std::printf("\n%d falha(s)\n", falhas);
  return falhas ? 1 : 0;
}
