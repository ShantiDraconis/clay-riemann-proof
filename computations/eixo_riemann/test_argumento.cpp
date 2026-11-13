// Argumento no eixo Riemann em C++: idempotentes de Idem, colapso de projeções 2x2, 3-4-1, torção.
// Compilar: g++ -std=c++17 -O2 -Wall
#include <cmath>
#include <complex>
#include <cstdio>
#include <random>
#include <vector>

using C = std::complex<double>;
static int falhas = 0;
static void confere(const char* nome, bool ok) {
  std::printf("%s %s\n", ok ? "ok   " : "FALHA", nome);
  if (!ok) ++falhas;
}

int main() {
  // 1. idempotentes de Idem numa grade de inteiros gaussianos
  int achados = 0;
  bool certos = true;
  for (int a = -3; a <= 3; ++a)
    for (int b = -3; b <= 3; ++b)
      for (int c = -3; c <= 3; ++c)
        for (int d = -3; d <= 3; ++d) {
          C z(a, b), w(c, d);
          if (std::abs(z * z - z) < 1e-12 && std::abs(z * w + w * z + w * w - w) < 1e-12) {
            ++achados;
            certos &= (b == 0 && d == 0) && ((a == 0 && (c == 0 || c == 1)) || (a == 1 && (c == 0 || c == -1)));
          }
        }
  confere("Idem: exatamente 4 idempotentes, 0, 1, e, 1 - e", achados == 4 && certos);

  // 2. colapso: projeção 2x2 de posto 1, P = v w^T / (w^T v): P^2 = P, autovalores 0 e 1
  std::mt19937_64 rng(5);
  std::normal_distribution<double> g(0, 1);
  bool col = true;
  for (int it = 0; it < 2000; ++it) {
    C v0(g(rng), g(rng)), v1(g(rng), g(rng)), w0(g(rng), g(rng)), w1(g(rng), g(rng));
    C k = w0 * v0 + w1 * v1;
    if (std::abs(k) < 1e-3) continue;
    C P[2][2] = {{v0 * w0 / k, v0 * w1 / k}, {v1 * w0 / k, v1 * w1 / k}};
    C tr = P[0][0] + P[1][1], det = P[0][0] * P[1][1] - P[0][1] * P[1][0];
    C disc = std::sqrt(tr * tr - 4.0 * det);
    C l1 = (tr + disc) / 2.0, l2 = (tr - disc) / 2.0;
    auto bin = [](C l) { return std::fmin(std::abs(l), std::abs(l - 1.0)) < 1e-7; };
    double err = 0;
    for (int i = 0; i < 2; ++i)
      for (int j = 0; j < 2; ++j) err += std::abs(P[i][0] * P[0][j] + P[i][1] * P[1][j] - P[i][j]);
    col &= err < 1e-8 && bin(l1) && bin(l2);
  }
  confere("colapso: 2000 projecoes 2x2, autovalores so 0 e 1", col);
  confere("autovalor 1/(1 + 4 delta^2) = 4/5 em delta = 1/4: nao e 0 nem 1",
          std::fabs(1.0 / (1.0 + 4 * 0.0625) - 0.8) < 1e-15);

  // 3. 3-4-1
  double mn = 1e9;
  for (int i = 0; i <= 200000; ++i) {
    double t = 2 * M_PI * i / 200000.0;
    mn = std::fmin(mn, 3 + 4 * std::cos(t) + std::cos(2 * t));
  }
  confere("3 + 4 cos + cos 2 >= 0", mn >= -1e-12);

  // 4. torção: isometria e troca os lados
  std::uniform_real_distribution<double> u(-3, 3);
  bool iso = true;
  for (int it = 0; it < 2000; ++it) {
    C a(u(rng), u(rng)), b(u(rng), u(rng));
    C ta = 1.0 - std::conj(a), tb = 1.0 - std::conj(b);
    iso &= std::fabs(std::abs(ta - tb) - std::abs(a - b)) < 1e-12;
    if (std::fabs(a.real() - 0.5) > 1e-9) iso &= (a.real() - 0.5) * (ta.real() - 0.5) < 0;
  }
  confere("torcao: isometria e troca os lados da reta", iso);

  std::printf("\n%d falha(s)\n", falhas);
  return falhas ? 1 : 0;
}
