// Testes do "eixo Riemann" em C++, espelhando ClayRiemannProof/EixoRiemann/Algebra.lean.
// Compilar: g++ -std=c++17 -O2 -o test_eixo test_eixo.cpp && ./test_eixo
#include <array>
#include <cmath>
#include <complex>
#include <cstdio>
#include <random>

using R3 = std::array<double, 3>;
using C = std::complex<double>;
struct P { C z, w; };

static R3 r3_mul(const R3& x, const R3& y) {
  return {x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0],
          x[0] * y[2] + x[2] * y[0] + x[2] * y[2] + x[1] * y[2] + x[2] * y[1]};
}
static P dual_mul(const P& x, const P& y) { return {x.z * y.z, x.z * y.w + x.w * y.z}; }
static P idem_mul(const P& x, const P& y) { return {x.z * y.z, x.z * y.w + x.w * y.z + x.w * y.w}; }

static bool perto(double a, double b) { return std::fabs(a - b) <= 1e-9 * (1 + std::fabs(a) + std::fabs(b)); }
static bool perto(const R3& u, const R3& v) { return perto(u[0], v[0]) && perto(u[1], v[1]) && perto(u[2], v[2]); }
static bool perto(const P& u, const P& v) {
  return std::abs(u.z - v.z) <= 1e-9 * (1 + std::abs(u.z)) && std::abs(u.w - v.w) <= 1e-9 * (1 + std::abs(u.w));
}

static int falhas = 0;
static void confere(const char* nome, bool ok) {
  std::printf("%s %s\n", ok ? "OK   " : "FALHA", nome);
  if (!ok) ++falhas;
}

int main() {
  std::mt19937_64 g(20261112);
  std::uniform_real_distribution<double> u(-3, 3);
  auto r3 = [&] { return R3{u(g), u(g), u(g)}; };
  auto p = [&] { return P{C(u(g), u(g)), C(u(g), u(g))}; };

  confere("R3: (5+2i+0,1R)(3+i+0,2R) = 13+11i+1,82R", perto(r3_mul({5, 2, 0.1}, {3, 1, 0.2}), R3{13, 11, 1.82}));

  const R3 i{0, 1, 0}, R{0, 0, 1};
  R3 esq = r3_mul(r3_mul(i, i), R), dir = r3_mul(i, r3_mul(i, R));
  std::printf("      (i*i)*R = (%g, %g, %g)   i*(i*R) = (%g, %g, %g)\n", esq[0], esq[1], esq[2], dir[0], dir[1], dir[2]);
  confere("R3: nao associativa em (i, i, R)", !perto(esq, dir));

  int quebra = 0;
  for (int k = 0; k < 2000; ++k) {
    R3 x = r3(), y = r3(), z = r3();
    if (!perto(r3_mul(r3_mul(x, y), z), r3_mul(x, r3_mul(y, z)))) ++quebra;
  }
  std::printf("      associatividade falha em %d de 2000 trios\n", quebra);
  confere("R3: associatividade falha em trios aleatorios", quebra > 0);

  bool dual_ok = true, idem_ok = true;
  for (int k = 0; k < 2000; ++k) {
    P x = p(), y = p(), z = p();
    dual_ok = dual_ok && perto(dual_mul(dual_mul(x, y), z), dual_mul(x, dual_mul(y, z)));
    idem_ok = idem_ok && perto(idem_mul(idem_mul(x, y), z), idem_mul(x, idem_mul(y, z)));
  }
  confere("Dual (eps^2 = 0): associativa em 2000 trios", dual_ok);
  confere("Idem (e^2 = e): associativa em 2000 trios", idem_ok);

  P e{0, 1}, ie = idem_mul(P{C(0, 1), 0}, e);
  confere("Idem: i*e = (0, i), nao e", perto(ie, P{0, C(0, 1)}));

  std::printf("RESUMO: %d falha(s)\n", falhas);
  return falhas ? 1 : 0;
}
