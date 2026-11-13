// Quartetos, Idem e C^4 em C++: mesmos testes geométricos e algébricos de test_quarteto.py.
// Pontos em coordenadas inteiras: s = (a/20, b), com 1 - s = (20 - a)/20. Compilar: g++ -std=c++17 -O2 -Wall
#include <algorithm>
#include <complex>
#include <cstdio>
#include <random>
#include <set>
#include <utility>
#include <vector>

using P = std::pair<int, int>;  // (20·Re, Im)
using C = std::complex<double>;
static int falhas = 0;

static void confere(const char* nome, bool ok) {
  std::printf("%s %s\n", ok ? "ok   " : "FALHA", nome);
  if (!ok) ++falhas;
}

static P esp(P s) { return {s.first, -s.second}; }
static P ten(P s) { return {20 - s.first, -s.second}; }
static P tor(P s) { return {20 - s.first, s.second}; }
static std::set<P> orb(P s) { return {s, esp(s), ten(s), tor(s)}; }

int main() {
  // 1. tamanhos das órbitas
  bool t4 = true, t2 = true;
  for (int a = -20; a <= 40; ++a)
    for (int b = -10; b <= 10; ++b) {
      size_t n = orb({a, b}).size();
      if (a != 10 && b != 0 && n != 4) t4 = false;
      if (a == 10 && b != 0 && n != 2) t2 = false;
    }
  confere("quarteto: 4 pontos fora da reta e do eixo real; 2 na reta", t4 && t2);

  // 2. iguais ou disjuntos, busca exaustiva
  std::vector<P> g;
  for (int a = -10; a <= 30; a += 2)
    for (int b = -6; b <= 6; ++b) g.push_back({a, b});
  long parciais = 0, pares = 0;
  for (size_t i = 0; i < g.size(); ++i)
    for (size_t j = i + 1; j < g.size(); ++j) {
      ++pares;
      auto A = orb(g[i]), B = orb(g[j]);
      std::vector<P> in;
      std::set_intersection(A.begin(), A.end(), B.begin(), B.end(), std::back_inserter(in));
      if (!in.empty() && A != B) ++parciais;
    }
  std::printf("      %ld pares, %ld com interseccao parcial\n", pares, parciais);
  confere("quartetos iguais ou disjuntos (nao existem quartetos conectados)", parciais == 0);

  // 3. contagem 4k / 2k / N(T) = 2k + m
  std::mt19937_64 rng(20261112);
  bool cont = true;
  for (int it = 0; it < 500; ++it) {
    int k = rng() % 7, m = rng() % 5;
    std::set<P> reps, reta, S;
    while ((int)reps.size() < k) reps.insert({11 + (int)(rng() % 9), 1 + (int)(rng() % 60)});
    while ((int)reta.size() < m) reta.insert({10, 1 + (int)(rng() % 60)});
    for (auto r : reps) for (auto x : orb(r)) S.insert(x);
    for (auto r : reta) for (auto x : orb(r)) S.insert(x);
    int fora = 0, cimaFora = 0, cima = 0;
    for (auto x : S) {
      if (x.first != 10) { ++fora; if (x.second > 0) ++cimaFora; }
      if (x.second > 0) ++cima;
    }
    if (fora != 4 * k || cimaFora != 2 * k || cima != 2 * k + m) cont = false;
  }
  confere("contagem: #fora = 4k, #fora com Im>0 = 2k, N(T) = 2k + m", cont);

  // 4. Idem = C x C, associativa
  std::uniform_real_distribution<double> u(-3, 3);
  auto rc = [&] { return C(u(rng), u(rng)); };
  auto mul = [](std::pair<C, C> x, std::pair<C, C> y) {
    return std::make_pair(x.first * y.first, x.first * y.second + x.second * y.first + x.second * y.second);
  };
  bool iso = true, ass = true;
  for (int it = 0; it < 2000; ++it) {
    std::pair<C, C> x{rc(), rc()}, y{rc(), rc()}, w{rc(), rc()};
    auto p = mul(x, y);
    iso &= std::abs(p.first - x.first * y.first) +
               std::abs(p.first + p.second - (x.first + x.second) * (y.first + y.second)) < 1e-9;
    auto a = mul(mul(x, y), w), b = mul(x, mul(y, w));
    ass &= std::abs(a.first - b.first) + std::abs(a.second - b.second) < 1e-9;
  }
  confere("Idem: (z, w) -> (z, z + w) preserva o produto; associativa", iso && ass);

  // 5. C^4: idempotentes ortogonais, associativa
  bool c4 = true;
  for (int i = 0; i < 4; ++i)
    for (int j = 0; j < 4; ++j) {
      int eij = (i == j) ? 1 : 0;  // (e_i e_j)_k = [i=k][j=k]
      for (int k = 0; k < 4; ++k) c4 &= ((i == k) * (j == k)) == eij * (i == k);
    }
  confere("C^4: e_i^2 = e_i, e_i e_j = 0 para i != j", c4);

  std::printf("\n%d falha(s)\n", falhas);
  return falhas ? 1 : 0;
}
