module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.MinimalPrime.Colon
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Associated primes are functorial along a ring map with Noetherian target

Proof of `Module.associatedPrimes.image_comap_associatedPrimes_eq_associatedPrimes` (Stacks 05DZ):
for an `R`-algebra `S` and an `S`-module `M`, viewed as an `R`-module through `algebraMap R S`,
contraction of ideals along `algebraMap R S` carries `Ass_S(M)` onto `Ass_R(M)` as soon as `S` is
Noetherian.

Everything rests on one identity, valid for any `R`-algebra: contracting the colon ideal of an
`S`-submodule `N ⊆ M` along `algebraMap R S` gives the colon ideal of `N` read as an `R`-submodule,
because `algebraMap R S r` and `r` act on `M` by the same map. With `N = ⊥` and a singleton this
says `Ann_R(m) = Ann_S(m) ∩ R`.

The inclusion `⊆` follows at once and needs no Noetherian hypothesis: contraction commutes with
taking radicals and carries primes to primes, so the radical of `Ann_S(m)` contracts to the radical
of `Ann_R(m)`. This is Stacks 05BW.

For the inclusion `⊇` let `𝔭 = √(Ann_R(m))` be prime and put `I = Ann_S(m)`, so that
`𝔭 = √(Ann_S(m)) ∩ R` is the contraction of `√I`. Over the Noetherian ring `S` the ideal `√I` is
the intersection of the *finitely many* primes minimal over `I`, and contraction preserves
intersections, so `𝔭` is a finite intersection of primes of `R`; being itself prime it is equal to
one of them, say to the contraction of `𝔮 ∈ minimalPrimes I`. A prime minimal over a colon ideal
`Ann_S(m)` of a Noetherian ring is again a colon ideal `Ann_S(y)`
(`Submodule.exists_eq_colon_of_mem_minimalPrimes`, the cyclic case of Stacks 02CE), and a prime is
its own radical, so `𝔮 ∈ Ass_S(M)` and it contracts to `𝔭`.

## Main results

* `Stacks.AssociatedPrimes.Contraction.solution`: the statement of Tag 05DZ.

## Implementation notes

The source reaches the prime `𝔮` over `𝔭` from the injection `R/𝔭 ⊆ S/I` by way of Stacks 00FK
and 0CAN, that is by exhibiting a point of `Spec(S/I)` over the point `𝔭` of `Spec(R/𝔭)`. The route
taken here replaces that pair of lemmas by prime avoidance in the finite set `minimalPrimes I`,
which is available because `S` is Noetherian — a hypothesis of the statement anyway — and which
produces a *minimal* prime over `I` directly, as the next step of the source's own argument
needs. The two remaining inputs are the source's: the cyclic case of Stacks 02CE, and Stacks
05BW for the easy inclusion, proved here as `IsAssociatedPrime.comap_algebraMap` because the library
holds no statement of that tag. Stacks 02M3 is not needed: `Ann_S(y)` is produced as a colon
ideal in `M` itself, never in the submodule `S/I ⊆ M`, so no transport of associated primes along
that injection takes place.

Both auxiliary results are stated at the generality they hold at rather than the one used here:
`Submodule.comap_algebraMap_colon` for an arbitrary `S`-submodule `N` and an arbitrary set of
elements, with no Noetherian hypothesis anywhere, and `IsAssociatedPrime.comap_algebraMap` with
none either.

## References

* [StacksProject 05DZ](https://stacks.math.columbia.edu/tag/05DZ)
-/

@[expose] public section

namespace Stacks.AssociatedPrimes.Contraction

section

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M]
  [Module S M] [Module R M] [IsScalarTower R S M]

/-- The colon ideal of an `S`-submodule `N` of `M` with respect to a set `s` of elements of `M`
contracts along `algebraMap R S` to the colon ideal of `N` viewed as an `R`-submodule:
`(N : s) ∩ R = (N|_R : s)`. -/
private theorem comap_algebraMap_colon (N : Submodule S M) (s : Set M) :
    Ideal.comap (algebraMap R S) (N.colon s) = (N.restrictScalars R).colon s := by
  ext r
  simp [Ideal.mem_comap, Submodule.mem_colon, algebraMap_smul]

/-- The annihilator in `S` of a set `s` of elements of `M` contracts along `algebraMap R S` to the
annihilator of `s` in `R`. -/
private theorem comap_algebraMap_bot_colon (s : Set M) :
    Ideal.comap (algebraMap R S) ((⊥ : Submodule S M).colon s) = (⊥ : Submodule R M).colon s := by
  rw [comap_algebraMap_colon, Submodule.restrictScalars_bot]

/-- **Stacks 05BW.** The contraction along `algebraMap R S` of an associated prime of `M` over `S`
is an associated prime of `M` over `R`. No Noetherian hypothesis is needed. -/
private theorem IsAssociatedPrime.comap_algebraMap {q : Ideal S} (hq : IsAssociatedPrime q M) :
    IsAssociatedPrime (q.comap (algebraMap R S)) M := by
  obtain ⟨hprime, m, hm⟩ := hq
  have : q.IsPrime := hprime
  exact ⟨inferInstance, m, by rw [hm, Ideal.comap_radical, comap_algebraMap_bot_colon]⟩

/-- The converse inclusion of Stacks 05BW for `S` Noetherian: every associated prime of `M` over
`R` is the contraction of an associated prime of `M` over `S`.

Given `𝔭 = √(Ann_R(m))`, the ideal `𝔭` is the contraction of `√(Ann_S(m))`, hence — `S` being
Noetherian — a finite intersection of contractions of the primes minimal over `Ann_S(m)`. As `𝔭` is
prime it equals one of them, and a prime minimal over `Ann_S(m)` is itself of the form `Ann_S(y)`,
so it is associated to `M` over `S`. -/
private theorem exists_mem_associatedPrimes_comap_eq [IsNoetherianRing S] {p : Ideal R}
    (hp : p ∈ associatedPrimes R M) :
    ∃ q ∈ associatedPrimes S M, Ideal.comap (algebraMap R S) q = p := by
  obtain ⟨hprime, m, hm⟩ := hp
  set I : Ideal S := (⊥ : Submodule S M).colon {m} with hI
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing S I
  have hpinf : p = hfin.toFinset.inf (Ideal.comap (algebraMap R S)) := by
    have h : p = ⨅ q ∈ I.minimalPrimes, Ideal.comap (algebraMap R S) q := by
      rw [← Ideal.comap_sInf, Ideal.sInf_minimalPrimes, Ideal.comap_radical,
        comap_algebraMap_bot_colon, hm]
    rw [h, Finset.inf_eq_iInf]
    simp only [Set.Finite.mem_toFinset]
  have hp' : (hfin.toFinset.inf (Ideal.comap (algebraMap R S))).IsPrime := by
    rwa [← hpinf]
  obtain ⟨q, hqF, hq⟩ := Ideal.eq_inf_of_isPrime_inf hp'
  have hqmin : q ∈ I.minimalPrimes := hfin.mem_toFinset.mp hqF
  have hqmin' : q ∈ ((⊥ : Submodule S M).colon {m}).minimalPrimes := by rwa [← hI]
  obtain ⟨y, hy⟩ := Submodule.exists_eq_colon_of_mem_minimalPrimes (x := m) hqmin'
  exact ⟨q, ⟨hqmin.isPrime, y, by rw [← hy, hqmin.isPrime.radical]⟩, by rw [hq, ← hpinf]⟩

end

/-- For an `R`-algebra `S` with `S` Noetherian and an `S`-module `M`, viewed as an `R`-module
through `algebraMap R S`, contraction along `algebraMap R S` carries `Ass_S(M)` onto `Ass_R(M)`. -/
public theorem solution {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [IsNoetherianRing S] {M : Type*} [AddCommMonoid M] [Module S M] [Module R M]
    [IsScalarTower R S M] :
    Ideal.comap (algebraMap R S) '' associatedPrimes S M = associatedPrimes R M :=
  Set.Subset.antisymm
    (fun _ ⟨_, hq, hq'⟩ ↦ hq' ▸ IsAssociatedPrime.comap_algebraMap hq)
    (fun _ hp ↦ exists_mem_associatedPrimes_comap_eq hp)

end Stacks.AssociatedPrimes.Contraction

end

/-!
# Associated primes are functorial along a ring map with Noetherian target

Let `φ : R → S` be a ring map and let `M` be an `S`-module, regarded as an `R`-module by
restriction of scalars. Contracting an ideal of `S` to `R` along `φ` — this is the map
`Spec(φ)` on points of the spectrum — always carries `Ass_S(M)` into `Ass_R(M)`: if the
annihilator of `m : M` in `S` is a prime `𝔮`, then the annihilator of `m` in `R` is `𝔮 ∩ R`
(Stacks 05BW). When `S` is Noetherian the two sets correspond exactly:
`Spec(φ)(Ass_S(M)) = Ass_R(M)`.

For the reverse inclusion one takes `𝔭 ∈ Ass_R(M)`, say `𝔭 = Ann_R(m)`, and lets
`I = Ann_S(m)`, so that `R/𝔭 → S/I` is injective. Then some prime `𝔮` of `S` minimal over `I`
contracts to `𝔭`, and over a Noetherian ring a prime minimal over the annihilator of an element
is again the annihilator of an element (`Submodule.exists_eq_colon_of_mem_minimalPrimes`, the
cyclic case of Stacks 02CE); since `S/I ⊆ M`, that `𝔮` lies in `Ass_S(M)`. Concretely, over a
Noetherian `S` the radical of `Ann_S(m)` is the intersection of the *finitely many* primes
minimal over it, and contracting that finite intersection to the prime `𝔭` forces `𝔭` to be the
contraction of one of them.

## Main results

* `Module.associatedPrimes.image_comap_associatedPrimes_eq_associatedPrimes`: for a Noetherian
  ring `S` and an `S`-module `M`, the image of `associatedPrimes S M` under contraction along
  `algebraMap R S` is `associatedPrimes R M`.

## Implementation notes

Departures from the source's form, none of them weakening it.

The source writes the ring map as `φ : R → S` and gives `M` its `R`-module structure by
restriction of scalars; here `S` is an `R`-algebra and `M` carries compatible `R`- and
`S`-module structures (`IsScalarTower R S M`). This is Mathlib's spelling for this situation and
is more general: restriction of scalars along `φ` is one instance of it. Correspondingly
`Spec(φ)` is written at the level of ideals, as `Ideal.comap (algebraMap R S)`, because
`associatedPrimes` is a `Set (Ideal _)`; on points of the spectrum this is `PrimeSpectrum.comap`
(`PrimeSpectrum.comap_asIdeal`), so the displayed set equality is the source's. This also
matches the shape of the sibling result for a localization,
`Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule`,
whose name this one mutates (`preimage` to `image`, the localization hypothesis dropped).

Only `CommSemiring` and `AddCommMonoid` are assumed, matching the generality at which Mathlib
develops `associatedPrimes` and at which the one nontrivial input,
`Submodule.exists_eq_colon_of_mem_minimalPrimes`, is stated. No Noetherian hypothesis is placed
on `R`, and `M` is an arbitrary module — neither is used.

`associatedPrimes R M` is Mathlib's set of primes that are the *radical* of the annihilator of
an element, whereas the source's `Ass_R(M)` (Definition 00LA) asks the prime to be that
annihilator on the nose. Over the Noetherian ring `S` the two agree (`isAssociatedPrime_iff`),
so the left-hand side is literally the source's `Ass_S(M)`. On the right-hand side, where `R` is
not assumed Noetherian, Mathlib's set is a priori the larger one, so the equality stated here is
at least as strong as the source's: it contains it, and, since every ideal in the image is a
genuine annihilator `Ann_R(m)`, it also yields that the two notions of `Ass_R(M)` coincide for
such an `M`.

Faithfulness. (1) No hypothesis is dead: `IsNoetherianRing S` is what makes the primes minimal
over `Ann_S(m)` finite in number and annihilators themselves, and the source's Remark 05BX shows
that without it the inclusion `⊇` fails for the source's notion of `Ass_S` (for `R = k` a field
and `S = k[x_1, x_2, …]/(x_i^2)` with `M = S`, no element of `S` has prime annihilator while
`Ass_k(S) = {(0)}`); no necessity is claimed for a non-Noetherian `S` under Mathlib's
radical-taking convention, where that example is not a counterexample. Every other hypothesis is
a structure needed to write the two sides down. (2) The scalars and the base are the source's:
`Ass_S(M)` is taken over `S` and `Ass_R(M)` over `R`, with the `R`-action on `M` the one induced
by `algebraMap R S`, not an unrelated one — that is exactly `IsScalarTower R S M`. (3) The map
the source names, `Spec(φ)`, is pinned: it is contraction along `algebraMap R S`, and the
statement is an equality of sets rather than an assertion that some prime of `S` exists over
each `𝔭 ∈ Ass_R(M)`. (4) The instantiation is not degenerate: for `R = ℤ`, `S = ℤ[x]` and
`M = S ⧸ (x^2 - 2)`, both sides are nonempty and the equality has content, while `M = 0` gives
`∅ = ∅`; the inclusion `⊆` alone is Stacks 05BW and holds without any Noetherian hypothesis, so
the Noetherian content of the statement is the inclusion `⊇`.

## References

* [StacksProject 05DZ](https://stacks.math.columbia.edu/tag/05DZ)

## Tags

associated prime, Noetherian ring, ring map, spectrum
-/

@[expose] public section

/-- **Stacks 05DZ.** Let `S` be an `R`-algebra and let `M` be an `S`-module, viewed as an
`R`-module through `algebraMap R S`. If `S` is Noetherian, then contracting ideals along
`algebraMap R S` — the map `Spec(φ)` on spectra — carries the associated primes of `M` over `S`
onto the associated primes of `M` over `R`: `Spec(φ)(Ass_S(M)) = Ass_R(M)`.

The inclusion `⊆` needs no Noetherian hypothesis (Stacks 05BW), and by Stacks 05BX the reverse
inclusion genuinely does. -/
@[stacks 05DZ]
public theorem Module.associatedPrimes.image_comap_associatedPrimes_eq_associatedPrimes
    {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [IsNoetherianRing S]
    {M : Type*} [AddCommMonoid M] [Module S M] [Module R M] [IsScalarTower R S M] :
    Ideal.comap (algebraMap R S) '' associatedPrimes S M = associatedPrimes R M :=
  Stacks.AssociatedPrimes.Contraction.solution

end

end

/-!
# Associated primes contract along a ring map

Let `φ : R → S` be a ring map and let `M` be an `S`-module, viewed as an `R`-module by
restriction of scalars along `φ`, so that `r • m = φ r • m`. Then
`Spec(φ)(Ass_S(M)) ⊆ Ass_R(M)`: the contraction `φ⁻¹(q)` of every prime
`q ∈ Ass_S(M)` is an associated prime of `M` over `R`. This is Stacks tag 05BW
(Lemma 10.63.11).

Here `Ann_R(m) = {r ∈ R | r • m = 0}` is the annihilator of an element, and a prime
`p ⊂ R` is *associated* to `M` when `Ann_R(m) = p` for some `m ∈ M`; this is the
classical definition of Stacks tag 00LA. The zero module has no associated prime, since
the annihilator of its only element is all of `R`, which is not prime. The induced map
on spectra `Spec(φ) : Spec(S) → Spec(R)` sends `q` to `φ⁻¹(q) = Ideal.comap φ q`.

## Main definitions

* `annElem m`: the ideal `Ann_R(m)`.
* `assOf R`: the set `Ass_R(M)` of primes associated to `M`.

## Main results

* `spec_image_ass_subset` (Stacks tag 05BW): `Spec(φ) '' Ass_S(M) ⊆ Ass_R(M)`. Given
  `q = Ann_S(m)`, the same element `m` works over `R`, because `r • m = φ r • m` makes
  `Ann_R(m)` the contraction of `Ann_S(m)`.

## Implementation notes

`assOf` is not Mathlib's `IsAssociatedPrime` / `associatedPrimes`, which use the more
general "radical of a colon ideal" condition `∃ x, I = (N.colon {x}).radical`. That is
not equivalent to `p = Ann(m)` for a single `m`, so the classical definition is spelled
out here.

Restriction of scalars along `φ` is modelled by equipping `M` with an `R`-module
structure together with the compatibility hypothesis `r • m = φ r • m`, which pins the
`R`-action down to exactly `Module.compHom M φ`.
-/

@[expose] public section

/-- The annihilator in `R` of an element `m` of an `R`-module `M`, i.e. the
ideal `{ r ∈ R | r • m = 0 }`. -/
noncomputable def annElem {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (m : M) : Ideal R :=
  LinearMap.ker (LinearMap.toSpanSingleton R M m)

/-- `annElem m` consists of exactly those `r ∈ R` with `r • m = 0`. -/
theorem mem_annElem {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (m : M) (r : R) : r ∈ annElem m ↔ r • m = 0 := by
  simp [annElem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]

/-- The set of primes associated to the `R`-module `M`, in the classical sense
(Stacks Tag 00LA): a prime `p` such that `p = Ann_R(m)` for some `m ∈ M`. -/
def assOf (R : Type*) {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] :
    Set (Ideal R) :=
  { p | p.IsPrime ∧ ∃ m : M, annElem m = p }

/-- Stacks Tag 05BW (Lemma 10.63.11): for a ring map `φ : R → S` and an
`S`-module `M` viewed as an `R`-module via restriction of scalars along `φ`
(encoded by `hcompat : ∀ r m, r • m = φ r • m`), the image of `Ass_S(M)` under
the contraction map `Spec(φ) = Ideal.comap φ` is contained in `Ass_R(M)`. -/
@[stacks 05BW, ega "IV 3.1.10.1" "Contraction inclusion"]
theorem spec_image_ass_subset
    {R S M : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] [Module R M] [Module S M] (φ : R →+* S)
    (hcompat : ∀ (r : R) (m : M), r • m = φ r • m) :
    (Ideal.comap φ) '' (assOf S (M := M)) ⊆ assOf R (M := M) := by
  rintro p ⟨q, ⟨hq, m, hm⟩, rfl⟩
  refine ⟨Ideal.comap_isPrime φ q, m, ?_⟩
  ext r
  rw [mem_annElem, Ideal.mem_comap, ← hm, mem_annElem, hcompat]

end

/-!
# Associated primes are not functorial along a ring map

For a commutative ring `A` and an `A`-module `N`, a prime `p ⊆ A` is an *associated
prime* of `N` when `p = Ann_A(n) = {a ∈ A | a • n = 0}` for some single element `n ∈ N`,
and `Ass_A(N)` is the set of these. This is the definition of Stacks tag 00LA; the
annihilator itself is `annElem`, defined earlier in this file.

Stacks tag 05BX exhibits a ring map along which associated primes do not transport in
the direction opposite to tag 05BW. Fix a field `k` and set
`S = k[x_1, x_2, x_3, …] / (x_1^2, x_2^2, x_3^2, …)`,
the polynomial ring in countably many variables modulo all the squares of the
variables, with structure map `φ : k → S`. Take `M = S`, as an `S`-module and, via
`φ`, as a `k`-vector space. Then `Ass_k(M) = {(0)}` is nonempty, while
`Ass_S(S) = ∅`, so `Spec(φ)(Ass_S(M)) ⊇ Ass_k(M)` fails: the left-hand side is the
image of the empty set.

The reason `Ass_S(S)` is empty is that no annihilator in `S` is prime. For nonzero
`s = f̄`, every variable class `x̄_i` satisfies `x̄_i^2 = 0` and so lies in any prime
containing `Ann_S(s)`; if `Ann_S(s)` were prime it would therefore contain every
`x̄_i`, forcing `x_i f ∈ (x_1^2, x_2^2, …)` for all `i`, which fails for any `f` outside
that ideal.

## Main definitions

* `assExact A N`: the set `Ass_A(N)` of exact-annihilator associated primes.
* `sqIdeal k`: the ideal `(x_1^2, x_2^2, …)` of `MvPolynomial ℕ k`.
* `S k`: the ring `k[x_1, x_2, …] / (x_1^2, x_2^2, …)`.
* `IsSqFree d`: the monomial exponent `d` has every variable to power at most `1`.
* `aug k`: the augmentation `S k → k` sending every variable to `0`.

## Main results

* `mem_sqIdeal_iff`: `f ∈ sqIdeal k` iff every squarefree-monomial coefficient of `f`
  vanishes.
* `exists_X_mul_notMem_sqIdeal`: if `f ∉ sqIdeal k` then `X i * f ∉ sqIdeal k` for some
  variable `X i`; take `i` outside the support of a squarefree monomial of `f`.
* `assExact_field_eq_singleton_bot`: `Ass_k(S k) = {(0)}`, since `(0)` is the only prime of a
  field and `S k ≠ 0`.
* `assExact_S_eq_empty`: `Ass_S(S) = ∅`.
* `assExact_not_functorial` (Stacks tag 05BX): the two facts together.

## Implementation notes

`assExact` is the exact-annihilator definition rather than Mathlib's
`associatedPrimes` / `IsAssociatedPrime`, which ask that `p` be the *radical* of an
annihilator, `p.IsPrime ∧ ∃ x, p = (⊥.colon {x}).radical`. The two genuinely differ for
the ring `S` here: `Ann_S(s)` for nonzero `s` has radical the maximal ideal, so
Mathlib's `Ass_S(S)` is nonempty, while the exact-annihilator set is empty. Emptiness is
what the counterexample needs.
-/

@[expose] public section

open MvPolynomial

/-- The set of associated primes of an `A`-module `N`, in the exact-annihilator
sense: primes `p` such that `p = Ann_A(n)` for some `n ∈ N`. -/
def assExact (A : Type*) [CommRing A] (N : Type*) [AddCommGroup N] [Module A N] :
    Set (Ideal A) :=
  {p | p.IsPrime ∧ ∃ n : N, p = annElem n}

/-- The ideal generated by the squares `x_i^2` of all the variables in
`k[x_1, x_2, …]`. -/
noncomputable def sqIdeal (k : Type*) [Field k] : Ideal (MvPolynomial ℕ k) :=
  Ideal.span (Set.range (fun i : ℕ => (X i) ^ 2))

/-- The ring `S = k[x_1, x_2, …] / (x_1^2, x_2^2, …)`. -/
noncomputable abbrev S (k : Type*) [Field k] := (MvPolynomial ℕ k) ⧸ sqIdeal k

/-- A monomial exponent `d` is squarefree if every variable appears to power ≤ 1. -/
def IsSqFree (d : ℕ →₀ ℕ) : Prop := ∀ i, d i ≤ 1

/-- Every squarefree-monomial coefficient of an element of `sqIdeal k` vanishes. -/
theorem coeff_eq_zero_of_mem_sqIdeal {k : Type*} [Field k] {f : MvPolynomial ℕ k}
    (hf : f ∈ sqIdeal k) (d : ℕ →₀ ℕ) (hd : IsSqFree d) : f.coeff d = 0 := by
  induction hf using Submodule.span_induction generalizing d with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    dsimp only
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial, ite_eq_right]
    rintro rfl
    simpa using hd i
  | zero => simp
  | add x y _ _ hx hy => rw [MvPolynomial.coeff_add, hx d hd, hy d hd, add_zero]
  | smul c x _ hx =>
    rw [smul_eq_mul, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun ⟨u, v⟩ huv => ?_
    rw [hx v fun i => le_trans ?_ (hd i), mul_zero]
    rw [← Finset.mem_antidiagonal.mp huv]
    simp

/-- A polynomial whose squarefree-monomial coefficients all vanish lies in `sqIdeal k`. -/
theorem mem_sqIdeal_of_coeff_eq_zero {k : Type*} [Field k] {f : MvPolynomial ℕ k}
    (h : ∀ d : ℕ →₀ ℕ, IsSqFree d → f.coeff d = 0) : f ∈ sqIdeal k := by
  rw [f.as_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  rw [MvPolynomial.mem_support_iff] at hd
  obtain ⟨i, hi⟩ := not_forall.mp fun hsf => hd (h d hsf)
  have hde : d = (d - Finsupp.single i 2) + Finsupp.single i 2 :=
    (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (by omega))).symm
  have hdec : monomial d (f.coeff d)
      = monomial (d - Finsupp.single i 2) (f.coeff d) * X i ^ 2 := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, mul_one, ← hde]
  rw [hdec]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- Characterization of membership in `sqIdeal`: a polynomial lies in the ideal
generated by the squares iff all of its squarefree-monomial coefficients vanish. -/
theorem mem_sqIdeal_iff {k : Type*} [Field k] {f : MvPolynomial ℕ k} :
    f ∈ sqIdeal k ↔ ∀ d : ℕ →₀ ℕ, IsSqFree d → f.coeff d = 0 :=
  ⟨coeff_eq_zero_of_mem_sqIdeal, mem_sqIdeal_of_coeff_eq_zero⟩

/-- If `f ∉ sqIdeal` then `X i * f ∉ sqIdeal` for some variable `X i`. -/
theorem exists_X_mul_notMem_sqIdeal {k : Type*} [Field k] {f : MvPolynomial ℕ k}
    (hf : f ∉ sqIdeal k) : ∃ i : ℕ, X i * f ∉ sqIdeal k := by
  -- get a squarefree d with nonzero coeff
  rw [mem_sqIdeal_iff] at hf
  push Not at hf
  obtain ⟨d, hdsf, hdne⟩ := hf
  -- choose i not in support of d
  obtain ⟨i, hi⟩ := Infinite.exists_notMem_finset d.support
  rw [Finsupp.mem_support_iff, not_not] at hi
  refine ⟨i, ?_⟩
  rw [mem_sqIdeal_iff]
  push Not
  refine ⟨Finsupp.single i 1 + d, ?_, ?_⟩
  · -- single i 1 + d is squarefree
    intro j
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    by_cases hj : i = j
    · subst hj
      rw [ite_eq_left rfl, hi]
      omega
    · rw [ite_eq_right hj, zero_add]
      exact hdsf j
  · rwa [MvPolynomial.coeff_X_mul]

/-- Augmentation: the `k`-algebra map `S k → k` sending each `X i ↦ 0`. -/
noncomputable def aug (k : Type*) [Field k] : S k →ₐ[k] k :=
  Ideal.Quotient.liftₐ (sqIdeal k) (MvPolynomial.aeval (fun _ : ℕ => (0 : k))) fun a ha => by
    -- need: every element of sqIdeal maps to 0 under aeval (fun _ => 0)
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      simp
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [smul_eq_mul, map_mul, hx, mul_zero]

/-- The ring `S k = k[x_1, x_2, …]/(x_1^2, x_2^2, …)` is nontrivial. -/
instance instNontrivialS (k : Type*) [Field k] : Nontrivial (S k) :=
  ⟨0, 1, fun h => by simpa using congrArg (aug k) h⟩

/-- With `S k` viewed as a `k`-vector space, its set of associated primes over `k` is
`{(0)}`; in particular it is nonempty. -/
theorem assExact_field_eq_singleton_bot (k : Type*) [Field k] :
    assExact k (S k) = {⊥} := by
  ext p
  simp only [assExact, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp, n, rfl⟩
    -- a prime ideal of a field is ⊥
    exact (Ideal.eq_bot_or_top (K := k) (annElem n)).resolve_right hp.ne_top
  · rintro rfl
    -- `annElem (1 : S k) = ⊥`, since `1 ≠ 0` in the `k`-vector space `S k`
    refine ⟨Ideal.isPrime_bot, 1, (Ideal.ext fun a => ?_).symm⟩
    rw [mem_annElem, Ideal.mem_bot, smul_eq_zero, or_iff_left one_ne_zero]

/-- The set of associated primes of `S k` as a module over itself is empty: no
annihilator of an element of `S k` is a prime ideal. -/
theorem assExact_S_eq_empty (k : Type*) [Field k] :
    assExact (S k) (S k) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro p ⟨hp, s, hps⟩
  set q : MvPolynomial ℕ k →+* S k := Ideal.Quotient.mk (sqIdeal k) with hq
  -- s ≠ 0, because 1 ∉ p = annElem s
  have hs0 : s ≠ 0 := by
    intro h
    apply hp.ne_top
    rw [hps, Ideal.eq_top_iff_one, mem_annElem, h, smul_zero]
  -- represent s
  obtain ⟨f, rfl⟩ : ∃ f, q f = s := Ideal.Quotient.mk_surjective s
  -- f ∉ sqIdeal
  have hf : f ∉ sqIdeal k := fun hf => hs0 (Ideal.Quotient.eq_zero_iff_mem.mpr hf)
  -- some variable multiple of `f` escapes `sqIdeal k`
  obtain ⟨i, hi⟩ := exists_X_mul_notMem_sqIdeal hf
  -- (X̄ i)^2 = 0, so X̄ i ∈ p = annElem (q f), i.e. X i * f ∈ sqIdeal, a contradiction
  have hXi : q (X i) ∈ p := hp.mem_of_pow_mem 2 <| by
    rw [hps, mem_annElem, smul_eq_mul, ← map_pow, ← map_mul, hq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩))
  rw [hps, mem_annElem, smul_eq_mul, ← map_mul, hq] at hXi
  exact hi (Ideal.Quotient.eq_zero_iff_mem.mp hXi)

/-- Together, the two statements above witness the failure of functoriality of
associated primes along `algebraMap k (S k)`: `Ass_k(S) ≠ ∅` while `Ass_S(S) = ∅`. -/
@[stacks 05BX]
theorem assExact_not_functorial (k : Type*) [Field k] :
    (assExact k (S k)).Nonempty ∧ assExact (S k) (S k) = ∅ :=
  ⟨by simp [assExact_field_eq_singleton_bot], assExact_S_eq_empty k⟩

end
