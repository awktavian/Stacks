module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Unramified.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Conormal modules and universal first order thickenings

Let `R → S` be a formally unramified ring map (`Algebra.FormallyUnramified`, Tag 00UM), that is,
one along which a square-zero extension admits at most one lift. Then `S` is the target of a
*universal* square-zero extension: there is a surjection of `R`-algebras `S' → S` whose kernel
`I' ⊆ S'` satisfies `I' ^ 2 = 0` and which is initial among all square-zero situations over `S`.
Concretely, given a commutative ring `A`, an ideal `I ⊆ A` with `I ^ 2 = 0`, a ring map `b : R → A`
and a map `a : S → A ⧸ I` making the square

```
S  --a-→  A ⧸ I
↑           ↑
R  --b-→    A
```

commute, there is a *unique* `R`-algebra map `a' : S' → A` with `S' → A → A ⧸ I` equal to
`S' → S → A ⧸ I`. Existence of `a'` says that the obstruction to lifting `a` vanishes after
passing to the thickening `S'`; uniqueness is where formal unramifiedness enters, and it is what
determines `S' → S` up to unique isomorphism, so that one may speak of *the* universal first order
thickening of `S` over `R` and of its kernel, the conormal module `C_{S/R}`.

For a surjection `R → R ⧸ I₀` the universal first order thickening is `R ⧸ I₀ ^ 2 → R ⧸ I₀` and the
conormal module is `I₀ / I₀ ^ 2`. Thickenings, hence conormal modules, are compatible with
localization on either side: for multiplicative `M ⊆ R` and `N ⊆ S` the localization
`φ⁻¹(N)⁻¹S' → N⁻¹S` of `φ : S' → S` is the universal first order thickening of `N⁻¹S` over `M⁻¹R`,
and `N⁻¹C_{S/R} = C_{N⁻¹S/M⁻¹R}`.

## Main definitions

* `Algebra.Extension.IsUniversalFirstOrderThickening`: the property, of a surjection of
  `R`-algebras onto `S`, of having square-zero kernel and of lifting every square-zero situation
  over `S` uniquely. It is the form in which "`S' → S` is the universal first order thickening of
  `S` over `R`" is stated, and it holds for at most one such surjection up to unique isomorphism.
* `Algebra.FormallyUnramified.universalFirstOrderThickening`: the universal first order thickening
  `S' → S` of `S` over a formally unramified base `R`, as an `Algebra.Extension R S`.
* `Algebra.FormallyUnramified.conormal`: the conormal module `C_{S/R}`, the kernel of `S' → S`
  seen as an `S`-module.

## Main results

* `Algebra.FormallyUnramified.exists_extension_ker_sq_eq_bot_and_existsUnique_lift`: for a
  formally unramified `R → S` there is a surjection of `R`-algebras onto `S` with square-zero
  kernel through which every square-zero extension of `S` lifts uniquely (Tag 04EB).
* `Algebra.FormallyUnramified.isUniversalFirstOrderThickening`: the universal first order
  thickening does have that universal property; this is the only access to it that is needed, and
  it is what pins the object down (Tag 04EC).
* `Algebra.Extension.IsUniversalFirstOrderThickening.localization`: a localization of a universal
  first order thickening, over the matching localization of the base, is again a universal first
  order thickening, and its kernel is the extension of the original kernel — the localization of
  the conormal module (Tag 04EE).

## Implementation notes

A surjection of `R`-algebras `S' → S` is packaged as an `Algebra.Extension R S`, Mathlib's
structure whose data is exactly that: a ring `P.Ring`, compatible algebra structures
`R → P.Ring → S`, and a set-theoretic section of `algebraMap P.Ring S` witnessing surjectivity.
The surjection itself is `algebraMap P.Ring S`, an `R`-algebra map through
`IsScalarTower.toAlgHom R P.Ring S`, and its kernel is `P.ker`. The commutative square above is
encoded, as everywhere in Mathlib's square-zero lifting API
(`Algebra.FormallyUnramified.comp_injective`, `derivationToSquareZeroEquivLift`), by giving the
test ring `A` an `R`-algebra structure — the source's `b : R → A` is `algebraMap R A` — and asking
`a` to be an `R`-algebra map, so that commutativity of the square is `a`'s `R`-linearity.

Formal unramifiedness is not only sufficient for such a thickening to exist but necessary: two
lifts `S →ₐ[R] A` of one `a : S →ₐ[R] A ⧸ I` compose with `S' → S` to two lifts of
`a ∘ (S' → S)`, hence agree, hence are equal because `S' → S` is surjective (Tag 00UM,
`Algebra.FormallyUnramified.iff_comp_injective`).

The kernel "seen as an `S`-module" is `Algebra.Extension.Cotangent`, that is `P.ker / P.ker ^ 2`:
an ideal of `P.Ring` is a module over `P.Ring` and carries no `S`-action, whereas the quotient by
its square does, being killed by `P.ker`. Since `P.ker ^ 2 = 0` for the universal first order
thickening, `Ideal.toCotangent` is an isomorphism onto it and no information is lost.
`Algebra.FormallyUnramified.conormal` is a reducible abbreviation, so it inherits that `S`-module
structure and every lemma about `Algebra.Extension.Cotangent` verbatim.

The extension produced for Tag 04EB is *not* `Algebra.Extension.infinitesimal P` for a
presentation `P` of `S`: that has square-zero kernel, but not the uniqueness. For `R = k` and
`S = k` with the presentation `k[x] → k`, `x ↦ 0`, the infinitesimal extension is `k[x]/(x²) → k`,
and `x ↦ c·t` lifts the identity of `k` into `k[t]/(t²)` for every `c ∈ k`; the universal
thickening is instead `k → k`. What is constructed is the source's `P/J'` for the presentation
`P = R[x_s ; s ∈ S] → S` with kernel `J`: since `Ω[S⁄R] = 0`, the map `d : J/J² → Ω[P⁄R] ⊗_P S` of
the naive cotangent complex is surjective (Tags 00RU and 00UO), and one divides `P` by
`J' = J² + (g_s)` for elements `g_s ∈ J` with `d g_s = d x_s ⊗ 1`, so that `d` is split. The
source's Taylor expansion `β'(g) = β(g) + ∑ δ_i β(∂g/∂x_i)`, which compares two lifts on `g`, is
Mathlib's homotopy identity `Algebra.Extension.Cotangent.map_sub_map` evaluated at the class of
`g`; that comparison is the whole content of both halves of the universal property.

Test algebras are quantified over one universe: over its own, in Tag 04EB, and over the universe
of the thickening's ring in `Algebra.Extension.IsUniversalFirstOrderThickening`. The restriction
in the second case comes from the way the thickening is obtained rather than from any limit on what
a `Prop`-valued predicate may quantify over: `universalFirstOrderThickening` is `Exists.choose` of
Tag 04EB instantiated at one test universe, and instantiating that existential at a second universe
chooses an unrelated extension, since `∃ P, ∀ ⦃A : Type t⦄ …` with `t` a parameter of the theorem
yields a `P` for each `t` and not one `P` good for every `t`. Quantifying the predicate over all
test universes therefore means naming the construction below, `G.Ring ⧸ J'` for
`G = Algebra.Generators.self R S`, as a definition and proving its lifting property with the test
universe free. Lifting into test algebras of the size of the thickening already determines the
thickening up to unique isomorphism, which is the property used here; compare
`Algebra.FormallyUnramified.iff_comp_injective` and
`Algebra.FormallyUnramified.iff_comp_injective_of_small`, where the same reduction is made for
formal unramifiedness itself.

Tag 04EE's two parts, localization on the base and on the target, are one statement:
`Algebra.Extension.IsUniversalFirstOrderThickening.localization`, whose base ring is written `A`
and whose target `B`, for `N` the image of `M` in `B` is the first, and for `M = ⊥` the second,
where `A` is its own localization because `⊥ ≤ IsUnit.submonoid A`; that instance is not found by
synthesis and is supplied as `IsLocalization.of_le_isUnit bot_le`. Localizations are taken
abstractly, as rings carrying `IsLocalization` instances rather than as the constructions
`Localization M`, and the localized thickening is an arbitrary `Q : Algebra.Extension Aₘ Bₙ`
constrained by hypotheses rather than a constructed term: localizing an extension over a
*localized base* is not among Mathlib's constructions (`Algebra.Extension.localization` keeps the
base fixed, so it realizes the second part only), and constructing it inside the statement would
fix a model. The hypotheses pin `Q` up to unique isomorphism over its data: `Q.Ring` is a
localization of `P.Ring` at `φ⁻¹(N)`, its structure map to `Bₙ` is pinned by `algebraMap_comp`
since a ring map out of a localization is determined by its restriction, and its `Aₘ`-algebra
structure is pinned by `IsScalarTower A P.Ring Q.Ring` for the same reason. No hypothesis relating
`M` and `N` is imposed, and none is needed: `[Algebra Aₘ Bₙ]` with `[IsScalarTower A Aₘ Bₙ]`
already forces the image of `M` in `Bₙ`, and likewise in `Q.Ring`, to consist of units.

The localized conormal module is the second conclusion of that lemma, the ideal equation
`Q.ker = P.ker.map (algebraMap P.Ring Q.Ring)`: the conormal module of `A → B` is `P.ker`, equal
to `Algebra.Extension.Cotangent P` because `P.ker ^ 2 = ⊥`, and
`Algebra.idealMap_isLocalizedModule` already says that the extension of an ideal to a localization
is its localization. The localization is taken at `φ⁻¹(N) ⊆ P.Ring` rather than at `N ⊆ B`; the two
agree on `P.ker`, whose `P.Ring`-action factors through `B` because `P.ker ^ 2 = ⊥`.

## References

* [StacksProject 04EB](https://stacks.math.columbia.edu/tag/04EB)
* [StacksProject 04EC](https://stacks.math.columbia.edu/tag/04EC)
* [StacksProject 04EE](https://stacks.math.columbia.edu/tag/04EE)
* [StacksProject 00UM](https://stacks.math.columbia.edu/tag/00UM)
-/

@[expose] public section

universe u v w

/-- The image of `K` in `P ⧸ J` has vanishing `n`-th power as soon as `K ^ n ≤ J`. -/
private lemma Ideal.map_mk_pow_eq_bot_of_pow_le {P : Type*} [CommRing P] {J K : Ideal P} {n : ℕ}
    (h : K ^ n ≤ J) : K.map (Ideal.Quotient.mk J) ^ n = ⊥ := by
  rw [← Ideal.map_pow]
  exact le_bot_iff.1 ((Ideal.map_mono h).trans_eq (Ideal.map_quotient_self J))

/-- The product of two elements of an ideal `I` with `I ^ 2 = ⊥` vanishes. -/
private lemma Ideal.mul_eq_zero_of_pow_two_eq_bot {C : Type*} [CommRing C] {I : Ideal C}
    (hI : I ^ 2 = ⊥) {x y : C} (hx : x ∈ I) (hy : y ∈ I) : x * y = 0 := by
  have := Ideal.mul_mem_mul hx hy
  rwa [← pow_two, hI, Ideal.mem_bot] at this

section Thickening

open TensorProduct MvPolynomial KaehlerDifferential

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι : Type*}
  (G : Algebra.Generators R S ι) {A : Type*} [CommRing A] [Algebra R A] {I : Ideal A}
  (a : S →ₐ[R] A ⧸ I) (β β' : G.Ring →ₐ[R] A)

/-- For a formally unramified `R → S` the map `d : J/J² → Ω[P⁄R] ⊗_P S` of the naive cotangent
complex of a family of generators is surjective, its cokernel being `Ω[S⁄R] = 0`. In particular
each basis element `1 ⊗ d(X j)` of `Ω[P⁄R] ⊗_P S` is `d g` for some `g ∈ J`. -/
private lemma Algebra.Generators.exists_cotangentComplex_mk_eq [Algebra.FormallyUnramified R S]
    (j : ι) :
    ∃ g : G.ker, G.toExtension.cotangentComplex (Algebra.Extension.Cotangent.mk g) =
      (1 : S) ⊗ₜ[G.toExtension.Ring] D R G.toExtension.Ring (X j) := by
  have hsurj : Function.Surjective G.toExtension.cotangentComplex := by
    rw [← LinearMap.range_eq_top,
      ← LinearMap.exact_iff.mp G.toExtension.exact_cotangentComplex_toKaehler,
      LinearMap.ker_eq_top]
    exact Subsingleton.elim _ _
  obtain ⟨z, hz⟩ := hsurj (G.cotangentSpaceBasis j)
  obtain ⟨g, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective z
  exact ⟨g, hz.trans (G.cotangentSpaceBasis_apply j)⟩

/-- **The Taylor expansion of the source.** Let `I ⊆ A` be an ideal with `I ^ 2 = 0` and let
`β, β'` be two lifts of `a : S →ₐ[R] A ⧸ I` through a family of generators of `S`. If `x ∈ J` has
class in `J/J²` mapping to the basis element `1 ⊗ d(X j)` of the cotangent space, then `β` and `β'`
differ on `x` exactly as they differ on the variable `X j`. This is the source's
`β'(g) = β(g) + ∑ δ_i β(∂g/∂x_i)` in the case in which it is used, and it is Mathlib's homotopy
identity `Algebra.Extension.Cotangent.map_sub_map` evaluated at the class of `x`. -/
private lemma Algebra.Generators.sub_eq_sub_of_cotangentComplex_mk_eq (hI : I ^ 2 = ⊥)
    (hβ : (Ideal.Quotient.mkₐ R I).comp β = a.comp (IsScalarTower.toAlgHom R G.Ring S))
    (hβ' : (Ideal.Quotient.mkₐ R I).comp β' = a.comp (IsScalarTower.toAlgHom R G.Ring S))
    (x : G.toExtension.ker) (j : ι)
    (hx : G.toExtension.cotangentComplex (Algebra.Extension.Cotangent.mk x) =
      (1 : S) ⊗ₜ[G.toExtension.Ring] D R G.toExtension.Ring (X j)) :
    β x.1 - β' x.1 = β (X j) - β' (X j) := by
  let : Algebra S (A ⧸ I) := a.toRingHom.toAlgebra
  have : IsScalarTower R S (A ⧸ I) := IsScalarTower.of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra]
  let E : Algebra.Extension R (A ⧸ I) :=
    .ofSurjective (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective
  have hker : E.ker ^ 2 = ⊥ := by
    change RingHom.ker (Ideal.Quotient.mk I) ^ 2 = ⊥
    rwa [Ideal.mk_ker]
  let f : G.toExtension.Hom E := Algebra.Extension.Hom.ofAlgHom β hβ
  let f' : G.toExtension.Hom E := Algebra.Extension.Hom.ofAlgHom β' hβ'
  have key := LinearMap.congr_fun (Algebra.Extension.Cotangent.map_sub_map f f')
    (Algebra.Extension.Cotangent.mk x)
  rwa [LinearMap.sub_apply, LinearMap.comp_apply, hx,
    Algebra.Extension.Hom.sub_one_tmul f f' (X j), Algebra.Extension.Cotangent.map_mk,
    Algebra.Extension.Cotangent.map_mk, ← map_sub,
    Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem, hker, Ideal.mem_bot, sub_eq_zero] at key

/-- A family of lifts of the values `a (G.val j)` of `a` on the generators defines a lift of `a`. -/
private lemma Algebra.Generators.mkₐ_comp_aeval (d : ι → A)
    (hd : ∀ j, Ideal.Quotient.mk I (d j) = a (G.val j)) :
    (Ideal.Quotient.mkₐ R I).comp (aeval (R := R) d) =
      a.comp (IsScalarTower.toAlgHom R G.Ring S) :=
  MvPolynomial.algHom_ext fun j => by simpa using hd j

/-- A lift of `a : S →ₐ[R] A ⧸ I` through a family of generators maps `J` into `I`. -/
private lemma Algebra.Generators.lift_mem_of_mem_ker
    (hβ : (Ideal.Quotient.mkₐ R I).comp β = a.comp (IsScalarTower.toAlgHom R G.Ring S))
    {p : G.Ring} (hp : p ∈ G.ker) : β p ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk R I, ← AlgHom.comp_apply, hβ]
  simp [show algebraMap G.Ring S p = 0 from hp]

/-- A lift of `a : S →ₐ[R] A ⧸ I` kills `J²` when `I ^ 2 = 0`, since it maps `J` into `I`. -/
private lemma Algebra.Generators.ker_sq_le_ker (hI : I ^ 2 = ⊥)
    (hβ : (Ideal.Quotient.mkₐ R I).comp β = a.comp (IsScalarTower.toAlgHom R G.Ring S)) :
    G.ker ^ 2 ≤ RingHom.ker (β : G.Ring →+* A) := by
  rw [pow_two, Ideal.mul_le]
  intro p hp q hq
  rw [RingHom.mem_ker, map_mul]
  exact Ideal.mul_eq_zero_of_pow_two_eq_bot hI (G.lift_mem_of_mem_ker a β hβ hp)
    (G.lift_mem_of_mem_ker a β hβ hq)

/-- **Existence half of the universal property.** Given elements `g j ∈ J` splitting the cotangent
complex, every `a : S →ₐ[R] A ⧸ I` with `I ^ 2 = 0` has a lift `β` through the generators with
`β (g j) = 0` for all `j`: take any lift `β₀` and correct it by `X j ↦ β₀ (X j) - β₀ (g j)`. -/
private lemma Algebra.Generators.exists_lift_apply_eq_zero (hI : I ^ 2 = ⊥) (g : ι → G.ker)
    (hg : ∀ j, G.toExtension.cotangentComplex (Algebra.Extension.Cotangent.mk (g j)) =
      (1 : S) ⊗ₜ[G.toExtension.Ring] D R G.toExtension.Ring (X j)) :
    ∃ β : G.Ring →ₐ[R] A,
      (Ideal.Quotient.mkₐ R I).comp β = a.comp (IsScalarTower.toAlgHom R G.Ring S) ∧
        ∀ j, β (g j : G.Ring) = 0 := by
  choose c hc using fun j : ι => Ideal.Quotient.mk_surjective (a (G.val j))
  let β₀ : G.Ring →ₐ[R] A := aeval c
  have hβ₀ : (Ideal.Quotient.mkₐ R I).comp β₀ = a.comp (IsScalarTower.toAlgHom R G.Ring S) :=
    G.mkₐ_comp_aeval a c hc
  let β : G.Ring →ₐ[R] A := aeval fun j => c j - β₀ (g j : G.Ring)
  have hβ : (Ideal.Quotient.mkₐ R I).comp β = a.comp (IsScalarTower.toAlgHom R G.Ring S) :=
    G.mkₐ_comp_aeval a _ fun j => by
      rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.2
        (G.lift_mem_of_mem_ker a β₀ hβ₀ (g j).2), sub_zero, hc]
  refine ⟨β, hβ, fun j => ?_⟩
  have hX : β (X j) - β₀ (X j) = -β₀ (g j : G.Ring) := by simp [β, β₀]
  linear_combination G.sub_eq_sub_of_cotangentComplex_mk_eq a β β₀ hI hβ hβ₀ (g j) j (hg j) + hX

/-- **Uniqueness half of the universal property.** Two lifts of `a : S →ₐ[R] A ⧸ I` through a
family of generators that both kill elements `g j ∈ J` splitting the cotangent complex are equal:
they agree on `g j`, hence on the variable `X j`, hence everywhere. -/
private lemma Algebra.Generators.lift_eq_of_apply_eq_zero (hI : I ^ 2 = ⊥)
    (hβ : (Ideal.Quotient.mkₐ R I).comp β = a.comp (IsScalarTower.toAlgHom R G.Ring S))
    (hβ' : (Ideal.Quotient.mkₐ R I).comp β' = a.comp (IsScalarTower.toAlgHom R G.Ring S))
    (g : ι → G.ker)
    (hg : ∀ j, G.toExtension.cotangentComplex (Algebra.Extension.Cotangent.mk (g j)) =
      (1 : S) ⊗ₜ[G.toExtension.Ring] D R G.toExtension.Ring (X j))
    (hβg : ∀ j, β (g j : G.Ring) = 0) (hβ'g : ∀ j, β' (g j : G.Ring) = 0) : β = β' :=
  MvPolynomial.algHom_ext fun j => by
    have h := G.sub_eq_sub_of_cotangentComplex_mk_eq a β β' hI hβ hβ' (g j) j (hg j)
    rw [hβg j, hβ'g j] at h
    linear_combination -h

/-- **Stacks 04EB.** Let `R → S` be a formally unramified ring map. There is a surjection of
`R`-algebras `S' → S` whose kernel is an ideal of square zero and which is universal: for every
`R`-algebra `A`, every ideal `I ⊆ A` with `I ^ 2 = 0` and every `R`-algebra map `a : S → A/I`,
there is a unique `R`-algebra map `a' : S' → A` such that `S' → A → A/I` equals `S' → S → A/I`.
The surjection `S' → S` is `algebraMap P.Ring S` for the produced `Algebra.Extension P`. -/
@[stacks 04EB "The surjection of `R`-algebras `S' → S` is an `Algebra.Extension R S` (the
structure whose data is exactly a surjection onto `S` of `R`-algebras). The source's square is
encoded by `A` being an `R`-algebra — its `b : R → A` is `algebraMap R A` — and `a` being an
`R`-algebra map, so that commutativity of the square is `a`'s `R`-linearity. The test algebra
lives in a universe of its own; see the module docstring."]
theorem Algebra.FormallyUnramified.exists_extension_ker_sq_eq_bot_and_existsUnique_lift
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FormallyUnramified R S] :
    ∃ P : Algebra.Extension.{max u v} R S, P.ker ^ 2 = ⊥ ∧
      ∀ ⦃A : Type w⦄ [CommRing A] [Algebra R A] (I : Ideal A), I ^ 2 = ⊥ →
        ∀ a : S →ₐ[R] A ⧸ I, ∃! a' : P.Ring →ₐ[R] A,
          (Ideal.Quotient.mkₐ R I).comp a' = a.comp (IsScalarTower.toAlgHom R P.Ring S) := by
  classical
  let G : Algebra.Generators R S S := Algebra.Generators.self R S
  choose g hg using G.exists_cotangentComplex_mk_eq
  let J' : Ideal G.Ring := G.ker ^ 2 ⊔ Ideal.span (Set.range fun j => (g j : G.Ring))
  have hgJ' : ∀ j, (g j : G.Ring) ∈ J' := fun j =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)
  have hJ'le : J' ≤ G.ker := sup_le (Ideal.pow_le_self two_ne_zero)
    (Ideal.span_le.2 <| by rintro _ ⟨j, rfl⟩; exact (g j).2)
  let f : (G.Ring ⧸ J') →ₐ[R] S :=
    Ideal.Quotient.liftₐ J' (IsScalarTower.toAlgHom R G.Ring S) fun _ hp => hJ'le hp
  have hfsurj : Function.Surjective f := fun s => by
    obtain ⟨p, hp⟩ := G.algebraMap_surjective s
    exact ⟨Ideal.Quotient.mk J' p, hp⟩
  have hkerf : RingHom.ker (f : (G.Ring ⧸ J') →+* S) ^ 2 = ⊥ :=
    Ideal.ker_quotient_lift (algebraMap G.Ring S) hJ'le ▸
      Ideal.map_mk_pow_eq_bot_of_pow_le (le_sup_left : G.ker ^ 2 ≤ J')
  refine ⟨.ofSurjective f hfsurj, hkerf, ?_⟩
  intro A _ _ I hI a
  obtain ⟨β, hβ, hβg⟩ := G.exists_lift_apply_eq_zero a hI g hg
  have hker : J' ≤ RingHom.ker (β : G.Ring →+* A) := sup_le (G.ker_sq_le_ker a β hI hβ)
    (Ideal.span_le.2 <| by rintro _ ⟨j, rfl⟩; exact hβg j)
  let mkQ : G.Ring →ₐ[R] (Algebra.Extension.ofSurjective f hfsurj).Ring := Ideal.Quotient.mkₐ R J'
  refine ⟨Ideal.Quotient.liftₐ J' β fun _ hp => hker hp, ?_, ?_⟩
  · refine AlgHom.ext fun x => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congr($hβ p)
  · intro a'' h
    have hγ : (Ideal.Quotient.mkₐ R I).comp (a''.comp mkQ) =
        a.comp (IsScalarTower.toAlgHom R G.Ring S) := AlgHom.ext fun p => congr($h (mkQ p))
    have hγg : ∀ j : S, (a''.comp mkQ) (g j : G.Ring) = 0 := fun j => by
      rw [AlgHom.comp_apply, show mkQ (g j : G.Ring) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.2 (hgJ' j), map_zero]
    have heq := G.lift_eq_of_apply_eq_zero a _ β hI hγ hβ g hg hγg hβg
    refine AlgHom.ext fun x => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congr($heq p)

end Thickening

namespace Algebra

/-- A surjection of `R`-algebras `P.Ring → S` **is the universal first order thickening** of `S`
over `R` if its kernel has square zero and every square-zero situation over `S` is lifted
uniquely through it: for every `R`-algebra `A`, every ideal `I ⊆ A` with `I ^ 2 = 0` and every
`R`-algebra map `a : S → A ⧸ I`, there is a unique `R`-algebra map `a' : P.Ring → A` with
`P.Ring → A → A ⧸ I` equal to `P.Ring → S → A ⧸ I`. Two such surjections are related by a unique
isomorphism, whence the definite article. -/
structure Extension.IsUniversalFirstOrderThickening {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] [Algebra R S] (P : Extension.{w} R S) : Prop where
  /-- The kernel of the universal first order thickening is an ideal of square zero. -/
  ker_sq_eq_bot : P.ker ^ 2 = ⊥
  /-- Every square-zero situation over `S` is lifted uniquely through the universal first order
  thickening. -/
  existsUnique_lift : ∀ ⦃A : Type w⦄ [CommRing A] [Algebra R A] (I : Ideal A), I ^ 2 = ⊥ →
    ∀ a : S →ₐ[R] A ⧸ I, ∃! a' : P.Ring →ₐ[R] A,
      (Ideal.Quotient.mkₐ R I).comp a' = a.comp (IsScalarTower.toAlgHom R P.Ring S)

namespace FormallyUnramified

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  [FormallyUnramified R S]

/-- The **universal first order thickening** `S' → S` of `S` over a formally unramified base
`R`: the surjection of `R`-algebras onto `S` with square-zero kernel through which every
square-zero situation over `S` lifts uniquely, provided by Tag 04EB. It is determined up to
unique isomorphism by `Algebra.FormallyUnramified.isUniversalFirstOrderThickening`, which is all
that is ever used about it. -/
@[stacks 04EC "Part (1). The surjection `S' → S` is an `Algebra.Extension R S`, the structure
whose data is exactly a surjection of `R`-algebras onto `S`; the surjection is
`algebraMap S'.Ring S`. Only determined up to unique isomorphism, so defined by choosing one of
the thickenings produced by Tag 04EB and used only through
`Algebra.FormallyUnramified.isUniversalFirstOrderThickening`. See the module docstring."]
noncomputable def universalFirstOrderThickening : Extension.{max u v} R S :=
  (exists_extension_ker_sq_eq_bot_and_existsUnique_lift.{u, v, max u v} R S).choose

/-- The universal first order thickening of `S` over `R` has square-zero kernel and lifts every
square-zero situation over `S` uniquely. -/
theorem isUniversalFirstOrderThickening :
    (universalFirstOrderThickening R S).IsUniversalFirstOrderThickening :=
  have h := (exists_extension_ker_sq_eq_bot_and_existsUnique_lift.{u, v, max u v} R S).choose_spec
  ⟨h.1, h.2⟩

/-- The **conormal module** `C_{S/R}` of a formally unramified ring map `R → S`: the kernel of
the universal first order thickening `S' → S`, as a module over `S`. Being an ideal of square
zero in `S'`, that kernel equals its own image in `S' / (ker) ^ 2`, which is where the `S`-action
lives. -/
@[stacks 04EC "Part (2). The kernel of `algebraMap S'.Ring S` seen as an `S`-module is
`Algebra.Extension.Cotangent`, the quotient of the kernel by its square — equal to the kernel
because the square is zero, and the object on which `S` acts. See the module docstring."]
abbrev conormal : Type (max u v) :=
  (universalFirstOrderThickening R S).Cotangent

end FormallyUnramified

end Algebra

section Localization

/-- Two `S`-algebra maps out of a localization `R'` of `R` are equal as soon as they agree on the
image of `R`. This is `IsLocalization.algHom_ext` for an `S` that is a base of `R'` only, and not
of `R`. -/
private lemma IsLocalization.algHom_ext' {R R' S E : Type*} [CommSemiring R] [CommSemiring R']
    [CommSemiring S] [CommSemiring E] [Algebra R R'] (T : Submonoid R) [IsLocalization T R']
    [Algebra S R'] [Algebra S E] {y z : R' →ₐ[S] E}
    (h : ∀ x : R, y (algebraMap R R' x) = z (algebraMap R R' x)) : y = z :=
  AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext T (RingHom.ext h))

/-- Let `algebraMap R S` be surjective, let `N ⊆ S` be a submonoid, let `Rₙ` be a localization of
`R` at `N.comap (algebraMap R S)` and `Sₙ` a localization of `S` at `N`, and let `h : Rₙ → Sₙ` be
compatible with `R → S`. Then the kernel of `h` is the extension of the kernel of `R → S`. This is
`IsLocalization.ker_map` with its canonical `IsLocalization.map` replaced by an arbitrary
compatible map, the two agreeing because a ring map out of a localization is determined by its
restriction. -/
private lemma IsLocalization.ker_eq_map_ker {R S : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] (hsurj : Function.Surjective (algebraMap R S)) (N : Submonoid S)
    {Rₙ : Type*} [CommSemiring Rₙ] [Algebra R Rₙ]
    [IsLocalization (N.comap (algebraMap R S)) Rₙ]
    {Sₙ : Type*} [CommSemiring Sₙ] [Algebra S Sₙ] [IsLocalization N Sₙ]
    (h : Rₙ →+* Sₙ) (hh : h.comp (algebraMap R Rₙ) = (algebraMap S Sₙ).comp (algebraMap R S)) :
    RingHom.ker h = (RingHom.ker (algebraMap R S)).map (algebraMap R Rₙ) := by
  have hT : Submonoid.map (algebraMap R S) (N.comap (algebraMap R S)) = N :=
    Submonoid.map_comap_eq_of_surjective hsurj N
  have he : h = IsLocalization.map (M := N.comap (algebraMap R S)) (S := Rₙ) Sₙ (algebraMap R S)
      (hT.symm ▸ Submonoid.le_comap_map _) :=
    IsLocalization.ringHom_ext (N.comap (algebraMap R S))
      (hh.trans (IsLocalization.map_comp _).symm)
  rw [he, IsLocalization.ker_map Sₙ (algebraMap R S) hT]

/-- Let `Q.Ring → Sₙ` be a localization of `φ : P.Ring → S` at `φ⁻¹(N)` and `N`, over a base `Rₘ`
of `Sₙ` extending `R`, let `I` be an ideal of an `Rₘ`-algebra `D` and let `a : Sₙ → D ⧸ I` be a
square-zero situation over `Sₙ`. An `Rₘ`-algebra map `y : Q.Ring → D` lifts `a` if and only if its
restriction `b : P.Ring → D` lifts the square-zero situation over `S` obtained from `a` along
`S → Sₙ`. Both conditions say that `b` and `a ∘ (S → Sₙ) ∘ φ` agree modulo `I`, the first because
a map out of the localization `Q.Ring` is determined on the image of `P.Ring`. -/
private lemma Algebra.Extension.isLift_iff_of_isLocalization {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] {P : Extension.{w} R S} (N : Submonoid S)
    {Rₘ : Type*} [CommRing Rₘ] [Algebra R Rₘ]
    {Sₙ : Type*} [CommRing Sₙ] [Algebra S Sₙ]
    [Algebra R Sₙ] [IsScalarTower R S Sₙ] [Algebra Rₘ Sₙ] [IsScalarTower R Rₘ Sₙ]
    {Q : Extension.{w} Rₘ Sₙ} [Algebra P.Ring Q.Ring]
    [IsLocalization (N.comap (algebraMap P.Ring S)) Q.Ring]
    (hQS : ∀ x : P.Ring, algebraMap Q.Ring Sₙ (algebraMap P.Ring Q.Ring x)
      = algebraMap S Sₙ (algebraMap P.Ring S x))
    {D : Type w} [CommRing D] [Algebra Rₘ D] [Algebra R D] [IsScalarTower R Rₘ D]
    {I : Ideal D} (a : Sₙ →ₐ[Rₘ] D ⧸ I) (y : Q.Ring →ₐ[Rₘ] D) (b : P.Ring →ₐ[R] D)
    (hb : ∀ x : P.Ring, b x = y (algebraMap P.Ring Q.Ring x)) :
    (Ideal.Quotient.mkₐ Rₘ I).comp y = a.comp (IsScalarTower.toAlgHom Rₘ Q.Ring Sₙ) ↔
      (Ideal.Quotient.mkₐ R I).comp b
        = ((a.restrictScalars R).comp (IsScalarTower.toAlgHom R S Sₙ)).comp
          (IsScalarTower.toAlgHom R P.Ring S) := by
  constructor
  · refine fun h => AlgHom.ext fun x => ?_
    have hx := DFunLike.congr_fun h (algebraMap P.Ring Q.Ring x)
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, IsScalarTower.coe_toAlgHom'] at hx ⊢
    rw [hb x, hx, hQS x]
    rfl
  · refine fun h => IsLocalization.algHom_ext' (N.comap (algebraMap P.Ring S)) fun x => ?_
    have hx := DFunLike.congr_fun h x
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, IsScalarTower.coe_toAlgHom',
      AlgHom.coe_restrictScalars'] at hx ⊢
    rw [← hb x, hx, ← hQS x]

/-- **Stacks 04EE.** Let `A → B` be a ring map, let `φ : P.Ring → B` be a universal first order
thickening of `B` over `A`, let `M ⊆ A` and `N ⊆ B` be multiplicative subsets, and let `Aₘ` and
`Bₙ` be localizations of `A` at `M` and of `B` at `N`, compatibly. Then the localization
`φ⁻¹(N)⁻¹P.Ring → N⁻¹B` of `φ` is a universal first order thickening of `N⁻¹B` over `Aₘ`, and its
kernel is the extension of `ker φ`, so that the conormal module localizes:
`N⁻¹C_{B/A} = C_{N⁻¹B/Aₘ}`. Taking `N` to be the image of `M` gives the source's part (1), and
taking `M = ⊥`, so that `Aₘ = A`, gives its part (2). -/
@[stacks 04EE "Both parts at once: part (1) is `N = Algebra.algebraMapSubmonoid B M`, part (2) is
`M = ⊥`, whose instance `IsLocalization (⊥ : Submonoid A) A` is not found by synthesis and is
supplied as `IsLocalization.of_le_isUnit bot_le`. The localized thickening is an arbitrary
`Q : Algebra.Extension Aₘ Bₙ` pinned by the `IsLocalization` and `IsScalarTower` hypotheses and
by `algebraMap_comp`, because Mathlib's `Algebra.Extension.localization` does not localize the
base. The `In particular` on conormal modules is the ideal equation,
`Algebra.idealMap_isLocalizedModule` supplying the rest. That `φ⁻¹(N)` is multiplicative is
`Submonoid.comap`. See the module docstring."]
theorem Algebra.Extension.IsUniversalFirstOrderThickening.localization {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    {P : Extension.{w} A B} (hP : P.IsUniversalFirstOrderThickening)
    (M : Submonoid A) (N : Submonoid B)
    {Aₘ : Type*} [CommRing Aₘ] [Algebra A Aₘ] [IsLocalization M Aₘ]
    {Bₙ : Type*} [CommRing Bₙ] [Algebra B Bₙ] [IsLocalization N Bₙ]
    [Algebra A Bₙ] [IsScalarTower A B Bₙ] [Algebra Aₘ Bₙ] [IsScalarTower A Aₘ Bₙ]
    (Q : Extension.{w} Aₘ Bₙ) [Algebra P.Ring Q.Ring] [IsScalarTower A P.Ring Q.Ring]
    [IsLocalization (N.comap (algebraMap P.Ring B)) Q.Ring]
    (algebraMap_comp : (algebraMap Q.Ring Bₙ).comp (algebraMap P.Ring Q.Ring)
      = (algebraMap B Bₙ).comp (algebraMap P.Ring B)) :
    Q.IsUniversalFirstOrderThickening ∧ Q.ker = P.ker.map (algebraMap P.Ring Q.Ring) := by
  have hQB (x : P.Ring) : algebraMap Q.Ring Bₙ (algebraMap P.Ring Q.Ring x)
      = algebraMap B Bₙ (algebraMap P.Ring B x) := congr($algebraMap_comp x)
  have hker : Q.ker = P.ker.map (algebraMap P.Ring Q.Ring) :=
    IsLocalization.ker_eq_map_ker P.algebraMap_surjective N _ algebraMap_comp
  refine ⟨⟨?_, ?_⟩, hker⟩
  · rw [hker, ← Ideal.map_pow, hP.ker_sq_eq_bot, Ideal.map_bot]
  · intro D _ _ I hI a
    let _ : Algebra A D := ((algebraMap Aₘ D).comp (algebraMap A Aₘ)).toAlgebra
    have _ : IsScalarTower A Aₘ D := IsScalarTower.of_algebraMap_eq' rfl
    obtain ⟨b, hb, hbuniq⟩ := hP.existsUnique_lift I hI
      ((a.restrictScalars A).comp (IsScalarTower.toAlgHom A B Bₙ))
    have hunit : ∀ t : N.comap (algebraMap P.Ring B), IsUnit (b t) := fun t =>
      (IsNilpotent.isUnit_quotient_mk_iff ⟨2, hI⟩).1 <| by
        rw [show Ideal.Quotient.mk I (b t) = _ from DFunLike.congr_fun hb (t : P.Ring)]
        exact (IsLocalization.map_units Bₙ (⟨algebraMap P.Ring B t, t.2⟩ : N)).map a
    refine ⟨(IsLocalization.liftAlgHom hunit).extendScalarsOfIsLocalization Aₘ M,
      (Extension.isLift_iff_of_isLocalization N hQB a _ b fun x =>
        (IsLocalization.lift_eq hunit x).symm).2 hb, fun y hy => ?_⟩
    have hres := hbuniq ((y.restrictScalars A).comp (IsScalarTower.toAlgHom A P.Ring Q.Ring))
      ((Extension.isLift_iff_of_isLocalization N hQB a y _ fun _ => rfl).1 hy)
    exact IsLocalization.algHom_ext' (N.comap (algebraMap P.Ring B)) fun x =>
      (DFunLike.congr_fun hres x).trans (IsLocalization.lift_eq hunit x).symm

end Localization

end


@[expose] public section

universe u v w

/-!
# Differentials of the universal first order thickening

Proof of Stacks 04EF: let `R → A → B` be ring maps and let `B' → B` be the universal first order
thickening of `B` over `A`. Then `B'` is formally unramified over `A`, and the canonical map
`Ω_{A/R} ⊗_A B → Ω_{B'/R} ⊗_{B'} B` is an isomorphism.

The argument for the first assertion does not use the presentation of `B'` that the source's proof
uses. Formal unramifiedness of `A → B'` says that two `A`-algebra maps `g₁, g₂ : B' → C` that agree
modulo a square-zero ideal `I ⊆ C` are equal. Write `𝔮` for the ideal of `C` generated by
`g₁(ker(B' → B))`; it satisfies `𝔮² = 0`, because `ker(B' → B)² = 0`. In `C/𝔮I` the ideal generated
by `𝔮` and `I` has square zero and `C/(𝔮 + I)` receives a map from `B`, so the *uniqueness* half of
the universal property of `B' → B` applies and shows `g₁ ≡ g₂` modulo `𝔮I`. Feeding that back into
the same argument, with `I` replaced by `𝔮I`, gives `g₁ ≡ g₂` modulo `𝔮 · 𝔮I = 𝔮²I = 0`. So the
Nakayama step of the source's proof is replaced by two applications of one lemma; the ideal `𝔮` is
the trace on `C` of the nilpotent ideal `J'/J²` of the source.

Surjectivity of the canonical map is then formal: since `Ω_{B'/A} = 0`, the conormal sequence
`B' ⊗_A Ω_{A/R} → Ω_{B'/R} → Ω_{B'/A} → 0` of Tag 00RU exhibits `Ω_{B'/R}` as generated by the
differentials of elements of the image of `A`, and tensoring with `B` preserves that.

## Main results

* `Stacks.Unramified.ThickeningDifferentials.solution`: the statement of tag 04EF.

## Implementation notes

`Stacks.Unramified.ThickeningDifferentials.sub_mem_map_ker_mul` is the one-step lemma described
above, stated for an arbitrary square-zero ideal of an arbitrary `A`-algebra: `g₁ x - g₂ x ∈ 𝔮 · I`
whenever `g₁ x - g₂ x ∈ I` for all `x`. It is not in Mathlib, and it is the whole content of the
first assertion.

Injectivity of the canonical map is `Stacks.Unramified.ThickeningDifferentials.injective_map`. By
the source's route it is the construction of a retraction, and a retraction is the same thing as an
`R`-derivation `D : B' → M` extending `a ↦ 1 ⊗ da`, where `M` is the source `Ω_{A/R} ⊗_A B` of the
map. Such a `D` is exactly a lift of `id_B` through the trivial square-zero extension `B' ⋉ M → B`
of `B` by `M`, taken with the twisted `A`-algebra structure `a ↦ (algebraMap a, D a)`; that is a
square-zero situation over `B`, so the universal property of `B' → B` is the tool.
`Stacks.Unramified.ThickeningDifferentials.exists_derivation_restrict_eq` is that step, and
`Stacks.Unramified.ThickeningDifferentials.exists_linearMap_comp_map_eq` restates it for `Ω_{A/R}`
in place of `A`.

Tag 04EC's `existsUnique_lift` quantifies test algebras over the universe of `B'` alone, whereas
`Ω_{A/R} ⊗_A B` lies in the universes of `R`, `A` and `B` together, so the retraction cannot be
built on that module itself. It does not have to be: an element of a module is zero as soon as every
character of the module kills it, and `B` does have a model in the universe of `B'`, namely `N =
B'/ker(B' → B)`, so that `N⋆ = Hom_ℤ(N, ℚ⧸ℤ)` is a `B`-module in the universe of `B'`. Given a
character `c` of `Ω_{A/R} ⊗_A B`, the map `t ↦ (n ↦ c (e n · t))` into `N⋆`, where `e : N ≃ B`, is
`B`-linear, hence factors through the canonical map by the previous paragraph, and evaluating the
factorization at `n = 1` shows that `c` kills the kernel. That is
`Stacks.Unramified.ThickeningDifferentials.character_apply_eq_zero`, and
`CharacterModule.eq_zero_of_character_apply` finishes. So `N⋆` enters only as a cogenerator of the
category of `B`-modules that is small enough to be a legal test module, and no restriction on the
universes of the statement is needed.

## References

* [StacksProject 04EF](https://stacks.math.columbia.edu/tag/04EF)
* [StacksProject 04EC](https://stacks.math.columbia.edu/tag/04EC)
* [StacksProject 00RU](https://stacks.math.columbia.edu/tag/00RU)
* [StacksProject 00UO](https://stacks.math.columbia.edu/tag/00UO)
-/

namespace Stacks.Unramified.ThickeningDifferentials

open Algebra Algebra.Extension

open scoped TensorProduct


variable {A : Type v} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {P : Extension.{w} A B}

/-- A ring map `φ : P.Ring → T` over `A` killing `ker (P.Ring → B)` factors through `B`. -/
private lemma exists_algHom_comp_eq {T : Type*} [CommRing T] [Algebra A T] (φ : P.Ring →+* T)
    (hφ : ∀ r, φ (algebraMap A P.Ring r) = algebraMap A T r) (h : P.ker ≤ RingHom.ker φ) :
    ∃ a : B →ₐ[A] T, ∀ p, a (algebraMap P.Ring B p) = φ p :=
  ⟨{ toRingHom := RingHom.liftOfRightInverse (algebraMap P.Ring B) P.σ P.algebraMap_σ ⟨φ, h⟩
     commutes' := fun r => by
       rw [IsScalarTower.algebraMap_apply A P.Ring B r]
       exact (RingHom.liftOfRightInverse_comp_apply (algebraMap P.Ring B) P.σ P.algebraMap_σ
         _ (algebraMap A P.Ring r)).trans (hφ r) },
    RingHom.liftOfRightInverse_comp_apply (algebraMap P.Ring B) P.σ P.algebraMap_σ _⟩

/-- The image of `ker (P.Ring → B)` under a ring map has square zero. -/
private lemma map_ker_pow_two_eq_bot (hP : P.IsUniversalFirstOrderThickening) {C : Type*}
    [CommRing C] (g : P.Ring →+* C) : Ideal.map g P.ker ^ 2 = ⊥ := by
  rw [← Ideal.map_pow, hP.ker_sq_eq_bot, Ideal.map_bot]

/-- Two `A`-algebra maps that agree modulo `I` have differences in `I`. -/
private lemma sub_mem_of_mkₐ_comp_eq {C : Type*} [CommRing C] [Algebra A C] {I : Ideal C}
    {g₁ g₂ : P.Ring →ₐ[A] C}
    (h : (Ideal.Quotient.mkₐ A I).comp g₁ = (Ideal.Quotient.mkₐ A I).comp g₂)
    (x : P.Ring) : g₁ x - g₂ x ∈ I := by
  have hx := AlgHom.congr_fun h x
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at hx
  exact (Ideal.Quotient.eq).1 hx

/-- One step towards formal unramifiedness of the universal first order thickening: if two
`A`-algebra maps `g₁ g₂ : B' → C` agree modulo a square-zero ideal `I`, then they agree modulo
`𝔮 · I`, where `𝔮` is the ideal generated by the image of `ker (B' → B)` under `g₁`. -/
private lemma sub_mem_map_ker_mul (hP : P.IsUniversalFirstOrderThickening) {C : Type w}
    [CommRing C] [Algebra A C] {I : Ideal C} (hI : I ^ 2 = ⊥) (g₁ g₂ : P.Ring →ₐ[A] C)
    (h : ∀ x, g₁ x - g₂ x ∈ I) (x : P.Ring) :
    g₁ x - g₂ x ∈ Ideal.map (g₁ : P.Ring →+* C) P.ker * I := by
  have hq2 := map_ker_pow_two_eq_bot hP (g₁ : P.Ring →+* C)
  set q : Ideal C := Ideal.map (g₁ : P.Ring →+* C) P.ker with hqdef
  set 𝔟 : Ideal C := q * I with hbdef
  set 𝔞 : Ideal (C ⧸ 𝔟) := (q ⊔ I).map (Ideal.Quotient.mk 𝔟) with hadef
  have hle : (q ⊔ I) ^ 2 ≤ 𝔟 := by
    rw [pow_two, Ideal.mul_le]
    intro r hr s hs
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := Submodule.mem_sup.1 hr
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := Submodule.mem_sup.1 hs
    have e1 := Ideal.mul_eq_zero_of_pow_two_eq_bot hq2 hr₁ hs₁
    have e2 := Ideal.mul_eq_zero_of_pow_two_eq_bot hI hr₂ hs₂
    have e3 : (r₁ + r₂) * (s₁ + s₂) = r₁ * s₁ + (r₁ * s₂ + (s₁ * r₂ + r₂ * s₂)) := by ring
    rw [e3, e1, e2, zero_add, add_zero]
    exact Ideal.add_mem _ (Ideal.mul_mem_mul hr₁ hs₂) (Ideal.mul_mem_mul hs₁ hr₂)
  have ha2 : 𝔞 ^ 2 = ⊥ := by
    rw [hadef, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact hle
  obtain ⟨a, ha⟩ := exists_algHom_comp_eq
    (((Ideal.Quotient.mkₐ A 𝔞).comp ((Ideal.Quotient.mkₐ A 𝔟).comp g₁)).toRingHom)
    (fun r => AlgHom.commutes _ r) fun y hy => by
      simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply,
        Ideal.Quotient.mkₐ_eq_mk]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hy))
  obtain ⟨a', -, huniq⟩ := hP.existsUnique_lift 𝔞 ha2 a
  have h1 : (Ideal.Quotient.mkₐ A 𝔞).comp ((Ideal.Quotient.mkₐ A 𝔟).comp g₁)
      = a.comp (IsScalarTower.toAlgHom A P.Ring B) := by
    refine AlgHom.ext fun y => ?_
    exact (ha y).symm
  have h2 : (Ideal.Quotient.mkₐ A 𝔞).comp ((Ideal.Quotient.mkₐ A 𝔟).comp g₂)
      = a.comp (IsScalarTower.toAlgHom A P.Ring B) := by
    refine AlgHom.ext fun y => ?_
    change Ideal.Quotient.mk 𝔞 (Ideal.Quotient.mk 𝔟 (g₂ y)) = a (algebraMap P.Ring B y)
    rw [ha y]
    change _ = Ideal.Quotient.mk 𝔞 (Ideal.Quotient.mk 𝔟 (g₁ y))
    rw [Ideal.Quotient.eq]
    have hmem : g₂ y - g₁ y ∈ I := by
      have h' := neg_mem (h y)
      rwa [neg_sub] at h'
    have h'' : (Ideal.Quotient.mk 𝔟) (g₂ y - g₁ y) ∈ 𝔞 :=
      Ideal.mem_map_of_mem _ (Ideal.mem_sup_right hmem)
    rwa [map_sub] at h''
  have key : (Ideal.Quotient.mkₐ A 𝔟).comp g₁ = (Ideal.Quotient.mkₐ A 𝔟).comp g₂ :=
    (huniq _ h1).trans (huniq _ h2).symm
  exact sub_mem_of_mkₐ_comp_eq key x

/-- **The first half of Stacks 04EF.** The universal first order thickening `B' → B` of `B` over
`A` has `B'` formally unramified over `A`. -/
private lemma formallyUnramified (hP : P.IsUniversalFirstOrderThickening) :
    FormallyUnramified A P.Ring := by
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro C _ _ I hI g₁ g₂ hg
  have h1 := sub_mem_of_mkₐ_comp_eq hg
  have h2 : ∀ x, g₁ x - g₂ x ∈ Ideal.map (g₁ : P.Ring →+* C) P.ker * I := fun x =>
    sub_mem_map_ker_mul hP hI g₁ g₂ h1 x
  have hq2 := map_ker_pow_two_eq_bot hP (g₁ : P.Ring →+* C)
  have hI2 : (Ideal.map (g₁ : P.Ring →+* C) P.ker * I) ^ 2 = ⊥ := by
    rw [pow_two, mul_mul_mul_comm, ← pow_two, hq2, Ideal.bot_mul]
  have h3 : ∀ x, g₁ x - g₂ x ∈ Ideal.map (g₁ : P.Ring →+* C) P.ker *
      (Ideal.map (g₁ : P.Ring →+* C) P.ker * I) := fun x =>
    sub_mem_map_ker_mul hP hI2 g₁ g₂ h2 x
  have hfin : Ideal.map (g₁ : P.Ring →+* C) P.ker *
      (Ideal.map (g₁ : P.Ring →+* C) P.ker * I) = ⊥ := by
    rw [← mul_assoc, ← pow_two, hq2, Ideal.bot_mul]
  refine AlgHom.ext fun x => ?_
  have hx := h3 x
  rw [hfin] at hx
  exact sub_eq_zero.1 (by simpa using hx)

section Map

variable (R : Type u) [CommRing R] [Algebra R A] [Algebra R B] [IsScalarTower R A B]

/-- **Derivations extend along the universal first order thickening.** If `M` is a module in the
universe of `B'` on which the kernel of `B' → B` acts by zero, then every `R`-derivation `A → M`
is the restriction of an `R`-derivation `B' → M`.

The derivation is read off from the second component of a lift of `B → C ⧸ I` through the trivial
square-zero extension `C = B' ⋉ M`, given the `A`-algebra structure `a ↦ (algebraMap a, D a)` and
the ideal `I` of pairs whose first component dies in `B`; that `I ^ 2 = 0` uses both
`ker (B' → B) ^ 2 = 0` and the hypothesis on the action. -/
private lemma exists_derivation_restrict_eq (hP : P.IsUniversalFirstOrderThickening) {M : Type w}
    [AddCommGroup M] [Module R M] [Module A M] [Module P.Ring M] [IsScalarTower R P.Ring M]
    [IsScalarTower A P.Ring M] (hM : ∀ x ∈ P.ker, ∀ m : M, x • m = 0) (D : Derivation R A M) :
    ∃ D' : Derivation R P.Ring M, ∀ a : A, D' (algebraMap A P.Ring a) = D a := by
  let _instOp : Module (P.Ring)ᵐᵒᵖ M :=
    Module.compHom M (RingEquiv.toOpposite P.Ring).symm.toRingHom
  have _instCentral : IsCentralScalar P.Ring M := ⟨fun _ _ => rfl⟩
  have hsub : ∀ {p p' : P.Ring}, p - p' ∈ P.ker → ∀ m : M, p • m = p' • m := by
    intro p p' h m
    have h' := hM _ h m
    rwa [sub_smul, sub_eq_zero] at h'
  let φ : A →+* TrivSqZeroExt P.Ring M :=
    { toFun := fun a => TrivSqZeroExt.inl (algebraMap A P.Ring a) + TrivSqZeroExt.inr (D a)
      map_one' := by simp
      map_mul' := fun x y => by
        refine TrivSqZeroExt.ext ?_ ?_
        · simp
        · simp [D.leibniz, add_comm]
      map_zero' := by simp
      map_add' := fun x y => by
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp }
  have hφ : ∀ x : A, φ x = TrivSqZeroExt.inl (algebraMap A P.Ring x) + TrivSqZeroExt.inr (D x) :=
    fun _ => rfl
  let _inst : Algebra A (TrivSqZeroExt P.Ring M) := φ.toAlgebra
  have halg : ∀ x : A, algebraMap A (TrivSqZeroExt P.Ring M) x
      = TrivSqZeroExt.inl (algebraMap A P.Ring x) + TrivSqZeroExt.inr (D x) := hφ
  let fstHom : TrivSqZeroExt P.Ring M →+* P.Ring :=
    { toFun := TrivSqZeroExt.fst
      map_one' := TrivSqZeroExt.fst_one
      map_mul' := TrivSqZeroExt.fst_mul
      map_zero' := TrivSqZeroExt.fst_zero
      map_add' := TrivSqZeroExt.fst_add }
  set I : Ideal (TrivSqZeroExt P.Ring M) := Ideal.comap fstHom P.ker with hIdef
  have hmemI : ∀ x : TrivSqZeroExt P.Ring M, x ∈ I ↔ x.fst ∈ P.ker := fun _ => Iff.rfl
  have hI2 : I ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [hmemI] at hx hy
    have h1 : x.fst * y.fst = 0 := Ideal.mul_eq_zero_of_pow_two_eq_bot hP.ker_sq_eq_bot hx hy
    refine Ideal.mem_bot.2 (TrivSqZeroExt.ext ?_ ?_)
    · simpa [TrivSqZeroExt.fst_mul] using h1
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_zero, op_smul_eq_smul]
      rw [hM _ hx, hM _ hy, add_zero]
  obtain ⟨a, ha⟩ := exists_algHom_comp_eq
    ((Ideal.Quotient.mk I).comp (TrivSqZeroExt.inlHom P.Ring M)) (fun r => by
      simp only [RingHom.coe_comp, Function.comp_apply]
      change Ideal.Quotient.mk I _ = Ideal.Quotient.mk I (algebraMap A (TrivSqZeroExt P.Ring M) r)
      rw [Ideal.Quotient.eq, halg r, hmemI]
      simp) fun y hy => by
    simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
    rw [Ideal.Quotient.eq_zero_iff_mem, hmemI]
    simpa using hy
  obtain ⟨g, hg, -⟩ := hP.existsUnique_lift I hI2 a
  have hga : ∀ x : A, g (algebraMap A P.Ring x)
      = TrivSqZeroExt.inl (algebraMap A P.Ring x) + TrivSqZeroExt.inr (D x) := fun x =>
    (g.commutes x).trans (halg x)
  have hgp : ∀ p : P.Ring, (g p).fst - p ∈ P.ker := by
    intro p
    have h := AlgHom.congr_fun hg p
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, IsScalarTower.coe_toAlgHom'] at h
    rw [ha p] at h
    change Ideal.Quotient.mk I _ = Ideal.Quotient.mk I (TrivSqZeroExt.inl p) at h
    rw [Ideal.Quotient.eq, hmemI] at h
    simpa using h
  have hcomm : ∀ (p : P.Ring) (m : M), (g p).fst • m = p • m := fun p m => hsub (hgp p) m
  let l : P.Ring →ₗ[R] M :=
    { toFun := fun p => (g p).snd
      map_add' := fun p q => by simp
      map_smul' := fun r p => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply R A P.Ring r, hga,
          Derivation.map_algebraMap]
        simp only [TrivSqZeroExt.inr_zero, add_zero, TrivSqZeroExt.snd_mul,
          TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, op_smul_eq_smul]
        rw [← IsScalarTower.algebraMap_apply R A P.Ring r, algebraMap_smul]
        simp }
  refine ⟨Derivation.mk' l ?_, fun x => ?_⟩
  · intro x y
    change (g (x * y)).snd = x • (g y).snd + y • (g x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul, hcomm, hcomm]
  · change (g (algebraMap A P.Ring x)).snd = D x
    rw [hga]
    simp

/-- **Every `A`-linear map out of `Ω_{A/R}` into a `B`-module in the universe of `B'` factors
through `Ω_{B'/R}`.** This is the previous lemma restated for modules of differentials. -/
private lemma exists_linearMap_comp_map_eq (hP : P.IsUniversalFirstOrderThickening) {M : Type w}
    [AddCommGroup M] [Module R M] [Module A M] [Module P.Ring M] [Module B M]
    [IsScalarTower R A M] [IsScalarTower R P.Ring M] [IsScalarTower A P.Ring M]
    [IsScalarTower P.Ring B M] (ℓ : Ω[A⁄R] →ₗ[A] M) :
    ∃ Φ : Ω[P.Ring⁄R] →ₗ[P.Ring] M,
      ℓ = (Φ.restrictScalars A).comp (KaehlerDifferential.map R R A P.Ring) := by
  have hM : ∀ x ∈ P.ker, ∀ m : M, x • m = 0 := by
    intro x hx m
    have hx' : algebraMap P.Ring B x = 0 := hx
    rw [← algebraMap_smul (A := B) x m, hx', zero_smul]
  obtain ⟨D', hD'⟩ := exists_derivation_restrict_eq R hP hM
    (KaehlerDifferential.linearMapEquivDerivation R A ℓ)
  refine ⟨D'.liftKaehlerDifferential, ?_⟩
  apply (KaehlerDifferential.linearMapEquivDerivation R A).injective
  ext x
  simpa using (hD' x).symm

/-- Transport of a scalar tower to character modules: if `X` acts on `Y` and both act on `N`
compatibly, the same holds on `N⋆ = Hom_ℤ(N, ℚ/ℤ)`, where the actions are by precomposition. -/
private lemma isScalarTower_characterModule (X Y N : Type*) [CommRing X] [CommRing Y]
    [AddCommGroup N] [Algebra X Y] [Module X N] [Module Y N] [IsScalarTower X Y N]
    [SMulCommClass X Y N] : IsScalarTower X Y (CharacterModule N) :=
  ⟨fun x y c => by
    ext n
    simp only [CharacterModule.smul_apply]
    rw [smul_assoc, smul_comm]⟩

/-- **Characters kill the kernel of the canonical map.** Let `c` be a character of
`Ω_{A/R} ⊗_A B` and let `z` be killed by the canonical map. Then `c z = 0`.

Together with `CharacterModule.eq_zero_of_character_apply` this is the injectivity of the canonical
map, and it is where the universe of `B'` is reconciled with that of `A`: put
`N := B' / ker (B' → B)`, a ring in the universe of `B'` isomorphic to `B`, and
`M := CharacterModule N`, a `B`-module in the universe of `B'` through that isomorphism. The map
`L : Ω_{A/R} ⊗_A B → M`, `L t = (n ↦ c (e n • t))` with `e : N ≃+* B`, is `B`-linear and satisfies
`(L z) 1 = c z`, so it suffices that `L` factor through the canonical map. Since `L` is `B`-linear
it is determined by `ℓ = L ∘ (1 ⊗ ·) : Ω_{A/R} → M`, and `exists_linearMap_comp_map_eq` applied to
`ℓ` produces a `Φ` whose base change `Φ.liftBaseChange B` is the required factorization. -/
private lemma character_apply_eq_zero (hP : P.IsUniversalFirstOrderThickening)
    (c : CharacterModule (B ⊗[A] Ω[A⁄R])) (z : B ⊗[A] Ω[A⁄R])
    (hz : (((TensorProduct.mk P.Ring B Ω[P.Ring⁄R] 1).restrictScalars A).comp
      (KaehlerDifferential.map R R A P.Ring)).liftBaseChange B z = 0) : c z = 0 := by
  have hsurj : Function.Surjective (algebraMap P.Ring B) := fun x => ⟨P.σ x, P.algebraMap_σ x⟩
  let e : (P.Ring ⧸ P.ker) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := IsScalarTower.toAlgHom A P.Ring B) hsurj
  have he : ∀ p : P.Ring, e (Ideal.Quotient.mk P.ker p) = algebraMap P.Ring B p := fun _ => rfl
  let _instAlg : Algebra B (P.Ring ⧸ P.ker) := (e.symm.toAlgHom.toRingHom).toAlgebra
  have _instTower : IsScalarTower P.Ring B (P.Ring ⧸ P.ker) :=
    IsScalarTower.of_algebraMap_eq fun p => by
      rw [RingHom.algebraMap_toAlgebra]
      exact ((e.symm_apply_eq).2 (he p).symm).symm
  have _instTowerAB : IsScalarTower A B (P.Ring ⧸ P.ker) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply A P.Ring (P.Ring ⧸ P.ker) a,
        IsScalarTower.algebraMap_apply P.Ring B (P.Ring ⧸ P.ker) (algebraMap A P.Ring a),
        ← IsScalarTower.algebraMap_apply A P.Ring B a]
  have _h1 : IsScalarTower R A (CharacterModule (P.Ring ⧸ P.ker)) :=
    isScalarTower_characterModule R A _
  have _h2 : IsScalarTower R P.Ring (CharacterModule (P.Ring ⧸ P.ker)) :=
    isScalarTower_characterModule R P.Ring _
  have _h3 : IsScalarTower A P.Ring (CharacterModule (P.Ring ⧸ P.ker)) :=
    isScalarTower_characterModule A P.Ring _
  have _h4 : IsScalarTower P.Ring B (CharacterModule (P.Ring ⧸ P.ker)) :=
    isScalarTower_characterModule P.Ring B _
  have _h5 : IsScalarTower A B (CharacterModule (P.Ring ⧸ P.ker)) :=
    isScalarTower_characterModule A B _
  -- `e` is `B`-linear for the `B`-algebra structure it defines on `N`.
  let eL : (P.Ring ⧸ P.ker) →ₗ[B] B :=
    { toFun := e
      map_add' := map_add e
      map_smul' := fun b n => by
        rw [Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra]
        simp }
  -- the `B`-linear map `L t = (n ↦ c (e n • t))`
  let φ : (B ⊗[A] Ω[A⁄R]) ⊗[B] (P.Ring ⧸ P.ker) →ₗ[B] B ⊗[A] Ω[A⁄R] :=
    (TensorProduct.rid B (B ⊗[A] Ω[A⁄R])).toLinearMap ∘ₗ LinearMap.lTensor _ eL
  let L : (B ⊗[A] Ω[A⁄R]) →ₗ[B] CharacterModule (P.Ring ⧸ P.ker) :=
    CharacterModule.curry (CharacterModule.dual φ c)
  have hL : ∀ (t : B ⊗[A] Ω[A⁄R]) (n : P.Ring ⧸ P.ker), L t n = c (e n • t) := fun _ _ => rfl
  -- its restriction along `ω ↦ 1 ⊗ ω`
  let ℓ : Ω[A⁄R] →ₗ[A] CharacterModule (P.Ring ⧸ P.ker) :=
    (L.restrictScalars A).comp (TensorProduct.mk A B Ω[A⁄R] 1)
  obtain ⟨Φ, hΦ⟩ := exists_linearMap_comp_map_eq R hP ℓ
  have hΦω : ∀ ω : Ω[A⁄R], ℓ ω = Φ (KaehlerDifferential.map R R A P.Ring ω) := fun ω =>
    LinearMap.congr_fun hΦ ω
  -- the retraction, and the factorization of `L` through the canonical map
  have hfac : ∀ t : B ⊗[A] Ω[A⁄R], L t = Φ.liftBaseChange B
      ((((TensorProduct.mk P.Ring B Ω[P.Ring⁄R] 1).restrictScalars A).comp
        (KaehlerDifferential.map R R A P.Ring)).liftBaseChange B t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b ω =>
        have hb : (b ⊗ₜ[A] ω : B ⊗[A] Ω[A⁄R]) = b • (1 ⊗ₜ[A] ω) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hb, map_smul, map_smul, map_smul]
        congr 1
        rw [show L (1 ⊗ₜ[A] ω) = ℓ ω from rfl, hΦω ω]
        simp
    | add t₁ t₂ ht₁ ht₂ => rw [map_add, map_add, map_add, ht₁, ht₂]
  have hLz : L z = 0 := by rw [hfac z, hz, map_zero]
  have := hL z 1
  rw [hLz] at this
  rw [map_one e, one_smul] at this
  exact this.symm

/-- Injectivity of the canonical map `Ω_{A/R} ⊗_A B → Ω_{B'/R} ⊗_{B'} B` of Stacks 04EF. -/
private lemma injective_map (hP : P.IsUniversalFirstOrderThickening) :
    Function.Injective
      ((((TensorProduct.mk P.Ring B Ω[P.Ring⁄R] 1).restrictScalars A).comp
        (KaehlerDifferential.map R R A P.Ring)).liftBaseChange B) := by
  intro z₁ z₂ h
  rw [← sub_eq_zero]
  refine CharacterModule.eq_zero_of_character_apply fun c =>
    character_apply_eq_zero R hP c _ ?_
  rw [map_sub, h, sub_self]

/-- Surjectivity of the canonical map `Ω_{A/R} ⊗_A B → Ω_{B'/R} ⊗_{B'} B` of Stacks 04EF: it
holds because `Ω_{B'/A} = 0`, so that `Ω_{B'/R}` is generated by the differentials of the image
of `A`. -/
private lemma surjective_map (hP : P.IsUniversalFirstOrderThickening) :
    Function.Surjective
      ((((TensorProduct.mk P.Ring B Ω[P.Ring⁄R] 1).restrictScalars A).comp
        (KaehlerDifferential.map R R A P.Ring)).liftBaseChange B) := by
  have hsub : Subsingleton Ω[P.Ring⁄A] :=
    (formallyUnramified hP).subsingleton_kaehlerDifferential
  have hmbc : Function.Surjective (KaehlerDifferential.mapBaseChange R A P.Ring) := fun ω =>
    (KaehlerDifferential.exact_mapBaseChange_map R A P.Ring ω).1 (Subsingleton.elim _ _)
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul b ω =>
      obtain ⟨y, rfl⟩ := hmbc ω
      induction y using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | tmul p ω₀ =>
          refine ⟨(algebraMap P.Ring B p * b) ⊗ₜ[A] ω₀, ?_⟩
          simp only [LinearMap.liftBaseChange_tmul, KaehlerDifferential.mapBaseChange_tmul,
            LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
            TensorProduct.mk_apply]
          simp [Algebra.smul_def, TensorProduct.smul_tmul', mul_comm]
      | add y₁ y₂ hy₁ hy₂ =>
          obtain ⟨x₁, hx₁⟩ := hy₁
          obtain ⟨x₂, hx₂⟩ := hy₂
          exact ⟨x₁ + x₂, by rw [map_add, hx₁, hx₂, map_add, TensorProduct.tmul_add]⟩
  | add t₁ t₂ ht₁ ht₂ =>
      obtain ⟨x₁, hx₁⟩ := ht₁
      obtain ⟨x₂, hx₂⟩ := ht₂
      exact ⟨x₁ + x₂, by rw [map_add, hx₁, hx₂]⟩

end Map

public theorem solution (R : Type u) {A : Type v} {B : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] {P : Extension.{w} A B} (hP : P.IsUniversalFirstOrderThickening) :
    FormallyUnramified A P.Ring ∧
      Function.Bijective
        ((((TensorProduct.mk P.Ring B Ω[P.Ring⁄R] 1).restrictScalars A).comp
          (KaehlerDifferential.map R R A P.Ring)).liftBaseChange B) :=
  ⟨formallyUnramified hP, injective_map R hP, surjective_map R hP⟩

end Stacks.Unramified.ThickeningDifferentials

/-!
# Differentials of the universal first order thickening

Let `R → A → B` be ring maps and let `B' → B` be the universal first order thickening of `B`
over `A`, that is, the surjection of `A`-algebras onto `B` with square-zero kernel through which
every square-zero situation over `B` lifts uniquely (Tag 04EC; it exists as soon as `A → B` is
formally unramified, Tag 04EB). Then two things happen.

First, `B'` is again formally unramified over `A`. The reason is that `B'` is, in the
construction of Tag 04EB, the quotient `P/J'` of a polynomial algebra `P = A[x_i]` by
`J' = (f_i) + J²`, where `J` is the kernel of `P → B` and the `f_i ∈ J` are chosen so that
`d f_i = d x_i ⊗ 1` in `Ω_{P/A} ⊗_P B`; the classes of the `f_i` then generate
`Ω_{P/A} ⊗_P B'` modulo the nilpotent ideal `J'/J²`, hence generate it outright by Nakayama
(Tag 00DV), so the conormal sequence of Tag 00RU forces `Ω_{B'/A} = 0` (Tag 00UO).

Second, and this is the point of the lemma, differentials *over `R`* do not change when `B` is
replaced by its thickening: the canonical map
`Ω_{A/R} ⊗_A B → Ω_{B'/R} ⊗_{B'} B`
is an isomorphism. Again by the conormal sequence, `Ω_{B'/R} ⊗_{B'} B` is the cokernel of
`J'/(J')² ⊗_{B'} B → Ω_{P/R} ⊗_P B`, the first map kills `J²/(J')²`, and under the splitting
`Ω_{P/R} ⊗_P B = Ω_{A/R} ⊗_A B ⊕ ⨁ B dx_i` coming from `P = A[x_i]` the remaining summand
`(f_i)/(J')² ⊗_{B'} B` maps isomorphically onto `⨁ B dx_i`. What survives is exactly
`Ω_{A/R} ⊗_A B`.

## Main results

* `Algebra.Extension.IsUniversalFirstOrderThickening.formallyUnramified_ring_and_bijective_map`:
  a universal first order thickening `B' → B` of `B` over `A` is formally unramified over `A`,
  and the canonical map `Ω_{A/R} ⊗_A B → Ω_{B'/R} ⊗_{B'} B` is bijective.

## Implementation notes

The thickening `B' → B` is an `Algebra.Extension A B` satisfying
`Algebra.Extension.IsUniversalFirstOrderThickening` (Tag 04EC), so `B'` is `P.Ring` and the
surjection is `algebraMap P.Ring B`. The ring maps `R → A → B` are the instances
`Algebra R A`, `Algebra A B`, `Algebra R B` together with `IsScalarTower R A B`, which pins
`algebraMap R B` to the composite; `Algebra.Extension` then supplies `Algebra R P.Ring`,
`IsScalarTower R A P.Ring` and `IsScalarTower R P.Ring B` for free, so no further structure is
assumed on `B'`. The statement is made for an arbitrary `P` with that property rather than for
the chosen `Algebra.FormallyUnramified.universalFirstOrderThickening A B`, to which it therefore
applies: the property is what the source uses, and the choice is immaterial.

Tensor products are written with the scalars on the left, as Mathlib does
(`KaehlerDifferential.mapBaseChange`, `Algebra.Extension.CotangentSpace`): the source's
`Ω_{A/R} ⊗_A B → Ω_{B'/R} ⊗_{B'} B` is `B ⊗[A] Ω[A⁄R] →ₗ[B] B ⊗[P.Ring] Ω[P.Ring⁄R]`.

The canonical map is written out rather than named, since Mathlib has no name for it: it is the
`B`-linear extension (`LinearMap.liftBaseChange`) of the `A`-linear map
`Ω[A⁄R] → B ⊗[P.Ring] Ω[P.Ring⁄R]`, `ω ↦ 1 ⊗ₜ KaehlerDifferential.map R R A P.Ring ω`. It is
characterised by `b ⊗ₜ D a ↦ b ⊗ₜ D (algebraMap A B' a)` for `b : B` and `a : A` (by
`LinearMap.liftBaseChange_tmul`, `KaehlerDifferential.map_D` and `TensorProduct.smul_tmul'`),
which is the source's map. It is the same construction as
`KaehlerDifferential.mapBaseChange R A B'` with `Ω_{B'/R}` replaced by its base change to `B`.

Formal unramifiedness of `A → B` is a hypothesis of the source but not of the statement: it is
implied by the hypothesis that a universal first order thickening exists, so assuming it as well
would leave a redundant hypothesis. Indeed two lifts `g₁ g₂ : B →ₐ[A] C` of one
`a : B →ₐ[A] C ⧸ I` with `I ^ 2 = ⊥` compose with the surjection `B' → B` to two lifts of
`a ∘ (B' → B)`, hence agree, hence are equal (Tag 00UM,
`Algebra.FormallyUnramified.iff_comp_injective`).

Faithfulness. (1) No hypothesis is dead: `hP` names `B'` and occurs in both conclusions, and it
is load-bearing rather than decorative — with `B'` replaced by `B` the second conclusion is false
(for `R = k`, `A = k[x]`, `B = k[x]/(x)`, the map `Ω_{A/R} ⊗_A B → Ω_{B/R}` is `k → 0`); the
tower `R → A → B` is used because both modules of differentials are taken over `R` while the
tensor products are over `A` and over `B'`; and formal unramifiedness of `A → B` is omitted
exactly because it is implied (see above). (2) The scalars and the base are the source's:
`Ω[A⁄R]` and `Ω[P.Ring⁄R]` are relative to `R`, the two tensor products are over `A` and over
`B'` respectively, and the map is `B`-linear, not merely `A`-linear. (3) The source's canonical
map is pinned, not merely asserted to exist: the statement is `Function.Bijective` of one
explicit map, the one sending `b ⊗ₜ D a` to `b ⊗ₜ D (algebraMap A B' a)`. (4) The instantiation
is not degenerate: for `R = k` a field of characteristic `≠ 2`, `A = k[x]`, `B = k[x]/(x)` the
thickening is `B' = k[x]/(x²)` (Tag 04ED), and both sides are one-dimensional over `k` — namely
`B dx` and `(B' dx / B' · 2x dx) ⊗_{B'} B` — so neither the source nor the target of the
bijection is forced to be zero.

## References

* [StacksProject 04EF](https://stacks.math.columbia.edu/tag/04EF)
* [StacksProject 04EB](https://stacks.math.columbia.edu/tag/04EB)
* [StacksProject 04EC](https://stacks.math.columbia.edu/tag/04EC)
* [StacksProject 00RU](https://stacks.math.columbia.edu/tag/00RU)
* [StacksProject 00UO](https://stacks.math.columbia.edu/tag/00UO)
-/


open scoped TensorProduct


namespace Algebra.Extension.IsUniversalFirstOrderThickening

/-- **Stacks 04EF.** Let `R → A → B` be ring maps and let `B' → B` be the universal first order
thickening of `B` over `A`. Then `B'` is formally unramified over `A`, and the canonical map
`Ω_{A/R} ⊗_A B → Ω_{B'/R} ⊗_{B'} B`, which sends `b ⊗ D a` to `b ⊗ D (algebraMap A B' a)`, is
an isomorphism. -/
@[stacks 04EF "The thickening `B' → B` is an `Algebra.Extension A B` satisfying
`Algebra.Extension.IsUniversalFirstOrderThickening` (04EC); existence is 04EB. Tensor products
carry the scalars on the left, as in `KaehlerDifferential.mapBaseChange`, and the source's
canonical map is spelled as the `B`-linear extension of `ω ↦ 1 ⊗ₜ KaehlerDifferential.map ω`.
Formal unramifiedness of `A → B` is not assumed: it follows from `hP`. See the module docstring."]
public theorem formallyUnramified_ring_and_bijective_map (R : Type u) {A : Type v} {B : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] {P : Extension.{w} A B} (hP : P.IsUniversalFirstOrderThickening) :
    FormallyUnramified A P.Ring ∧
      Function.Bijective
        ((((TensorProduct.mk P.Ring B Ω[P.Ring⁄R] 1).restrictScalars A).comp
          (KaehlerDifferential.map R R A P.Ring)).liftBaseChange B) :=
  Stacks.Unramified.ThickeningDifferentials.solution R hP

end Algebra.Extension.IsUniversalFirstOrderThickening

end

/-!
# The universal first order thickening of `R/I` over `R`

Fix a commutative unital ring `R` and an ideal `I ⊆ R`. Let
  `π : R/I² → R/I`
be the canonical surjection induced by the inclusion `I² ⊆ I`
(`π(r + I²) = r + I`). Both `R/I²` and `R/I` are `R`-algebras via the
canonical quotient maps `R → R/I²` and `R → R/I`, and `π` is an
`R`-algebra homomorphism.

This problem characterizes the *universal first order thickening* of
`R/I` over `R` (Stacks Project, Tag 04ED, Lemma 10.149.3). By
Definition 10.149.2 (Tag 04EC), the universal first order thickening of a
formally unramified ring map `R → S` is the (unique up to unique
isomorphism) surjection of `R`-algebras `S' → S` with square-zero kernel
satisfying the universal property of Lemma 10.149.1 (Tag 04EB). Since
`R → R/I` is surjective, hence formally unramified, this applies to
`S = R/I`. The content of Tag 04ED is that `π : R/I² → R/I` is such an
object.

The content is:

* (Statement 1) `π` is a surjective `R`-algebra homomorphism whose kernel
  is the ideal `I/I² ⊆ R/I²` (in Mathlib `Ideal.cotangentIdeal I`,
  the image of `I` under `R → R/I²`), and this kernel is of square zero,
  i.e. `(I/I²)² = 0`.
* (Statement 2) `π` satisfies the universal property of the first order
  thickening: for any ring `A` with a square-zero ideal `J`, and ring
  maps `b : R → A`, `a : R/I → A/J` forming a commuting square with the
  canonical projections, there is a unique `R`-algebra map `a' : R/I² → A`
  with `(A → A/J) ∘ a' = a ∘ π`.
* (Statement 3) Consequently the conormal module `C_{(R/I)/R}` (the kernel
  of the thickening regarded as a module) is `I/I²`; in Mathlib this
  module is `Ideal.Cotangent I`, which is `R`-linearly isomorphic to the
  kernel `Ideal.cotangentIdeal I` of `π`.
-/

@[expose] public section
-- We use Mathlib's `Ideal.cotangentIdeal I : Ideal (R ⧸ I^2)`, the image
-- of `I` in `R/I²` (this is `ker π`), and `Ideal.Cotangent I`, the
-- conormal module `I/I²` as an `R`- (resp. `R/I`-) module.

namespace UniversalThickening

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- An ideal `J` of a ring `A` is *of
square zero* if `J² = 0`, i.e. `x*y = 0` for all `x,y ∈ J`. We encode this
as `J^2 = ⊥`. -/
@[ega "IV 16.5.14"]
def IsSquareZero {A : Type*} [CommRing A] (J : Ideal A) : Prop :=
  J ^ 2 = ⊥

/-- The canonical `R`-algebra surjection `π : R/I² → R/I` induced by the
inclusion `I² ⊆ I` (sending `r + I² ↦ r + I`). This is the candidate
universal first order thickening of `R/I` over `R`. -/
noncomputable def pi : (R ⧸ I ^ 2) →ₐ[R] (R ⧸ I) :=
  Ideal.Quotient.factorₐ R (by
    simpa using Ideal.pow_le_self (n := 2) (by norm_num))

/-- Correctness statement for `pi`: it sends the class `r + I²` to `r + I`,
i.e. it is the canonical surjection described in the problem. -/
theorem pi_apply_mk (y : R) :
    (pi I) (Ideal.Quotient.mk (I ^ 2) y) = Ideal.Quotient.mk I y := by
  rw [pi, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk]

/-- The kernel-hypothesis: `I² ≤ I`. -/
theorem pow_two_le : I ^ 2 ≤ I :=
  by simpa using Ideal.pow_le_self (n := 2) (by norm_num : (2 : ℕ) ≠ 0)

/-- `pi I`, as a ring homomorphism, equals `Ideal.Quotient.factor`. -/
theorem pi_eq_factor :
    (pi I : (R ⧸ I ^ 2) →+* (R ⧸ I)) = Ideal.Quotient.factor (pow_two_le I) := by
  ext x
  simp [pi]

/-- The map `π : R/I² → R/I` is surjective. -/
theorem pi_surjective : Function.Surjective (pi I) := by
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk (I ^ 2) z, pi_apply_mk I z⟩

/-- The kernel of `π` (as an ideal of `R/I²`) is
`I/I²`, i.e. `Ideal.cotangentIdeal I` (the image of `I` in `R/I²`). -/
theorem ker_pi :
    RingHom.ker (pi I : (R ⧸ I ^ 2) →+* (R ⧸ I)) = I.cotangentIdeal := by
  rw [pi_eq_factor, Ideal.Quotient.factor]
  rw [Ideal.ker_quotient_lift (Ideal.Quotient.mk I)
    (by rw [Ideal.mk_ker]; exact pow_two_le I)]
  rw [Ideal.mk_ker, Ideal.cotangentIdeal]
  ext x
  simp [Ideal.mem_map_iff_of_surjective, Ideal.Quotient.mk_surjective]

/-- The kernel `I/I²` of `π` is an
ideal of square zero, i.e. `(I/I²)² = 0`. -/
@[ega "0 18.3.8" "Square-zero clause", ega "0 20.5.12" "partial"]
theorem ker_pi_isSquareZero :
    IsSquareZero (RingHom.ker (pi I : (R ⧸ I ^ 2) →+* (R ⧸ I))) := by
  rw [IsSquareZero, ker_pi, Ideal.cotangentIdeal_square]

/-- For any commutative ring `A` with a
square-zero ideal `J ⊆ A`, and ring homomorphisms `b : R → A`,
`a : R/I → A/J` such that the square
`a ∘ (R → R/I) = (A → A/J) ∘ b` commutes (where `R → A/J` is `b` followed
by `A → A/J`), there exists a **unique** `R`-algebra homomorphism
`a' : R/I² → A`, encoded as a unique ring homomorphism with
`a' ∘ (R → R/I²) = b` (the `R`-algebra condition), such that
`(A → A/J) ∘ a' = a ∘ π`. -/
@[stacks 04ED]
theorem universal_property
    {A : Type*} [CommRing A] (J : Ideal A) (hJ : IsSquareZero J)
    (b : R →+* A) (a : (R ⧸ I) →+* (A ⧸ J))
    (hcomm : a.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp b) :
    ∃! a' : (R ⧸ I ^ 2) →+* A,
      a'.comp (Ideal.Quotient.mk (I ^ 2)) = b ∧
      (Ideal.Quotient.mk J).comp a' = a.comp (pi I : (R ⧸ I ^ 2) →+* (R ⧸ I)) := by
  -- For `x ∈ I`, `b x ∈ J`.
  have hbI : ∀ x ∈ I, b x ∈ J := by
    intro x hx
    rw [← Ideal.Quotient.eq_zero_iff_mem (I := J)]
    have := RingHom.congr_fun hcomm x
    simp only [RingHom.comp_apply] at this
    rw [← this, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  -- Hence `I² ≤ ker b`, using `J² = ⊥`.
  have hker : I ^ 2 ≤ RingHom.ker b := by
    rw [sq, Ideal.mul_le]
    intro r hr s hs
    rw [RingHom.mem_ker, map_mul]
    exact Ideal.mul_eq_zero_of_pow_two_eq_bot hJ (hbI r hr) (hbI s hs)
  -- Define `a'` by lifting `b`.
  refine ⟨Ideal.Quotient.lift (I ^ 2) b (fun x hx => RingHom.mem_ker.mp (hker hx)),
    ⟨?_, ?_⟩, ?_⟩
  · ext x; simp [Ideal.Quotient.lift_mk]
  · ext x
    simp only [RingHom.comp_apply, Ideal.Quotient.lift_mk]
    have hpi : (pi I : (R ⧸ I ^ 2) →+* (R ⧸ I)) (Ideal.Quotient.mk (I ^ 2) x)
        = Ideal.Quotient.mk I x := pi_apply_mk I x
    rw [hpi]
    have := RingHom.congr_fun hcomm x
    simp only [RingHom.comp_apply] at this
    rw [this]
  · -- Uniqueness.
    intro g ⟨hg1, _⟩
    ext x
    have hgy := RingHom.congr_fun hg1 x
    simp only [RingHom.comp_apply] at hgy
    simp only [RingHom.comp_apply, Ideal.Quotient.lift_mk, hgy]

/-- Consequently the
universal first order thickening of `R/I` over `R` is the surjection
`π : R/I² → R/I`, whose kernel — the conormal module `C_{(R/I)/R}` — is
`I/I²`. Concretely, the kernel of `π` is `Ideal.cotangentIdeal I`
(Statement 1b), and the conormal module `Ideal.Cotangent I` (the `R`-module
`I/I²`) is `R`-linearly isomorphic to this kernel via
`Ideal.cotangentEquivIdeal`. We record both facts:
the kernel description and the existence of such an `R`-linear equivalence. -/
@[stacks 04ED, ega "0 20.5.12" "kernel of E → C is R/R²"]
theorem conormal_module :
    RingHom.ker (pi I : (R ⧸ I ^ 2) →+* (R ⧸ I)) = I.cotangentIdeal ∧
    Nonempty (I.Cotangent ≃ₗ[R] (RingHom.ker (pi I : (R ⧸ I ^ 2) →+* (R ⧸ I)))) := by
  refine ⟨ker_pi I, ?_⟩
  rw [ker_pi]
  exact ⟨I.cotangentEquivIdeal⟩

end UniversalThickening

end
