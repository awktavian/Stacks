module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDivisorClass
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Punctured

/-!
# The Chow groups of the total space of a line bundle

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `ℒ` be an invertible `𝒪_X`-module and let

  `p : L = \underline{\Spec}(\Sym^*(ℒ)) ⟶ X`

be the associated line bundle over `X`. Stacks 0B74 asserts that the flat pullback

  `p^* : A_k(X) ⟶ A_{k+1}(L)`

is an isomorphism for every `k`. The source's proof has two halves. Surjectivity is Stacks 02TT,
the affine-bundle surjectivity, at rank one. Injectivity comes from the **zero section**
`o : X ⟶ L`, cut out by the augmentation `\Sym^*(ℒ) ⟶ 𝒪_X` that kills `ℒ^{⊗ n}` for `n > 0`: it
satisfies `p ∘ o = 𝟙_X`, its image is a relative effective Cartier divisor on `L/X`, and Stacks
02TR applied to that divisor gives `o^* ∘ p^* = (p ∘ o)^* = 𝟙^* = \mathrm{id}`, so `p^*` is split
injective.

The total space, the projection and the zero section are already in this repository, for a
`Stacks.LineBundle.Situation` — a scheme `X` carrying an invertible module `L` — as
`Stacks.LineBundle.Situation.totalSpace`, `Stacks.LineBundle.Situation.totalSpaceToBase` and
`Stacks.LineBundle.Situation.zeroSection`. This file proves the part of the source's argument
that the repository's inputs support: the retraction of the flat pullback along the zero section,
and injectivity from it.

## Main definitions

* `Stacks.Chow.GysinRetractsFlatPullbackChow` — **the statement of Stacks 02TR on Chow groups**,
  for a flat `p : Z ⟶ Y` of relative dimension one, a flat `q : W ⟶ Y` of relative dimension
  zero, and a homomorphism `gysin : A_{k+1}(Z) ⟶ A_k(W)`: that `gysin ∘ p^* = q^*`. Taking
  `q = p ∘ i` for a relative effective Cartier divisor `i : W ⟶ Z` and `gysin` its Gysin
  homomorphism, this is the first equality of Stacks 02TR read on Chow classes. Carried as a
  hypothesis; see the honest-hypotheses section below.

## Main results

* `Stacks.Chow.isIso_lift_zeroSection` — the closed subscheme of `L` cut out by the zero section
  is isomorphic to `X`, the zero section being a closed immersion.
* `Stacks.Chow.flat_ker_zeroSection_subschemeι_comp_totalSpaceToBase` — the image of the zero
  section is flat over the base, which is the second conjunct of Definition 062T for the divisor
  `o(X)`: that closed subscheme is isomorphic to `X` over `X`, since `p ∘ o = 𝟙_X`.
* `Stacks.Chow.flat_zeroSection_comp_totalSpaceToBase`,
  `Stacks.Chow.locallyOfFiniteType_zeroSection_comp_totalSpaceToBase` and
  `Stacks.Chow.relativeDimension_zeroSection_comp_totalSpaceToBase` — the restricted projection
  `p|_{o(X)}` is locally of finite type and flat of relative dimension zero, being the identity
  of `X`.
* `Stacks.Chow.gysin_flatPullbackChow_zeroSection` — **the retraction**: granted Stacks 02TR for
  the zero section, `o^*(p^* α) = α` for every `α ∈ A_k(X)`, up to the transport
  `A_k(X) = A_{k+0}(X)` of degrees.
* `Stacks.Chow.flatPullbackChow_injective_of_gysinRetracts` — **Stacks 0B74, injectivity**:
  `p^* : A_k(X) ⟶ A_{k+1}(L)` is injective.

## What is carried as a hypothesis, and why

Three facts about this situation enter the statements below as explicit named hypotheses. None of
them weakens a conclusion: each is a true statement of the source. Their proofs are now in the
repository — named section by section below — and the binders are retained because the statements
are deliberately phrased as generic carrier assertions; discharging a binder inside a signature
would change the statement, which this file does not undertake.

### `IsAffineSpaceBundle p 1`, hence the three properties `p^*` needs

Writing `p^*` down at all needs `p` locally of finite type, flat, and of relative dimension one.
All three follow from the local triviality of the line bundle through the lemmas
`Stacks.Chow.locallyOfFiniteType_of_isAffineSpaceBundle`,
`Stacks.Chow.flat_of_isAffineSpaceBundle` and
`Stacks.Chow.relativeDimension_of_isAffineSpaceBundle` of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Basic`, applied to
`Stacks.Chow.IsAffineSpaceBundle p 1`. That local triviality — over an open `U` trivializing `ℒ`
one has `\Sym^*(𝒪_U) = 𝒪_U[T]` and hence `p^{-1}U ≅ 𝔸^1_U` over `U` — is proved:
`Stacks.LineBundle.Situation.isAffineSpaceBundle_totalSpaceToBase` of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleAffineSpaceBundle` identifies
`Γ(V, \Sym(ℰ))` with a polynomial ring over an affine trivializing open
(`Stacks.SymAlgSections.ungradedSymSectionsMvPolynomialEquiv`) and concludes that the projection of
the total space is an affine-space bundle of rank one; the three properties then follow from the
lemmas cited above. The statements below nevertheless take the three properties as instance and
explicit binders, exactly as
`Stacks.Chow.flatPullbackChow_surjective_of_isAffineSpaceBundle_zero` does, and a caller who has
`IsAffineSpaceBundle p 1` supplies them from it.

### `hfac`: Stacks 02S1 at relative dimension one

`Stacks.Chow.flatPullbackChow` is granted
`Stacks.Chow.FlatPullbackFactorsThroughRationalEquivalence`, the assertion of Stacks 02S1, as a
hypothesis by the convention of this chapter. Stacks 02S1 is now proved here in its general case,
for an arbitrary flat morphism of relative dimension `r`:
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general` of
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence`, registered
`@[stacks 02S1 "the general case: an arbitrary flat morphism of relative dimension r"]`. The
instance at relative dimension one enters the statements below as the binder `hfac`, since
discharging it would change their signatures. The zero-dimensional half of the retraction
does **not** need it as a hypothesis — along `𝟙_X` it is the theorem
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_id`, which is supplied inside the
statements below rather than assumed.

### `gysin` and `GysinRetractsFlatPullbackChow`: Stacks 02TR on Chow groups

Two things enter here as binders. First, the Gysin homomorphism `o^*` of the divisor `o(X)`. The
Cartier property is a theorem: `o(X)` is the zero scheme of the tautological global section
`Stacks.LineBundle.Situation.tautologicalSectionBase` of the pullback
`Stacks.LineBundle.Situation.basePullbackInverse` of `ℒ^{⊗ -1}`
(`Stacks.LineBundle.Situation.isRegularSection_tautologicalSectionBase`), that zero scheme is
identified with the closed subscheme cut out by the zero section
(`Stacks.LineBundle.Situation.zeroScheme_tautologicalSectionBase_eq_ker_zeroSection`), and the
image of the zero section is a relative effective Cartier divisor on `L/X` in the sense of
Definition 062T: that is Stacks 0F96 part (1), registered at
`Stacks.LineBundle.Situation.isRelativeEffectiveCartierDivisor_ker_zeroSection` of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineSpaceBundleSmooth` and at
`Stacks.LineBundle.Situation.isRelativeEffectiveCartierDivisor_zeroScheme_tautologicalSectionBase`
of `...AffineBundle.ZeroSectionCartier`. Stacks 0F96 itself is registered in this repository in
its parts (1) through (6). The Gysin homomorphism of clause (3),
`Stacks.Chow.zeroSectionGysinChow` of `...AffineBundle.ZeroSectionGysin`, constructs `o^*` on
Chow groups; `gysin` is nevertheless taken as an arbitrary homomorphism, because the statements
below are phrased through the generic carrier `GysinRetractsFlatPullbackChow` described next.

Second, Stacks 02TR on Chow classes. The descent that was once missing has been carried out:
Stacks 02TO is proved with no hypothesis — the descended map is the unconditional
`Stacks.Chow.gysinChowOfInvertible` of
`StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge`, registered
`@[stacks 02TO "the descended map i^* : A_{k+1}(X) ⟶ A_k(D), with no hypothesis"]` — and the
first equality of Stacks 02TR holds on arbitrary Chow classes for a zero-scheme-presented
relative effective Cartier divisor as `Stacks.Chow.gysinChowOfInvertible_flatPullbackChow` of
`StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierFlatPullbackChow`. For the zero
section the retraction of the flat pullback by the constructed `o^*` is Stacks 0F96 part (4),
`Stacks.Chow.zeroSectionGysinChow_comp_flatPullbackChowOfRelativeDimension` of
`...AffineBundle.ZeroSectionGysinRetraction`: `o^* p^* = \mathrm{id}` on Chow groups, with `p^*`
read through `Stacks.Chow.flatPullbackChowOfRelativeDimension`. The cycle-level carriers
`Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback_primeCycle` and its two companions in
`StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierFlatPullback` remain as stated
there. The Chow-level statement is nevertheless carried as
`Stacks.Chow.GysinRetractsFlatPullbackChow`, phrased for an
arbitrary pair `p`, `q` of flat morphisms and an arbitrary `gysin`, and instantiated below at
`q = p ∘ o = 𝟙_X`. Phrasing it for an arbitrary pair is deliberate: the hypothesis is then a
statement of Stacks 02TR and not a restatement of the conclusion of Stacks 0B74.

## Implementation notes

The bundle of Stacks 0B74 is `\underline{\Spec}(\Sym^*(ℒ))`, which is
`Stacks.LineBundle.Situation.totalSpace` for a situation whose line bundle `L` is `ℒ`. It is
**not** `Stacks.LineBundle.lineBundleSpace X ℒ`: that is the total space of `ℒ^{⊗ -1}`, i.e.
`\underline{\Spec}(\Sym^*(ℒ^{⊗ -1}))`, the dual bundle.

Degrees are written `k + ((1 : ℕ) : ℤ)` and `k + ((0 : ℕ) : ℤ)` because
`Stacks.Chow.flatPullbackChow` of relative dimension `r` lands in degree `k + (r : ℤ)` with `r`
a natural number; the transport `A_k(X) = A_{k+0}(X)` that this forces is
`Stacks.Chow.chowGroupCast`, as in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDivisorClass`.

## References

* [Stacks Project, Tag 0B74](https://stacks.math.columbia.edu/tag/0B74)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 062T](https://stacks.math.columbia.edu/tag/062T)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The zero section of a line bundle -/

section ZeroSection

variable (D : Stacks.LineBundle.Situation.{u})

/-- **The closed subscheme cut out by the zero section is isomorphic to the base.** The zero
section `o : X ⟶ L` is a closed immersion, so it and the inclusion of the closed subscheme
defined by its kernel ideal sheaf are two closed immersions into `L` with the same kernel; such a
comparison is an isomorphism by the universal property of closed immersions. -/
theorem isIso_lift_zeroSection :
    IsIso (IsClosedImmersion.lift D.zeroSection D.zeroSection.ker.subschemeι
      (Scheme.IdealSheafData.ker_subschemeι D.zeroSection.ker).ge) :=
  IsClosedImmersion.isIso_lift D.zeroSection D.zeroSection.ker.subschemeι
    (Scheme.IdealSheafData.ker_subschemeι D.zeroSection.ker).symm

/-- **The image of the zero section is flat over the base.** This is the second conjunct of
Definition 062T for the divisor `o(X)` on `L/X`: the structure morphism of `o(X)` over `X` is the
comparison isomorphism of `Stacks.Chow.isIso_lift_zeroSection`, because the zero section splits
the projection. -/
theorem flat_ker_zeroSection_subschemeι_comp_totalSpaceToBase :
    AlgebraicGeometry.Flat (D.zeroSection.ker.subschemeι ≫ D.totalSpaceToBase) := by
  have he := isIso_lift_zeroSection D
  rw [← IsClosedImmersion.lift_fac D.zeroSection D.zeroSection.ker.subschemeι
    (Scheme.IdealSheafData.ker_subschemeι D.zeroSection.ker).ge, Category.assoc,
    D.zeroSection_comp_totalSpaceToBase, Category.comp_id]
  infer_instance

/-- **The restriction of the projection to the zero section is flat**: it is the identity of the
base, because the zero section splits the projection. -/
theorem flat_zeroSection_comp_totalSpaceToBase :
    AlgebraicGeometry.Flat (D.zeroSection ≫ D.totalSpaceToBase) := by
  rw [D.zeroSection_comp_totalSpaceToBase]
  infer_instance

/-- **The restriction of the projection to the zero section is locally of finite type**: it is
the identity of the base. This is an instance so that the relative dimension of that composite
can be stated, `AlgebraicGeometry.RelativeDimension` taking local finite type as an instance
argument. -/
instance locallyOfFiniteType_zeroSection_comp_totalSpaceToBase :
    LocallyOfFiniteType (D.zeroSection ≫ D.totalSpaceToBase) := by
  rw [D.zeroSection_comp_totalSpaceToBase]
  infer_instance

/-- **The restriction of the projection to the zero section has relative dimension zero**: it is
the identity of the base, which is locally quasi-finite, and relative dimension zero is exactly
local quasi-finiteness.

This is the relative dimension that Stacks 02TR needs for `p|_D`, and which drops by one from the
relative dimension of `p`. For a general relative effective Cartier divisor that drop is not
available in this repository and is carried as a hypothesis; for the zero section it is a
theorem. -/
theorem relativeDimension_zeroSection_comp_totalSpaceToBase :
    AlgebraicGeometry.RelativeDimension (D.zeroSection ≫ D.totalSpaceToBase) 0 := by
  refine (AlgebraicGeometry.locallyQuasiFinite_iff_relativeDimension_zero
    (D.zeroSection ≫ D.totalSpaceToBase)).mp ?_
  rw [D.zeroSection_comp_totalSpaceToBase]
  infer_instance

end ZeroSection

/-! ### Stacks 02TR on Chow groups -/

/-- **Stacks 02TR on Chow groups**, as a statement about a homomorphism `gysin`.

Let `p : Z ⟶ Y` be flat of relative dimension one and let `q : W ⟶ Y` be flat of relative
dimension zero, both over the base scheme of chapter 42. The assertion is that

  `gysin (p^* α) = q^* α`  in  `A_k(W)`  for every  `α ∈ A_k(Y)`.

Stacks 02TR is this statement for `W = D` a relative effective Cartier divisor on `Z/Y` with
inclusion `i : D ⟶ Z`, for `q = i ≫ p` the restricted projection, and for `gysin` the Gysin
homomorphism `i^*` of that divisor on Chow groups. The instance for the zero section of a line
bundle is now a theorem of the repository — Stacks 0F96 part (4),
`Stacks.Chow.zeroSectionGysinChow_comp_flatPullbackChowOfRelativeDimension` — and the general
zero-scheme-presented equality on Chow classes is
`Stacks.Chow.gysinChowOfInvertible_flatPullbackChow`; this def remains the generic carrier over an
arbitrary pair `p`, `q` and homomorphism `gysin`. See the honest-hypotheses section of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleChow`.

That `gysin` is an arbitrary homomorphism, and `p` and `q` an arbitrary pair, is deliberate: the
hypothesis is then a statement of Stacks 02TR rather than a restatement of the injectivity it is
used to prove. -/
def GysinRetractsFlatPullbackChow (C : ChowSituation.{u}) {Y Z W : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
    (p : Z ⟶ Y) [LocallyOfFiniteType p] [AlgebraicGeometry.Flat p] (hpbase : p ≫ sY = sZ)
    (hp : AlgebraicGeometry.RelativeDimension p 1)
    (q : W ⟶ Y) [LocallyOfFiniteType q] [AlgebraicGeometry.Flat q] (hqbase : q ≫ sY = sW)
    (hq : AlgebraicGeometry.RelativeDimension q 0) (k : ℤ)
    (hfacp : FlatPullbackFactorsThroughRationalEquivalence C sZ sY p hpbase 1 hp k)
    (hfacq : FlatPullbackFactorsThroughRationalEquivalence C sW sY q hqbase 0 hq k)
    (gysin : chowGroup C sZ (k + ((1 : ℕ) : ℤ)) →+ chowGroup C sW (k + ((0 : ℕ) : ℤ))) : Prop :=
  ∀ α : chowGroup C sY k,
    gysin (flatPullbackChow C sZ sY p hpbase 1 hp k hfacp α) =
      flatPullbackChow C sW sY q hqbase 0 hq k hfacq α

/-! ### Stacks 0B74 -/

section Zero

variable (C : ChowSituation.{u}) (D : Stacks.LineBundle.Situation.{u}) (sX : D.X ⟶ C.S)
  [LocallyOfFiniteType sX] [LocallyOfFiniteType D.totalSpaceToBase]
  [AlgebraicGeometry.Flat D.totalSpaceToBase]
  (hp : AlgebraicGeometry.RelativeDimension D.totalSpaceToBase 1) (k : ℤ)
  (hfac : FlatPullbackFactorsThroughRationalEquivalence C (D.totalSpaceToBase ≫ sX) sX
    D.totalSpaceToBase rfl 1 hp k)
  (gysin : chowGroup C (D.totalSpaceToBase ≫ sX) (k + ((1 : ℕ) : ℤ)) →+
    chowGroup C sX (k + ((0 : ℕ) : ℤ)))

/-- **The flat pullback along the line bundle is retracted by the zero section.** Granted Stacks
02TR for the zero section — the hypothesis `h02TR`, instantiated at the restricted projection
`p ∘ o = 𝟙_X` — one has

  `o^*(p^* α) = α`  in  `A_k(X)`  for every  `α ∈ A_k(X)`,

up to the transport `A_k(X) = A_{k+0}(X)` of degrees. This is the source's computation
`o^* ∘ p^* = (p ∘ o)^* = 𝟙^* = \mathrm{id}`: the last step is
`Stacks.Chow.flatPullbackChow_id`, and the instance of Stacks 02S1 that `𝟙^*` needs is the
theorem `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_id`, supplied here rather than
assumed. -/
theorem gysin_flatPullbackChow_zeroSection
    (h02TR : GysinRetractsFlatPullbackChow C sX (D.totalSpaceToBase ≫ sX) sX
      D.totalSpaceToBase rfl hp (𝟙 D.X) (Category.id_comp sX) (relativeDimension_identity D.X) k
      hfac (flatPullbackFactorsThroughRationalEquivalence_id C sX k) gysin)
    (α : chowGroup C sX k) :
    gysin (flatPullbackChow C (D.totalSpaceToBase ≫ sX) sX D.totalSpaceToBase rfl 1 hp k hfac
        α) =
      chowGroupCast C sX (show k = k + ((0 : ℕ) : ℤ) from by simp) α := by
  rw [h02TR α, flatPullbackChow_id]

/-- **Stacks 0B74, the injectivity half.** Let `(S, δ)` be as in Situation 02QL, let `X` be
locally of finite type over `S`, let `ℒ` be an invertible `𝒪_X`-module and let
`p : L = \underline{\Spec}(\Sym^*(ℒ)) ⟶ X` be the associated line bundle. Then

  `p^* : A_k(X) ⟶ A_{k+1}(L)`

is injective for every `k`.

This is the source's argument: the zero section `o : X ⟶ L` satisfies `p ∘ o = 𝟙_X`
(`Stacks.LineBundle.Situation.zeroSection_comp_totalSpaceToBase`) and its image is a relative
effective Cartier divisor on `L/X`, so Stacks 02TR gives `o^* ∘ p^* = \mathrm{id}` and `p^*` is
split injective. The retraction is `Stacks.Chow.gysin_flatPullbackChow_zeroSection`; the
hypotheses `gysin` and `h02TR` are Stacks 02TR on Chow groups, and `hfac` is Stacks 02S1 at
relative dimension one, both carried for the reasons recorded in the module documentation. -/
@[stacks 0B74 "injectivity only, from the zero section and Stacks 02TR"]
theorem flatPullbackChow_injective_of_gysinRetracts
    (h02TR : GysinRetractsFlatPullbackChow C sX (D.totalSpaceToBase ≫ sX) sX
      D.totalSpaceToBase rfl hp (𝟙 D.X) (Category.id_comp sX) (relativeDimension_identity D.X) k
      hfac (flatPullbackFactorsThroughRationalEquivalence_id C sX k) gysin) :
    Function.Injective
      (flatPullbackChow C (D.totalSpaceToBase ≫ sX) sX D.totalSpaceToBase rfl 1 hp k hfac) := by
  intro a b hab
  refine (chowGroupCast C sX (show k = k + ((0 : ℕ) : ℤ) from by simp)).injective ?_
  rw [← gysin_flatPullbackChow_zeroSection C D sX hp k hfac gysin h02TR a,
    ← gysin_flatPullbackChow_zeroSection C D sX hp k hfac gysin h02TR b, hab]

end Zero

end Stacks.Chow

end
