module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.Topology.Category.TopCat.Opens
public import StacksCore.Tactic.StacksAttribute

/-!
# A concrete model for the pullback of presheaves of modules: extension of scalars

Mathlib defines `PresheafOfModules.pullback φ`, for `φ : S ⟶ F.op ⋙ R` a morphism of presheaves
of rings, as `(PresheafOfModules.pushforward φ).leftAdjoint`: an abstract left adjoint, with no
description of its sections.  Since `pushforward φ = pushforward₀ F R ⋙ restrictScalars φ`, that
left adjoint factors as

`pullback φ ≅ (left adjoint of restrictScalars φ) ⋙ (left adjoint of pushforward₀ F R)`,

the first factor being *extension of scalars* and the second the objectwise filtered colimit
`U ↦ colim_{V, U ⊆ F V} A(V)`.  This file builds the first factor concretely, with its
adjunction, and supplies the filteredness of the index category of the second.

## Main definitions

* `Stacks.PullbackModel.baseChange`: the base change of a semilinear map along a commuting
  square of ring homomorphisms, `B ⊗[A] M →ₛₗ[σ] B' ⊗[A'] M'`, and
  `Stacks.PullbackModel.baseChangeMap` the same map read between the `ModuleCat` objects
  `ModuleCat.extendScalars`.
* `Stacks.PullbackModel.tmul`: the pure tensor `b ⊗ m` as an element of
  `(ModuleCat.extendScalars f).obj M`.  Every statement below is phrased through this
  abbreviation; see the implementation notes.
* `Stacks.PullbackModel.extendScalarsObj` and `Stacks.PullbackModel.extendScalars`: for a
  morphism `α : R ⟶ R'` of presheaves of commutative rings, the objectwise extension of scalars
  `M ↦ (V ↦ R'(V) ⊗_{R(V)} M(V))`, as an object and as a functor
  `PresheafOfModules (R ⋙ forget₂ _ _) ⥤ PresheafOfModules (R' ⋙ forget₂ _ _)`.
* `Stacks.PullbackModel.toRingCat`: `α` read as a morphism of presheaves of not necessarily
  commutative rings, which is the shape `PresheafOfModules.restrictScalars` is stated for, and
  `Stacks.PullbackModel.toRingCatId` the same morphism with the identity functor inserted, which
  is the shape `PresheafOfModules.pushforward` and `PresheafOfModules.pullback` expect.
* `Stacks.PullbackModel.transposeApp`: the adjoint transpose of a morphism
  `M ⟶ restrictScalars (toRingCat α) N`, objectwise.

## Main results

* `Stacks.PullbackModel.extendScalarsAdjunction`: extension of scalars is left adjoint to
  restriction of scalars, `extendScalars α ⊣ PresheafOfModules.restrictScalars (toRingCat α)`.
  Hence `Stacks.PullbackModel.extendScalarsIsoLeftAdjoint`: the concrete objectwise construction
  *is* the left adjoint of `PresheafOfModules.restrictScalars (toRingCat α)`, canonically.
* `Stacks.PullbackModel.pushforward_id_eq_restrictScalars` and
  `Stacks.PullbackModel.extendScalarsIsoPullback`: restriction of scalars is the pushforward
  along `𝟭 C`, and so the objectwise extension of scalars is canonically isomorphic to Mathlib's
  abstract `PresheafOfModules.pullback (toRingCatId α)`.  No smallness hypothesis on `C` is
  needed, since the left adjoint is produced by the construction rather than by the adjoint
  functor theorem.
* `Stacks.PullbackModel.extendScalarsObj_map_tmul`, `extendScalars_map_app_tmul`,
  `homEquiv_apply_tmul`, `transposeApp_tmul`: the sections, the restriction maps, the
  functoriality and both directions of the adjunction isomorphism, computed on pure tensors.
* `Stacks.PullbackModel.representablyFlat_opensMap`: for `f : X ⟶ Y` in `TopCat`, the functor
  `Opens.map f : Opens Y ⥤ Opens X` is representably flat, because the opens `V` of `Y` with
  `U ⊆ f⁻¹V` contain `⊤` and are closed under intersection.  Consequently
  `Stacks.PullbackModel.isFiltered_costructuredArrow_opensMap`: the index category
  `CostructuredArrow (Opens.map f).op (op U)` of the objectwise colimit
  `U ↦ colim_{V, U ⊆ f⁻¹V} A(V)` is filtered.

## What remains for Tag 01CD

With `extendScalarsIsoPullback` and `PresheafOfModules.pullbackComp`, the pullback of presheaves
of modules along a general `F` factors as extension of scalars followed by the left adjoint
`L₀` of `PresheafOfModules.pushforward₀ F R`, and only `L₀` is still abstract.  A concrete model
for `L₀` is the objectwise filtered colimit `U ↦ colim_{V, U ⊆ F V} (R(U) ⊗_{R(F V)} A(V))`
over `CostructuredArrow F.op (op U)`; `isFiltered_costructuredArrow_opensMap` supplies the
filteredness of that index category for `F = Opens.map f`, and `baseChangeMap` the base change
occurring in each term, but the diagram functor, the colimit presheaf and the adjunction for
`L₀` are not built here.  Once they are, invertibility of
`Stacks.RingedSpace.comparison` (and so Tag 01CD) follows from the facts that the objectwise
tensor product commutes with filtered colimits and with extension of scalars, and that
sheafification commutes with the objectwise tensor product (Tag 0GMW,
`PresheafOfModules.sheafificationTensorIso`).

## Implementation notes

The whole difficulty here is that `(ModuleCat.extendScalars f).obj M` has underlying type
`B ⊗[A] M` only for the `Module A B` structure that `ModuleCat.restrictScalars f` puts on `B`,
and that structure is definitionally equal to, but not syntactically the same as,
`Module.compHom B f`.  A pure tensor written with either one typechecks against either object,
but `rw` and `simp` then fail to fire, and `change` is needed on every goal.  The definition
`tmul` fixes one spelling once: it is a single head symbol, so the computation lemmas about it
are ordinary rewrite rules, and the proofs below are rewriting rather than transparency
management.  For the same reason `extendScalars_hom_ext` restates
`ModuleCat.ExtendScalars.hom_ext` through `tmul`.

`ModuleCat.extendScalars` is available only for *commutative* rings, while
`PresheafOfModules` is indexed by a presheaf of `RingCat`.  So extension of scalars is stated
here for a morphism `α : R ⟶ R'` of presheaves of `CommRingCat`, and the presheaves of modules
are those over `R ⋙ forget₂ CommRingCat RingCat`; `toRingCat α` is the induced morphism of
presheaves of rings.

Everything is stated for `PresheafOfModules.{u}` over presheaves of `CommRingCat.{u}`, which
is what `ModuleCat.extendScalars` preserves (its target universe is `max v u`).

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct ChangeOfRings

universe u u₁ v₁

namespace Stacks.PullbackModel

section Algebra

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  {αV : A →+* B} {αW : A' →+* B'} {ρ : A →+* A'} {σ : B →+* B'}
  [Module A B] [SMulCommClass A B B] [Module A' B'] [SMulCommClass A' B' B']
  (hB : ∀ (r : A) (b : B), r • b = αV r * b)
  (hB' : ∀ (r : A') (b : B'), r • b = αW r * b)
  (hα : ∀ r, σ (αV r) = αW (ρ r))
  {M M' : Type u} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A' M']
  (φ : M →ₛₗ[ρ] M')

/-- Base change of a semilinear map along a commuting square of ring homomorphisms, as an
additive map: `b ⊗ m ↦ σ b ⊗ φ m`. -/
noncomputable def baseChangeAddHom : (B ⊗[A] M) →+ (B' ⊗[A'] M') :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun b => AddMonoidHom.mk' (fun m => σ b ⊗ₜ[A'] φ m)
        (by intro x y; simp [TensorProduct.tmul_add]))
      (by intro x y; ext m; simp [TensorProduct.add_tmul]))
    (by
      intro r b m
      change σ (r • b) ⊗ₜ[A'] φ m = σ b ⊗ₜ[A'] φ (r • m)
      rw [hB, map_mul, hα, ← hB', TensorProduct.smul_tmul, φ.map_smulₛₗ])

omit [SMulCommClass A B B] [SMulCommClass A' B' B'] in
/-- `baseChangeAddHom` sends the pure tensor `b ⊗ m` to `σ b ⊗ φ m`. -/
lemma baseChangeAddHom_tmul (b : B) (m : M) :
    baseChangeAddHom hB hB' hα φ (b ⊗ₜ[A] m) = σ b ⊗ₜ[A'] φ m := rfl

/-- Base change of a semilinear map along a commuting square of ring homomorphisms, as a
`σ`-semilinear map. -/
noncomputable def baseChange : (B ⊗[A] M) →ₛₗ[σ] (B' ⊗[A'] M') where
  toFun := baseChangeAddHom hB hB' hα φ
  map_add' := map_add _
  map_smul' s x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, baseChangeAddHom_tmul, baseChangeAddHom_tmul,
          map_mul, TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

end Algebra

section ModuleCat

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']

/-- The pure tensor `b ⊗ m` of `b : B` and `m : M`, as an element of the base change
`(ModuleCat.extendScalars f).obj M` of an `A`-module `M` along `f : A →+* B`. -/
noncomputable def tmul (f : A →+* B) {M : ModuleCat.{u} A} (b : B) (m : M) :
    (ModuleCat.extendScalars f).obj M :=
  b ⊗ₜ[A, f] m

/-- Scalar multiplication on a pure tensor: `b • (b' ⊗ m) = (b * b') ⊗ m`. -/
lemma smul_tmul (f : A →+* B) {M : ModuleCat.{u} A} (b b' : B) (m : M) :
    b • tmul f b' m = tmul f (b * b') m := rfl

/-- Two maps out of a base change agree as soon as they agree on the pure tensors `1 ⊗ m`. -/
lemma extendScalars_hom_ext (f : A →+* B) {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    {x y : (ModuleCat.extendScalars f).obj M ⟶ N}
    (h : ∀ m : M, x (tmul f 1 m) = y (tmul f 1 m)) : x = y :=
  ModuleCat.ExtendScalars.hom_ext h

/-- Extension of scalars of a morphism `ψ` sends the pure tensor `b ⊗ m` to `b ⊗ ψ m`. -/
lemma extendScalars_map_tmul (f : A →+* B) {M N : ModuleCat.{u} A} (ψ : M ⟶ N) (b : B) (m : M) :
    (ModuleCat.extendScalars f).map ψ (tmul f b m) = tmul f b (ψ m) := rfl

/-- Base change of a semilinear map along a commuting square of ring homomorphisms, read as a
morphism between the base changes as `ModuleCat` objects. -/
noncomputable def baseChangeMap (αV : A →+* B) (αW : A' →+* B') {ρ : A →+* A'} {σ : B →+* B'}
    (hα : ∀ r, σ (αV r) = αW (ρ r)) {M : ModuleCat.{u} A} {M' : ModuleCat.{u} A'}
    (φ : ↑M →ₛₗ[ρ] ↑M') :
    (ModuleCat.extendScalars αV).obj M ⟶
      (ModuleCat.restrictScalars σ).obj ((ModuleCat.extendScalars αW).obj M') := by
  letI : Module A B := Module.compHom B αV
  letI : Module A' B' := Module.compHom B' αW
  letI : SMulCommClass A B B := ⟨fun a b b' => by
    change αV a * (b * b') = b * (αV a * b'); ring⟩
  letI : SMulCommClass A' B' B' := ⟨fun a b b' => by
    change αW a * (b * b') = b * (αW a * b'); ring⟩
  exact ModuleCat.semilinearMapAddEquiv σ _ _
    (baseChange (αV := αV) (αW := αW) (fun _ _ => rfl) (fun _ _ => rfl) hα φ)

/-- `baseChangeMap` sends the pure tensor `b ⊗ m` to `σ b ⊗ φ m`. -/
lemma baseChangeMap_tmul (αV : A →+* B) (αW : A' →+* B') {ρ : A →+* A'} {σ : B →+* B'}
    (hα : ∀ r, σ (αV r) = αW (ρ r)) {M : ModuleCat.{u} A} {M' : ModuleCat.{u} A'}
    (φ : ↑M →ₛₗ[ρ] ↑M') (b : B) (m : M) :
    baseChangeMap αV αW hα φ (tmul αV b m) = tmul αW (σ b) (φ m) := rfl

/-- The adjunct along `ModuleCat.extendRestrictScalarsAdj f` of a morphism `x` out of the base
change sends `m` to `x (1 ⊗ m)`. -/
lemma homEquiv_apply_tmul (f : A →+* B) {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (x : (ModuleCat.extendScalars f).obj M ⟶ N) (m : M) :
    (ModuleCat.extendRestrictScalarsAdj f).homEquiv M N x m = x (tmul f 1 m) := rfl

/-- The inverse adjunct along `ModuleCat.extendRestrictScalarsAdj f` of a morphism `ψ` sends the
pure tensor `1 ⊗ m` to `ψ m`. -/
lemma homEquiv_symm_apply_tmul (f : A →+* B) {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (ψ : M ⟶ (ModuleCat.restrictScalars f).obj N) (m : M) :
    ((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N).symm ψ (tmul f 1 m) = ψ m := by
  rw [← homEquiv_apply_tmul, Equiv.apply_symm_apply]

end ModuleCat

section Presheaf

open PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R R' : Cᵒᵖ ⥤ CommRingCat.{u}} (α : R ⟶ R')

/-- A morphism of presheaves of commutative rings, read as a morphism of presheaves of
not necessarily commutative rings. -/
abbrev toRingCat : (R ⋙ forget₂ CommRingCat RingCat) ⟶ (R' ⋙ forget₂ CommRingCat RingCat) :=
  Functor.whiskerRight α (forget₂ CommRingCat RingCat)

/-- Naturality of `α` on elements: `R'(g) (α_V r) = α_W (R(g) r)`. -/
lemma app_naturality_apply {V W : Cᵒᵖ} (g : V ⟶ W) (r : R.obj V) :
    (R'.map g).hom ((α.app V).hom r) = (α.app W).hom ((R.map g).hom r) :=
  (RingHom.congr_fun (congrArg CommRingCat.Hom.hom (α.naturality g)) r).symm

/-- Objectwise extension of scalars of a presheaf of modules along a morphism `α : R ⟶ R'` of
presheaves of commutative rings: the presheaf of `R'`-modules `V ↦ R'(V) ⊗_{R(V)} M(V)`. -/
noncomputable def extendScalarsObj (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    PresheafOfModules.{u} (R' ⋙ forget₂ _ _) where
  obj V := (ModuleCat.extendScalars (α.app V).hom).obj (M.obj V)
  map {V W} g :=
    baseChangeMap (α.app V).hom (α.app W).hom (app_naturality_apply α g) (M.restrictₛₗ g)
  map_id V := by
    let iV : Module ↑(R.obj V) ↑(R'.obj V) :=
      ((ModuleCat.restrictScalars (α.app V).hom).obj (ModuleCat.of _ ↑(R'.obj V))).isModule
    ext m
    change ((R'.map (𝟙 V)).hom 1) ⊗ₜ[↑(R.obj V)] ((M.restrictₛₗ (𝟙 V)) m) = _
    rw [map_one, restrictₛₗ_apply, ConcreteCategory.congr_hom (M.map_id V) m]
    rfl
  map_comp {V W Z} g h := by
    let iZ : Module ↑(R.obj Z) ↑(R'.obj Z) :=
      ((ModuleCat.restrictScalars (α.app Z).hom).obj (ModuleCat.of _ ↑(R'.obj Z))).isModule
    ext m
    change ((R'.map (g ≫ h)).hom 1) ⊗ₜ[↑(R.obj Z)] (M.map (g ≫ h) m) = _
    rw [map_one, M.map_comp_apply]
    change (1 : ↑(R'.obj Z)) ⊗ₜ[↑(R.obj Z)] _ =
      ((R'.map h).hom ((R'.map g).hom 1)) ⊗ₜ[↑(R.obj Z)] _
    rw [map_one, map_one]
    rfl

/-- The restriction maps of the objectwise extension of scalars, on pure tensors. -/
lemma extendScalarsObj_map_tmul (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) {V W : Cᵒᵖ}
    (g : V ⟶ W) (b : R'.obj V) (m : M.obj V) :
    (extendScalarsObj α M).map g (tmul (α.app V).hom b m) =
      tmul (α.app W).hom ((R'.map g).hom b) (M.map g m) := rfl

/-- The restriction maps of the objectwise extension of scalars send `1 ⊗ m` to `1 ⊗ M(g) m`. -/
lemma extendScalarsObj_map_one_tmul (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) {V W : Cᵒᵖ}
    (g : V ⟶ W) (m : M.obj V) :
    (extendScalarsObj α M).map g (tmul (α.app V).hom 1 m) =
      tmul (α.app W).hom 1 (M.map g m) := by
  rw [extendScalarsObj_map_tmul, map_one]

/-- Objectwise extension of scalars, as a functor between categories of presheaves of
modules. -/
noncomputable def extendScalars :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{u} (R' ⋙ forget₂ CommRingCat RingCat) where
  obj M := extendScalarsObj α M
  map {M N} ψ :=
    { app V := (ModuleCat.extendScalars (α.app V).hom).map (Hom.app ψ V)
      naturality := fun {V W} g => by
        refine extendScalars_hom_ext _ fun m => ?_
        change tmul (α.app W).hom ((R'.map g).hom 1) (Hom.app ψ W (M.map g m))
            = tmul (α.app W).hom ((R'.map g).hom 1) (N.map g (Hom.app ψ V m))
        rw [naturality_apply] }
  map_id M := by
    refine PresheafOfModules.hom_ext fun V => ?_
    exact (ModuleCat.extendScalars (α.app V).hom).map_id (M.obj V)
  map_comp {M N P} ψ χ := by
    refine PresheafOfModules.hom_ext fun V => ?_
    exact (ModuleCat.extendScalars (α.app V).hom).map_comp (Hom.app ψ V) (Hom.app χ V)

/-- Extension of scalars of a morphism of presheaves of modules, on pure tensors. -/
lemma extendScalars_map_app_tmul {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : M ⟶ N)
    (V : Cᵒᵖ) (b : R'.obj V) (m : M.obj V) :
    Hom.app ((extendScalars α).map ψ) V (tmul (α.app V).hom b m) =
      tmul (α.app V).hom b (Hom.app ψ V m) := rfl

section Transpose

variable {M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
  {N : PresheafOfModules.{u} (R' ⋙ forget₂ CommRingCat RingCat)}

/-- The adjoint transpose of a morphism `M ⟶ restrictScalars (toRingCat α) N`, objectwise. -/
noncomputable def transposeApp
    (h : M ⟶ (PresheafOfModules.restrictScalars.{u} (toRingCat α)).obj N) (V : Cᵒᵖ) :
    (extendScalarsObj α M).obj V ⟶ N.obj V :=
  ((ModuleCat.extendRestrictScalarsAdj (α.app V).hom).homEquiv (M.obj V) (N.obj V)).symm
    (Hom.app h V)

/-- `transposeApp α h V` sends the pure tensor `1 ⊗ m` to `h_V m`. -/
lemma transposeApp_tmul (h : M ⟶ (PresheafOfModules.restrictScalars.{u} (toRingCat α)).obj N)
    (V : Cᵒᵖ) (m : M.obj V) :
    transposeApp α h V (tmul (α.app V).hom 1 m) = Hom.app h V m :=
  homEquiv_symm_apply_tmul (M := M.obj V) (N := N.obj V) (α.app V).hom (Hom.app h V) m

end Transpose

/-- **Extension of scalars is left adjoint to restriction of scalars** for presheaves of
modules.  The bijection is objectwise `ModuleCat.extendRestrictScalarsAdj`, and
`homEquiv_apply_tmul`, `transposeApp_tmul` compute both of its directions. -/
noncomputable def extendScalarsAdjunction :
    extendScalars α ⊣ PresheafOfModules.restrictScalars.{u} (toRingCat α) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N =>
        { toFun := fun f =>
            { app := fun V => (ModuleCat.extendRestrictScalarsAdj (α.app V).hom).homEquiv
                (M.obj V) (N.obj V) (Hom.app f V)
              naturality := fun {V W} g => by
                ext m
                change Hom.app f W (tmul (α.app W).hom 1 (M.map g m))
                    = N.map g (Hom.app f V (tmul (α.app V).hom 1 m))
                rw [← extendScalarsObj_map_one_tmul]
                exact naturality_apply f g (tmul (α.app V).hom 1 m) }
          invFun := fun h =>
            { app := fun V => transposeApp α h V
              naturality := fun {V W} g => by
                refine extendScalars_hom_ext _ fun m => ?_
                change transposeApp α h W
                      (tmul (α.app W).hom ((R'.map g).hom 1) (M.map g m))
                    = N.map g (transposeApp α h V (tmul (α.app V).hom 1 m))
                rw [map_one, transposeApp_tmul]
                exact (transposeApp_tmul α h W (M.map g m)).trans
                  (naturality_apply h g m) }
          left_inv := fun _ => PresheafOfModules.hom_ext fun _ => Equiv.symm_apply_apply _ _
          right_inv := fun _ => PresheafOfModules.hom_ext fun _ => Equiv.apply_symm_apply _ _ }
      homEquiv_naturality_left_symm := fun f h =>
        PresheafOfModules.hom_ext fun V =>
          (ModuleCat.extendRestrictScalarsAdj (α.app V).hom).homEquiv_naturality_left_symm
            (Hom.app f V) (Hom.app h V)
      homEquiv_naturality_right := fun f h =>
        PresheafOfModules.hom_ext fun V =>
          (ModuleCat.extendRestrictScalarsAdj (α.app V).hom).homEquiv_naturality_right
            (Hom.app f V) (Hom.app h V) }

/-- **The transpose along `extendScalarsAdjunction`, on a section.** The adjunct of a morphism
out of the extension of scalars sends a section `m` to the value of that morphism on the pure
tensor `1 ⊗ m`. -/
lemma extendScalarsAdjunction_homEquiv_app_apply
    {M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    {N : PresheafOfModules.{u} (R' ⋙ forget₂ CommRingCat RingCat)}
    (f : (extendScalars α).obj M ⟶ N) (V : Cᵒᵖ) (m : M.obj V) :
    Hom.app ((extendScalarsAdjunction α).homEquiv M N f) V m =
      Hom.app f V (tmul (α.app V).hom 1 m) := by
  simp only [extendScalarsAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact homEquiv_apply_tmul (α.app V).hom (Hom.app f V) m

/-- Objectwise extension of scalars is a left adjoint. -/
instance : (extendScalars α).IsLeftAdjoint := (extendScalarsAdjunction α).isLeftAdjoint

/-- Restriction of scalars of presheaves of modules is a right adjoint. -/
instance : (PresheafOfModules.restrictScalars.{u} (toRingCat α)).IsRightAdjoint :=
  (extendScalarsAdjunction α).isRightAdjoint

/-- The objectwise extension of scalars **is** the left adjoint of restriction of scalars,
canonically. -/
noncomputable def extendScalarsIsoLeftAdjoint :
    extendScalars α ≅ (PresheafOfModules.restrictScalars.{u} (toRingCat α)).leftAdjoint :=
  Adjunction.leftAdjointUniq (extendScalarsAdjunction α) (Adjunction.ofIsRightAdjoint _)

/-- `toRingCat α`, read as a morphism `R ⟶ (𝟭 C).op ⋙ R'` of presheaves of rings. -/
abbrev toRingCatId : (R ⋙ forget₂ CommRingCat RingCat) ⟶
    (𝟭 C).op ⋙ (R' ⋙ forget₂ CommRingCat RingCat) :=
  toRingCat α

/-- Restriction of scalars is the pushforward along the identity functor: this is the
factorisation `pushforward φ = pushforward₀ F R ⋙ restrictScalars φ` read in the case
`F = 𝟭 C`. -/
lemma pushforward_id_eq_restrictScalars :
    PresheafOfModules.pushforward.{u} (toRingCatId α) =
      PresheafOfModules.restrictScalars.{u} (toRingCat α) := rfl

/-- The pushforward along `toRingCatId α` is a right adjoint. -/
instance : (PresheafOfModules.pushforward.{u} (toRingCatId α)).IsRightAdjoint :=
  (extendScalarsAdjunction α).isRightAdjoint

/-- **The objectwise extension of scalars is Mathlib's `PresheafOfModules.pullback` along the
identity functor**, canonically.  Note that no smallness hypothesis on `C` is needed: the left
adjoint is produced by the construction rather than by the adjoint functor theorem. -/
noncomputable def extendScalarsIsoPullback :
    extendScalars α ≅ PresheafOfModules.pullback.{u} (toRingCatId α) :=
  Adjunction.leftAdjointUniq (extendScalarsAdjunction α)
    (PresheafOfModules.pullbackPushforwardAdjunction.{u} (toRingCatId α))

end Presheaf

section Filtered

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- `Opens.map f : Opens Y ⥤ Opens X` is representably flat: for an open `U` of `X`, the opens
`V` of `Y` with `U ⊆ f⁻¹V` form a cofiltered family, since they contain `⊤` and are closed
under intersection. -/
instance representablyFlat_opensMap : RepresentablyFlat (Opens.map f) where
  cofiltered U :=
    { cone_objs := fun A B =>
        ⟨StructuredArrow.mk (Y := A.right ⊓ B.right)
            (homOfLE (le_inf (leOfHom A.hom) (leOfHom B.hom))),
          StructuredArrow.homMk (homOfLE inf_le_left) (Subsingleton.elim _ _),
          StructuredArrow.homMk (homOfLE inf_le_right) (Subsingleton.elim _ _), trivial⟩
      cone_maps := fun A _ g h => ⟨A, 𝟙 A, by
        simp only [Category.id_comp]
        exact StructuredArrow.hom_ext g h (Subsingleton.elim _ _)⟩
      nonempty := ⟨StructuredArrow.mk (Y := (⊤ : Opens Y)) (homOfLE (by simp))⟩ }

/-- The index category of the objectwise colimit `U ↦ colim_{V, U ⊆ f⁻¹V} A(V)` computing the
left adjoint of `PresheafOfModules.pushforward₀ (Opens.map f)` is filtered. -/
instance isFiltered_costructuredArrow_opensMap (U : Opens X) :
    IsFiltered (CostructuredArrow (Opens.map f).op (op U)) :=
  inferInstance

end Filtered

end Stacks.PullbackModel
