module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Sections of a projective presheaf of modules, and objectwise quasi-isomorphisms

Let `R` be a presheaf of rings on a category `C`. This file records two facts about
`PresheafOfModules R`.

The first is that a projective presheaf of modules is objectwise projective: if `P` is a
projective object of `PresheafOfModules R` then `P.obj X` is a projective `R.obj X`-module for
every `X : Cᵒᵖ`. The free presheaf of modules on the underlying presheaf of sets of `P` maps
onto `P` (`PresheafOfModules.fromFreeUnderlying`, an epimorphism because it is objectwise
surjective), so when `P` is projective that epimorphism splits, and evaluating the splitting at
`X` exhibits `P.obj X` as a retract of a free `R.obj X`-module.

The second is that evaluation detects quasi-isomorphisms: a morphism of short complexes, or of
homological complexes, of presheaves of modules is a quasi-isomorphism if and only if it is one
after evaluation at every object. The evaluation functors are exact and jointly reflect
isomorphisms, which is all the statement needs; it is the exact analogue, for presheaves of
modules, of `HomologicalComplex.quasiIso_iff_evaluation` for complexes in a functor category.

## Main results

* `PresheafOfModules.isIso_iff_isIso_app`: a morphism of presheaves of modules is an
  isomorphism if and only if each of its components is.
* `PresheafOfModules.categoricalProjective_obj`: the sections of a projective presheaf of
  modules over any object form a projective object of `ModuleCat (R.obj X)`.
* `PresheafOfModules.module_projective_obj`: the same, stated as `Module.Projective`.
* `PresheafOfModules.quasiIso_shortComplex_iff_evaluation`,
  `PresheafOfModules.quasiIsoAt_iff_evaluation` and
  `PresheafOfModules.quasiIso_iff_evaluation`: a morphism of short complexes resp. of
  homological complexes of presheaves of modules is a quasi-isomorphism exactly when its
  evaluation at every object is.

## Implementation notes

Projectivity of the sections is stated for presheaves of modules in `PresheafOfModules.{u} R`
with `R : Cᵒᵖ ⥤ RingCat.{u}`, which is the generality of Mathlib's free presheaf of modules
functor `PresheafOfModules.free`; the category `C` is arbitrary and no smallness of `C` is
required, because the surjection used is the free presheaf of modules on the underlying presheaf
of sets rather than a coproduct of free presheaves on representables. Nothing here assumes the
presheaf of rings to be commutative.

The quasi-isomorphism statements are in the full generality of `PresheafOfModules.{v} R`.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory CategoryTheory.Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

section Isomorphisms

/-- **A morphism of presheaves of modules is an isomorphism exactly when each of its components
is.** -/
lemma isIso_iff_isIso_app {M N : PresheafOfModules.{v} R} (f : M ⟶ N) :
    IsIso f ↔ ∀ X, IsIso (f.app X) := by
  refine ⟨fun _ X ↦ inferInstanceAs (IsIso ((evaluation R X).map f)), fun h ↦ ?_⟩
  refine ⟨⟨{ app := fun X ↦ inv (f.app X)
             naturality := fun {X Y} i ↦ ?_ }, ?_, ?_⟩⟩
  · have := h X
    have := h Y
    rw [Functor.map_inv, IsIso.comp_inv_eq, Category.assoc, f.naturality,
      IsIso.inv_hom_id_assoc]
  all_goals
    ext X
    have := h X
    simp

end Isomorphisms

section Projective

/-- The canonical morphism to a presheaf of modules `P` from the free presheaf of modules on the
underlying presheaf of sets of `P`; it is the counit of the adjunction
`PresheafOfModules.freeAdjunction`, written out. -/
noncomputable def fromFreeUnderlying (P : PresheafOfModules.{u} R) :
    freeObj (R := R) (P.presheaf ⋙ forget Ab) ⟶ P :=
  freeObjDesc (𝟙 (P.presheaf ⋙ forget Ab))

/-- **Every presheaf of modules is a quotient of a free one**: the free presheaf of modules on
the underlying presheaf of sets of `P` maps onto `P`. -/
instance epi_fromFreeUnderlying (P : PresheafOfModules.{u} R) : Epi P.fromFreeUnderlying :=
  epi_of_surjective (fun _ x ↦ ⟨ModuleCat.freeMk x, ModuleCat.freeDesc_apply _ x⟩)

/-- The sections of the free presheaf of modules on a presheaf of sets form a free, hence
projective, module over the sections of the presheaf of rings. -/
instance projective_freeObj_obj (F : Cᵒᵖ ⥤ Type u) (X : Cᵒᵖ) :
    Projective ((freeObj (R := R) F).obj X) :=
  ModuleCat.projective_of_free (Finsupp.basisSingleOne (R := R.obj X) (ι := F.obj X))

/-- **The sections of a projective presheaf of modules are projective**: if `P` is projective in
`PresheafOfModules R`, then `P.obj X` is a projective object of `ModuleCat (R.obj X)`. -/
instance categoricalProjective_obj (P : PresheafOfModules.{u} R) [Projective P] (X : Cᵒᵖ) :
    Projective (P.obj X) :=
  Retract.projective (Y := (freeObj (R := R) (P.presheaf ⋙ forget Ab)).obj X)
    { i := (Projective.factorThru (𝟙 P) P.fromFreeUnderlying).app X
      r := P.fromFreeUnderlying.app X
      retract := congrArg (fun φ ↦ Hom.app φ X)
        (Projective.factorThru_comp (𝟙 P) P.fromFreeUnderlying) }

end Projective

section QuasiIso

/-- **A morphism of short complexes of presheaves of modules is a quasi-isomorphism exactly when
its evaluation at every object is.** -/
lemma quasiIso_shortComplex_iff_evaluation
    {S₁ S₂ : ShortComplex (PresheafOfModules.{v} R)} (f : S₁ ⟶ S₂) :
    ShortComplex.QuasiIso f ↔
      ∀ (X : Cᵒᵖ), ShortComplex.QuasiIso ((evaluation.{v} R X).mapShortComplex.map f) :=
  ⟨fun _ _ ↦ inferInstance, fun hf ↦ by
    rw [ShortComplex.quasiIso_iff, isIso_iff_isIso_app]
    exact fun X ↦ ((MorphismProperty.isomorphisms (ModuleCat (R.obj X))).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
        (ShortComplex.homologyFunctorIso (evaluation.{v} R X))).app (Arrow.mk f))).1
          ((ShortComplex.quasiIso_iff _).1 (hf X))⟩

variable {ι : Type*} {c : ComplexShape ι}
  {K₁ K₂ : HomologicalComplex (PresheafOfModules.{v} R) c}

/-- **A morphism of homological complexes of presheaves of modules is a quasi-isomorphism in
degree `i` exactly when its evaluation at every object is.** -/
lemma quasiIsoAt_iff_evaluation (f : K₁ ⟶ K₂) (i : ι) :
    QuasiIsoAt f i ↔ ∀ (X : Cᵒᵖ),
      QuasiIsoAt (((evaluation.{v} R X).mapHomologicalComplex c).map f) i := by
  simp only [quasiIsoAt_iff, quasiIso_shortComplex_iff_evaluation]
  rfl

/-- **A morphism of homological complexes of presheaves of modules is a quasi-isomorphism
exactly when its evaluation at every object is.** In particular a morphism of cochain complexes
of presheaves of modules which is a quasi-isomorphism over every object of the site is a
quasi-isomorphism. -/
lemma quasiIso_iff_evaluation (f : K₁ ⟶ K₂) :
    QuasiIso f ↔ ∀ (X : Cᵒᵖ),
      QuasiIso (((evaluation.{v} R X).mapHomologicalComplex c).map f) := by
  simp only [quasiIso_iff, quasiIsoAt_iff_evaluation]
  tauto

end QuasiIso

end PresheafOfModules
