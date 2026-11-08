module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Basic.Finite.Sum
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Geometry.RingedSpace.Basic
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Strictly perfect complexes and the cone

For a ringed space `(X, O_X)`, this file defines the direct summands of finite free
`O_X`-modules and the strictly perfect cochain complexes of `O_X`-modules (bounded complexes
whose terms are direct summands of finite free modules), and proves that the cone
`CochainComplex.mappingCone f` of a morphism of strictly perfect complexes is strictly perfect.

## Main definitions

* `StrictlyPerfect.structureSheafOfRings`: the structure sheaf of `X` as a sheaf of rings.
* `StrictlyPerfect.OXMod`: the category of `O_X`-modules.
* `StrictlyPerfect.structureModule`: `O_X` as a module over itself.
* `StrictlyPerfect.finiteFree`: the finite free module `O_X^{⊕ n}`.
* `StrictlyPerfect.IsDirectSummandOfFiniteFree`: being a retract of some `O_X^{⊕ n}`.
* `StrictlyPerfect.IsStrictlyPerfect`: a bounded complex whose terms are direct summands of
  finite free modules.

## Main results

* `StrictlyPerfect.isDirectSummandOfFiniteFree_biprod`: direct summands of finite free modules
  are closed under binary biproducts.
* `StrictlyPerfect.isStrictlyPerfect_mappingCone`: the cone on a morphism of strictly perfect
  complexes is strictly perfect.

## Implementation notes

`AlgebraicGeometry.RingedSpace.{u, v}` has `u` the universe of the rings and `v` that of the
underlying space, and the sections of a module may live in a third universe `w`. All three
are independent here. Forgetting commutativity is not performed with `sheafCompose`, which
would need `RingCat.{u}` to have limits indexed by the site `Opens X.carrier` and so force
`v ≤ u`; instead `structureSheafOfRings` checks the sheaf condition after composing with the
forgetful functor to types, which `ringForget_reflectsLimits` shows reflects the limits that
are already known to exist.

The finite free modules have the sections of the structure sheaf, so they live in the ring
universe `u` whatever `w` is. `moduleULift` moves a module into a larger section universe
without changing anything but a `ULift` wrapper, and `IsDirectSummandOfFiniteFree` is stated
after lifting both the module and the finite free module into their common universe.
`isDirectSummandOfFiniteFree_iff_retract` recovers the plain retract condition when the
module and ring universes agree.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace StrictlyPerfect

/-- A functor to types reflecting isomorphisms reflects limits of shapes whose limits it preserves
whenever the sections of the diagram are small. -/
private theorem reflectsLimitsOfSize_of_preservesLimit_of_small.{t, v, u', u, w}
    {C : Type u'} [Category.{w} C] (U : C ⥤ Type u) [U.ReflectsIsomorphisms]
    (hl : ∀ {J : Type v} [Category.{t} J] (F : J ⥤ C) [Small.{u} (F ⋙ U).sections], HasLimit F)
    (h : ∀ {J : Type v} [Category.{t} J] (F : J ⥤ C) [Small.{u} (F ⋙ U).sections],
      PreservesLimit F U) :
    ReflectsLimitsOfSize.{t, v} U :=
  { reflectsLimitsOfShape := {
    reflectsLimit := fun {F} => {
      reflects := fun {c} hc => by
        let : HasLimit (F ⋙ U) := ⟨⟨_, hc⟩⟩
        let : Small.{u} (F ⋙ U).sections :=
          (Types.hasLimit_iff_small_sections _).mp inferInstance
        let := h F
        let := hl F
        let : ReflectsLimit F U := reflectsLimit_of_reflectsIsomorphisms F U
        exact ⟨isLimitOfReflects U hc⟩ } } }

/-- The forgetful functor from rings to types reflects limits that are already known to
exist, even when the indexing category is larger than the rings. -/
theorem ringForget_reflectsLimits.{u, v, t} :
    ReflectsLimitsOfSize.{t, v} (forget RingCat.{u}) :=
  reflectsLimitsOfSize_of_preservesLimit_of_small _ (fun _ _ => inferInstance) fun F =>
    preservesLimit_of_preserves_limit_cone (RingCat.limitConeIsLimit F)
      (Types.Small.limitConeIsLimit _)

/-- The structure sheaf of `X` as a sheaf of (not-necessarily-commutative) rings,
obtained from the `CommRingCat`-valued structure sheaf by forgetting commutativity.
This is `O_X` viewed as a sheaf of rings. The universes of the rings and of the underlying
space are independent. -/
noncomputable def structureSheafOfRings.{u, v} (X : AlgebraicGeometry.RingedSpace.{u, v}) :
    Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u} := by
  letI : PreservesLimitsOfSize.{v, v} (forget CommRingCat.{u}) :=
    Functor.instPreservesLimitsOfSizeOfIsRightAdjoint _
  letI : ReflectsLimitsOfSize.{v, v} (forget RingCat.{u}) :=
    ringForget_reflectsLimits
  refine ⟨X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}, ?_⟩
  apply Presheaf.isSheaf_of_isSheaf_comp (Opens.grothendieckTopology X.carrier)
    (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) (forget RingCat.{u})
  exact Presheaf.isSheaf_comp_of_isSheaf _ X.presheaf (forget CommRingCat.{u})
    X.sheaf.property

/-- The category of `O_X`-modules: sheaves of modules over the structure sheaf of
rings of the ringed space `X`, with sections in the independent universe `w`. -/
abbrev OXMod.{u, w, v} (X : AlgebraicGeometry.RingedSpace.{u, v}) : Type _ :=
  SheafOfModules.{w} (structureSheafOfRings X)

/-- Raise the universe of the sections of an `O_X`-module without changing the
coefficient rings or the underlying space. -/
noncomputable def moduleULift.{w', w, u, v} (X : AlgebraicGeometry.RingedSpace.{u, v}) :
    OXMod.{u, w} X ⥤ OXMod.{u, max w w'} X where
  obj M := by
    letI : ∀ U, Module ((structureSheafOfRings X).obj.obj U)
        ((M.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{w'}).obj U) :=
      fun U => inferInstanceAs (Module _ (ULift.{w'} (M.val.obj U)))
    exact
      { val := PresheafOfModules.ofPresheaf
          (M.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{w'})
          (fun _ _ f r x => congrArg ULift.up (M.val.map_smul f r x.down))
        isSheaf := Presheaf.isSheaf_comp_of_isSheaf _ _ AddCommGrpCat.uliftFunctor M.isSheaf }
  map f :=
    { val :=
        { app := fun U => (ModuleCat.uliftFunctor _).map (f.val.app U)
          naturality := fun g => by
            ext x
            exact congrArg ULift.up (congrArg (fun f => f x.down) (f.val.naturality g)) } }

universe u v w w'

/-- Raising the universe of the sections preserves addition of morphisms. -/
instance (X : AlgebraicGeometry.RingedSpace.{u, v}) :
    (moduleULift.{w', w} X).Additive where
  map_add := by intros; ext U x; rfl

/-- Raising the universe of the sections is fully faithful: it changes no sections except
for wrapping them in `ULift`. -/
noncomputable def moduleULiftFullyFaithful (X : AlgebraicGeometry.RingedSpace.{u, v}) :
    (moduleULift.{w', w} X).FullyFaithful where
  preimage f :=
    { val :=
        { app := fun U => (ModuleCat.fullyFaithfulUliftFunctor _).preimage (f.val.app U)
          naturality := fun g => by
            ext x
            exact congrArg ULift.down
              (congrArg (fun f => f (ULift.up x)) (f.val.naturality g)) } }

/-- The forgetful functor from abelian groups to types reflects limits that are already known
to exist, without assuming all such limits exist, for shapes of any size; the universes of
the objects and of the morphisms of the indexing category are independent. -/
theorem groupForget_reflectsLimitsOfSize :
    ReflectsLimitsOfSize.{v, w'} (forget AddCommGrpCat.{u}) :=
  reflectsLimitsOfSize_of_preservesLimit_of_small _ (fun _ _ => inferInstance) fun F =>
    preservesLimit_of_preserves_limit_cone (AddCommGrpCat.limitConeIsLimit F)
      (Types.Small.limitConeIsLimit _)

/-- The forgetful functor from abelian groups to types reflects limits of the size of the
site that are already known to exist, without assuming all such limits exist. -/
theorem groupForget_reflectsLimits :
    ReflectsLimitsOfSize.{v, v} (forget AddCommGrpCat.{u}) :=
  groupForget_reflectsLimitsOfSize

variable (X : AlgebraicGeometry.RingedSpace.{u, v})

/-- The category of `O_X`-modules has finite biproducts (it is abelian). -/
noncomputable instance : HasFiniteBiproducts (OXMod.{u, w} X) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The category of `O_X`-modules has binary biproducts (it is abelian). -/
noncomputable instance : HasBinaryBiproducts (OXMod.{u, w} X) :=
  hasBinaryBiproducts_of_finite_biproducts _

/-- The structure sheaf `O_X` regarded as a module over itself (the unit object of
the category of `O_X`-modules). Its sections are those of the structure sheaf, so it lives
in the ring universe. -/
noncomputable def structureModule (X : AlgebraicGeometry.RingedSpace.{u, v}) :
    OXMod.{u, u} X := by
  letI : PreservesLimitsOfSize.{v, v} (forget CommRingCat.{u}) :=
    Functor.instPreservesLimitsOfSizeOfIsRightAdjoint _
  letI : ReflectsLimitsOfSize.{v, v} (forget AddCommGrpCat.{u}) :=
    groupForget_reflectsLimits
  refine ⟨PresheafOfModules.unit (structureSheafOfRings X).obj, ?_⟩
  apply Presheaf.isSheaf_of_isSheaf_comp (Opens.grothendieckTopology X.carrier)
    (PresheafOfModules.unit (structureSheafOfRings X).obj).presheaf (forget AddCommGrpCat.{u})
  exact Presheaf.isSheaf_comp_of_isSheaf _ X.presheaf (forget CommRingCat.{u})
    X.sheaf.property

/-- `O_X^{⊕ n}`, the finite free `O_X`-module on `n` copies of `O_X`, defined as the
`n`-fold biproduct of the structure module. -/
@[sga "6 II 2.0" "partial", sga "6 X 6.1" "special case"]
noncomputable def finiteFree (X : AlgebraicGeometry.RingedSpace.{u, v}) (n : ℕ) :
    OXMod.{u, u} X :=
  biproduct (fun _ : Fin n => structureModule X)

variable {X}

/-- An `O_X`-module `E` is *a direct summand of a finite free `O_X`-module* if it is a
retract of `O_X^{⊕ n}` for some `n ≥ 0`, after both have been moved into their common
section universe by `moduleULift`. When the module and ring universes agree this is the
plain condition that there are morphisms `i : E ⟶ O_X^{⊕ n}` and `r : O_X^{⊕ n} ⟶ E` with
`i ≫ r = 𝟙 E` (`isDirectSummandOfFiniteFree_iff_retract`). -/
@[sga "6 I 4.8" "partial", sga "6 I 7.1.1"]
def IsDirectSummandOfFiniteFree {X : AlgebraicGeometry.RingedSpace.{u, v}}
    (E : OXMod.{u, w} X) : Prop :=
  ∃ n : ℕ, Nonempty (Retract ((moduleULift.{u, w} X).obj E)
    ((moduleULift.{w, u} X).obj (finiteFree X n)))

/-- When the sections of the module live in the universe of the rings, being a direct
summand of a finite free module is the plain retract condition. -/
theorem isDirectSummandOfFiniteFree_iff_retract
    {X : AlgebraicGeometry.RingedSpace.{u, v}} (E : OXMod.{u, u} X) :
    IsDirectSummandOfFiniteFree E ↔ ∃ n : ℕ, Nonempty (Retract E (finiteFree X n)) := by
  constructor
  · rintro ⟨n, ⟨r⟩⟩
    let hF : (moduleULift.{u, u} X).FullyFaithful := moduleULiftFullyFaithful X
    refine ⟨n, ⟨⟨hF.preimage r.i, hF.preimage r.r, ?_⟩⟩⟩
    apply hF.map_injective
    simp [r.retract]
  · rintro ⟨n, ⟨r⟩⟩
    exact ⟨n, ⟨r.map (moduleULift.{u, u} X)⟩⟩

/-! ### Closure properties of `IsDirectSummandOfFiniteFree`

Being a direct summand of a finite free module is invariant under isomorphism and closed
under binary biproducts. -/

/-- If `E ≅ E'` and `E'` is a direct summand of a finite free module, then so is `E`. -/
theorem isDirectSummandOfFiniteFree_of_iso {E E' : OXMod.{u, w} X} (e : E ≅ E')
    (h : IsDirectSummandOfFiniteFree E') : IsDirectSummandOfFiniteFree E := by
  obtain ⟨n, ⟨ρ⟩⟩ := h
  exact ⟨n, ⟨((moduleULift.{u, w} X).mapIso e).retract.trans ρ⟩⟩

/-- The isomorphism `O_X^{⊕a} ⊞ O_X^{⊕b} ≅ O_X^{⊕(a+b)}`: the binary biproduct of the two
biproducts is the biproduct over `Fin a ⊕ Fin b`, reindexed along `finSumFinEquiv`. -/
noncomputable def finiteFreeBiprodIso (a b : ℕ) :
    (finiteFree X a ⊞ finiteFree X b) ≅ finiteFree X (a + b) := by
  have step1 :
      (⨁ (Sum.elim (fun _ : Fin a => structureModule X) (fun _ : Fin b => structureModule X)))
        ≅ finiteFree X (a + b) :=
    biproduct.whiskerEquiv finSumFinEquiv (fun j => by cases j <;> exact Iso.refl _)
  let f : Fin a → OXMod.{u, u} X := fun _ => structureModule X
  let g : Fin b → OXMod.{u, u} X := fun _ => structureModule X
  have step2 :
      (finiteFree X a ⊞ finiteFree X b) ≅ (⨁ (Sum.elim f g)) :=
    { hom := biproduct.lift (fun s => match s with
        | Sum.inl i => biprod.fst ≫ biproduct.π f i
        | Sum.inr j => biprod.snd ≫ biproduct.π g j)
      inv := biprod.lift
        (biproduct.lift (fun i => biproduct.π _ (Sum.inl i)))
        (biproduct.lift (fun j => biproduct.π _ (Sum.inr j)))
      hom_inv_id := by
        apply biprod.hom_ext
        · apply biproduct.hom_ext
          intro k
          simp only [Category.assoc, biprod.lift_fst, Category.id_comp, biproduct.lift_π]
          rfl
        · apply biproduct.hom_ext
          intro k
          simp only [Category.assoc, biprod.lift_snd, Category.id_comp, biproduct.lift_π]
          rfl
      inv_hom_id := by
        apply biproduct.hom_ext
        rintro (i | j)
        · simp only [Category.assoc, Category.id_comp, biproduct.lift_π]
          change biprod.lift _ _ ≫ (biprod.fst ≫ biproduct.π f i) = _
          rw [biprod.lift_fst_assoc, biproduct.lift_π]
        · simp only [Category.assoc, Category.id_comp, biproduct.lift_π]
          change biprod.lift _ _ ≫ (biprod.snd ≫ biproduct.π g j) = _
          rw [biprod.lift_snd_assoc, biproduct.lift_π] }
  exact step2.trans step1

/-- If `A` and `B` are each direct summands of finite free modules, then so is `A ⊞ B`. -/
theorem isDirectSummandOfFiniteFree_biprod {A B : OXMod.{u, w} X}
    (hA : IsDirectSummandOfFiniteFree A) (hB : IsDirectSummandOfFiniteFree B) :
    IsDirectSummandOfFiniteFree (A ⊞ B) := by
  obtain ⟨a, ⟨ρA⟩⟩ := hA
  obtain ⟨b, ⟨ρB⟩⟩ := hB
  let L := moduleULift.{u, w} X
  let R := moduleULift.{w, u} X
  let : PreservesBinaryBiproducts L := preservesBinaryBiproducts_of_preservesBiproducts L
  let : PreservesBinaryBiproducts R := preservesBinaryBiproducts_of_preservesBiproducts R
  refine ⟨a + b, ⟨(L.mapBiprod A B).retract.trans (Retract.trans ?_
    (((R.mapBiprod (finiteFree X a) (finiteFree X b)).symm).trans
      (R.mapIso (finiteFreeBiprodIso a b))).retract)⟩⟩
  refine ⟨biprod.map ρA.i ρB.i, biprod.map ρA.r ρB.r, ?_⟩
  apply biprod.hom_ext <;> simp

/-- A cochain complex `E` of `O_X`-modules is *strictly perfect* if it is bounded (only
finitely many terms are nonzero) and each term is a direct summand of a finite free
`O_X`-module. -/
@[sga "6 I 2.1" "special case", sga "6 I 7.1.1" "special case"]
structure IsStrictlyPerfect {X : AlgebraicGeometry.RingedSpace.{u, v}}
    (E : CochainComplex (OXMod.{u, w} X) ℤ) : Prop where
  /-- Boundedness: only finitely many terms of the complex are nonzero. -/
  bounded : {i : ℤ | ¬ IsZero (E.X i)}.Finite
  /-- Each term is a direct summand of a finite free `O_X`-module. -/
  directSummand : ∀ i : ℤ, IsDirectSummandOfFiniteFree (E.X i)

/-- The cone on a morphism of strictly perfect complexes is strictly perfect.

The cone `C(f)` is `CochainComplex.mappingCone f`, whose `n`-th term is `L^n ⊕ K^{n+1}`. The
hypothesis `HasHomotopyCofiber f` is the (automatically satisfied, since the category has
binary biproducts) condition ensuring the mapping cone exists. -/
@[stacks 08C5]
theorem isStrictlyPerfect_mappingCone {K L : CochainComplex (OXMod.{u, w} X) ℤ}
    (f : K ⟶ L) [HomologicalComplex.HasHomotopyCofiber f]
    (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L) :
    IsStrictlyPerfect (CochainComplex.mappingCone f) := by
  constructor
  · have hsub : {i : ℤ | ¬ IsZero ((CochainComplex.mappingCone f).X i)} ⊆
        (fun i => i - 1) '' {i : ℤ | ¬ IsZero (K.X i)} ∪ {i : ℤ | ¬ IsZero (L.X i)} := by
      intro i hi
      rw [Set.mem_ofPred_eq, CochainComplex.mappingCone.isZero_X_iff, not_and_or] at hi
      rcases hi with hK' | hL'
      · exact Or.inl ⟨i + 1, hK', by ring⟩
      · exact Or.inr hL'
    exact Set.Finite.subset ((hK.bounded.image _).union hL.bounded) hsub
  · intro i
    refine isDirectSummandOfFiniteFree_of_iso
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) (by simp)) ?_
    exact isDirectSummandOfFiniteFree_biprod (hK.directSummand (i + 1)) (hL.directSummand i)

end StrictlyPerfect
