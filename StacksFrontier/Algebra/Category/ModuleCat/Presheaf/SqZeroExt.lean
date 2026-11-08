module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Square-zero extensions of a presheaf of commutative rings

For a presheaf of commutative rings `R` and a presheaf of `R`-modules `M`, the sections of the
square-zero extension on an object `U` are the trivial square-zero extension
`TrivSqZeroExt (R.obj U) (M.obj U)`; the restriction maps act on the two components separately. A
relative derivation with values in `M` determines a morphism of presheaves of commutative rings
splitting the projection to `R`, and a splitting trivial on the base determines a relative
derivation.

## Main definitions

* `PresheafOfModules.sqZeroExtPresheaf`: the square-zero extension of `R` by `M`.
* `PresheafOfModules.sqZeroExtProj` and `PresheafOfModules.sqZeroExtInl`: the projection onto `R`
  and the inclusion of `R`.
* `PresheafOfModules.sqZeroExtLift`: a homomorphism into the sections of the square-zero extension,
  from a ring homomorphism and a Leibniz additive map.
* `PresheafOfModules.sqZeroExtOfDerivation`: the splitting of the projection determined by a
  relative derivation.
* `PresheafOfModules.sqZeroExtDerivation`: the relative derivation determined by a splitting of the
  projection that is trivial on the base.

## Main results

* `PresheafOfModules.isSheaf_sqZeroExtPresheaf`: the square-zero extension of a sheaf of
  commutative rings by a sheaf of modules is a sheaf.
* `PresheafOfModules.sqZeroExtOfDerivation_injective`: a relative derivation is determined by its
  splitting.

## Implementation notes

`TrivSqZeroExt A N` carries a commutative ring structure only in the presence of a right action of
`A` on `N` agreeing with the left one. Over a commutative ring that action is canonical, but
Mathlib has no instance for it; `moduleMulOpposite` and `isCentralScalar_of_commRing` supply it,
and are used as local instances only, so that the ring structure is fixed once and for all inside
`sqZeroExtObj` and no instance is exported.

The accessors `sqZeroExtMk`, `sqZeroExtFst` and `sqZeroExtSnd` repackage `TrivSqZeroExt`'s pair
structure at the bundled type `sqZeroExtObj M U`.

## References

* [Stacks Project, Tag 08RR](https://stacks.math.columbia.edu/tag/08RR)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace PresheafOfModules

/-- rc4 API drift shim: Mathlib moved the relative-derivation type from the `PresheafOfModules`
namespace to the reducibly defeq `PresheafOfModulesOfCommRing` namespace (the target file's
`M : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)` is exactly
`PresheafOfModulesOfCommRing R`). This abbrev restores the `PresheafOfModules.Derivation'`
projection point without changing any statement. -/
abbrev Derivation' {C : Type u} [Category.{u} C] {R S' : Cᵒᵖ ⥤ CommRingCat.{u}}
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (φ' : S' ⟶ R) : Type _ :=
  PresheafOfModulesOfCommRing.Derivation' M φ'

/-- For a commutative ring `A` and an `A`-module `N`, the right action of `A` on `N` obtained from
the left action through the canonical isomorphism `Aᵐᵒᵖ ≅ A`. -/
@[instance_reducible]
noncomputable def moduleMulOpposite (A : Type u) [CommRing A] (N : Type u) [AddCommGroup N]
    [Module A N] : Module Aᵐᵒᵖ N :=
  Module.compHom N (RingEquiv.toOpposite A).symm.toRingHom

attribute [local instance] moduleMulOpposite

/-- Over a commutative ring the canonical right action on a module agrees with the left action. -/
theorem isCentralScalar_of_commRing (A : Type u) [CommRing A] (N : Type u) [AddCommGroup N]
    [Module A N] : IsCentralScalar A N := ⟨fun _ _ => rfl⟩

attribute [local instance] isCentralScalar_of_commRing

/-- The restriction map of a presheaf of modules along an identity is the identity. -/
private theorem presheafMap_id_apply {C : Type u} [Category.{u} C] {R' : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R') {U : Cᵒᵖ} (x : M.obj U) : M.map (𝟙 U) x = x := by
  rw [← presheaf_map_apply_coe, M.presheaf.map_id]
  rfl

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

/-- The sections on `U` of the square-zero extension of `R` by `M`. -/
noncomputable def sqZeroExtObj (U : Cᵒᵖ) : CommRingCat.{u} :=
  CommRingCat.of (TrivSqZeroExt (R.obj U) (M.obj U))

/-- The restriction homomorphism of the square-zero extension, acting on the ring component and on
the module component separately. -/
noncomputable def sqZeroExtRingHom {U V : Cᵒᵖ} (i : U ⟶ V) :
    TrivSqZeroExt (R.obj U) (M.obj U) →+* TrivSqZeroExt (R.obj V) (M.obj V) where
  toFun x := (((R.map i).hom x.fst, M.map i x.snd) : TrivSqZeroExt _ _)
  map_one' := TrivSqZeroExt.ext (map_one _) (map_zero _)
  map_zero' := TrivSqZeroExt.ext (map_zero _) (map_zero _)
  map_add' x y := TrivSqZeroExt.ext (map_add _ _ _) (map_add _ _ _)
  map_mul' x y := TrivSqZeroExt.ext (map_mul _ _ _) (by
    change M.map i (x.fst • y.snd + y.fst • x.snd) =
      (R.map i).hom x.fst • M.map i y.snd + (R.map i).hom y.fst • M.map i x.snd
    rw [map_add]
    exact congrArg₂ (· + ·) (M.map_smul i x.fst y.snd) (M.map_smul i y.fst x.snd))

/-- The restriction map of the square-zero extension of `R` by `M`. -/
noncomputable def sqZeroExtMap {U V : Cᵒᵖ} (i : U ⟶ V) : sqZeroExtObj M U ⟶ sqZeroExtObj M V :=
  CommRingCat.ofHom (sqZeroExtRingHom M i)

variable {M}

/-- The section of the square-zero extension with the given ring and module components. -/
noncomputable def sqZeroExtMk {U : Cᵒᵖ} (r : R.obj U) (m : M.obj U) : sqZeroExtObj M U := (r, m)

/-- The ring component of a section of the square-zero extension. -/
noncomputable def sqZeroExtFst {U : Cᵒᵖ} (x : sqZeroExtObj M U) : R.obj U := x.1

/-- The module component of a section of the square-zero extension. -/
noncomputable def sqZeroExtSnd {U : Cᵒᵖ} (x : sqZeroExtObj M U) : M.obj U := x.2

/-- The ring component of `sqZeroExtMk r m` is `r`. -/
@[simp] theorem sqZeroExtFst_mk {U : Cᵒᵖ} (r : R.obj U) (m : M.obj U) :
    sqZeroExtFst (sqZeroExtMk r m) = r := rfl

/-- The module component of `sqZeroExtMk r m` is `m`. -/
@[simp] theorem sqZeroExtSnd_mk {U : Cᵒᵖ} (r : R.obj U) (m : M.obj U) :
    sqZeroExtSnd (sqZeroExtMk r m) = m := rfl

/-- Two sections of the square-zero extension with the same components are equal. -/
theorem sqZeroExt_ext {U : Cᵒᵖ} {x y : sqZeroExtObj M U}
    (h1 : sqZeroExtFst x = sqZeroExtFst y) (h2 : sqZeroExtSnd x = sqZeroExtSnd y) : x = y :=
  TrivSqZeroExt.ext h1 h2

/-- The ring component of zero. -/
@[simp] theorem sqZeroExtFst_zero {U : Cᵒᵖ} : sqZeroExtFst (0 : sqZeroExtObj M U) = 0 := rfl

/-- The module component of zero. -/
@[simp] theorem sqZeroExtSnd_zero {U : Cᵒᵖ} : sqZeroExtSnd (0 : sqZeroExtObj M U) = 0 := rfl

/-- The ring component of one. -/
@[simp] theorem sqZeroExtFst_one {U : Cᵒᵖ} : sqZeroExtFst (1 : sqZeroExtObj M U) = 1 := rfl

/-- The module component of one. -/
@[simp] theorem sqZeroExtSnd_one {U : Cᵒᵖ} : sqZeroExtSnd (1 : sqZeroExtObj M U) = 0 := rfl

/-- The ring component is additive. -/
@[simp] theorem sqZeroExtFst_add {U : Cᵒᵖ} (x y : sqZeroExtObj M U) :
    sqZeroExtFst (x + y) = sqZeroExtFst x + sqZeroExtFst y := rfl

/-- The module component is additive. -/
@[simp] theorem sqZeroExtSnd_add {U : Cᵒᵖ} (x y : sqZeroExtObj M U) :
    sqZeroExtSnd (x + y) = sqZeroExtSnd x + sqZeroExtSnd y := rfl

/-- The ring component is multiplicative. -/
@[simp] theorem sqZeroExtFst_mul {U : Cᵒᵖ} (x y : sqZeroExtObj M U) :
    sqZeroExtFst (x * y) = sqZeroExtFst x * sqZeroExtFst y := rfl

/-- The module component of a product, by the Leibniz rule of the square-zero multiplication. -/
@[simp] theorem sqZeroExtSnd_mul {U : Cᵒᵖ} (x y : sqZeroExtObj M U) :
    sqZeroExtSnd (x * y) = sqZeroExtFst x • sqZeroExtSnd y + sqZeroExtFst y • sqZeroExtSnd x :=
  rfl

/-- Restriction acts on the ring component through the restriction of `R`. -/
@[simp] theorem sqZeroExtFst_map {U V : Cᵒᵖ} (i : U ⟶ V) (x : sqZeroExtObj M U) :
    sqZeroExtFst ((sqZeroExtMap M i).hom x) = (R.map i).hom (sqZeroExtFst x) := rfl

/-- Restriction acts on the module component through the restriction of `M`. -/
@[simp] theorem sqZeroExtSnd_map {U V : Cᵒᵖ} (i : U ⟶ V) (x : sqZeroExtObj M U) :
    sqZeroExtSnd ((sqZeroExtMap M i).hom x) = M.map i (sqZeroExtSnd x) := rfl

variable (M)

/-- The square-zero extension of `R` by `M`, as a presheaf of commutative rings. -/
noncomputable def sqZeroExtPresheaf : Cᵒᵖ ⥤ CommRingCat.{u} where
  obj U := sqZeroExtObj M U
  map i := sqZeroExtMap M i
  map_id U := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => sqZeroExt_ext ?_ ?_)
    · rw [sqZeroExtFst_map]
      exact congrArg (fun f => (CommRingCat.Hom.hom f) (sqZeroExtFst x)) (R.map_id U)
    · rw [sqZeroExtSnd_map]
      exact presheafMap_id_apply M (sqZeroExtSnd x)
  map_comp {U V W} i j := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => sqZeroExt_ext ?_ ?_)
    · rw [sqZeroExtFst_map]
      exact congrArg (fun f => (CommRingCat.Hom.hom f) (sqZeroExtFst x)) (R.map_comp i j)
    · rw [sqZeroExtSnd_map]
      exact map_comp_apply M i j (sqZeroExtSnd x)

/-- A homomorphism of commutative rings into the sections of a square-zero extension, built from a
ring homomorphism to the ring component and an additive map satisfying the Leibniz rule to the
module component. -/
noncomputable def sqZeroExtLift {A : CommRingCat.{u}} {U : Cᵒᵖ} (g : A ⟶ R.obj U)
    (dd : A →+ M.obj U) (hmul : ∀ a b : A, dd (a * b) = g.hom a • dd b + g.hom b • dd a) :
    A ⟶ sqZeroExtObj M U :=
  CommRingCat.ofHom
    ({ toFun := fun a => ((g.hom a, dd a) : TrivSqZeroExt _ _)
       map_one' := TrivSqZeroExt.ext (map_one _) (by simpa using hmul 1 1)
       map_mul' a b := TrivSqZeroExt.ext (map_mul _ _ _) (hmul a b)
       map_zero' := TrivSqZeroExt.ext (map_zero _) (map_zero _)
       map_add' a b := TrivSqZeroExt.ext (map_add _ _ _) (map_add _ _ _) } :
      A →+* TrivSqZeroExt (R.obj U) (M.obj U))

/-- The ring component of `sqZeroExtLift` is the given ring homomorphism. -/
@[simp] theorem sqZeroExtFst_lift {A : CommRingCat.{u}} {U : Cᵒᵖ} (g : A ⟶ R.obj U)
    (dd : A →+ M.obj U) (hmul : ∀ a b : A, dd (a * b) = g.hom a • dd b + g.hom b • dd a)
    (a : A) : sqZeroExtFst ((sqZeroExtLift M g dd hmul).hom a) = g.hom a := rfl

/-- The module component of `sqZeroExtLift` is the given additive map. -/
@[simp] theorem sqZeroExtSnd_lift {A : CommRingCat.{u}} {U : Cᵒᵖ} (g : A ⟶ R.obj U)
    (dd : A →+ M.obj U) (hmul : ∀ a b : A, dd (a * b) = g.hom a • dd b + g.hom b • dd a)
    (a : A) : sqZeroExtSnd ((sqZeroExtLift M g dd hmul).hom a) = dd a := rfl

/-- The projection of the square-zero extension onto the presheaf of commutative rings. -/
noncomputable def sqZeroExtProj : sqZeroExtPresheaf M ⟶ R where
  app U := CommRingCat.ofHom
    ({ toFun := TrivSqZeroExt.fst
       map_one' := rfl
       map_mul' _ _ := rfl
       map_zero' := rfl
       map_add' _ _ := rfl } : TrivSqZeroExt (R.obj U) (M.obj U) →+* R.obj U)
  naturality _ _ _ := rfl

/-- The inclusion of the presheaf of commutative rings into its square-zero extension. -/
noncomputable def sqZeroExtInl : R ⟶ sqZeroExtPresheaf M where
  app U := CommRingCat.ofHom
    ({ toFun := TrivSqZeroExt.inl
       map_one' := rfl
       map_mul' r r' := TrivSqZeroExt.ext rfl (by simp)
       map_zero' := rfl
       map_add' r r' := TrivSqZeroExt.ext rfl (by simp) } :
      R.obj U →+* TrivSqZeroExt (R.obj U) (M.obj U))
  naturality U V i :=
    CommRingCat.hom_ext (RingHom.ext fun r => TrivSqZeroExt.ext rfl (map_zero _).symm)

/-- The projection is the ring component. -/
@[simp] theorem sqZeroExtProj_app_apply {U : Cᵒᵖ} (x : sqZeroExtObj M U) :
    ((sqZeroExtProj M).app U).hom x = sqZeroExtFst x := rfl

/-- The inclusion has vanishing module component. -/
@[simp] theorem sqZeroExtInl_app_apply {U : Cᵒᵖ} (r : R.obj U) :
    ((sqZeroExtInl M).app U).hom r = sqZeroExtMk r 0 := rfl

/-- The square-zero extension of a sheaf of commutative rings by a sheaf of modules is a sheaf. -/
theorem isSheaf_sqZeroExtPresheaf {X : TopCat.{u}} {R : (Opens (X : Type u))ᵒᵖ ⥤ CommRingCat.{u}}
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (hR : TopCat.Presheaf.IsSheaf R) (hM : TopCat.Presheaf.IsSheaf M.presheaf) :
    TopCat.Presheaf.IsSheaf (sqZeroExtPresheaf M) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hcR : TopCat.Presheaf.IsCompatible R U (fun i => sqZeroExtFst (sf i)) := fun i j =>
    congrArg sqZeroExtFst (hsf i j)
  have hcM : TopCat.Presheaf.IsCompatible M.presheaf U (fun i => sqZeroExtSnd (sf i)) := fun i j =>
    congrArg sqZeroExtSnd (hsf i j)
  obtain ⟨r, hr, hrU⟩ := hR.isSheafUniqueGluing U _ hcR
  obtain ⟨m, hm, hmU⟩ := hM.isSheafUniqueGluing U _ hcM
  refine ⟨sqZeroExtMk r m, fun i => sqZeroExt_ext ?_ ?_, ?_⟩
  · exact (congrArg (R.map (Opens.leSupr U i).op) (sqZeroExtFst_mk r m)).trans (hr i)
  · exact (congrArg (M.presheaf.map (Opens.leSupr U i).op) (sqZeroExtSnd_mk r m)).trans (hm i)
  · intro s hs
    refine sqZeroExt_ext ?_ ?_
    · exact (hrU _ fun i => congrArg sqZeroExtFst (hs i)).trans (sqZeroExtFst_mk r m).symm
    · exact (hmU _ fun i => congrArg sqZeroExtSnd (hs i)).trans (sqZeroExtSnd_mk r m).symm

variable (g : R ⟶ sqZeroExtPresheaf M)

/-- The component at `U` of a morphism of presheaves of commutative rings into the square-zero
extension, at the bundled type of its sections. -/
noncomputable def sqZeroExtApp (U : Cᵒᵖ) : R.obj U ⟶ sqZeroExtObj M U := g.app U

/-- A splitting of the projection acts as the identity on the ring component. -/
theorem sqZeroExtFst_of_section (hsec : g ≫ sqZeroExtProj M = 𝟙 R) (U : Cᵒᵖ) (r : R.obj U) :
    sqZeroExtFst (M := M) (U := U) ((sqZeroExtApp M g U).hom r) = r :=
  ConcreteCategory.congr_hom (NatTrans.congr_app hsec U) r

/-- The additive map to the module component determined by a morphism into the square-zero
extension. -/
noncomputable def sqZeroExtSndHom (U : Cᵒᵖ) : R.obj U →+ M.obj U :=
  AddMonoidHom.mk' (fun r => sqZeroExtSnd (M := M) (U := U) ((sqZeroExtApp M g U).hom r))
    (fun r r' => (congrArg (sqZeroExtSnd (M := M) (U := U))
      (map_add (sqZeroExtApp M g U).hom r r')).trans (sqZeroExtSnd_add _ _))

/-- `sqZeroExtSndHom` is the module component of the morphism. -/
@[simp] theorem sqZeroExtSndHom_apply (U : Cᵒᵖ) (r : R.obj U) :
    sqZeroExtSndHom M g U r = sqZeroExtSnd (M := M) (U := U) ((sqZeroExtApp M g U).hom r) := rfl

/-- A splitting of the square-zero extension, trivial on `S`, is a relative derivation. -/
noncomputable def sqZeroExtDerivation {S : Cᵒᵖ ⥤ CommRingCat.{u}} (ψ : S ⟶ R)
    (hsec : g ≫ sqZeroExtProj M = 𝟙 R) (hker : ψ ≫ g = ψ ≫ sqZeroExtInl M) :
    M.Derivation' ψ where
  d {U} := sqZeroExtSndHom M g U
  d_mul {U} a b := by
    rw [sqZeroExtSndHom_apply, map_mul, sqZeroExtSnd_mul,
      sqZeroExtFst_of_section M g hsec, sqZeroExtFst_of_section M g hsec]
    rfl
  d_map {U V} i x := by
    rw [sqZeroExtSndHom_apply, sqZeroExtSndHom_apply]
    refine (congrArg (sqZeroExtSnd (M := M) (U := V)) (congrArg
      (fun m : CommRingCat.Hom (R.obj U) (sqZeroExtObj M V) => m.hom x)
      (g.naturality i))).trans ?_
    exact sqZeroExtSnd_map i ((sqZeroExtApp M g U).hom x)
  d_app {U} a := by
    rw [sqZeroExtSndHom_apply]
    refine (congrArg (fun m : CommRingCat.Hom _ _ => sqZeroExtSnd (m.hom a))
      (congrArg (fun n : S ⟶ sqZeroExtPresheaf M => n.app U) hker)).trans ?_
    exact sqZeroExtSnd_mk _ 0

variable {S : Cᵒᵖ ⥤ CommRingCat.{u}} {ψ : S ⟶ R}

/-- Two relative derivations agreeing on all local sections are equal. -/
theorem derivation_ext {D D' : M.Derivation' ψ} (h : ∀ (U : Cᵒᵖ) (a : R.obj U), D.d a = D'.d a) :
    D = D' := by
  ext U a
  exact h U a

/-- The splitting of the projection from the square-zero extension determined by a relative
derivation. -/
noncomputable def sqZeroExtOfDerivation (D : M.Derivation' ψ) : R ⟶ sqZeroExtPresheaf M where
  app U := sqZeroExtLift M (𝟙 (R.obj U)) D.d (fun a b => D.d_mul a b)
  naturality _U _V i := CommRingCat.hom_ext (RingHom.ext fun a =>
    sqZeroExt_ext rfl (D.d_map i a))

/-- The splitting determined by a relative derivation has that derivation as its module
component. -/
@[simp] theorem sqZeroExtSnd_ofDerivation (D : M.Derivation' ψ) (U : Cᵒᵖ) (a : R.obj U) :
    sqZeroExtSnd (M := M) (U := U)
      ((sqZeroExtApp M (sqZeroExtOfDerivation M D) U).hom a) = D.d a := rfl

/-- A relative derivation is determined by its splitting of the square-zero extension. -/
theorem sqZeroExtOfDerivation_injective :
    Function.Injective (sqZeroExtOfDerivation M (ψ := ψ)) := by
  intro D D' h
  refine derivation_ext M fun U a => ?_
  rw [← sqZeroExtSnd_ofDerivation M D U a, h, sqZeroExtSnd_ofDerivation]

end PresheafOfModules
