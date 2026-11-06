module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Morphisms out of a generator, on retracts of finite free objects

Let `C` be a preadditive category with finite biproducts, `O` an object of `C`, `R` a
commutative ring and `ρ : R →+* End O` a ring isomorphism. Then `Hom(O, M)` is an `R`-module,
`r • s = ρ r ≫ s`, functorially in `M`. On the retracts of finite biproducts of copies of `O`
this functor is fully faithful with finite projective values, and it is compatible with base
change along an additive functor `F` with `F O ≅ O'`.

## Main definitions

* `CategoryTheory.homModule`: the functor `Hom(O, -) : C ⥤ ModuleCat R`.
* `CategoryTheory.IsRetractOfFiniteFree`: an object is a retract of `O^{⊕n}` for some `n`.
* `CategoryTheory.baseChangeRingHom` and `CategoryTheory.homModuleBaseChange`: the ring map
  `R → R'` induced by an additive functor and the base-change comparison
  `R' ⊗_R Hom(O, M) ⟶ Hom(O', F M)`.

## Main results

* `CategoryTheory.bijective_homModule_map`: `Hom(O, -)` is fully faithful on morphisms out of
  a retract of a finite free object.
* `CategoryTheory.nonempty_homotopyEquiv_of_homModule`: homotopy equivalences between complexes
  with retract terms are detected after applying `Hom(O, -)`.
* `CategoryTheory.isIso_homModuleBaseChange_app`: the base-change comparison is an isomorphism
  at every retract of a finite free object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v w u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {R : Type w} [CommRing R]

/-! ### The module of morphisms out of `O` -/

/-- The morphisms `O ⟶ M`, as a type carrying the `R`-module structure `r • s = ρ r ≫ s`. -/
def HomFrom (O M : C) (_ρ : R →+* End O) : Type v := O ⟶ M

namespace HomFrom

variable {O M : C} {ρ : R →+* End O}

/-- rc4 compat bridges: `End` became a structure in Mathlib (2026-09-12), so the
`rc2`-era syntactic identification `End X = X ⟶ X` is recovered by the pair of coercions
`End.asHom` and `End.of`. -/
instance coeEndAsHom {X : C} : Coe (End X) (X ⟶ X) := ⟨End.asHom⟩

instance coeHomAsEnd {X : C} : Coe (X ⟶ X) (End X) := ⟨End.of⟩

/-- A morphism `O ⟶ M` read as an element of `HomFrom O M ρ`. -/
def mk (s : O ⟶ M) : HomFrom O M ρ := s

/-- The morphism `O ⟶ M` underlying an element of `HomFrom O M ρ`. -/
def hom (s : HomFrom O M ρ) : O ⟶ M := s

/-- The morphism underlying `mk s` is `s`. -/
@[simp] lemma hom_mk (s : O ⟶ M) : (mk s : HomFrom O M ρ).hom = s := rfl

/-- `mk` of the underlying morphism of `s` is `s`. -/
@[simp] lemma mk_hom (s : HomFrom O M ρ) : mk s.hom = s := rfl

/-- Two elements of `HomFrom O M ρ` with the same underlying morphism are equal. -/
@[ext] lemma ext {s t : HomFrom O M ρ} (h : s.hom = t.hom) : s = t := h

/-- The additive group structure of `HomFrom O M ρ` is that of `O ⟶ M`. -/
instance : AddCommGroup (HomFrom O M ρ) := inferInstanceAs (AddCommGroup (O ⟶ M))

/-- The morphism underlying a sum is the sum of the underlying morphisms. -/
@[simp] lemma hom_add (s t : HomFrom O M ρ) : (s + t).hom = s.hom + t.hom := rfl

/-- The morphism underlying `0` is the zero morphism. -/
@[simp] lemma hom_zero : (0 : HomFrom O M ρ).hom = 0 := rfl

/-- The morphism underlying `-s` is the negative of the morphism underlying `s`. -/
@[simp] lemma hom_neg (s : HomFrom O M ρ) : (-s).hom = -s.hom := rfl

/-- The morphism underlying a difference is the difference of the underlying morphisms. -/
@[simp] lemma hom_sub (s t : HomFrom O M ρ) : (s - t).hom = s.hom - t.hom := rfl

/-- The `R`-module structure `r • s = ρ r ≫ s` on `HomFrom O M ρ`. -/
instance : Module R (HomFrom O M ρ) where
  smul r s := mk (ρ r ≫ s.hom)
  one_smul s := by
    change mk (ρ 1 ≫ s.hom) = s
    rw [map_one, End.one_asHom, Category.id_comp, mk_hom]
  mul_smul r t s := by
    change mk ((ρ (r * t)).asHom ≫ s.hom) = mk ((ρ r).asHom ≫ (ρ t).asHom ≫ s.hom)
    rw [mul_comm, map_mul, End.mul_asHom, Category.assoc]
  smul_zero r := Limits.comp_zero
  smul_add r s s' := Preadditive.comp_add _ _ _ _ _ _
  add_smul r t s := by
    change mk ((ρ (r + t)).asHom ≫ s.hom) = mk ((ρ r).asHom ≫ s.hom + (ρ t).asHom ≫ s.hom)
    rw [map_add, show (ρ r + ρ t).asHom = (ρ r).asHom + (ρ t).asHom from rfl, Preadditive.add_comp]
  zero_smul s := by
    change mk ((ρ 0).asHom ≫ s.hom) = 0
    rw [map_zero]
    show mk ((0 : End O).asHom ≫ s.hom) = 0
    rw [show (0 : End O).asHom = (0 : O ⟶ O) from rfl, Limits.zero_comp]; rfl

/-- The morphism underlying `r • s` is `ρ r ≫ s`. -/
@[simp] lemma hom_smul (r : R) (s : HomFrom O M ρ) : (r • s).hom = ρ r ≫ s.hom := rfl

end HomFrom

/-- The functor `Hom(O, -) : C ⥤ ModuleCat R`, with `r • s = ρ r ≫ s`. -/
def homModule (O : C) (ρ : R →+* End O) : C ⥤ ModuleCat.{v} R where
  obj M := ModuleCat.of R (HomFrom O M ρ)
  map f := ModuleCat.ofHom
    { toFun s := HomFrom.mk (s.hom ≫ f)
      map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _
      map_smul' r s := Category.assoc ((ρ r).asHom) s.hom f }
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun s => Category.comp_id s.hom)
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun s => (Category.assoc s.hom f g).symm)

variable (O : C) (ρ : R →+* End O)

/-- `Hom(O, f)` sends `s` to `s ≫ f`. -/
@[simp]
lemma homModule_map_apply_hom {M N : C} (f : M ⟶ N) (s : (homModule O ρ).obj M) :
    HomFrom.hom (ρ := ρ) (((homModule O ρ).map f).hom s) = HomFrom.hom (ρ := ρ) s ≫ f :=
  rfl

/-- `Hom(O, -)` is additive. -/
instance : (homModule O ρ).Additive where
  map_add {_ _ f g} := ModuleCat.hom_ext (LinearMap.ext fun s =>
    Preadditive.comp_add _ _ _ (HomFrom.hom (ρ := ρ) s) f g)

/-- On underlying abelian groups `Hom(O, -)` is the preadditive co-Yoneda functor of `O`. -/
def homModuleCompForget₂Iso :
    homModule O ρ ⋙ forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v} ≅
      preadditiveCoyoneda.obj (Opposite.op O) :=
  NatIso.ofComponents (fun M => (AddEquiv.refl (O ⟶ M)).toAddCommGrpIso) (fun _ => rfl)

/-- `Hom(O, -)` preserves limits. -/
instance preservesLimits_homModule : PreservesLimits (homModule O ρ) :=
  have : PreservesLimits (homModule O ρ ⋙ forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) :=
    preservesLimits_of_natIso (homModuleCompForget₂Iso O ρ).symm
  preservesLimits_of_reflects_of_preserves (homModule O ρ) (forget₂ (ModuleCat.{v} R) AddCommGrpCat)

/-- `Hom(O, -)` preserves epimorphisms when `O` is projective. -/
instance preservesEpimorphisms_homModule [Projective O] :
    (homModule O ρ).PreservesEpimorphisms where
  preserves {M N} g hg := (ModuleCat.epi_iff_surjective _).2 fun s => by
    exact ⟨HomFrom.mk (ρ := ρ) (Projective.factorThru (HomFrom.hom (ρ := ρ) s) g),
      HomFrom.ext (R := R) (ρ := ρ) (Projective.factorThru_comp _ _)⟩

/-! ### Retracts of finite free objects -/

/-- An object is a *retract of a finite free object* when it is a retract of `O^{⊕n}`, the
biproduct of `n` copies of `O`, for some `n`. -/
def IsRetractOfFiniteFree [HasFiniteBiproducts C] (O M : C) : Prop :=
  ∃ (n : ℕ) (i : M ⟶ ⨁ fun _ : Fin n => O) (p : (⨁ fun _ : Fin n => O) ⟶ M), i ≫ p = 𝟙 M

variable {O} in
/-- Being a retract of a finite free object is invariant under isomorphism. -/
lemma IsRetractOfFiniteFree.of_iso [HasFiniteBiproducts C] {M N : C}
    (h : IsRetractOfFiniteFree O M) (e : M ≅ N) : IsRetractOfFiniteFree O N := by
  obtain ⟨n, i, p, hip⟩ := h
  exact ⟨n, e.inv ≫ i, p ≫ e.hom, by simp [reassoc_of% hip]⟩

/-- A finite biproduct of copies of `O` is a retract of a finite free object. -/
lemma isRetractOfFiniteFree_biproduct [HasFiniteBiproducts C] (n : ℕ) :
    IsRetractOfFiniteFree O (⨁ fun _ : Fin n => O) :=
  ⟨n, 𝟙 _, 𝟙 _, Category.id_comp _⟩

/-- `O` itself is a retract of a finite free object. -/
lemma isRetractOfFiniteFree_self [HasFiniteBiproducts C] : IsRetractOfFiniteFree O O :=
  ⟨1, biproduct.ι (fun _ : Fin 1 => O) 0, biproduct.π _ 0, biproduct.ι_π_self _ _⟩

/-! ### Full faithfulness -/

section FullyFaithful

variable {O ρ}

/-- If `homModule` is bijective on morphisms out of `A` and `M` is a retract of `A`, then it is
bijective on morphisms out of `M`. -/
lemma bijective_homModule_map_of_retract {A M N : C} (i : M ⟶ A) (p : A ⟶ M) (hip : i ≫ p = 𝟙 M)
    (hA : Function.Bijective ((homModule O ρ).map : (A ⟶ N) →
      ((homModule O ρ).obj A ⟶ (homModule O ρ).obj N))) :
    Function.Bijective ((homModule O ρ).map : (M ⟶ N) →
      ((homModule O ρ).obj M ⟶ (homModule O ρ).obj N)) := by
  refine ⟨fun f g hfg => ?_, fun φ => ?_⟩
  · have : p ≫ f = p ≫ g := hA.1 (by simp only [Functor.map_comp, hfg])
    simpa [← Category.assoc, hip] using congrArg (i ≫ ·) this
  · obtain ⟨h, hh⟩ := hA.2 ((homModule O ρ).map p ≫ φ)
    refine ⟨i ≫ h, ?_⟩
    rw [Functor.map_comp, hh, ← Category.assoc, ← Functor.map_comp, hip, Functor.map_id,
      Category.id_comp]

variable (hρ : Function.Bijective ρ)
include hρ

/-- Every element of `Hom(O, O)` is `r • 𝟙 O` for some `r`, when `ρ` is bijective. -/
private lemma exists_smul_id_eq (s : (homModule O ρ).obj O) :
    ∃ r : R, HomFrom.hom (ρ := ρ) s = ρ r ∧
      s = r • (HomFrom.mk (ρ := ρ) (𝟙 O) : (homModule O ρ).obj O) := by
  obtain ⟨r, hr⟩ := hρ.2 (HomFrom.hom (ρ := ρ) s)
  refine ⟨r, congrArg End.asHom hr.symm, HomFrom.ext (R := R) (ρ := ρ) ?_⟩
  change HomFrom.hom (ρ := ρ) s = (ρ r).asHom ≫ 𝟙 O
  rw [hr, Category.comp_id]

/-- `homModule` is bijective on morphisms out of `O`. -/
lemma bijective_homModule_map_self (N : C) :
    Function.Bijective ((homModule O ρ).map : (O ⟶ N) →
      ((homModule O ρ).obj O ⟶ (homModule O ρ).obj N)) := by
  refine ⟨fun f g hfg => ?_,
    fun φ => ⟨HomFrom.hom (ρ := ρ) (φ.hom (HomFrom.mk (ρ := ρ) (𝟙 O))), ?_⟩⟩
  · have := congrArg (fun ψ : (homModule O ρ).obj O ⟶ (homModule O ρ).obj N =>
      HomFrom.hom (ρ := ρ) (ψ.hom (HomFrom.mk (ρ := ρ) (𝟙 O)))) hfg
    change 𝟙 O ≫ f = 𝟙 O ≫ g at this
    simpa using this
  · refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
    obtain ⟨r, -, hs⟩ := exists_smul_id_eq hρ s
    let e : (homModule O ρ).obj O := HomFrom.mk (ρ := ρ) (𝟙 O)
    have hs' : s = r • e := hs
    have key : φ.hom (r • e) = r • φ.hom e := φ.hom.map_smul r e
    show HomFrom.mk (ρ := ρ) (HomFrom.hom (ρ := ρ) s ≫ HomFrom.hom (ρ := ρ) (φ.hom e)) = φ.hom s
    rw [hs', key]
    apply HomFrom.ext (R := R) (ρ := ρ)
    show ((ρ r).asHom ≫ 𝟙 O) ≫ _ = (ρ r).asHom ≫ _
    rw [Category.comp_id]

/-- `homModule` is bijective on morphisms out of a finite biproduct of copies of `O`. -/
lemma bijective_homModule_map_biproduct [HasFiniteBiproducts C] (n : ℕ) (N : C) :
    Function.Bijective ((homModule O ρ).map : ((⨁ fun _ : Fin n => O) ⟶ N) →
      ((homModule O ρ).obj (⨁ fun _ : Fin n => O) ⟶ (homModule O ρ).obj N)) := by
  have hO := bijective_homModule_map_self hρ N
  refine ⟨fun f g hfg => ?_, fun φ => ?_⟩
  · refine biproduct.hom_ext' _ _ fun j => hO.1 ?_
    simp only [Functor.map_comp, hfg]
  · choose h hh using fun j : Fin n =>
      hO.2 ((homModule O ρ).map (biproduct.ι (fun _ : Fin n => O) j) ≫ φ)
    refine ⟨biproduct.desc h, ?_⟩
    have htot : (𝟙 (⨁ fun _ : Fin n => O)) =
        ∑ j, biproduct.π (fun _ : Fin n => O) j ≫ biproduct.ι (fun _ : Fin n => O) j :=
      biproduct.total.symm
    calc (homModule O ρ).map (biproduct.desc h)
        = (homModule O ρ).map (𝟙 _ ≫ biproduct.desc h) := by rw [Category.id_comp]
      _ = ∑ j, (homModule O ρ).map (biproduct.π (fun _ : Fin n => O) j) ≫
            ((homModule O ρ).map (biproduct.ι (fun _ : Fin n => O) j) ≫ φ) := by
          rw [htot, Preadditive.sum_comp, Functor.map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Category.assoc, biproduct.ι_desc, Functor.map_comp, hh]
      _ = (homModule O ρ).map (∑ j, biproduct.π (fun _ : Fin n => O) j ≫
            biproduct.ι (fun _ : Fin n => O) j) ≫ φ := by
          rw [Functor.map_sum, Preadditive.sum_comp]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Functor.map_comp, Category.assoc]
      _ = φ := by rw [← htot, Functor.map_id, Category.id_comp]

/-- **`Hom(O, -)` is fully faithful on morphisms out of a retract of a finite free object.** -/
lemma bijective_homModule_map [HasFiniteBiproducts C] {M : C} (hM : IsRetractOfFiniteFree O M)
    (N : C) : Function.Bijective ((homModule O ρ).map : (M ⟶ N) →
      ((homModule O ρ).obj M ⟶ (homModule O ρ).obj N)) := by
  obtain ⟨n, i, p, hip⟩ := hM
  exact bijective_homModule_map_of_retract i p hip (bijective_homModule_map_biproduct hρ n N)

end FullyFaithful

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] {R : Type w} [CommRing R] (O : C)
  (ρ : R →+* End O) [Projective O]

/-- `Hom(O, -)` preserves homology when `O` is projective in an abelian category. -/
instance preservesHomology_homModule :
    (homModule O ρ).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- `Hom(O, -)` is right exact when `O` is projective in an abelian category. -/
instance preservesFiniteColimits_homModule :
    PreservesFiniteColimits (homModule O ρ) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

end Abelian

/-! ### Finite projectivity -/

section Projective

variable {O ρ} (hρ : Function.Bijective ρ)
include hρ

/-- `Hom(O, O)` is free of rank one: `ρ` is an `R`-linear isomorphism `R ≃ Hom(O, O)`. -/
def homModuleSelfEquiv : R ≃ₗ[R] (homModule O ρ).obj O :=
  LinearEquiv.ofBijective
    { toFun a := HomFrom.mk (ρ := ρ) (ρ a).asHom
      map_add' a b := by
        apply HomFrom.ext (R := R) (ρ := ρ)
        show (ρ (a + b)).asHom = (ρ a).asHom + (ρ b).asHom
        rw [map_add]
        rfl
      map_smul' r a := by
        apply HomFrom.ext (R := R) (ρ := ρ)
        change (ρ (r * a)).asHom = (ρ r).asHom ≫ (ρ a).asHom
        rw [mul_comm, map_mul, End.mul_asHom] }
    ⟨fun a b hab => hρ.1 (End.ext hab), fun y => by
      obtain ⟨a, ha⟩ := hρ.2 (End.of (y : O ⟶ O))
      exact ⟨a, congrArg End.asHom ha⟩⟩

variable [HasFiniteBiproducts C]

/-- `Hom(O, O^{⊕n})` is the free module `R^n`. -/
def homModuleFiniteFreeEquiv (n : ℕ) :
    (homModule O ρ).obj (⨁ fun _ : Fin n => O) ≃ₗ[R] (Fin n → R) :=
  ((homModule O ρ).mapBiproduct _ ≪≫
    ModuleCat.biproductIsoPi (fun _ : Fin n => (homModule O ρ).obj O)).toLinearEquiv.trans
    (LinearEquiv.piCongrRight fun _ => (homModuleSelfEquiv hρ).symm)

/-- `Hom(O, M)` is a finite projective `R`-module for a retract `M` of a finite free object. -/
lemma homModule_finite_projective {M : C} (hM : IsRetractOfFiniteFree O M) :
    Module.Finite R ((homModule O ρ).obj M) ∧ Module.Projective R ((homModule O ρ).obj M) := by
  obtain ⟨n, i, p, hip⟩ := hM
  let e := homModuleFiniteFreeEquiv hρ n
  let s : (homModule O ρ).obj M →ₗ[R] (Fin n → R) := e.toLinearMap.comp ((homModule O ρ).map i).hom
  let t : (Fin n → R) →ₗ[R] (homModule O ρ).obj M :=
    ((homModule O ρ).map p).hom.comp e.symm.toLinearMap
  have hst : t.comp s = LinearMap.id := by
    ext x
    show ((homModule O ρ).map p).hom (e.symm (e (((homModule O ρ).map i).hom x))) = x
    rw [LinearEquiv.symm_apply_apply, ← ModuleCat.comp_apply, ← Functor.map_comp, hip,
      Functor.map_id, ModuleCat.id_apply]
  exact ⟨Module.Finite.of_surjective t fun x => ⟨s x, congrArg (fun φ : _ →ₗ[R] _ => φ x) hst⟩,
    Module.Projective.of_split s t hst⟩

end Projective

/-! ### Lifting morphisms, homotopies and homotopy equivalences -/

section Lift

variable {O ρ} (hρ : Function.Bijective ρ) [HasFiniteBiproducts C]
include hρ

/-- The morphism `M ⟶ N` out of a retract of a finite free object with a prescribed image under
`Hom(O, -)`. -/
def homModulePreimage {M N : C} (hM : IsRetractOfFiniteFree O M)
    (φ : (homModule O ρ).obj M ⟶ (homModule O ρ).obj N) : M ⟶ N :=
  (Equiv.ofBijective _ (bijective_homModule_map hρ hM N)).symm φ

/-- `Hom(O, -)` sends `homModulePreimage hρ hM φ` to `φ`. -/
@[simp]
lemma homModule_map_homModulePreimage {M N : C} (hM : IsRetractOfFiniteFree O M)
    (φ : (homModule O ρ).obj M ⟶ (homModule O ρ).obj N) :
    (homModule O ρ).map (homModulePreimage hρ hM φ) = φ :=
  (Equiv.ofBijective _ (bijective_homModule_map hρ hM N)).apply_symm_apply φ

/-- `Hom(O, -)` is injective on morphisms out of a retract of a finite free object. -/
lemma homModule_map_injective {M N : C} (hM : IsRetractOfFiniteFree O M) {f g : M ⟶ N}
    (h : (homModule O ρ).map f = (homModule O ρ).map g) : f = g :=
  (bijective_homModule_map hρ hM N).1 h

variable {ι : Type*} {c : ComplexShape ι}

/-- A morphism of complexes with retract terms, lifted along `Hom(O, -)`. -/
def homModuleComplexPreimage {K L : HomologicalComplex C c}
    (hK : ∀ j, IsRetractOfFiniteFree O (K.X j))
    (φ : ((homModule O ρ).mapHomologicalComplex c).obj K ⟶
      ((homModule O ρ).mapHomologicalComplex c).obj L) : K ⟶ L where
  f j := homModulePreimage hρ (hK j) (φ.f j)
  comm' i j _ := homModule_map_injective hρ (hK i) (by simpa using φ.comm i j)

/-- `Hom(O, -)` sends `homModuleComplexPreimage hρ hK φ` to `φ`. -/
@[simp]
lemma mapHomologicalComplex_map_homModuleComplexPreimage {K L : HomologicalComplex C c}
    (hK : ∀ j, IsRetractOfFiniteFree O (K.X j))
    (φ : ((homModule O ρ).mapHomologicalComplex c).obj K ⟶
      ((homModule O ρ).mapHomologicalComplex c).obj L) :
    ((homModule O ρ).mapHomologicalComplex c).map (homModuleComplexPreimage hρ hK φ) = φ := by
  ext j : 1
  simp [homModuleComplexPreimage]

/-- A homotopy between images under `Hom(O, -)` of morphisms of complexes with retract source
terms, lifted to a homotopy between the morphisms. -/
def homModulePreimageHomotopy {K L : HomologicalComplex C c}
    (hK : ∀ j, IsRetractOfFiniteFree O (K.X j)) {f₁ f₂ : K ⟶ L}
    (H : Homotopy (((homModule O ρ).mapHomologicalComplex c).map f₁)
      (((homModule O ρ).mapHomologicalComplex c).map f₂)) :
    Homotopy f₁ f₂ where
  hom i j := homModulePreimage hρ (hK i) (H.hom i j)
  zero i j hij := homModule_map_injective hρ (hK i)
    (by simp only [homModule_map_homModulePreimage, Functor.map_zero, H.zero i j hij])
  comm i := homModule_map_injective hρ (hK i) (by simp [dsimp% H.comm i, dNext, prevD])

/-- **Homotopy equivalences are detected by `Hom(O, -)`** between complexes all of whose terms
are retracts of finite free objects. -/
lemma nonempty_homotopyEquiv_of_homModule {K L : HomologicalComplex C c}
    (hK : ∀ j, IsRetractOfFiniteFree O (K.X j)) (hL : ∀ j, IsRetractOfFiniteFree O (L.X j))
    (e : HomotopyEquiv (((homModule O ρ).mapHomologicalComplex c).obj K)
      (((homModule O ρ).mapHomologicalComplex c).obj L)) :
    Nonempty (HomotopyEquiv K L) :=
  ⟨{ hom := homModuleComplexPreimage hρ hK e.hom
     inv := homModuleComplexPreimage hρ hL e.inv
     homotopyHomInvId := homModulePreimageHomotopy hρ hK
       (by simpa using e.homotopyHomInvId)
     homotopyInvHomId := homModulePreimageHomotopy hρ hL
       (by simpa using e.homotopyInvHomId) }⟩

end Lift

/-- Extension of scalars is additive. -/
instance _root_.ModuleCat.extendScalars_additive {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    (f : R →+* S) : (ModuleCat.extendScalars.{u, w, max w v} f).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (ModuleCat.extendScalars.{u, w, max w v} f)
  exact Functor.additive_of_preservesBinaryBiproducts _

section EndConj

variable {D : Type u'} [Category.{v} D] [Preadditive D] {O : C} {O' : D}
  (F : C ⥤ D) [hF : F.Additive] (e : F.obj O ≅ O')

/-- Conjugation `End O → End O'`, `a ↦ e⁻¹ ≫ F a ≫ e`. -/
def endConj : End O →+* End O' where
  toFun a := e.inv ≫ F.map (a : O ⟶ O) ≫ e.hom
  map_one' := by
    rw [End.ext_iff, End.one_asHom]
    change e.inv ≫ F.map (𝟙 O) ≫ e.hom = 𝟙 O'
    simp
  map_mul' a b := by
    rw [End.ext_iff, End.mul_asHom]
    change e.inv ≫ F.map (b.asHom ≫ a.asHom) ≫ e.hom =
      (e.inv ≫ F.map b.asHom ≫ e.hom) ≫ e.inv ≫ F.map a.asHom ≫ e.hom
    rw [F.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  map_zero' := by
    rw [End.ext_iff]
    change e.inv ≫ F.map (0 : O ⟶ O) ≫ e.hom = (0 : O' ⟶ O')
    simp
  map_add' a b := by
    rw [End.ext_iff]
    change e.inv ≫ F.map (a.asHom + b.asHom) ≫ e.hom =
      (e.inv ≫ F.map a.asHom ≫ e.hom : O' ⟶ O') + e.inv ≫ F.map b.asHom ≫ e.hom
    rw [F.map_add, Preadditive.add_comp, Preadditive.comp_add]

end EndConj

/-! ### Base change along an additive functor -/

section BaseChange

open scoped ChangeOfRings TensorProduct

variable {C : Type u} [Category.{w + 1} C] [Preadditive C] {R : Type w} [CommRing R]
  {O : C} {ρ : R →+* End O} {D : Type u'} [Category.{w + 1} D] [Preadditive D]
  {R' : Type w} [CommRing R']
  {O' : D} (ρ' : R' →+* End O') (hρ' : Function.Bijective ρ')
  (F : C ⥤ D) [hF : F.Additive] (e : F.obj O ≅ O')

/-- The ring map `R → R'` induced by `F` and `e : F O ≅ O'`: `ρ' (ψ a) = e⁻¹ ≫ F (ρ a) ≫ e`. -/
def baseChangeRingHom : R →+* R' :=
  (RingEquiv.ofBijective ρ' hρ').symm.toRingHom.comp ((endConj F e).comp ρ)

/-- `ρ' (ψ a) = e⁻¹ ≫ F (ρ a) ≫ e` for the ring map `ψ = baseChangeRingHom ρ' hρ' F e`. -/
lemma map_baseChangeRingHom (a : R) :
    ρ' (baseChangeRingHom (ρ := ρ) ρ' hρ' F e a) = e.inv ≫ F.map (ρ a : O ⟶ O) ≫ e.hom :=
  (RingEquiv.ofBijective ρ' hρ').apply_symm_apply ((endConj F e).comp ρ a)

/-- The `ψ`-semilinear map `Hom(O, M) → Hom(O', F M)`, `s ↦ e⁻¹ ≫ F s`. -/
def homModuleBaseChangeAux (M : C) :
    (homModule O ρ).obj M ⟶ (ModuleCat.restrictScalars (baseChangeRingHom (ρ := ρ) ρ' hρ' F e)).obj
      ((homModule O' ρ').obj (F.obj M)) :=
  ModuleCat.semilinearMapAddEquiv _ _ _
    { toFun s := HomFrom.mk (ρ := ρ') (e.inv ≫ F.map (HomFrom.hom (ρ := ρ) s))
      map_add' s t := by
        apply HomFrom.ext (R := R') (ρ := ρ')
        change e.inv ≫ F.map (HomFrom.hom (ρ := ρ) s + HomFrom.hom (ρ := ρ) t) =
          e.inv ≫ F.map (HomFrom.hom (ρ := ρ) s) + e.inv ≫ F.map (HomFrom.hom (ρ := ρ) t)
        rw [F.map_add, Preadditive.comp_add]
      map_smul' r s := by
        apply HomFrom.ext (R := R') (ρ := ρ')
        change e.inv ≫ F.map ((ρ r).asHom ≫ HomFrom.hom (ρ := ρ) s) =
          ρ' (baseChangeRingHom (ρ := ρ) ρ' hρ' F e r) ≫ e.inv ≫ F.map (HomFrom.hom (ρ := ρ) s)
        rw [map_baseChangeRingHom]
        simp }

/-- **The base-change comparison** `R' ⊗_R Hom(O, M) ⟶ Hom(O', F M)`, adjoint to
`s ↦ e⁻¹ ≫ F s`. -/
def homModuleBaseChange :
    homModule O ρ ⋙ ModuleCat.extendScalars.{w, w, w + 1} (baseChangeRingHom (ρ := ρ) ρ' hρ' F e) ⟶
      F ⋙ homModule O' ρ' where
  app M := ((ModuleCat.extendRestrictScalarsAdj.{w + 1} _).homEquiv _ _).symm
    (homModuleBaseChangeAux ρ' hρ' F e M)
  naturality M N f := by
    dsimp only [Functor.comp_obj, Functor.comp_map]
    rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
    apply HomFrom.ext (R := R') (ρ := ρ')
    change e.inv ≫ F.map (HomFrom.hom (ρ := ρ) s ≫ f) =
      (e.inv ≫ F.map (HomFrom.hom (ρ := ρ) s)) ≫ F.map f
    simp

/-- The comparison on a pure tensor: `r' ⊗ s ↦ r' • (e⁻¹ ≫ F s)`. -/
lemma homModuleBaseChange_app_tmul (M : C) (r' : R') (s : (homModule O ρ).obj M) :
    ((homModuleBaseChange (ρ := ρ) ρ' hρ' F e).app M).hom
        (r' ⊗ₜ[R, baseChangeRingHom (ρ := ρ) ρ' hρ' F e] s) =
      r' • (HomFrom.mk (ρ := ρ') (e.inv ≫ F.map (HomFrom.hom (ρ := ρ) s)) :
        (homModule O' ρ').obj (F.obj M)) :=
  rfl

/-- The base-change comparison is bijective at `O`. -/
lemma bijective_homModuleBaseChange_app_self (hρ : Function.Bijective ρ) :
    Function.Bijective ((homModuleBaseChange (ρ := ρ) ρ' hρ' F e).app O).hom := by
  set ψ := baseChangeRingHom (ρ := ρ) ρ' hρ' F e
  set β := (homModuleBaseChange (ρ := ρ) ρ' hρ' F e).app O
  let ρe := RingEquiv.ofBijective ρ' hρ'
  let one : (homModule O ρ).obj O := HomFrom.mk (ρ := ρ) (𝟙 O)
  let u : (ModuleCat.extendScalars.{w, w, w + 1} ψ).obj ((homModule O ρ).obj O) :=
    (ModuleCat.extendRestrictScalarsAdj.{w + 1} ψ).unit.app _ one
  have hβu : ∀ t : R', β.hom (t • u) = HomFrom.mk (ρ := ρ') (ρ' t ≫ e.inv) := by
    intro t
    rw [β.hom.map_smul]
    show t • β.hom ((1 : R') ⊗ₜ[R, ψ] one) = _
    rw [homModuleBaseChange_app_tmul, one_smul]
    apply HomFrom.ext (R := R') (ρ := ρ')
    show (ρ' t).asHom ≫ e.inv ≫ F.map (𝟙 O) = (ρ' t).asHom ≫ e.inv
    rw [F.map_id, Category.comp_id]
  let toR : (homModule O' ρ').obj (F.obj O) →ₗ[R'] R' :=
    { toFun x := ρe.symm (HomFrom.hom (ρ := ρ') x ≫ e.hom)
      map_add' x y := by
        show ρe.symm ((HomFrom.hom (ρ := ρ') x + HomFrom.hom (ρ := ρ') y) ≫ e.hom) = _
        rw [Preadditive.add_comp]
        exact map_add ρe.symm _ _
      map_smul' r x := by
        show ρe.symm (((ρ' r).asHom ≫ HomFrom.hom (ρ := ρ') x) ≫ e.hom) =
          r * ρe.symm (HomFrom.hom (ρ := ρ') x ≫ e.hom)
        obtain ⟨s, hs⟩ := hρ'.2 (HomFrom.hom (ρ := ρ') x ≫ e.hom)
        have hs' : ρe s = HomFrom.hom (ρ := ρ') x ≫ e.hom := hs
        rw [Category.assoc, ← hs', RingEquiv.symm_apply_apply]
        apply ρe.injective
        rw [RingEquiv.apply_symm_apply, map_mul]
        have hs'' : (ρe s).asHom = HomFrom.hom (ρ := ρ') x ≫ e.hom := congrArg End.asHom hs'
        apply End.ext
        rw [End.mul_asHom, ← hs'']
        show (ρe s * ρe r).asHom = (ρe r * ρe s).asHom
        rw [← map_mul, ← map_mul, mul_comm] }
  let Λ : (homModule O' ρ').obj (F.obj O) →ₗ[R']
      ((ModuleCat.extendScalars.{w, w, w + 1} ψ).obj ((homModule O ρ).obj O)) :=
    (LinearMap.toSpanSingleton R'
      ((ModuleCat.extendScalars.{w, w, w + 1} ψ).obj ((homModule O ρ).obj O)) u).comp toR
  let ιT : (homModule O ρ).obj O →
      (ModuleCat.extendScalars.{w, w, w + 1} ψ).obj ((homModule O ρ).obj O) :=
    fun m => (1 : R') ⊗ₜ[R, ψ] m
  have hΛm : ∀ m : (homModule O ρ).obj O, Λ (β.hom (ιT m)) = ιT m := by
    intro m
    obtain ⟨a, ha, hm⟩ := exists_smul_id_eq hρ m
    show Λ (β.hom ((1 : R') ⊗ₜ[R, ψ] m)) = _
    rw [homModuleBaseChange_app_tmul, one_smul]
    show toR (HomFrom.mk (ρ := ρ') (e.inv ≫ F.map (HomFrom.hom (ρ := ρ) m))) • u = _
    have h1 : toR (HomFrom.mk (ρ := ρ') (e.inv ≫ F.map (HomFrom.hom (ρ := ρ) m))) = ψ a := by
      show ρe.symm ((e.inv ≫ F.map (HomFrom.hom (ρ := ρ) m)) ≫ e.hom) =
        ρe.symm (e.inv ≫ F.map (ρ a : O ⟶ O) ≫ e.hom)
      rw [ha, Category.assoc]
    have h3 : ψ a • u = ψ a ⊗ₜ[R, ψ] one :=
      (ModuleCat.ExtendScalars.smul_tmul ψ (ψ a) 1 one).trans (by rw [mul_one])
    have h4 : (1 : R') ⊗ₜ[R, ψ] m = ψ a ⊗ₜ[R, ψ] one := by
      rw [hm]
      refine (TensorProduct.smul_tmul (R := R) a
        (show (ModuleCat.restrictScalars ψ).obj (ModuleCat.of R' R') from (1 : R'))
          one).symm.trans ?_
      congr 1
      exact (ModuleCat.restrictScalars.smul_def ψ (M := ModuleCat.of R' R') a
        (show (ModuleCat.restrictScalars ψ).obj (ModuleCat.of R' R') from (1 : R'))).trans
        (mul_one (ψ a))
    rw [h1]
    exact h3.trans h4.symm
  have hΛ' : β ≫ ModuleCat.ofHom Λ = 𝟙 _ := ModuleCat.ExtendScalars.hom_ext fun m => hΛm m
  have hΛ : ∀ x, Λ (β.hom x) = x := fun x =>
    congrArg (fun φ => (ConcreteCategory.hom φ) x) hΛ'
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · simpa only [hΛ] using congrArg Λ hxy
  · obtain ⟨t, ht⟩ := hρ'.2 (HomFrom.hom (ρ := ρ') x ≫ e.hom)
    refine ⟨t • u, ?_⟩
    rw [hβu]
    apply HomFrom.ext (R := R') (ρ := ρ')
    show ρ' t ≫ e.inv = HomFrom.hom (ρ := ρ') x
    rw [ht, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end BaseChange

/-! ### Natural transformations between additive functors on retracts -/

section RetractIso

variable {O} {E : Type*} [Category E] [Preadditive E] [HasFiniteBiproducts C]
  {G H : C ⥤ E} [G.Additive] [H.Additive] (α : G ⟶ H)

/-- A natural transformation between additive functors which is an isomorphism at `O` is an
isomorphism at every retract of a finite free object. -/
lemma isIso_app_of_isRetractOfFiniteFree [IsIso (α.app O)] {M : C}
    (hM : IsRetractOfFiniteFree O M) : IsIso (α.app M) := by
  obtain ⟨n, i, p, hip⟩ := hM
  have hB : IsIso (α.app (⨁ fun _ : Fin n => O)) := by
    refine ⟨∑ j, H.map (biproduct.π (fun _ : Fin n => O) j) ≫ inv (α.app O) ≫
      G.map (biproduct.ι (fun _ : Fin n => O) j), ?_, ?_⟩
    · rw [Preadditive.comp_sum]
      calc ∑ j, α.app _ ≫ H.map (biproduct.π (fun _ : Fin n => O) j) ≫ inv (α.app O) ≫
            G.map (biproduct.ι (fun _ : Fin n => O) j)
          = ∑ j, G.map (biproduct.π (fun _ : Fin n => O) j ≫
              biproduct.ι (fun _ : Fin n => O) j) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← α.naturality_assoc, IsIso.hom_inv_id_assoc, G.map_comp]
        _ = 𝟙 _ := by rw [← G.map_sum, biproduct.total, G.map_id]
    · rw [Preadditive.sum_comp]
      calc ∑ j, (H.map (biproduct.π (fun _ : Fin n => O) j) ≫ inv (α.app O) ≫
            G.map (biproduct.ι (fun _ : Fin n => O) j)) ≫ α.app _
          = ∑ j, H.map (biproduct.π (fun _ : Fin n => O) j ≫
              biproduct.ι (fun _ : Fin n => O) j) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Category.assoc, Category.assoc, α.naturality, IsIso.inv_hom_id_assoc,
              H.map_comp]
        _ = 𝟙 _ := by rw [← H.map_sum, biproduct.total, H.map_id]
  refine ⟨H.map i ≫ inv (α.app _) ≫ G.map p, ?_, ?_⟩
  · rw [← α.naturality_assoc, IsIso.hom_inv_id_assoc, ← G.map_comp, hip, G.map_id]
  · rw [Category.assoc, Category.assoc, α.naturality, IsIso.inv_hom_id_assoc, ← H.map_comp, hip,
      H.map_id]

end RetractIso

section BaseChangeIso

variable {C : Type u} [Category.{w + 1} C] [Preadditive C] {R : Type w} [CommRing R]
  {O : C} {ρ : R →+* End O} {D : Type u'} [Category.{w + 1} D] [Preadditive D]
  {R' : Type w} [CommRing R']
  {O' : D} (ρ' : R' →+* End O') (hρ' : Function.Bijective ρ')
  (F : C ⥤ D) [hF : F.Additive] (e : F.obj O ≅ O') [HasFiniteBiproducts C]

/-- Extension of scalars between rings in the universe `w` on modules in the universe `w + 1` is
additive. -/
local instance extendScalars_additive_succ {R₁ R₂ : Type w} [CommRing R₁] [CommRing R₂]
    (f : R₁ →+* R₂) : (ModuleCat.extendScalars.{w, w, w + 1} f).Additive :=
  ModuleCat.extendScalars_additive.{w + 1, w, w} f

/-- **The base-change comparison is an isomorphism at every retract of a finite free object.** -/
lemma isIso_homModuleBaseChange_app (hρ : Function.Bijective ρ) {M : C}
    (hM : IsRetractOfFiniteFree O M) : IsIso ((homModuleBaseChange (ρ := ρ) ρ' hρ' F e).app M) := by
  have : IsIso ((homModuleBaseChange (ρ := ρ) ρ' hρ' F e).app O) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_homModuleBaseChange_app_self ρ' hρ' F e hρ)
  exact isIso_app_of_isRetractOfFiniteFree _ hM

/-- `F` carries retracts of finite free objects to retracts of finite free objects. -/
lemma IsRetractOfFiniteFree.map [HasFiniteBiproducts D] (e : F.obj O ≅ O') {M : C}
    (hM : IsRetractOfFiniteFree O M) : IsRetractOfFiniteFree O' (F.obj M) := by
  obtain ⟨n, i, p, hip⟩ := hM
  let b : F.obj (⨁ fun _ : Fin n => O) ≅ ⨁ fun _ : Fin n => O' :=
    F.mapBiproduct _ ≪≫ biproduct.mapIso fun _ => e
  exact ⟨n, F.map i ≫ b.hom, b.inv ≫ F.map p, by simp [← F.map_comp, hip]⟩

/-- **Base change of a complex with retract terms.** For a complex `K` all of whose terms are
retracts of finite free objects, `R' ⊗_R Hom(O, K) ≅ Hom(O', F K)` as complexes. -/
def homModuleBaseChangeComplexIso (hρ : Function.Bijective ρ) {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex C c) (hK : ∀ j, IsRetractOfFiniteFree O (K.X j)) :
    ((ModuleCat.extendScalars.{w, w, w + 1}
        (baseChangeRingHom (ρ := ρ) ρ' hρ' F e)).mapHomologicalComplex c).obj
        (((homModule O ρ).mapHomologicalComplex c).obj K) ≅
      ((homModule O' ρ').mapHomologicalComplex c).obj ((F.mapHomologicalComplex c).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => have := isIso_homModuleBaseChange_app ρ' hρ' F e hρ (hK j)
      asIso ((homModuleBaseChange (ρ := ρ) ρ' hρ' F e).app (K.X j)))
    (fun i j _ => ((homModuleBaseChange (ρ := ρ) ρ' hρ' F e).naturality (K.d i j)).symm)

end BaseChangeIso

end CategoryTheory
