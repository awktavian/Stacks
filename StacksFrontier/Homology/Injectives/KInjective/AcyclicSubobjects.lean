module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Acyclicity along short exact sequences, subobject preimages, and filtered colimits

Elementary facts about acyclic complexes and about subobjects: acyclicity propagates along a short
exact sequence of complexes, the preimage of a subobject of a cokernel is an extension of the
kernel by that subobject, and a filtered colimit of acyclic complexes is acyclic when filtered
colimits are exact.

## Main results

* `Stacks.Injectives.acyclic_middle_of_shortExact` and
  `Stacks.Injectives.acyclic_right_of_shortExact`: in a short exact sequence of cochain
  complexes, acyclicity of the two outer terms gives acyclicity of the middle one, and
  acyclicity of the first two gives acyclicity of the third.
* `Stacks.Injectives.pullbackPreimage_shortExact`: for a monomorphism `i : Y ⟶ Z` in an
  abelian category and a subobject `T` of `cokernel i`, the preimage of `T` along the
  projection sits in a short exact sequence with `Y` on the left and `T` on the right.
* `Stacks.Injectives.subobject_le_pullback_of_comp_zero_subobject`: a subobject annihilated by
  a morphism lies below every preimage along it.
* `Stacks.Injectives.acyclic_of_filtered_colimit`: a colimit of acyclic cochain complexes over
  a shape whose colimits are exact is acyclic.

## References

* [Stacks Project, Tag 079L](https://stacks.math.columbia.edu/tag/079L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.Injectives

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The homology of an acyclic cochain complex vanishes in every degree. -/
private theorem isZero_homology_of_acyclic {K : CochainComplex C ℤ} (h : K.Acyclic) (n : ℤ) :
    IsZero (K.homology n) :=
  (HomologicalComplex.exactAt_iff_isZero_homology K n).1 (h n)

/-- In a short exact sequence of cochain complexes, the middle term is acyclic as soon as the
two outer terms are. -/
theorem acyclic_middle_of_shortExact
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (h₁ : S.X₁.Acyclic) (h₃ : S.X₃.Acyclic) : S.X₂.Acyclic := fun n =>
  (HomologicalComplex.exactAt_iff_isZero_homology S.X₂ n).2 <|
    (hS.homology_exact₂ n).isZero_X₂ ((isZero_homology_of_acyclic h₁ n).eq_of_src _ _)
      ((isZero_homology_of_acyclic h₃ n).eq_of_tgt _ _)

/-- In a short exact sequence of cochain complexes, the third term is acyclic as soon as the
first two are. -/
theorem acyclic_right_of_shortExact
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (h₁ : S.X₁.Acyclic) (h₂ : S.X₂.Acyclic) : S.X₃.Acyclic := fun n =>
  (HomologicalComplex.exactAt_iff_isZero_homology S.X₃ n).2 <|
    (hS.homology_exact₃ n (n + 1) (by simp)).isZero_X₂
      ((isZero_homology_of_acyclic h₂ n).eq_of_src _ _)
      ((isZero_homology_of_acyclic h₁ (n + 1)).eq_of_tgt _ _)

/-- For a monomorphism `i : Y ⟶ Z` in an abelian category and a subobject `T` of `cokernel i`,
the morphism `i` factors through the preimage of `T` along `cokernel.π i`, and the resulting
sequence from `Y` to the preimage to `T` is short exact. -/
theorem pullbackPreimage_shortExact {Y Z : C}
    (i : Y ⟶ Z) [Mono i] (T : Subobject (cokernel i)) :
    ∃ s : Y ⟶ (Subobject.pullback (cokernel.π i)).obj T,
      s ≫ ((Subobject.pullback (cokernel.π i)).obj T).arrow = i ∧
      ∃ hs : s ≫ Subobject.pullbackπ (cokernel.π i) T = 0,
        ShortComplex.ShortExact
          (ShortComplex.mk s (Subobject.pullbackπ (cokernel.π i) T) hs) := by
  classical
  let q := cokernel.π i
  let P := (Subobject.pullback q).obj T
  let p := Subobject.pullbackπ q T
  let j := P.arrow
  let hp := Subobject.isPullback q T
  let s := hp.lift (0 : Y ⟶ T) i (by simp [q])
  have hsj : s ≫ j = i := hp.lift_snd 0 i (by simp [q])
  have hs : s ≫ p = 0 := by simp [s, p]
  have : Mono s := ⟨fun {_} a b hab => by
    apply (cancel_mono i).1
    have h := congrArg (fun k => k ≫ j) hab
    rw [Category.assoc, hsj, Category.assoc, hsj] at h
    exact h⟩
  have hker : IsLimit (KernelFork.ofι s hs) := by
    apply KernelFork.IsLimit.ofι' s hs
    intro W g hg
    have hgq : (g ≫ j) ≫ q = 0 := by
      calc
        (g ≫ j) ≫ q = g ≫ (j ≫ q) := Category.assoc _ _ _
        _ = g ≫ (p ≫ T.arrow) := by rw [← hp.w]
        _ = (g ≫ p) ≫ T.arrow := (Category.assoc _ _ _).symm
        _ = 0 := by simp [hg]
    let u := Abelian.monoLift i (g ≫ j) hgq
    have hui : u ≫ i = g ≫ j := Abelian.monoLift_comp i (g ≫ j) hgq
    refine ⟨u, ?_⟩
    apply hp.hom_ext
    · calc
        (u ≫ s) ≫ p = u ≫ (s ≫ p) := Category.assoc _ _ _
        _ = 0 := by simp [hs]
        _ = g ≫ p := by simp [hg]
    · calc
        (u ≫ s) ≫ j = u ≫ (s ≫ j) := Category.assoc _ _ _
        _ = g ≫ j := by rw [hsj, hui]
  have hS : (ShortComplex.mk s p hs).Exact :=
    ShortComplex.exact_of_f_is_kernel (ShortComplex.mk s p hs) hker
  have : Epi (pullback.fst T.arrow q) := Abelian.epi_pullback_of_epi_g T.arrow q
  have hpE : Epi p := by
    have h : Epi (hp.isoPullback.hom ≫ pullback.fst T.arrow q) := inferInstance
    rw [hp.isoPullback_hom_fst] at h
    exact h
  exact ⟨s, hsj, hs, ShortComplex.ShortExact.mk' hS inferInstance hpE⟩

/-- A monomorphism annihilated by a morphism `q` represents a subobject below the preimage
along `q` of any subobject of the target of `q`. -/
theorem subobject_le_pullback_of_comp_zero {D : Type u}
    [Category.{v} D] [HasZeroMorphisms D] [HasPullbacks D] {X₀ Y₀ : D} (q : X₀ ⟶ Y₀)
    (T : Subobject Y₀) {S₀ : D} (s : S₀ ⟶ X₀) [Mono s]
    (h : s ≫ q = 0) : Subobject.mk s ≤ (Subobject.pullback q).obj T := by
  have hfac : T.Factors (s ≫ q) := by
    rw [h]
    exact (Subobject.factors_iff T 0).2 ⟨0, CategoryTheory.Limits.zero_comp⟩
  have hpull : ((Subobject.pullback q).obj T).Factors s :=
    (CategoryTheory.Limits.pullback_factors_iff q T s).2 hfac
  rw [← Subobject.mk_arrow ((Subobject.pullback q).obj T)]
  exact Subobject.mk_le_mk_of_comm (Subobject.factorThru _ _ hpull)
    (Subobject.factorThru_arrow _ _ hpull)

/-- A subobject annihilated by a morphism `q` lies below the preimage along `q` of any
subobject of the target of `q`. -/
theorem subobject_le_pullback_of_comp_zero_subobject {D : Type u}
    [Category.{v} D] [HasZeroMorphisms D] [HasPullbacks D] {X₀ Y₀ : D}
    (q : X₀ ⟶ Y₀) (S : Subobject X₀) (T : Subobject Y₀)
    (h : S.arrow ≫ q = 0) : S ≤ (Subobject.pullback q).obj T := by
  simpa only [Subobject.mk_arrow] using
    (subobject_le_pullback_of_comp_zero q T S.arrow h)

/-- A colimit of acyclic cochain complexes over a shape `J` is acyclic when colimits of shape `J`
are exact. -/
theorem acyclic_of_filtered_colimit.{t, q}
    {J : Type t} [Category.{q} J] [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C]
    (D : J ⥤ CochainComplex C ℤ) (c : Cocone D) (hc : IsColimit c)
    (hD : ∀ j, (D.obj j).Acyclic) : c.pt.Acyclic := by
  intro n
  let E₁ := D ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) (n - 1)
  let E₂ := D ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n
  let E₃ := D ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) (n + 1)
  let α : E₁ ⟶ E₂ := {
    app j := (D.obj j).d (n - 1) n
    naturality := fun i j f => (D.map f).comm' (n - 1) n (by simp) }
  let β : E₂ ⟶ E₃ := {
    app j := (D.obj j).d n (n + 1)
    naturality := fun i j f => (D.map f).comm' n (n + 1) (by simp) }
  let S : ShortComplex (J ⥤ C) := ShortComplex.mk α β (by
    ext j
    exact (D.obj j).d_comp_d (n - 1) n (n + 1))
  have hS : S.Exact := by
    let F : ∀ _ : J, (J ⥤ C) ⥤ C := fun j => (evaluation J C).obj j
    have hF : JointlyReflectIsomorphisms F := ⟨by
      intro X Y f
      exact (NatTrans.isIso_iff_isIso_app f).2 (fun j => by
        show IsIso ((F j).map f)
        infer_instance)⟩
    apply (hF.exact_iff S).2
    intro j
    let Sj := S.map (F j)
    let Tj := HomologicalComplex.sc' (D.obj j) (n - 1) n (n + 1)
    have hj' : Tj.Exact :=
      (HomologicalComplex.exactAt_iff' (D.obj j) (n - 1) n (n + 1)
        (by simp) (by simp)).1 (hD j n)
    have e : Sj ≅ Tj := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        dsimp [Sj, Tj, S, F, α, E₁, E₂]
        exact (Category.id_comp _).trans (Category.comp_id _).symm)
      (by
        dsimp [Sj, Tj, S, F, β, E₂, E₃]
        exact (Category.id_comp _).trans (Category.comp_id _).symm)
    exact (ShortComplex.exact_iff_of_iso e).2 hj'
  let c₁ := (HomologicalComplex.eval C (ComplexShape.up ℤ) (n - 1)).mapCocone c
  let c₂ := (HomologicalComplex.eval C (ComplexShape.up ℤ) n).mapCocone c
  let c₃ := (HomologicalComplex.eval C (ComplexShape.up ℤ) (n + 1)).mapCocone c
  have hc₁ : IsColimit c₁ := isColimitOfPreserves _ hc
  have hc₂ : IsColimit c₂ := isColimitOfPreserves _ hc
  have hc₃ : IsColimit c₃ := isColimitOfPreserves _ hc
  let f := c.pt.d (n - 1) n
  let g := c.pt.d n (n + 1)
  have hf : ∀ j, c₁.ι.app j ≫ f = α.app j ≫ c₂.ι.app j := fun j =>
    (c.ι.app j).comm' (n - 1) n (by simp)
  have hg : ∀ j, c₂.ι.app j ≫ g = β.app j ≫ c₃.ι.app j := fun j =>
    (c.ι.app j).comm' n (n + 1) (by simp)
  have hcol := Limits.colim.exact_mapShortComplex (S := S) hS hc₁
    (c₂ := c₂) hc₂ (c₃ := c₃) hc₃ f g hf hg
  rw [HomologicalComplex.exactAt_iff' (c.pt) (n - 1) n (n + 1) (by simp) (by simp)]
  show (Limits.colim.mapShortComplex S hc₁ c₂ c₃ f g hf hg).Exact
  exact hcol

end Stacks.Injectives
