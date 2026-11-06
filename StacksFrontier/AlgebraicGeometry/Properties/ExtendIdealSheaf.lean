module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Gluing quasi-coherent ideal sheaves from ideals on a finite affine cover

`AlgebraicGeometry.Scheme.IdealSheafData` presents a quasi-coherent sheaf of ideals on a scheme
`X` by its ideal on *every* affine open, together with the compatibility with localization. That
presentation is excellent for *comparing* ideal sheaves — `Scheme.IdealSheafData.le_of_iSup_eq_top`
tests an inequality on an affine cover — but it gives no way to *build* one from local data, since
the structure asks for an ideal on every affine open at once.

This file supplies the missing construction. The ingredient is
`Stacks.IdealSheaf.extendAffineIdeal`: for an ideal `I` of `Γ(X, V)` on an affine open `V` it is
the largest quasi-coherent ideal sheaf whose ideal on `V` is contained in `I`, realised as the
kernel of `Spec (Γ(X, V) ⧸ I) ⟶ Spec Γ(X, V) ⟶ X`. Its ideal on every affine open is computable
through `AlgebraicGeometry.Scheme.Hom.ker_apply`, which is what makes the construction usable.
`Stacks.IdealSheaf.glueAffineIdeals` is then the infimum of these extensions over a finite family
of affine opens, and for a family that is compatible on overlaps its ideal on an affine open
contained in a member of the family is the expected restriction.

## Main definitions

* `Stacks.IdealSheaf.extendAffineIdeal` is the largest quasi-coherent ideal sheaf on `X` whose
  ideal on an affine open `V` is contained in a given ideal of `Γ(X, V)`.
* `Stacks.IdealSheaf.IsCompatibleOnAffineOpens` says that a family of ideals on affine opens has
  the same restriction to every affine open contained in two members of the family.
* `Stacks.IdealSheaf.glueAffineIdeals` is the quasi-coherent ideal sheaf glued from a finite
  family of ideals on affine opens.

## Main results

* `Stacks.IdealSheaf.ideal_extendAffineIdeal_of_le` computes the ideal of an extension on an
  affine open contained in the one the ideal lives on.
* `Stacks.IdealSheaf.mem_ideal_extendAffineIdeal_of_locally`: membership in the ideal of an
  extension on an affine open `W` may be tested on the basic opens of `W` contained in `V`.
  There is no condition on the part of `W` away from `V`, which is what makes an extension big
  enough to be glued with others.
* `Stacks.IdealSheaf.ideal_glueAffineIdeals` computes the ideal of the glued sheaf, so gluing
  really does recover the given local data.
* `Stacks.IdealSheaf.glueAffineIdeals_le` and `Stacks.IdealSheaf.fg_ideal_glueAffineIdeals`: the
  glued sheaf is contained in an ambient ideal sheaf whenever the local data is, and it is
  finitely generated on *every* affine open as soon as the local data is finitely generated and
  the family covers `X`.
* `Stacks.IdealSheaf.exists_fg_le_of_mem` is Tag 01PF for quasi-coherent sheaves of ideals: on a
  quasi-compact and quasi-separated scheme, a section of a quasi-coherent ideal sheaf `K` over an
  affine open lies in a finite type quasi-coherent subsheaf of ideals of `K`.
* `Stacks.IdealSheaf.le_iSup_fg` is Tag 01PG for quasi-coherent sheaves of ideals: such a `K` is
  the supremum of its finite type quasi-coherent subsheaves of ideals.

Neither of the last two carries a `@[stacks]` attribute: Tags 01PF and 01PG are statements about
an arbitrary quasi-coherent module and an arbitrary quasi-compact open, and what is proved here is
their special case for sheaves of ideals, which is what the limit half of Tag 0EV9 consumes.

## Implementation notes

Affine opens appear as a pair `(V, hV : IsAffineOpen V)` rather than as an element of
`X.affineOpens`: the latter is a `Set`, so the second component of an element has type
`↑V ∈ X.affineOpens` rather than `IsAffineOpen ↑V`, and terms built from it are not type-correct
at `implicit` transparency, which breaks `rw`.

Quasi-separatedness of `X` enters only to make the morphisms whose kernels are taken
quasi-compact, which is what `AlgebraicGeometry.Scheme.Hom.ker_apply` needs; with the source
affine this is automatic from `AlgebraicGeometry.quasiCompact_of_compactSpace`-style instances.

The finite generation statement is the local-to-global step for ideals, `Ideal`
`.fg_of_localizationSpan`, applied to a cover of an arbitrary affine open by basic opens each
contained in a member of the family. Transporting it to the sections over a basic open uses
`AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`.

## References

* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.IdealSheafData TopologicalSpace

universe u

namespace Stacks.IdealSheaf

/-- The restriction map of a presheaf along an inclusion of opens which are in fact equal is the
transport along that equality. -/
theorem map_homOfLE_of_eq {Y : Scheme.{u}} {A B : Y.Opens} (h : A ≤ B) (e : B = A) :
    Y.presheaf.map (homOfLE h).op = eqToHom (by rw [e]) := by
  subst e
  simp

/-- The kernel of `Scheme.Hom.appLE` on the whole preimage is the kernel of `Scheme.Hom.app`.
Stated with the preimage given by an equation so that it can be used at a spelling of the
preimage other than the literal one. -/
theorem ker_appLE_eq_ker_app {Y Z : Scheme.{u}} (f : Y ⟶ Z) (U : Z.Opens) {W : Y.Opens}
    (e : f ⁻¹ᵁ U = W) :
    RingHom.ker (f.appLE U W (e ▸ le_rfl)).hom = RingHom.ker (f.app U).hom := by
  subst e
  rw [Scheme.Hom.appLE_eq_app]

variable {X : Scheme.{u}} {V : X.Opens}

section Ker

variable (hV : IsAffineOpen V) {S : CommRingCat.{u}} (φ : Γ(X, V) ⟶ S)

/-- An affine open is the preimage of itself under any morphism factoring through its
`AlgebraicGeometry.IsAffineOpen.fromSpec`. -/
theorem preimage_eq_top : (Spec.map φ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤ := by
  simp [hV.fromSpec_preimage_self]

/-- On global sections, a morphism `Spec S ⟶ X` factoring through the affine open `V` is `φ`
itself, read through `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
theorem appLE_top : (Spec.map φ ≫ hV.fromSpec).appLE V ⊤ (by rw [preimage_eq_top]) =
    φ ≫ (Scheme.ΓSpecIso _).inv := by
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ)
      hV.fromSpec V ⊤ ⊤ (by rw [hV.fromSpec_preimage_self]) (by simp)]
  dsimp only [Scheme.Hom.appLE]
  rw [hV.fromSpec_app_self, map_homOfLE_of_eq _ hV.fromSpec_preimage_self]
  simp only [Category.assoc, Opens.map_top, eqToHom_op, eqToHom_map, eqToHom_trans,
    eqToHom_refl, Category.id_comp, homOfLE_refl, op_id]
  exact (Scheme.ΓSpecIso_inv_naturality φ).symm

variable [QuasiSeparatedSpace X]

/-- The ideal on `V` of the kernel of a morphism `Spec S ⟶ X` factoring through the affine open
`V` is the kernel of the corresponding ring map. -/
theorem ideal_ker_self : (Spec.map φ ≫ hV.fromSpec).ker.ideal ⟨V, hV⟩ = RingHom.ker φ.hom := by
  rw [Scheme.Hom.ker_apply, ← ker_appLE_eq_ker_app _ V (preimage_eq_top hV φ), appLE_top,
    CommRingCat.hom_comp]
  exact RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso S).symm.commRingCatIsoToRingEquiv

/-- Membership in the ideal of the kernel of a morphism factoring through the affine open `V` is
local on the basic opens contained in `V`: a section over an affine open `W` lies in it as soon
as its restriction to every basic open of `W` contained in `V` does. No condition is imposed on
the part of `W` away from `V`, since the morphism does not meet it. -/
theorem mem_ideal_ker_of_locally {W : X.Opens} (hW : IsAffineOpen W) (s : Γ(X, W))
    (h : ∀ r : Γ(X, W), X.basicOpen r ≤ V →
      X.presheaf.map (homOfLE (X.basicOpen_le r)).op s ∈
        (Spec.map φ ≫ hV.fromSpec).ker.ideal ⟨X.basicOpen r, hW.basicOpen r⟩) :
    s ∈ (Spec.map φ ≫ hV.fromSpec).ker.ideal ⟨W, hW⟩ := by
  set g := Spec.map φ ≫ hV.fromSpec with hg
  have hrange : Set.range g.base ⊆ (V : Set X) := by
    rw [hg, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← hV.range_fromSpec]
    exact Set.image_subset_range _ _
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  refine (Spec S).IsSheaf.section_ext (U := Opposite.op (g ⁻¹ᵁ W)) fun p hp ↦ ?_
  obtain ⟨r, hrle, hpr⟩ :=
    hW.exists_basicOpen_le (V := W ⊓ V) ⟨g.base p, ⟨hp, hrange ⟨p, rfl⟩⟩⟩ hp
  refine ⟨g ⁻¹ᵁ X.basicOpen r, fun x hx ↦ le_trans hrle inf_le_left hx, hpr, ?_⟩
  have hs := h r (hrle.trans inf_le_right)
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at hs
  have key : g.app W ≫ (Spec S).presheaf.map
        (homOfLE (((Opens.map g.base).map (homOfLE (X.basicOpen_le r))).le)).op =
      X.presheaf.map (homOfLE (X.basicOpen_le r)).op ≫ g.app (X.basicOpen r) := by
    rw [← Scheme.Hom.appLE_eq_app (f := g) (U := X.basicOpen r), Scheme.Hom.map_appLE]
    rfl
  rwa [map_zero, ← ConcreteCategory.comp_apply, key, ConcreteCategory.comp_apply]

end Ker

section Extend

variable [QuasiSeparatedSpace X]

/-- The largest quasi-coherent ideal sheaf on `X` whose ideal on an affine open `V` is contained
in a given ideal `I` of `Γ(X, V)`: the kernel of the composite
`Spec (Γ(X, V) ⧸ I) ⟶ Spec Γ(X, V) ⟶ X`. -/
noncomputable def extendAffineIdeal (hV : IsAffineOpen V) (I : Ideal Γ(X, V)) :
    X.IdealSheafData :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.fromSpec).ker

/-- The ideal of `Stacks.IdealSheaf.extendAffineIdeal hV I` on `V` itself is `I`. -/
theorem ideal_extendAffineIdeal_self (hV : IsAffineOpen V) (I : Ideal Γ(X, V)) :
    (extendAffineIdeal hV I).ideal ⟨V, hV⟩ = I := by
  rw [extendAffineIdeal, ideal_ker_self hV (CommRingCat.ofHom (Ideal.Quotient.mk I))]
  exact Ideal.mk_ker

/-- The ideal of `Stacks.IdealSheaf.extendAffineIdeal hV I` on an affine open contained in `V` is
the restriction of `I`. -/
theorem ideal_extendAffineIdeal_of_le (hV : IsAffineOpen V) (I : Ideal Γ(X, V)) {W : X.Opens}
    (hW : IsAffineOpen W) (h : W ≤ V) :
    (extendAffineIdeal hV I).ideal ⟨W, hW⟩ = I.map (X.presheaf.map (homOfLE h).op).hom := by
  rw [← (extendAffineIdeal hV I).map_ideal (U := ⟨W, hW⟩) (V := ⟨V, hV⟩) h,
    ideal_extendAffineIdeal_self]
  rfl

/-- Membership in the ideal of `Stacks.IdealSheaf.extendAffineIdeal hV I` on an affine open `W`
may be tested on the basic opens of `W` contained in `V` only. -/
theorem mem_ideal_extendAffineIdeal_of_locally (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    {W : X.Opens} (hW : IsAffineOpen W) (s : Γ(X, W))
    (h : ∀ r : Γ(X, W), X.basicOpen r ≤ V →
      X.presheaf.map (homOfLE (X.basicOpen_le r)).op s ∈
        (extendAffineIdeal hV I).ideal ⟨X.basicOpen r, hW.basicOpen r⟩) :
    s ∈ (extendAffineIdeal hV I).ideal ⟨W, hW⟩ :=
  mem_ideal_ker_of_locally hV _ hW s h

end Extend

/-- An ideal of the sections over an affine open is finitely generated as soon as its restriction
to each member of a family of basic opens covering that affine open is. This is the local-to-global
step for finite generation, Tag 00EO, in the form the ideal sheaf lattice needs. -/
theorem fg_of_fg_basicOpen {W : X.Opens} (hW : IsAffineOpen W) (J : Ideal Γ(X, W))
    (t : Set Γ(X, W)) (ht : Ideal.span t = ⊤)
    (h : ∀ r : t, (J.map (X.presheaf.map (homOfLE (X.basicOpen_le r.1)).op).hom).FG) : J.FG := by
  refine Ideal.fg_of_localizationSpan t ht fun g ↦ ?_
  have hloc := hW.isLocalization_basicOpen g.1
  let e : Localization.Away g.1 ≃ₐ[Γ(X, W)] Γ(X, X.basicOpen g.1) :=
    IsLocalization.algEquiv (Submonoid.powers g.1) _ _
  have he : J.map (algebraMap Γ(X, W) (Localization.Away g.1)) =
      (J.map (algebraMap Γ(X, W) Γ(X, X.basicOpen g.1))).map (e.symm : _ →+* _) := by
    rw [Ideal.map_map]
    congr 1
    exact e.symm.toAlgHom.comp_algebraMap.symm
  rw [he]
  exact (h g).map _

/-- An inclusion of ideals of the sections over an affine open may be tested on a family of
basic opens covering that affine open. -/
theorem le_of_le_basicOpen {W : X.Opens} (hW : IsAffineOpen W) {J J' : Ideal Γ(X, W)}
    (t : Set Γ(X, W)) (ht : Ideal.span t = ⊤)
    (h : ∀ r : t, J.map (X.presheaf.map (homOfLE (X.basicOpen_le r.1)).op).hom ≤
      J'.map (X.presheaf.map (homOfLE (X.basicOpen_le r.1)).op).hom) : J ≤ J' := by
  have := hW.isLocalization_basicOpen
  refine Submodule.le_of_isLocalized_span _ ht (fun r ↦ Γ(X, X.basicOpen r.1))
    (fun r ↦ Algebra.linearMap Γ(X, W) Γ(X, X.basicOpen r.1)) fun r ↦ ?_
  simp only [← Submodule.restrictScalars_localized' Γ(X, X.basicOpen r.1),
    Ideal.localized'_eq_map, RingHom.algebraMap_toAlgebra]
  exact h r

/-- The restrictions of the ideals of a quasi-coherent ideal sheaf on two affine opens to an affine
open contained in both agree. -/
private theorem map_ideal_eq_map_ideal {X : Scheme.{u}} (K : X.IdealSheafData) {A B C : X.Opens}
    (hA : IsAffineOpen A) (hB : IsAffineOpen B) (hC : IsAffineOpen C) (hAB : A ≤ B) (hAC : A ≤ C) :
    (K.ideal ⟨B, hB⟩).map (X.presheaf.map (homOfLE hAB).op).hom =
      (K.ideal ⟨C, hC⟩).map (X.presheaf.map (homOfLE hAC).op).hom :=
  (K.map_ideal (U := ⟨A, hA⟩) (V := ⟨B, hB⟩) hAB).trans
    (K.map_ideal (U := ⟨A, hA⟩) (V := ⟨C, hC⟩) hAC).symm

/-- A quasi-coherent ideal sheaf whose ideal is finitely generated on every member of a family of
affine opens covering `X` is finitely generated on *every* affine open. This is the local-to-global
step hidden in Tag 01PB, in the form the ideal sheaf lattice needs: no finiteness of the index
type is required, only that the family covers. -/
theorem fg_ideal_of_fg_cover {K : X.IdealSheafData} {ι : Type*} {V : ι → X.Opens}
    (hV : ∀ i, IsAffineOpen (V i)) (hcover : ⨆ i, V i = ⊤)
    (hfg : ∀ i, (K.ideal ⟨V i, hV i⟩).FG) (U : X.affineOpens) : (K.ideal U).FG := by
  obtain ⟨W, hW⟩ := U
  have key : ∀ x : W, ∃ r : Γ(X, W), ((x : X) ∈ X.basicOpen r) ∧ ∃ i, X.basicOpen r ≤ V i := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover.ge (Set.mem_univ x.1))
    obtain ⟨r, hrle, hxr⟩ := hW.exists_basicOpen_le (V := W ⊓ V i) ⟨x.1, ⟨x.2, hi⟩⟩ x.2
    exact ⟨r, hxr, i, hrle.trans inf_le_right⟩
  choose r hxr i hri using key
  refine fg_of_fg_basicOpen hW _ (Set.range r) ?_ ?_
  · rw [← hW.self_le_iSup_basicOpen_iff]
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨r ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩, hxr ⟨x, hx⟩⟩
  · rintro ⟨_, ⟨x, rfl⟩⟩
    rw [map_ideal_eq_map_ideal K (hW.basicOpen (r x)) hW (hV (i x)) (X.basicOpen_le _) (hri x)]
    exact (hfg _).map _

/-- An ideal is the supremum of the principal ideals generated by its elements. -/
theorem iSup_span_singleton_eq {R : Type*} [CommRing R] (N : Ideal R) :
    ⨆ x : N, Ideal.span {(x : R)} = N :=
  le_antisymm (iSup_le fun x ↦ Ideal.span_le.mpr (by simp))
    fun y hy ↦ le_iSup (fun x : N ↦ Ideal.span {(x : R)}) ⟨y, hy⟩
      (Ideal.mem_span_singleton_self y)

/-- The shrinking step: an ideal `N` of a commutative ring whose image under each of finitely many
ring maps is finitely generated contains a finitely generated ideal with the same images. The
finitely many ring maps are the localizations at the basic opens covering the part of an affine
chart already dealt with. -/
theorem exists_fg_le_map_eq {R : Type*} [CommRing R] (N : Ideal R) {ι : Type*} [Finite ι]
    {S : ι → Type*} [∀ i, CommRing (S i)] (f : ∀ i, R →+* S i)
    (h : ∀ i, (N.map (f i)).FG) :
    ∃ J : Ideal R, J ≤ N ∧ J.FG ∧ ∀ i, N.map (f i) ≤ J.map (f i) := by
  classical
  cases nonempty_fintype ι
  have key : ∀ i, ∃ t : Finset N,
      N.map (f i) ≤ (Ideal.span ((t.image Subtype.val : Finset R) : Set R)).map (f i) := by
    intro i
    have hsup : N.map (f i) ≤ ⨆ x : N, (Ideal.span {(x : R)}).map (f i) := by
      rw [← Ideal.map_iSup, iSup_span_singleton_eq]
    obtain ⟨t, ht⟩ := IsCompactElement.exists_finset_of_le_iSup ((Submodule.fg_iff_compact _).mp (h i))
      (fun x : N ↦ (Ideal.span {(x : R)}).map (f i)) hsup
    refine ⟨t, ht.trans (iSup₂_le fun x hx ↦ Ideal.map_mono (Ideal.span_le.mpr ?_))⟩
    rintro _ rfl
    exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))
  choose t ht using key
  refine ⟨Ideal.span ((Finset.univ.biUnion fun i ↦ (t i).image Subtype.val : Finset R) : Set R),
    Ideal.span_le.mpr ?_, Submodule.fg_span (Set.toFinite _), fun i ↦ ?_⟩
  · intro x hx
    simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_iUnion, Finset.coe_image] at hx
    obtain ⟨i, -, y, -, rfl⟩ := hx
    exact y.2
  · refine (ht i).trans (Ideal.map_mono (Ideal.span_mono ?_))
    intro x hx
    simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_iUnion]
    exact ⟨i, Set.mem_univ _, hx⟩

section Glue

variable {ι : Type*} {V : ι → X.Opens}

/-- A family of ideals on affine opens is compatible when any two members have the same
restriction to every affine open contained in both of the opens they live on. This is exactly
what is needed for the family to be the restriction of a single quasi-coherent ideal sheaf. -/
def IsCompatibleOnAffineOpens (V : ι → X.Opens) (I : ∀ i, Ideal Γ(X, V i)) : Prop :=
  ∀ (i j : ι) {W : X.Opens}, IsAffineOpen W → ∀ (hi : W ≤ V i) (hj : W ≤ V j),
    (I i).map (X.presheaf.map (homOfLE hi).op).hom =
      (I j).map (X.presheaf.map (homOfLE hj).op).hom

variable [QuasiSeparatedSpace X]

/-- The quasi-coherent ideal sheaf glued from a finite family of ideals on affine opens: the
infimum of the maximal extensions of the members of the family. -/
noncomputable def glueAffineIdeals (hV : ∀ i, IsAffineOpen (V i)) (I : ∀ i, Ideal Γ(X, V i)) :
    X.IdealSheafData :=
  ⨅ i, extendAffineIdeal (hV i) (I i)

variable {hV : ∀ i, IsAffineOpen (V i)} {I : ∀ i, Ideal Γ(X, V i)} [Finite ι]

/-- For a compatible family, the ideal of the glued sheaf on an affine open contained in a member
of the family is the restriction of the corresponding member of the family. So gluing recovers the
local data it was built from. -/
theorem ideal_glueAffineIdeals (hc : IsCompatibleOnAffineOpens V I) {W : X.Opens}
    (hW : IsAffineOpen W) (i : ι) (hi : W ≤ V i) :
    (glueAffineIdeals hV I).ideal ⟨W, hW⟩ = (I i).map (X.presheaf.map (homOfLE hi).op).hom := by
  rw [glueAffineIdeals, ideal_iInf, iInf_apply]
  refine le_antisymm
    ((iInf_le _ i).trans_eq (ideal_extendAffineIdeal_of_le (hV i) (I i) hW hi))
    (le_iInf fun j ↦ ?_)
  refine Ideal.map_le_iff_le_comap.mpr fun a ha ↦
    mem_ideal_extendAffineIdeal_of_locally (hV j) (I j) hW _ fun r hr ↦ ?_
  rw [ideal_extendAffineIdeal_of_le (hV j) (I j) (hW.basicOpen r) hr, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← op_comp, homOfLE_comp,
    ← hc i j (hW.basicOpen r) ((X.basicOpen_le r).trans hi) hr]
  exact Ideal.mem_map_of_mem _ ha

/-- For a compatible family, the ideal of the glued sheaf on a member of the family is that
member. -/
theorem ideal_glueAffineIdeals_self (hc : IsCompatibleOnAffineOpens V I) (i : ι) :
    (glueAffineIdeals hV I).ideal ⟨V i, hV i⟩ = I i := by
  rw [ideal_glueAffineIdeals hc (hV i) i le_rfl]
  simp

/-- The glued sheaf of a compatible family covering `X` is contained in an ambient quasi-coherent
ideal sheaf as soon as every member of the family is. -/
theorem glueAffineIdeals_le (hc : IsCompatibleOnAffineOpens V I) (hcover : ⨆ i, V i = ⊤)
    {K : X.IdealSheafData} (hK : ∀ i, I i ≤ K.ideal ⟨V i, hV i⟩) : glueAffineIdeals hV I ≤ K :=
  le_of_iSup_eq_top (fun i ↦ (⟨V i, hV i⟩ : X.affineOpens)) hcover
    fun i ↦ (ideal_glueAffineIdeals_self hc i).trans_le (hK i)

/-- The glued sheaf of a compatible family of finitely generated ideals covering `X` is finitely
generated on *every* affine open, not only on the members of the family. -/
theorem fg_ideal_glueAffineIdeals (hc : IsCompatibleOnAffineOpens V I) (hcover : ⨆ i, V i = ⊤)
    (hfg : ∀ i, (I i).FG) (U : X.affineOpens) : ((glueAffineIdeals hV I).ideal U).FG :=
  fg_ideal_of_fg_cover hV hcover
    (fun i ↦ (ideal_glueAffineIdeals_self hc i).symm ▸ hfg i) U

end Glue

section Extension

/-- The ideal of a quasi-coherent ideal sheaf on an affine open contained in another is the
restriction of the ideal on the larger one. A restatement of
`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal` oriented for rewriting. -/
theorem ideal_eq_map (K : X.IdealSheafData) {W V : X.Opens} (hW : IsAffineOpen W)
    (hV : IsAffineOpen V) (h : W ≤ V) :
    K.ideal ⟨W, hW⟩ = (K.ideal ⟨V, hV⟩).map (X.presheaf.map (homOfLE h).op).hom :=
  (K.map_ideal (U := ⟨W, hW⟩) (V := ⟨V, hV⟩) h).symm

/-- Restricting an ideal twice along inclusions of opens is restricting it once. -/
theorem map_restrict_comp {A B C : X.Opens} (hAB : A ≤ B) (hBC : B ≤ C) (I : Ideal Γ(X, C)) :
    (I.map (X.presheaf.map (homOfLE hBC).op).hom).map (X.presheaf.map (homOfLE hAB).op).hom =
      I.map (X.presheaf.map (homOfLE (hAB.trans hBC)).op).hom := by
  rw [Ideal.map_map, ← CommRingCat.hom_comp, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- The key inclusion behind the gluing induction. Suppose an ideal `I₁` of `Γ(X, V₁)` recovers a
quasi-coherent ideal sheaf `J` on each of finitely many basic opens of `V₁`. Then it recovers `J`
on every affine open contained in `V₁` which those basic opens cover — which is how the shrunk
ideal is seen to agree with the data already built on the overlap. -/
theorem le_map_shrunk {V₁ : X.Opens} (hV₁ : IsAffineOpen V₁) (J : X.IdealSheafData)
    {I₁ : Ideal Γ(X, V₁)} (T : Finset Γ(X, V₁))
    (hmap : ∀ g ∈ T, J.ideal ⟨X.basicOpen g, hV₁.basicOpen g⟩ ≤
        I₁.map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom)
    {W : X.Opens} (hW : IsAffineOpen W) (hWV : W ≤ V₁)
    (hWcover : W ≤ ⨆ g ∈ T, X.basicOpen g) :
    J.ideal ⟨W, hW⟩ ≤ I₁.map (X.presheaf.map (homOfLE hWV).op).hom := by
  classical
  refine le_of_le_basicOpen hW
    ((T.image fun g ↦ X.presheaf.map (homOfLE hWV).op g : Finset Γ(X, W)) : Set Γ(X, W)) ?_ ?_
  · rw [← hW.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨g, hg⟩ := Opens.mem_iSup.mp (hWcover hx)
    obtain ⟨hgT, hxg⟩ := Opens.mem_iSup.mp hg
    refine Opens.mem_iSup.mpr ⟨⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hgT)⟩, ?_⟩
    rw [Scheme.basicOpen_res]
    exact ⟨hx, hxg⟩
  · rintro ⟨r, hr⟩
    obtain ⟨g, hgT, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hr)
    have hAg : X.basicOpen (X.presheaf.map (homOfLE hWV).op g) ≤ X.basicOpen g := by
      rw [Scheme.basicOpen_res]
      exact inf_le_right
    have hA := hW.basicOpen (X.presheaf.map (homOfLE hWV).op g)
    calc (J.ideal ⟨W, hW⟩).map (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom
        = (J.ideal ⟨X.basicOpen g, hV₁.basicOpen g⟩).map
            (X.presheaf.map (homOfLE hAg).op).hom :=
          map_ideal_eq_map_ideal J hA hW (hV₁.basicOpen g) _ hAg
      _ ≤ (I₁.map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom).map
            (X.presheaf.map (homOfLE hAg).op).hom := Ideal.map_mono (hmap g hgT)
      _ = (I₁.map (X.presheaf.map (homOfLE hWV).op).hom).map
            (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom := by
          rw [map_restrict_comp, map_restrict_comp]

/-- On a quasi-separated scheme the intersection of an affine open `V` with a finite union of
affine opens is covered by finitely many basic opens of `V`, each contained in `V ⊓ W i` for a
single `i`. This is the finiteness that makes the shrinking step of Tag 01PF possible. -/
theorem exists_finite_basicOpen_cover_inter [QuasiSeparatedSpace X] {V : X.Opens}
    (hV : IsAffineOpen V) {ι : Type*} {W : ι → X.Opens} (hW : ∀ i, IsAffineOpen (W i))
    [Finite ι] :
    ∃ T : Finset Γ(X, V), (∀ g ∈ T, ∃ i, X.basicOpen g ≤ V ⊓ W i) ∧
      V ⊓ (⨆ i, W i) ≤ ⨆ g ∈ T, X.basicOpen g := by
  classical
  have hcpt : IsCompact ((V ⊓ ⨆ i, W i : X.Opens) : Set X) := by
    rw [show ((V ⊓ ⨆ i, W i : X.Opens) : Set X) = ⋃ i, ((V : Set X) ∩ (W i : Set X)) by
      simp [Set.inter_iUnion]]
    exact isCompact_iUnion fun i ↦
      quasiSeparatedSpace_iff_forall_affineOpens.mp ‹_› ⟨V, hV⟩ ⟨W i, hW i⟩
  have hsub : ((V ⊓ ⨆ i, W i : X.Opens) : Set X) ⊆
      ⋃ g : {g : Γ(X, V) // ∃ i, X.basicOpen g ≤ V ⊓ W i},
        ((X.basicOpen g.1 : X.Opens) : Set X) := by
    rintro x ⟨hxV, hxW⟩
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxW
    obtain ⟨g, hgle, hxg⟩ := hV.exists_basicOpen_le (V := V ⊓ W i) ⟨x, ⟨hxV, hi⟩⟩ hxV
    exact Set.mem_iUnion.mpr ⟨⟨g, i, hgle⟩, hxg⟩
  obtain ⟨T, hT⟩ := hcpt.elim_finite_subcover
    (fun g : {g : Γ(X, V) // ∃ i, X.basicOpen g ≤ V ⊓ W i} ↦ ((X.basicOpen g.1 : X.Opens) : Set X))
    (fun g ↦ (X.basicOpen g.1).isOpen) hsub
  refine ⟨T.image Subtype.val, fun g hg ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hg
    exact y.2
  · obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.mp (hT hx)
    exact Opens.mem_iSup.mpr ⟨g.1, Opens.mem_iSup.mpr ⟨Finset.mem_image_of_mem _ hg, hxg⟩⟩

/-- A quasi-coherent ideal sheaf finitely generated on an affine open `V₂` has finitely generated
restriction to every basic open of an affine open `V₁` which is contained in `V₂`. -/
theorem fg_map_basicOpen_of_le (J : X.IdealSheafData) {V₁ V₂ : X.Opens} (hV₁ : IsAffineOpen V₁)
    (hV₂ : IsAffineOpen V₂) {g : Γ(X, V₁)} (hg : X.basicOpen g ≤ V₂)
    (hfg : (J.ideal ⟨V₂, hV₂⟩).FG) :
    ((J.ideal ⟨V₁, hV₁⟩).map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom).FG := by
  rw [map_ideal_eq_map_ideal J (hV₁.basicOpen g) hV₁ hV₂ (X.basicOpen_le g) hg]
  exact hfg.map _

/-- Replacing the ideal of a quasi-coherent ideal sheaf `J` on one chart `V i₁` by a smaller ideal
`I₁` which still recovers `J` on finitely many basic opens covering the overlap of `V i₁` with the
charts `V j`, `j ∈ s`, gives a compatible family on the charts indexed by `insert i₁ s`. -/
theorem isCompatibleOnAffineOpens_of_shrunk {ι : Type*} [DecidableEq ι] {V : ι → X.Opens}
    (hV : ∀ i, IsAffineOpen (V i)) (J : X.IdealSheafData) {s : Finset ι} {i₁ : ι}
    {I₁ : Ideal Γ(X, V i₁)} (hI₁N : I₁ ≤ J.ideal ⟨V i₁, hV i₁⟩) {T : Finset Γ(X, V i₁)}
    (hmapT : ∀ g ∈ T, J.ideal ⟨X.basicOpen g, (hV i₁).basicOpen g⟩ ≤
      I₁.map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom)
    (hT2 : V i₁ ⊓ ⨆ j : {x // x ∈ s}, V j.1 ≤ ⨆ g ∈ T, X.basicOpen g)
    {I : ∀ j, Ideal Γ(X, V j)} (hIi₁ : I i₁ = I₁)
    (hIne : ∀ j, j ≠ i₁ → I j = J.ideal ⟨V j, hV j⟩) :
    IsCompatibleOnAffineOpens (fun j : {x // x ∈ insert i₁ s} ↦ V j.1) (fun j ↦ I j.1) := by
  have key : ∀ (i j : ι), i ∈ insert i₁ s → j ∈ insert i₁ s →
      ∀ {W : X.Opens}, IsAffineOpen W → ∀ (hi : W ≤ V i) (hj : W ≤ V j),
        (I i).map (X.presheaf.map (homOfLE hi).op).hom ≤
          (I j).map (X.presheaf.map (homOfLE hj).op).hom := by
    intro i j hi_mem hj_mem W hW hi hj
    obtain rfl | hji := eq_or_ne j i₁
    · obtain rfl | hij := eq_or_ne i j
      · exact le_rfl
      · rw [hIne i hij, hIi₁, ← ideal_eq_map J hW (hV i) hi]
        exact le_map_shrunk (hV j) J T hmapT hW hj fun x hx ↦ hT2 ⟨hj hx,
          Opens.mem_iSup.mpr ⟨⟨i, Finset.mem_of_mem_insert_of_ne hi_mem hij⟩, hi hx⟩⟩
    · rw [hIne j hji, ← ideal_eq_map J hW (hV j) hj]
      obtain rfl | hij := eq_or_ne i i₁
      · rw [hIi₁]
        exact (Ideal.map_mono hI₁N).trans (ideal_eq_map J hW (hV i) hi).ge
      · rw [hIne i hij, ← ideal_eq_map J hW (hV i) hi]
  intro i j W hW hi hj
  exact le_antisymm (key i.1 j.1 i.2 j.2 hW hi hj) (key j.1 i.1 j.2 i.2 hW hj hi)

/-- The inductive step of Tag 01PF for quasi-coherent sheaves of ideals. Given a quasi-coherent
ideal sheaf `J ≤ K` whose ideal is finitely generated on the members `V j`, `j ∈ s`, of a family
of affine opens, there is another one, still below `K`, finitely generated on one more member and
with unchanged ideals on the old ones.

The new sheaf is glued from the old ideals on `V j`, `j ∈ s`, together with a finitely generated
ideal on the new chart obtained by shrinking `J`'s ideal there without changing its restriction to
the overlap with the old charts. The old family is automatically compatible, being the restriction
of `J`; compatibility of the new member with the old ones is exactly what the shrinking
preserves. -/
theorem exists_fg_step [QuasiSeparatedSpace X] {K : X.IdealSheafData}
    {ι : Type*} [DecidableEq ι] {V : ι → X.Opens} (hV : ∀ i, IsAffineOpen (V i))
    {J : X.IdealSheafData} (hJK : J ≤ K) {s : Finset ι}
    (hfg : ∀ j ∈ s, (J.ideal ⟨V j, hV j⟩).FG) {i₁ : ι} (hi₁ : i₁ ∉ s) :
    ∃ J' : X.IdealSheafData, J' ≤ K ∧ (∀ j ∈ insert i₁ s, (J'.ideal ⟨V j, hV j⟩).FG) ∧
      ∀ j ∈ s, J'.ideal ⟨V j, hV j⟩ = J.ideal ⟨V j, hV j⟩ := by
  obtain ⟨T, hT1, hT2⟩ := exists_finite_basicOpen_cover_inter (hV i₁)
    (W := fun j : {x // x ∈ s} ↦ V j.1) (fun j ↦ hV j.1)
  obtain ⟨I₁, hI₁N, hI₁fg, hI₁map⟩ := exists_fg_le_map_eq (J.ideal ⟨V i₁, hV i₁⟩)
    (f := fun g : {g : Γ(X, V i₁) // g ∈ T} ↦
      (X.presheaf.map (homOfLE (X.basicOpen_le g.1)).op).hom) fun g ↦ by
    obtain ⟨j, hj⟩ := hT1 g.1 g.2
    exact fg_map_basicOpen_of_le J (hV i₁) (hV j.1) (hj.trans inf_le_right) (hfg j.1 j.2)
  obtain ⟨I, hIi₁, hIne⟩ : ∃ I : ∀ j : ι, Ideal Γ(X, V j), I i₁ = I₁ ∧
      ∀ j, j ≠ i₁ → I j = J.ideal ⟨V j, hV j⟩ :=
    ⟨Function.update (fun j ↦ J.ideal ⟨V j, hV j⟩) i₁ I₁, Function.update_self _ _ _,
      fun j hj ↦ Function.update_of_ne hj _ _⟩
  have hmapT : ∀ g ∈ T, J.ideal ⟨X.basicOpen g, (hV i₁).basicOpen g⟩ ≤
      I₁.map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom := fun g hgT ↦
    (ideal_eq_map J ((hV i₁).basicOpen g) (hV i₁) (X.basicOpen_le g)).le.trans
      (hI₁map ⟨g, hgT⟩)
  have hIle : ∀ j ∈ insert i₁ s, I j ≤ K.ideal ⟨V j, hV j⟩ := by
    intro j hj
    obtain rfl | hji := eq_or_ne j i₁
    · rw [hIi₁]
      exact hI₁N.trans (hJK _)
    · rw [hIne j hji]
      exact hJK _
  have hc := isCompatibleOnAffineOpens_of_shrunk hV J hI₁N hmapT hT2 hIi₁ hIne
  refine ⟨glueAffineIdeals (fun j : {x // x ∈ insert i₁ s} ↦ hV j.1) (fun j ↦ I j.1) ⊓ K,
    inf_le_right, ?_, ?_⟩
  · intro j hj
    have h1 : (glueAffineIdeals (fun j : {x // x ∈ insert i₁ s} ↦ hV j.1)
        (fun j ↦ I j.1) ⊓ K).ideal ⟨V j, hV j⟩ = I j := by
      rw [ideal_inf, Pi.inf_apply, ideal_glueAffineIdeals_self hc ⟨j, hj⟩]
      exact inf_eq_left.mpr (hIle j hj)
    rw [h1]
    obtain rfl | hji := eq_or_ne j i₁
    · rw [hIi₁]
      exact hI₁fg
    · rw [hIne j hji]
      exact hfg j (Finset.mem_of_mem_insert_of_ne hj hji)
  · intro j hj
    have hji : j ≠ i₁ := fun h ↦ hi₁ (h ▸ hj)
    rw [ideal_inf, Pi.inf_apply,
      ideal_glueAffineIdeals_self hc ⟨j, Finset.mem_insert_of_mem hj⟩, hIne j hji]
    exact inf_eq_left.mpr (hJK _)

/-- Tag 01PF for quasi-coherent sheaves of ideals, in the form produced by the induction over a
finite family of affine opens covering `X`: a quasi-coherent ideal sheaf below `K` which is
finitely generated everywhere and has a prescribed ideal on one distinguished chart. -/
theorem exists_fg_of_cover [QuasiSeparatedSpace X] {K : X.IdealSheafData} {ι : Type*}
    [Finite ι] {V : ι → X.Opens} (hV : ∀ i, IsAffineOpen (V i))
    (hcover : ⨆ i, V i = ⊤) {J₀ : X.IdealSheafData} (hJ₀ : J₀ ≤ K) (i₀ : ι)
    (hfg₀ : (J₀.ideal ⟨V i₀, hV i₀⟩).FG) :
    ∃ J : X.IdealSheafData, J ≤ K ∧ (∀ W : X.affineOpens, (J.ideal W).FG) ∧
      J.ideal ⟨V i₀, hV i₀⟩ = J₀.ideal ⟨V i₀, hV i₀⟩ := by
  classical
  cases nonempty_fintype ι
  have main : ∀ s : Finset ι, ∃ J : X.IdealSheafData, J ≤ K ∧
      (∀ j ∈ insert i₀ s, (J.ideal ⟨V j, hV j⟩).FG) ∧
      J.ideal ⟨V i₀, hV i₀⟩ = J₀.ideal ⟨V i₀, hV i₀⟩ := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨J₀, hJ₀, by simpa using hfg₀, rfl⟩
    | @insert i₁ s hi₁ ih =>
      obtain ⟨J, hJK, hJfg, hJ0⟩ := ih
      by_cases hmem : i₁ ∈ insert i₀ s
      · exact ⟨J, hJK, by rwa [Finset.insert_comm, Finset.insert_eq_self.mpr hmem], hJ0⟩
      · obtain ⟨J', hJ'K, hJ'fg, hJ'eq⟩ := exists_fg_step hV hJK hJfg hmem
        refine ⟨J', hJ'K, by rwa [Finset.insert_comm], ?_⟩
        rw [hJ'eq i₀ (Finset.mem_insert_self _ _), hJ0]
  obtain ⟨J, hJK, hJfg, hJ0⟩ := main Finset.univ
  exact ⟨J, hJK, fg_ideal_of_fg_cover hV hcover
    (fun i ↦ hJfg i (Finset.mem_insert_of_mem (Finset.mem_univ i))), hJ0⟩

/-- **Stacks Project, Tag 01PF** for quasi-coherent sheaves of ideals: a section of a
quasi-coherent ideal sheaf over an affine open of a quasi-compact and quasi-separated scheme lies
in a finite type quasi-coherent subsheaf of ideals. -/
theorem exists_fg_le_of_mem [CompactSpace X] [QuasiSeparatedSpace X] (K : X.IdealSheafData)
    {U : X.Opens} (hU : IsAffineOpen U) {a : Γ(X, U)} (ha : a ∈ K.ideal ⟨U, hU⟩) :
    ∃ J : X.IdealSheafData, J ≤ K ∧ (∀ W : X.affineOpens, (J.ideal W).FG) ∧
      a ∈ J.ideal ⟨U, hU⟩ := by
  classical
  have hcov : (Set.univ : Set X) ⊆ ⋃ W : X.affineOpens, ((W.1 : X.Opens) : Set X) := by
    intro x _
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩
  obtain ⟨t, ht⟩ := (isCompact_univ (X := (X : TopCat))).elim_finite_subcover
    (fun W : X.affineOpens ↦ ((W.1 : X.Opens) : Set X)) (fun W ↦ W.1.2) hcov
  have hfg : ((extendAffineIdeal hU (Ideal.span {a}) ⊓ K).ideal ⟨U, hU⟩).FG := by
    rw [ideal_inf, Pi.inf_apply, ideal_extendAffineIdeal_self,
      inf_eq_left.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha))]
    exact Submodule.fg_span (Set.finite_singleton a)
  obtain ⟨J, hJK, hJfg, hJ0⟩ := exists_fg_of_cover
    (K := K) (ι := Option {W // W ∈ t})
    (V := fun o ↦ o.elim U fun W ↦ (W.1.1 : X.Opens))
    (fun o ↦ by cases o with | none => exact hU | some W => exact W.1.2)
    (by
      refine top_le_iff.mp fun x _ ↦ ?_
      obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
      exact Opens.mem_iSup.mpr ⟨some ⟨W, hW⟩, hxW⟩)
    (J₀ := extendAffineIdeal hU (Ideal.span {a}) ⊓ K) inf_le_right none hfg
  refine ⟨J, hJK, hJfg, ?_⟩
  have hJ0' : J.ideal ⟨U, hU⟩ =
    (extendAffineIdeal hU (Ideal.span {a}) ⊓ K).ideal ⟨U, hU⟩ := hJ0
  rw [hJ0', ideal_inf, Pi.inf_apply, ideal_extendAffineIdeal_self]
  exact ⟨Ideal.mem_span_singleton_self a, ha⟩

/-- **Stacks Project, Tag 01PG** for quasi-coherent sheaves of ideals: on a quasi-compact and
quasi-separated scheme a quasi-coherent sheaf of ideals is the supremum of its finite type
quasi-coherent subsheaves of ideals. -/
theorem le_iSup_fg [CompactSpace X] [QuasiSeparatedSpace X] (K : X.IdealSheafData) :
    K ≤ ⨆ J : {J : X.IdealSheafData // (∀ W : X.affineOpens, (J.ideal W).FG) ∧ J ≤ K},
      (J : X.IdealSheafData) := by
  intro W a ha
  obtain ⟨J, hJK, hJfg, haJ⟩ := exists_fg_le_of_mem K W.2 (a := a) ha
  exact le_iSup (fun J : {J : X.IdealSheafData // (∀ W : X.affineOpens, (J.ideal W).FG) ∧ J ≤ K} ↦
    (J : X.IdealSheafData)) ⟨J, hJfg, hJK⟩ W haJ

end Extension

end Stacks.IdealSheaf

end
