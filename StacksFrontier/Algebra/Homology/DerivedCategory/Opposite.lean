module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Monoidal.Mon
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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

/-!
# The opposite of the derived category

Let `𝒜` be an abelian category. Passing to opposite categories reads a cochain complex backwards:
the opposite of the category of cochain complexes of `𝒜` is the category of cochain complexes of
`𝒜ᵒᵖ` (`CochainComplex.opEquivalence`), the degree `i` becoming the degree `-i`. This file carries
that duality up to the homotopy category and to the derived category, as equivalences

`K(𝒜)ᵒᵖ ≌ K(𝒜ᵒᵖ)` and `D(𝒜)ᵒᵖ ≌ D(𝒜ᵒᵖ)`

compatible with the localization functors, and proves the three compatibilities of the second one
with the canonical t-structure of the derived category: the cohomology in degree `i` becomes the
cohomology in degree `-i`, an object cohomologically `≤ i` becomes one cohomologically `≥ -i`, and
the truncation `τ_{≤ i}` becomes the truncation `τ_{≥ -i}`, compatibly with the canonical maps.

## Main results

* `CochainComplex.quasiIso_opEquivalence_functor_map_iff`: a morphism of cochain complexes is a
  quasi-isomorphism exactly when the opposite morphism is one, and
  `CochainComplex.homotopyEquivalences_opEquivalence_functor_map_iff` for homotopy equivalences.
* `CochainComplex.homologyOpNatIso`: the homology of the opposite complex in degree `m` is the
  opposite of the homology of the complex in degree `-m`.
* `HomotopyCategory.homotopyOpEquivalence`: the duality `K(𝒜)ᵒᵖ ≌ K(𝒜ᵒᵖ)`.
* `DerivedCategory.derivedOpEquivalence`: the duality `D(𝒜)ᵒᵖ ≌ D(𝒜ᵒᵖ)`.
* `DerivedCategory.derivedHomologyOpNatIso`: the homology exchange in the derived category.
* `DerivedCategory.isGE_derivedOpEquivalence_functor_obj_iff` and
  `DerivedCategory.isLE_derivedOpEquivalence_functor_obj_iff`: the exchange of the two bounds of
  the canonical t-structure.
* `DerivedCategory.exists_truncOpIso` and `DerivedCategory.exists_truncOpIso'`: the exchange of
  the two truncations of the canonical t-structure, compatibly with their canonical maps.

## Implementation notes

Neither equivalence is constructed; both come from the uniqueness of localizations.
`Q : CochainComplex 𝒜 ℤ ⥤ D(𝒜)` localizes the quasi-isomorphisms, hence `Q.op` localizes their
opposites (`CategoryTheory.Functor.IsLocalization.op`), and the duality of complexes matches the
opposites of the quasi-isomorphisms of `𝒜` with the quasi-isomorphisms of `𝒜ᵒᵖ`, so that
`DerivedCategory.opQ : CochainComplex 𝒜ᵒᵖ ℤ ⥤ D(𝒜)ᵒᵖ` is a second localization of
`CochainComplex 𝒜ᵒᵖ ℤ` at the quasi-isomorphisms, which `Localization.uniq` compares with `Q`.
`HomotopyCategory.opQuotient` and `HomotopyCategory.homotopyOpEquivalence` are the same
construction one level down, for the homotopy equivalences.

What this yields is an equivalence of plain categories: it is not shown here to be triangulated,
and none of the three compatibilities needs it to be. The homology exchange is transported from
the level of complexes, where the short complex computing the homology of the opposite complex in
degree `m` **is** the opposite of the one computing the homology of the original complex in degree
`-m` (`CochainComplex.shortComplexOpBridge`, an equality of functors, so that
`CochainComplex.homologyOpNatIso` inherits no naturality obligation), and is then lifted along the
localization with `Localization.liftNatIso`. The bounds exchange follows from it, both bounds being
the vanishing of homology outside a range (`DerivedCategory.isGE_iff`, `DerivedCategory.isLE_iff`).
The truncation exchange rests only on the universal properties of the truncations: an object which
is `≥ n` and receives a map from `X` through which every map from `X` to an object `≥ n` factors
uniquely *is* `τ_{≥ n} X` (`CategoryTheory.Triangulated.TStructure.exists_isoTruncGE`, and its
dual `exists_isoTruncLE`), and the transported truncation has that property because the duality is
fully faithful and exchanges the two bounds. Only the existence of the comparison isomorphism is
asserted, the factorizations that produce it depending on no choice.

## References

* `Mathlib/Algebra/Homology/CochainComplexOpposite.lean`, the duality of cochain complexes
* `Mathlib/Algebra/Homology/Opposite.lean`, the homology of an opposite complex
* `Mathlib/CategoryTheory/Localization/Opposite.lean`, the opposite of a localization functor
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory Limits

namespace CategoryTheory.Triangulated.TStructure

/-- **`τ_{≥ n} X` recognized by its universal property.** An object `Y` which is `≥ n` and receives
a map `u` from `X` through which every map from `X` to an object `≥ n` factors uniquely *is* the
truncation `τ_{≥ n} X`, compatibly with the canonical map.

This is the reason the duality of derived categories need not be shown to be triangulated: the
truncations are pinned by `TStructure.descTruncGE` and `TStructure.from_truncGE_obj_ext` alone.
The isomorphism is `u`'s factorization through `τ_{≥ n} X` in one direction and
`TStructure.descTruncGE u n` in the other; one composite is an identity by the uniqueness in the
hypothesis, the other by extensionality of maps out of a truncation. -/
public lemma exists_isoTruncGE {𝒟 : Type u₃} [Category.{v₃} 𝒟] [Preadditive 𝒟]
    [HasZeroObject 𝒟] [HasShift 𝒟 ℤ] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
    [Pretriangulated 𝒟] (t : Triangulated.TStructure 𝒟) (n : ℤ) {X Y : 𝒟} (u : X ⟶ Y)
    [t.IsGE Y n]
    (hu : ∀ (Z : 𝒟), t.IsGE Z n → ∀ g : X ⟶ Z, ∃! v : Y ⟶ Z, u ≫ v = g) :
    ∃ θ : Y ≅ (t.truncGE n).obj X, u ≫ θ.hom = (t.truncGEπ n).app X := by
  obtain ⟨v, hv, -⟩ := hu ((t.truncGE n).obj X) inferInstance ((t.truncGEπ n).app X)
  obtain ⟨u₀, -, huniq⟩ := hu Y ‹t.IsGE Y n› u
  refine ⟨⟨v, t.descTruncGE u n, ?_, ?_⟩, hv⟩
  · rw [huniq (v ≫ t.descTruncGE u n)
      (by change u ≫ v ≫ t.descTruncGE u n = u
          rw [← Category.assoc, hv, t.π_descTruncGE]),
      huniq (𝟙 Y) (by change u ≫ 𝟙 Y = u; rw [Category.comp_id])]
  · exact t.from_truncGE_obj_ext (by rw [← Category.assoc, t.π_descTruncGE, hv, Category.comp_id])

/-- **`τ_{≤ n} X` recognized by its universal property**, the dual of `exists_isoTruncGE`: an object
`Y` which is `≤ n` and maps to `X` universally among objects `≤ n` *is* `τ_{≤ n} X`. -/
public lemma exists_isoTruncLE {𝒟 : Type u₃} [Category.{v₃} 𝒟] [Preadditive 𝒟]
    [HasZeroObject 𝒟] [HasShift 𝒟 ℤ] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
    [Pretriangulated 𝒟] (t : Triangulated.TStructure 𝒟) (n : ℤ) {X Y : 𝒟} (u : Y ⟶ X)
    [t.IsLE Y n]
    (hu : ∀ (Z : 𝒟), t.IsLE Z n → ∀ g : Z ⟶ X, ∃! v : Z ⟶ Y, v ≫ u = g) :
    ∃ θ : Y ≅ (t.truncLE n).obj X, θ.hom ≫ (t.truncLEι n).app X = u := by
  obtain ⟨v, hv, -⟩ := hu ((t.truncLE n).obj X) inferInstance ((t.truncLEι n).app X)
  obtain ⟨u₀, -, huniq⟩ := hu Y ‹t.IsLE Y n› u
  refine ⟨⟨t.liftTruncLE u n, v, ?_, ?_⟩, t.liftTruncLE_ι u n⟩
  · rw [huniq (t.liftTruncLE u n ≫ v)
      (by change (t.liftTruncLE u n ≫ v) ≫ u = u
          rw [Category.assoc, hv, t.liftTruncLE_ι]),
      huniq (𝟙 Y) (by change 𝟙 Y ≫ u = u; rw [Category.id_comp])]
  · exact t.to_truncLE_obj_ext
      (by rw [Category.assoc, t.liftTruncLE_ι, hv, Category.id_comp])

end CategoryTheory.Triangulated.TStructure

namespace CochainComplex

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

/-- Under the duality `(CochainComplex 𝒞 ℤ)ᵒᵖ ≌ CochainComplex 𝒞ᵒᵖ ℤ` of
`CochainComplex.opEquivalence`, a morphism of cochain complexes is a quasi-isomorphism in
degree `n` exactly when the opposite morphism is one in the opposite degree `m = -n`: the
short complex computing the homology of the opposite complex in degree `m` is the one computing
the homology of the original in degree `n`, read through `ShortComplex.opMap`. -/
public lemma quasiIsoAt_opEquivalence_functor_map_iff {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (n m : ℤ) (hm : n + m = 0) :
    QuasiIsoAt ((CochainComplex.opEquivalence C).functor.map f.op) m ↔ QuasiIsoAt f n := by
  obtain rfl : n = -m := by omega
  rw [quasiIsoAt_iff' _ (m - 1) m (m + 1) (by simp) (by simp),
    quasiIsoAt_iff' f (-(m + 1)) (-m) (-(m - 1))
      (by grind [CochainComplex.prev]) (by grind [CochainComplex.next]),
    ← ShortComplex.quasiIso_opMap_iff ((HomologicalComplex.shortComplexFunctor' C
      (ComplexShape.up ℤ) (-(m + 1)) (-m) (-(m - 1))).map f)]
  exact ShortComplex.quasiIso_iff_of_arrow_mk_iso _ _ (Iso.refl _)

/-- A morphism of cochain complexes is a quasi-isomorphism exactly when its image under the
duality `(CochainComplex 𝒞 ℤ)ᵒᵖ ≌ CochainComplex 𝒞ᵒᵖ ℤ` is one. -/
public lemma quasiIso_opEquivalence_functor_map_iff {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    QuasiIso ((CochainComplex.opEquivalence C).functor.map f.op) ↔ QuasiIso f := by
  rw [quasiIso_iff, quasiIso_iff]
  exact ⟨fun h n ↦ (quasiIsoAt_opEquivalence_functor_map_iff f n (-n) (by omega)).1 (h (-n)),
    fun h m ↦ (quasiIsoAt_opEquivalence_functor_map_iff f (-m) m (by omega)).2 (h (-m))⟩

/-- A morphism of cochain complexes is a homotopy equivalence exactly when its image under the
duality `(CochainComplex 𝒞 ℤ)ᵒᵖ ≌ CochainComplex 𝒞ᵒᵖ ℤ` is one. The duality matches homotopies
with homotopies (`CochainComplex.homotopyOpEquiv`) and is fully faithful, so a homotopy inverse
on one side is a homotopy inverse on the other. -/
public lemma homotopyEquivalences_opEquivalence_functor_map_iff {K L : CochainComplex C ℤ}
    (f : K ⟶ L) :
    HomologicalComplex.homotopyEquivalences Cᵒᵖ (ComplexShape.up ℤ)
        ((CochainComplex.opEquivalence C).functor.map f.op) ↔
      HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ) f := by
  constructor
  · rintro ⟨e, he⟩
    let Φ := (CochainComplex.opEquivalence C).functor
    let g : L ⟶ K := (Φ.preimage e.inv).unop
    have hg : Φ.map g.op = e.inv := Φ.map_preimage e.inv
    refine ⟨{ hom := f, inv := g, homotopyHomInvId := ?_, homotopyInvHomId := ?_ }, rfl⟩
    · refine CochainComplex.homotopyOpEquiv.symm
        ((Homotopy.ofEq ?_).trans (e.homotopyInvHomId.trans (Homotopy.ofEq ?_)))
      · rw [show ((f ≫ g).op) = g.op ≫ f.op from rfl, Φ.map_comp, hg, he]
      · simp
    · refine CochainComplex.homotopyOpEquiv.symm
        ((Homotopy.ofEq ?_).trans (e.homotopyHomInvId.trans (Homotopy.ofEq ?_)))
      · rw [show ((g ≫ f).op) = f.op ≫ g.op from rfl, Φ.map_comp, hg, he]
      · simp
  · rintro ⟨e, rfl⟩
    let Φ := (CochainComplex.opEquivalence C).functor
    exact ⟨{ hom := Φ.map e.hom.op
             inv := Φ.map e.inv.op
             homotopyHomInvId := (Homotopy.ofEq (by rw [← Φ.map_comp]; rfl)).trans
               ((CochainComplex.homotopyOpEquiv e.homotopyInvHomId).trans
                 (Homotopy.ofEq (by simp)))
             homotopyInvHomId := (Homotopy.ofEq (by rw [← Φ.map_comp]; rfl)).trans
               ((CochainComplex.homotopyOpEquiv e.homotopyHomInvId).trans
                 (Homotopy.ofEq (by simp))) }, rfl⟩

/-- The short complex computing the homology of the opposite complex in degree `m` **is** the
opposite of the one computing the homology of the original complex in degree `-m`: both are
`Xᵒᵖ(-(m+1)) ⟶ Xᵒᵖ(-m) ⟶ Xᵒᵖ(-(m-1))`, read in the two possible orders.

The two functors are equal, not merely isomorphic, once the three degrees are named explicitly
with `shortComplexFunctor'` instead of being produced by `ComplexShape.prev` and
`ComplexShape.next`; so `Iso.refl` bridges them and `homologyOpNatIso` below inherits no
naturality obligation. Building the comparison pointwise instead does not work: the naturality
square of `ShortComplex.homologyOpIso` then asks for exactly this equality of short complexes at
`implicit` transparency, where it does not hold. -/
public def shortComplexOpBridge (m : ℤ) :
    (CochainComplex.opEquivalence C).functor ⋙
        HomologicalComplex.shortComplexFunctor' Cᵒᵖ (ComplexShape.up ℤ) (m - 1) m (m + 1) ≅
      (HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℤ)
          (-(m + 1)) (-m) (-(m - 1))).op ⋙ ShortComplex.opFunctor C :=
  Iso.refl _

/-- **The homology exchange, at the level of complexes.** Under the duality
`(CochainComplex 𝒞 ℤ)ᵒᵖ ≌ CochainComplex 𝒞ᵒᵖ ℤ`, the homology of the opposite complex in degree
`m` is the opposite of the homology of the complex in degree `-m`, naturally in the complex.

The three steps are: name the degrees explicitly (`natIsoSc'`), exchange the two short complexes
(`shortComplexOpBridge`, an equality of functors), and exchange homology of a short complex with
the opposite of homology (`ShortComplex.homologyFunctorOpNatIso`). -/
public noncomputable def homologyOpNatIso (m : ℤ) :
    (CochainComplex.opEquivalence C).functor ⋙
        HomologicalComplex.homologyFunctor Cᵒᵖ (ComplexShape.up ℤ) m ≅
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (-m)).op :=
  Functor.isoWhiskerLeft (CochainComplex.opEquivalence C).functor
      (Functor.isoWhiskerRight
        (HomologicalComplex.natIsoSc' Cᵒᵖ (ComplexShape.up ℤ) (m - 1) m (m + 1)
          (by simp) (by simp)) (ShortComplex.homologyFunctor Cᵒᵖ)) ≪≫
    Functor.isoWhiskerRight (shortComplexOpBridge m) (ShortComplex.homologyFunctor Cᵒᵖ) ≪≫
    Functor.isoWhiskerLeft
      ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℤ)
        (-(m + 1)) (-m) (-(m - 1))).op) (ShortComplex.homologyFunctorOpNatIso C).symm ≪≫
    NatIso.op (Functor.isoWhiskerRight
      (HomologicalComplex.natIsoSc' C (ComplexShape.up ℤ) (-(m + 1)) (-m) (-(m - 1))
        (by simp; ring) (by simp; ring)) (ShortComplex.homologyFunctor C))

/-- `homologyOpNatIso` read from the side of the inverse functor of the duality: the homology of
a complex of `𝒞ᵒᵖ` in degree `m` is the opposite of the homology in degree `-m` of the complex
of `𝒞` it comes from. -/
public noncomputable def homologyOpNatIso' (m : ℤ) :
    HomologicalComplex.homologyFunctor Cᵒᵖ (ComplexShape.up ℤ) m ≅
      (CochainComplex.opEquivalence C).inverse ⋙
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (-m)).op :=
  ((CochainComplex.opEquivalence C).invFunIdAssoc
      (HomologicalComplex.homologyFunctor Cᵒᵖ (ComplexShape.up ℤ) m)).symm ≪≫
    Functor.isoWhiskerLeft _ (homologyOpNatIso m)

/-- A localization `L` at `W` yields a localization `opEquivalence.inverse ⋙ L.op` at any
isomorphism-closed `W'` whose members are exactly the images of the members of `W.op`. -/
private lemma isLocalization_inverse_comp_op {D : Type u₂} [Category.{v₂} D]
    (L : CochainComplex C ℤ ⥤ D) (W : MorphismProperty (CochainComplex C ℤ))
    (W' : MorphismProperty (CochainComplex Cᵒᵖ ℤ)) [L.IsLocalization W] [W'.RespectsIso]
    (h : ∀ {K L : CochainComplex C ℤ} (f : K ⟶ L),
      W' ((CochainComplex.opEquivalence C).functor.map f.op) ↔ W f) :
    ((CochainComplex.opEquivalence C).inverse ⋙ L.op).IsLocalization W' := by
  refine Functor.IsLocalization.of_equivalence_source L.op W.op _ _
    (CochainComplex.opEquivalence C) ?_ ?_ ?_
  · rintro ⟨K⟩ ⟨L⟩ f hf
    exact MorphismProperty.le_isoClosure _ _ ((h f.unop).2 hf)
  · rintro K L' g hg
    have hW : W ((CochainComplex.opEquivalence C).inverse.map g).unop := by
      rw [← h]
      have key : (CochainComplex.opEquivalence C).functor.map
          (((CochainComplex.opEquivalence C).inverse.map g).unop).op =
          (CochainComplex.opEquivalence C).counitIso.hom.app K ≫ g ≫
            (CochainComplex.opEquivalence C).counitIso.inv.app L' := by
        simp
      rw [key]
      exact (MorphismProperty.arrow_mk_iso_iff _
        (Arrow.isoMk ((CochainComplex.opEquivalence C).counitIso.app K)
          ((CochainComplex.opEquivalence C).counitIso.app L') (by simp))).2 hg
    have := Localization.inverts L W _ hW
    exact (inferInstance : IsIso (L.map ((CochainComplex.opEquivalence C).inverse.map g).unop).op)
  · exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CochainComplex.opEquivalence C).unitIso.symm _ ≪≫
      Functor.leftUnitor _

end CochainComplex

namespace HomotopyCategory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

/-- The quotient functor `CochainComplex 𝒞ᵒᵖ ℤ ⥤ K(𝒞)ᵒᵖ`: the quotient functor
`CochainComplex 𝒞 ℤ ⥤ K(𝒞)` read in the opposite categories, transported along the duality
`CochainComplex 𝒞ᵒᵖ ℤ ≌ (CochainComplex 𝒞 ℤ)ᵒᵖ` of `CochainComplex.opEquivalence`. -/
public def opQuotient : CochainComplex Cᵒᵖ ℤ ⥤ (HomotopyCategory C (ComplexShape.up ℤ))ᵒᵖ :=
  (CochainComplex.opEquivalence C).inverse ⋙
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).op

/-- `opQuotient` is a localization functor for the homotopy equivalences of
`CochainComplex 𝒞ᵒᵖ ℤ`. Indeed the opposite of the quotient functor is one for the opposites of
the homotopy equivalences of `CochainComplex 𝒞 ℤ`, and the duality
`CochainComplex 𝒞ᵒᵖ ℤ ≌ (CochainComplex 𝒞 ℤ)ᵒᵖ` matches the two classes of morphisms by
`CochainComplex.homotopyEquivalences_opEquivalence_functor_map_iff`. -/
public lemma isLocalization_opQuotient :
    (opQuotient (C := C)).IsLocalization
      (HomologicalComplex.homotopyEquivalences Cᵒᵖ (ComplexShape.up ℤ)) := by
  exact CochainComplex.isLocalization_inverse_comp_op
    (HomotopyCategory.quotient C (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ)) _
    fun f ↦ CochainComplex.homotopyEquivalences_opEquivalence_functor_map_iff f

attribute [local instance] isLocalization_opQuotient

/-- The duality `K(𝒞)ᵒᵖ ≌ K(𝒞ᵒᵖ)`, as the comparison of two localizations of
`CochainComplex 𝒞ᵒᵖ ℤ` at the homotopy equivalences: `opQuotient` and the quotient functor. -/
public noncomputable def homotopyOpEquivalence :
    (HomotopyCategory C (ComplexShape.up ℤ))ᵒᵖ ≌ HomotopyCategory Cᵒᵖ (ComplexShape.up ℤ) :=
  Localization.uniq opQuotient (HomotopyCategory.quotient Cᵒᵖ (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences Cᵒᵖ (ComplexShape.up ℤ))

/-- The comparison of `opQuotient` with the quotient functor along `homotopyOpEquivalence`. -/
public noncomputable def opQuotientCompHomotopyOpEquivalenceFunctorIso :
    opQuotient ⋙ (homotopyOpEquivalence (C := C)).functor ≅
      HomotopyCategory.quotient Cᵒᵖ (ComplexShape.up ℤ) :=
  Localization.compUniqFunctor _ _ _

end HomotopyCategory

namespace DerivedCategory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory C]

/-- The localization functor `CochainComplex 𝒜ᵒᵖ ℤ ⥤ D(𝒜)ᵒᵖ`: the localization functor
`Q : CochainComplex 𝒜 ℤ ⥤ D(𝒜)` read in the opposite categories, transported along the duality
`CochainComplex 𝒜ᵒᵖ ℤ ≌ (CochainComplex 𝒜 ℤ)ᵒᵖ` of `CochainComplex.opEquivalence`. -/
public noncomputable def opQ : CochainComplex Cᵒᵖ ℤ ⥤ (DerivedCategory C)ᵒᵖ :=
  (CochainComplex.opEquivalence C).inverse ⋙ (DerivedCategory.Q (C := C)).op

/-- `opQ` is a localization functor for the quasi-isomorphisms of `CochainComplex 𝒜ᵒᵖ ℤ`. Indeed
`Q.op` is one for the opposites of the quasi-isomorphisms of `CochainComplex 𝒜 ℤ`
(`CategoryTheory.Functor.IsLocalization.op`), and the duality
`CochainComplex 𝒜ᵒᵖ ℤ ≌ (CochainComplex 𝒜 ℤ)ᵒᵖ` matches the two classes of morphisms by
`CochainComplex.quasiIso_opEquivalence_functor_map_iff`. -/
public lemma isLocalization_opQ :
    (opQ (C := C)).IsLocalization (HomologicalComplex.quasiIso Cᵒᵖ (ComplexShape.up ℤ)) := by
  exact CochainComplex.isLocalization_inverse_comp_op DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _
    fun f ↦ CochainComplex.quasiIso_opEquivalence_functor_map_iff f

attribute [local instance] isLocalization_opQ

variable [HasDerivedCategory Cᵒᵖ]

/-- The duality `D(𝒜)ᵒᵖ ≌ D(𝒜ᵒᵖ)`, as the comparison of two localizations of
`CochainComplex 𝒜ᵒᵖ ℤ` at the quasi-isomorphisms: `opQ` and `Q`. -/
public noncomputable def derivedOpEquivalence :
    (DerivedCategory C)ᵒᵖ ≌ DerivedCategory Cᵒᵖ :=
  Localization.uniq opQ DerivedCategory.Q (HomologicalComplex.quasiIso Cᵒᵖ (ComplexShape.up ℤ))

/-- The comparison of `opQ` with `Q` along `derivedOpEquivalence`: a complex of `𝒜ᵒᵖ`, viewed in
`D(𝒜)ᵒᵖ` through `opQ` and then transported to `D(𝒜ᵒᵖ)`, is its own image under `Q`. -/
public noncomputable def opQCompDerivedOpEquivalenceFunctorIso :
    opQ ⋙ (derivedOpEquivalence (C := C)).functor ≅ DerivedCategory.Q :=
  Localization.compUniqFunctor _ _ _

/-- `(Q ⋙ H)ᵒᵖ ≅ Qᵒᵖ ⋙ Hᵒᵖ`, whiskered with the duality of complexes: the type has to be written
out for the reassociation to happen, exactly as for `shortComplexOpBridge`. -/
public noncomputable def opQHomologyBridge (m : ℤ) :
    (CochainComplex.opEquivalence C).inverse ⋙
        (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor C (-m)).op ≅
      opQ ⋙ (DerivedCategory.homologyFunctor C (-m)).op :=
  Iso.refl _

/-- **The homology exchange, at the level of derived categories.** Under the duality
`D(𝒜)ᵒᵖ ≌ D(𝒜ᵒᵖ)`, the homology of the transported object in degree `m` is the opposite of the
homology in degree `-m`, naturally.

Both sides are functors out of `D(𝒜)ᵒᵖ`, which is a localization of `CochainComplex 𝒜ᵒᵖ ℤ` at the
quasi-isomorphisms through `opQ`; so it is enough to compare their restrictions along `opQ`
(`Localization.liftNatIso`), and there the comparison is `CochainComplex.homologyOpNatIso'`
between the two factorizations of homology through complexes
(`DerivedCategory.homologyFunctorFactors`). -/
public noncomputable def derivedHomologyOpNatIso (m : ℤ) :
    (derivedOpEquivalence (C := C)).functor ⋙ DerivedCategory.homologyFunctor Cᵒᵖ m ≅
      (DerivedCategory.homologyFunctor C (-m)).op :=
  Localization.liftNatIso (opQ (C := C))
    (HomologicalComplex.quasiIso Cᵒᵖ (ComplexShape.up ℤ))
    (opQ ⋙ ((derivedOpEquivalence (C := C)).functor ⋙ DerivedCategory.homologyFunctor Cᵒᵖ m))
    (opQ ⋙ (DerivedCategory.homologyFunctor C (-m)).op) _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (opQCompDerivedOpEquivalenceFunctorIso (C := C))
        (DerivedCategory.homologyFunctor Cᵒᵖ m) ≪≫
      DerivedCategory.homologyFunctorFactors Cᵒᵖ m ≪≫
      CochainComplex.homologyOpNatIso' m ≪≫
      Functor.isoWhiskerLeft (CochainComplex.opEquivalence C).inverse
        (NatIso.op (DerivedCategory.homologyFunctorFactors C (-m))) ≪≫
      opQHomologyBridge m)

/-- `derivedHomologyOpNatIso` with the two degrees named by the relation `m + n = 0` rather than by
a negation, so that using it does not require rewriting with `neg_neg`. -/
public noncomputable def derivedHomologyOpNatIso' (m n : ℤ) (hmn : m + n = 0) :
    (derivedOpEquivalence (C := C)).functor ⋙ DerivedCategory.homologyFunctor Cᵒᵖ m ≅
      (DerivedCategory.homologyFunctor C n).op := by
  obtain rfl : n = -m := by omega
  exact derivedHomologyOpNatIso m

/-- `derivedHomologyOpNatIso` at an object, with the two degrees named by the relation `m + n = 0`
rather than by a negation, so that using it does not require rewriting with `neg_neg`. -/
public noncomputable def derivedHomologyOpObjIso (m n : ℤ) (hmn : m + n = 0)
    (X : DerivedCategory C) :
    (DerivedCategory.homologyFunctor Cᵒᵖ m).obj
        ((derivedOpEquivalence (C := C)).functor.obj (Opposite.op X)) ≅
      Opposite.op ((DerivedCategory.homologyFunctor C n).obj X) := by
  obtain rfl : n = -m := by omega
  exact (derivedHomologyOpNatIso m).app (Opposite.op X)

/-- **The bounds exchange.** The transported object is cohomologically `≥ -m` exactly when the
original is cohomologically `≤ m`. Both conditions are the vanishing of homology outside a range
(`DerivedCategory.isGE_iff`, `DerivedCategory.isLE_iff`), and `derivedHomologyOpObjIso` matches
the two ranges degree by degree. -/
public lemma isGE_derivedOpEquivalence_functor_obj_iff (X : DerivedCategory C) (m : ℤ) :
    ((derivedOpEquivalence (C := C)).functor.obj (Opposite.op X)).IsGE (-m) ↔ X.IsLE m := by
  rw [DerivedCategory.isGE_iff, DerivedCategory.isLE_iff]
  constructor
  · intro h i hi
    exact ((h (-i) (by omega)).of_iso (derivedHomologyOpObjIso (-i) i (by omega) X).symm).unop
  · intro h i hi
    exact ((h (-i) (by omega)).op).of_iso (derivedHomologyOpObjIso i (-i) (by omega) X)

/-- Precomposition with the transported `truncLEι` is injective on morphisms into any object that
comes from the duality: the duality is fully faithful, so such a composite is the image of a
composite in `D(𝒜)`, and `truncLE` is characterized by the fact that
`- ≫ (truncLEι m).app X` is injective on morphisms out of an object which is `≤ m`
(`TStructure.to_truncLE_obj_ext`). -/
public lemma cancel_functor_map_op_truncLEι (m : ℤ) (X W : DerivedCategory C)
    [TStructure.t.IsLE W m]
    {f g : (derivedOpEquivalence (C := C)).functor.obj
        (Opposite.op ((TStructure.t.truncLE m).obj X)) ⟶
      (derivedOpEquivalence (C := C)).functor.obj (Opposite.op W)}
    (h : (derivedOpEquivalence (C := C)).functor.map ((TStructure.t.truncLEι m).app X).op ≫ f =
      (derivedOpEquivalence (C := C)).functor.map ((TStructure.t.truncLEι m).app X).op ≫ g) :
    f = g := by
  obtain ⟨f', rfl⟩ := (derivedOpEquivalence (C := C)).functor.map_surjective f
  obtain ⟨g', rfl⟩ := (derivedOpEquivalence (C := C)).functor.map_surjective g
  rw [← Functor.map_comp, ← Functor.map_comp] at h
  have h' := Quiver.Hom.op_inj ((derivedOpEquivalence (C := C)).functor.map_injective h)
  congr 1
  exact Quiver.Hom.unop_inj (TStructure.t.to_truncLE_obj_ext h')

/-- **The truncation exchange.** Under the duality `D(𝒜)ᵒᵖ ≌ D(𝒜ᵒᵖ)`, the transport of
`τ_{≤ m} X ⟶ X` is `X' ⟶ τ_{≥ -m} X'`: there is an isomorphism identifying the transported
truncation with the canonical one, compatibly with the two canonical maps.

No triangulated structure on the duality is needed, only the universal properties of the two
truncations. The transported object `X'` is `≥ -m` by `isGE_derivedOpEquivalence_functor_obj_iff`,
so `TStructure.descTruncGE` produces a map `τ_{≥ -m} X' ⟶ (τ_{≤ m} X)'` under `X'`. In the other
direction, the object `W` of `D(𝒜)` from which `τ_{≥ -m} X'` comes is `≤ m` by the same
equivalence, so `TStructure.liftTruncLE` factors the corresponding map `W ⟶ X` through
`τ_{≤ m} X`, and transporting that factorization back gives a map under `X'`. The two composites
are identities by the two extensionality lemmas, `TStructure.from_truncGE_obj_ext` on one side and
`cancel_functor_map_op_truncLEι` on the other. -/
public lemma exists_truncOpIso (m : ℤ) (X : DerivedCategory C) :
    ∃ θ : (derivedOpEquivalence (C := C)).functor.obj
          (Opposite.op ((TStructure.t.truncLE m).obj X)) ≅
        (TStructure.t.truncGE (-m)).obj
          ((derivedOpEquivalence (C := C)).functor.obj (Opposite.op X)),
      (derivedOpEquivalence (C := C)).functor.map ((TStructure.t.truncLEι m).app X).op ≫ θ.hom =
        (TStructure.t.truncGEπ (-m)).app
          ((derivedOpEquivalence (C := C)).functor.obj (Opposite.op X)) := by
  have hX' : TStructure.t.IsGE ((derivedOpEquivalence (C := C)).functor.obj
      (Opposite.op ((TStructure.t.truncLE m).obj X))) (-m) :=
    (isGE_derivedOpEquivalence_functor_obj_iff ((TStructure.t.truncLE m).obj X) m).2 inferInstance
  refine Triangulated.TStructure.exists_isoTruncGE TStructure.t (-m)
    ((derivedOpEquivalence (C := C)).functor.map ((TStructure.t.truncLEι m).app X).op)
    (fun Z hZ g ↦ ?_)
  have : TStructure.t.IsGE ((𝟭 (DerivedCategory Cᵒᵖ)).obj Z) (-m) := hZ
  -- `Z` comes from an object of `D(𝒜)` which is `≤ m`
  have hZ₀ : TStructure.t.IsLE ((derivedOpEquivalence (C := C)).inverse.obj Z).unop m :=
    (isGE_derivedOpEquivalence_functor_obj_iff _ m).1
      (TStructure.t.isGE_of_iso ((derivedOpEquivalence (C := C)).counitIso.app Z).symm (-m))
  set ζ := (derivedOpEquivalence (C := C)).counitIso.app Z with hζ
  -- the morphism of `D(𝒜)` corresponding to `g`, factored through `τ_{≤ m} X`
  set q := (derivedOpEquivalence (C := C)).functor.preimage (g ≫ ζ.inv) with hq
  set w := (derivedOpEquivalence (C := C)).functor.map
    (TStructure.t.liftTruncLE q.unop m).op ≫ ζ.hom with hw
  have hwg : (derivedOpEquivalence (C := C)).functor.map
      ((TStructure.t.truncLEι m).app X).op ≫ w = g := by
    rw [hw, ← Category.assoc, ← Functor.map_comp,
      show ((TStructure.t.truncLEι m).app X).op ≫ (TStructure.t.liftTruncLE q.unop m).op =
        q from Quiver.Hom.unop_inj (TStructure.t.liftTruncLE_ι q.unop m),
      hq, Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨w, hwg, fun v hv ↦ ?_⟩
  refine (cancel_mono ζ.inv).1 (cancel_functor_map_op_truncLEι m X
    ((derivedOpEquivalence (C := C)).inverse.obj Z).unop ?_)
  rw [← Category.assoc, ← Category.assoc, hv, hwg]

/-- **The bounds exchange, the other side.** The transported object is cohomologically `≤ -m`
exactly when the original is cohomologically `≥ m`. -/
public lemma isLE_derivedOpEquivalence_functor_obj_iff (X : DerivedCategory C) (m : ℤ) :
    ((derivedOpEquivalence (C := C)).functor.obj (Opposite.op X)).IsLE (-m) ↔ X.IsGE m := by
  rw [DerivedCategory.isLE_iff, DerivedCategory.isGE_iff]
  constructor
  · intro h i hi
    exact ((h (-i) (by omega)).of_iso (derivedHomologyOpObjIso (-i) i (by omega) X).symm).unop
  · intro h i hi
    exact ((h (-i) (by omega)).op).of_iso (derivedHomologyOpObjIso i (-i) (by omega) X)

/-- Postcomposition with the transported `truncGEπ` is injective on morphisms out of any object
that comes from the duality: the dual of `cancel_functor_map_op_truncLEι`, resting on
`TStructure.from_truncGE_obj_ext`. -/
public lemma cancel_functor_map_op_truncGEπ (m : ℤ) (X W : DerivedCategory C)
    [TStructure.t.IsGE W m]
    {f g : (derivedOpEquivalence (C := C)).functor.obj (Opposite.op W) ⟶
      (derivedOpEquivalence (C := C)).functor.obj
        (Opposite.op ((TStructure.t.truncGE m).obj X))}
    (h : f ≫ (derivedOpEquivalence (C := C)).functor.map ((TStructure.t.truncGEπ m).app X).op =
      g ≫ (derivedOpEquivalence (C := C)).functor.map ((TStructure.t.truncGEπ m).app X).op) :
    f = g := by
  obtain ⟨f', rfl⟩ := (derivedOpEquivalence (C := C)).functor.map_surjective f
  obtain ⟨g', rfl⟩ := (derivedOpEquivalence (C := C)).functor.map_surjective g
  rw [← Functor.map_comp, ← Functor.map_comp] at h
  have h' := Quiver.Hom.op_inj ((derivedOpEquivalence (C := C)).functor.map_injective h)
  congr 1
  exact Quiver.Hom.unop_inj (TStructure.t.from_truncGE_obj_ext h')

/-- **The truncation exchange, the other side.** Under the duality `D(𝒜)ᵒᵖ ≌ D(𝒜ᵒᵖ)`, the transport
of `X ⟶ τ_{≥ m} X` is `τ_{≤ -m} X' ⟶ X'`. Dual to `exists_truncOpIso`, and again only the
universal properties of the truncations are used: `TStructure.descTruncGE` provides the
factorizations in `D(𝒜)` and `Triangulated.TStructure.exists_isoTruncLE` turns them into the
isomorphism. -/
public lemma exists_truncOpIso' (m : ℤ) (X : DerivedCategory C) :
    ∃ θ : (derivedOpEquivalence (C := C)).functor.obj
          (Opposite.op ((TStructure.t.truncGE m).obj X)) ≅
        (TStructure.t.truncLE (-m)).obj
          ((derivedOpEquivalence (C := C)).functor.obj (Opposite.op X)),
      θ.hom ≫ (TStructure.t.truncLEι (-m)).app
          ((derivedOpEquivalence (C := C)).functor.obj (Opposite.op X)) =
        (derivedOpEquivalence (C := C)).functor.map
          ((TStructure.t.truncGEπ m).app X).op := by
  have hX' : TStructure.t.IsLE ((derivedOpEquivalence (C := C)).functor.obj
      (Opposite.op ((TStructure.t.truncGE m).obj X))) (-m) :=
    (isLE_derivedOpEquivalence_functor_obj_iff ((TStructure.t.truncGE m).obj X) m).2 inferInstance
  refine Triangulated.TStructure.exists_isoTruncLE TStructure.t (-m)
    ((derivedOpEquivalence (C := C)).functor.map ((TStructure.t.truncGEπ m).app X).op)
    (fun Z hZ g ↦ ?_)
  have : TStructure.t.IsLE ((𝟭 (DerivedCategory Cᵒᵖ)).obj Z) (-m) := hZ
  -- `Z` comes from an object of `D(𝒜)` which is `≥ m`
  have hZ₀ : TStructure.t.IsGE ((derivedOpEquivalence (C := C)).inverse.obj Z).unop m :=
    (isLE_derivedOpEquivalence_functor_obj_iff _ m).1
      (TStructure.t.isLE_of_iso ((derivedOpEquivalence (C := C)).counitIso.app Z).symm (-m))
  set ζ := (derivedOpEquivalence (C := C)).counitIso.app Z with hζ
  set q := (derivedOpEquivalence (C := C)).functor.preimage (ζ.hom ≫ g) with hq
  set w := ζ.inv ≫ (derivedOpEquivalence (C := C)).functor.map
    (TStructure.t.descTruncGE q.unop m).op with hw
  have hwg : w ≫ (derivedOpEquivalence (C := C)).functor.map
      ((TStructure.t.truncGEπ m).app X).op = g := by
    rw [hw, Category.assoc, ← Functor.map_comp,
      show (TStructure.t.descTruncGE q.unop m).op ≫ ((TStructure.t.truncGEπ m).app X).op =
        q from Quiver.Hom.unop_inj (TStructure.t.π_descTruncGE q.unop m),
      hq, Functor.map_preimage, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine ⟨w, hwg, fun v hv ↦ ?_⟩
  refine (cancel_epi ζ.hom).1 (cancel_functor_map_op_truncGEπ m X
    ((derivedOpEquivalence (C := C)).inverse.obj Z).unop ?_)
  rw [Category.assoc, Category.assoc, hv, hwg]

end DerivedCategory


/-! ### Opposites of Kan extensions

The machinery relating a left Kan extension along `L` to a right Kan extension along `L.op`,
shared by the developments that read a derived functor on the opposite category. -/

namespace CategoryTheory.Functor

/-- Invertibility of a morphism is unchanged by composing with isomorphisms on either side. -/
public lemma isIso_iff_of_eq_comp {H : Type u₃} [Category.{v₃} H] {X Y Z T : H} (u : X ≅ Y)
    (f : Y ⟶ Z) (v : Z ≅ T) (g : X ⟶ T) (h : g = u.hom ≫ f ≫ v.hom) : IsIso g ↔ IsIso f := by
  subst h
  exact (isIso_comp_left_iff u.hom (f ≫ v.hom)).trans (isIso_comp_right_iff f v.hom)

section Op

variable {C : Type u₁} {D : Type u₂} {H : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H]

/-- The opposite of a counit `α : L ⋙ LF ⟶ F`, read as a unit `F.op ⟶ L.op ⋙ LF.op`. This is
`NatTrans.op α`; it is given a name because the unifier of `IsLeftKanExtension` does not see
through the definitional equality `(L ⋙ LF).op = L.op ⋙ LF.op` and a type ascription does not
help. -/
public def opCounit {L : C ⥤ D} {F : C ⥤ H} (LF : D ⥤ H) (α : L ⋙ LF ⟶ F) :
    F.op ⟶ L.op ⋙ LF.op := NatTrans.op α

public lemma opCounit_app {L : C ⥤ D} {F : C ⥤ H} (LF : D ⥤ H) (α : L ⋙ LF ⟶ F) (X : Cᵒᵖ) :
    (opCounit LF α).app X = (α.app X.unop).op := rfl

attribute [local simp] opCounit_app

/-- A unit `β : F.op ⟶ L.op ⋙ G` read as a counit `L ⋙ G.unop ⟶ F`. -/
public def unopUnit {L : C ⥤ D} {F : C ⥤ H} (G : Dᵒᵖ ⥤ Hᵒᵖ) (β : F.op ⟶ L.op ⋙ G) :
    L ⋙ G.unop ⟶ F :=
  NatTrans.removeOp (β ≫ whiskerLeft L.op G.unopOpIso.inv)

public lemma opCounit_unopUnit {L : C ⥤ D} {F : C ⥤ H} (G : Dᵒᵖ ⥤ Hᵒᵖ)
    (β : F.op ⟶ L.op ⋙ G) :
    opCounit G.unop (unopUnit G β) = β ≫ whiskerLeft L.op G.unopOpIso.inv := by
  ext X; simp [opCounit, unopUnit]

/-- Two morphisms into a functor whose opposite is a left Kan extension agree as soon as they
agree after whiskering by `L` and composing with the counit.

The hypothesis `LF.op.IsLeftKanExtension (opCounit LF α)` is written as a binder of the
declaration rather than as a `variable` of the section: in a `variable` binder the application
`opCounit LF α` of the private definition `opCounit` does not elaborate. -/
public lemma hom_ext_of_op {L : C ⥤ D} {F : C ⥤ H} (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    [LF.op.IsLeftKanExtension (opCounit LF α)] {G : D ⥤ H} (γ₁ γ₂ : G ⟶ LF)
    (h : whiskerLeft L γ₁ ≫ α = whiskerLeft L γ₂ ≫ α) : γ₁ = γ₂ := by
  have key : NatTrans.op γ₁ = NatTrans.op γ₂ := by
    refine LF.op.hom_ext_of_isLeftKanExtension (opCounit LF α) _ _ ?_
    ext X
    have := NatTrans.congr_app h X.unop
    dsimp at this ⊢
    exact this
  ext X
  exact Quiver.Hom.op_inj (NatTrans.congr_app key (Opposite.op X))

/-- If `LF.op` is a left Kan extension of `F.op` along `L.op`, then `LF` is a right Kan
extension of `F` along `L`. -/
public lemma isRightKanExtension_of_op {L : C ⥤ D} {F : C ⥤ H} (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    [LF.op.IsLeftKanExtension (opCounit LF α)] : LF.IsRightKanExtension α where
  nonempty_isUniversal := ⟨IsTerminal.ofUniqueHom
    (fun e => CostructuredArrow.homMk
      (NatTrans.removeOp (LF.op.descOfIsLeftKanExtension
        (opCounit LF α) e.left.op (NatTrans.op e.hom))) (by
        ext X
        have := LF.op.descOfIsLeftKanExtension_fac_app
          (opCounit LF α) e.left.op (NatTrans.op e.hom) (Opposite.op X)
        dsimp at this ⊢
        exact Quiver.Hom.op_inj this))
    (fun e m => by
      ext1
      refine hom_ext_of_op LF α _ _ ?_
      ext X
      have h1 := NatTrans.congr_app (CostructuredArrow.w m) X
      have h2 := LF.op.descOfIsLeftKanExtension_fac_app
        (opCounit LF α) e.left.op (NatTrans.op e.hom) (Opposite.op X)
      dsimp at h1 h2 ⊢
      rw [h1]
      exact (Quiver.Hom.op_inj h2).symm)⟩

/-- If `(LF, α)` is a right Kan extension of `F` along `L`, then `(LF.op, opCounit LF α)` is a
left Kan extension of `F.op` along `L.op`. This is the converse of `isRightKanExtension_of_op`:
the universal property is read in the opposite categories, a terminal object of the category of
right extensions of `F` along `L` becoming an initial object of the category of left extensions
of `F.op` along `L.op`. -/
public lemma isLeftKanExtension_op {L : C ⥤ D} {F : C ⥤ H} (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    [LF.IsRightKanExtension α] : LF.op.IsLeftKanExtension (opCounit LF α) where
  nonempty_isUniversal := ⟨IsInitial.ofUniqueHom
    (fun e => StructuredArrow.homMk
      (NatTrans.op (LF.liftOfIsRightKanExtension α e.right.unop (unopUnit e.right e.hom)) ≫
        e.right.unopOpIso.hom) (by
        ext X
        have h := LF.liftOfIsRightKanExtension_fac_app α e.right.unop
          (unopUnit e.right e.hom) X.unop
        dsimp [unopUnit] at h ⊢
        simp only [unopOpIso_hom_app, unopOpIso_inv_app, Category.id_comp,
          unop_id] at h ⊢
        exact h))
    (fun e m => by
      ext1
      have hm := StructuredArrow.w m
      have key : NatTrans.removeOp (m.right ≫ e.right.unopOpIso.inv) =
          LF.liftOfIsRightKanExtension α e.right.unop (unopUnit e.right e.hom) := by
        refine LF.hom_ext_of_isRightKanExtension α _ _ ?_
        rw [LF.liftOfIsRightKanExtension_fac α _ _]
        ext x
        have h2 := NatTrans.congr_app hm (Opposite.op x)
        dsimp [unopUnit] at h2 ⊢
        simp only [unopOpIso_inv_app, unop_id, Category.id_comp] at h2 ⊢
        rw [← h2]
        exact rfl
      ext X
      have h3 := NatTrans.congr_app key X.unop
      dsimp at h3 ⊢
      simp only [unopOpIso_inv_app, unopOpIso_hom_app, unop_id, Category.id_comp] at h3 ⊢
      rw [← h3])⟩

/-- A right Kan extension along `L` exists as soon as a left Kan extension along `L.op` does. -/
public lemma hasRightKanExtension_of_op {L : C ⥤ D} {Φ : C ⥤ H}
    (h : HasLeftKanExtension L.op Φ.op) : HasRightKanExtension L Φ := by
  have := h
  let G : Dᵒᵖ ⥤ Hᵒᵖ := leftKanExtension L.op Φ.op
  let β : Φ.op ⟶ L.op ⋙ G := leftKanExtensionUnit L.op Φ.op
  have h2 : (G.unop).op.IsLeftKanExtension (β ≫ whiskerLeft L.op G.unopOpIso.inv) :=
    isLeftKanExtension_of_iso G.unopOpIso.symm β _ rfl
  rw [← opCounit_unopUnit G β] at h2
  have := h2
  have := isRightKanExtension_of_op (G.unop) (unopUnit G β)
  exact HasRightKanExtension.mk (G.unop) (unopUnit G β)

/-- Transport of the existence of a left Kan extension along equivalences of the source, of the
target of `L`, and of the target of `Φ`. -/
public lemma hasLeftKanExtension_of_equivalence {C₁ C₂ D₁ D₂ H₁ H₂ : Type*}
    [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂] [Category* H₁] [Category* H₂]
    (eC : C₁ ≌ C₂) (eD : D₁ ≌ D₂) (eH : H₁ ≌ H₂)
    {L : C₁ ⥤ D₁} {Φ : C₁ ⥤ H₁} {L' : C₂ ⥤ D₂} {Φ' : C₂ ⥤ H₂}
    (ia : eC.inverse ⋙ L ⋙ eD.functor ≅ L') (ib : eC.inverse ⋙ Φ ⋙ eH.functor ≅ Φ')
    (h : HasLeftKanExtension L' Φ') : HasLeftKanExtension L Φ := by
  have h1 : HasLeftKanExtension (eC.functor ⋙ L') (eC.functor ⋙ Φ') :=
    (LeftExtension.precomp L' Φ' eC.functor).asEquivalence.hasInitial_iff.mp h
  rw [hasLeftExtension_iff_of_iso₁
    (Functor.isoWhiskerLeft eC.functor ia.symm ≪≫ eC.funInvIdAssoc _)] at h1
  rw [hasLeftExtension_iff_of_iso₂ _
    (Functor.isoWhiskerLeft eC.functor ib.symm ≪≫ eC.funInvIdAssoc _)] at h1
  rw [hasLeftExtension_iff_postcomp₁ (G := eD.functor) (Iso.refl (L ⋙ eD.functor))] at h1
  exact (LeftExtension.postcompose₂ L Φ eH.functor).asEquivalence.hasInitial_iff.mpr h1

end Op

end CategoryTheory.Functor


/-! ### Reading a derived functor on the opposite category

The comparison isomorphisms between the two dualities `K(A)ᵒᵖ ≌ K(Aᵒᵖ)` and `D(A)ᵒᵖ ≌ D(Aᵒᵖ)`,
and the transport of a left derived functor and its unit across them. -/

namespace CategoryTheory.Functor

open ZeroObject HomotopyCategory DerivedCategory

/-- An equivalence's inverse undoes its functor up to conjugation by the unit isomorphism, so any
functor inverts `e.inverse.map (e.functor.map f)` exactly when it inverts `f`. -/
public lemma isIso_map_inverse_map_functor_map_iff {𝒞 : Type u₃} [Category.{v₃} 𝒞]
    {𝒟 : Type u₄} [Category.{v₄} 𝒟] {ℰ : Type u₂} [Category.{v₂} ℰ]
    (e : 𝒞 ≌ 𝒟) (Φ : 𝒞 ⥤ ℰ) {X Y : 𝒞} (f : X ⟶ Y) :
    IsIso (Φ.map (e.inverse.map (e.functor.map f))) ↔ IsIso (Φ.map f) := by
  rw [show e.inverse.map (e.functor.map f) =
      (e.unitIso.app X).inv ≫ f ≫ (e.unitIso.app Y).hom by simp, Φ.map_comp, Φ.map_comp]
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  have h1 : IsIso (Φ.map f ≫ Φ.map (e.unitIso.app Y).hom) :=
    IsIso.of_isIso_comp_left (Φ.map (e.unitIso.app X).inv) _
  exact IsIso.of_isIso_comp_right (Φ.map f) (Φ.map (e.unitIso.app Y).hom)

section DualityComparison

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory Aᵒᵖ] [HasDerivedCategory Bᵒᵖ]

attribute [local instance] isLocalization_opQ isLocalization_opQuotient

/-- The two dualities `K(𝒜)ᵒᵖ ≌ K(𝒜ᵒᵖ)` and `D(𝒜)ᵒᵖ ≌ D(𝒜ᵒᵖ)` are compatible with the
localization functors `Qh`. Both sides restrict along the localization functor `opQuotient` to
`Q : CochainComplex 𝒜ᵒᵖ ℤ ⥤ D(𝒜ᵒᵖ)`, so `Localization.liftNatIso` produces the isomorphism. -/
public noncomputable def homotopyOpEquivalenceFunctorCompQhIso :
    (homotopyOpEquivalence (C := A)).functor ⋙ DerivedCategory.Qh ≅
      DerivedCategory.Qh.op ⋙ (derivedOpEquivalence (C := A)).functor :=
  letI _h₁ : Localization.Lifting (opQuotient (C := A))
      (HomologicalComplex.homotopyEquivalences Aᵒᵖ (ComplexShape.up ℤ))
      DerivedCategory.Q ((homotopyOpEquivalence (C := A)).functor ⋙ DerivedCategory.Qh) :=
    ⟨Functor.isoWhiskerRight (opQuotientCompHomotopyOpEquivalenceFunctorIso (C := A))
      DerivedCategory.Qh ≪≫ DerivedCategory.quotientCompQhIso Aᵒᵖ⟩
  letI _h₂ : Localization.Lifting (opQuotient (C := A))
      (HomologicalComplex.homotopyEquivalences Aᵒᵖ (ComplexShape.up ℤ))
      DerivedCategory.Q (DerivedCategory.Qh.op ⋙ (derivedOpEquivalence (C := A)).functor) :=
    ⟨Functor.isoWhiskerLeft (CochainComplex.opEquivalence A).inverse
      (Functor.isoWhiskerRight (NatIso.op (DerivedCategory.quotientCompQhIso A)).symm
        (derivedOpEquivalence (C := A)).functor) ≪≫
      opQCompDerivedOpEquivalenceFunctorIso⟩
  Localization.liftNatIso (opQuotient (C := A))
    (HomologicalComplex.homotopyEquivalences Aᵒᵖ (ComplexShape.up ℤ))
    DerivedCategory.Q DerivedCategory.Q _ _ (Iso.refl _)

variable (F : A ⥤ B) [F.Additive]

/-- The duality `K(𝒜)ᵒᵖ ≌ K(𝒜ᵒᵖ)` carries the functor `K ↦ F(K)` followed by `Qh` to the same
functor for `F.op`, up to the duality `D(ℬ)ᵒᵖ ≌ D(ℬᵒᵖ)`. Both sides restrict along the
localization functor `opQuotient` to `K ↦ F.op(K)` followed by `Q`; the only computation is the
equality of `(CochainComplex 𝒜ᵒᵖ ℤ ⥤ (CochainComplex ℬ ℤ)ᵒᵖ)`-valued functors
`(CochainComplex.opEquivalence 𝒜).inverse ⋙ (F.mapHomologicalComplex (.up ℤ)).op` and
`F.op.mapHomologicalComplex (.up ℤ) ⋙ (CochainComplex.opEquivalence ℬ).inverse`, which holds by
definition since both restrict a complex `K` to `i ↦ op (F (K (-i)))`. -/
public noncomputable def homotopyOpEquivalenceFunctorCompMapQhIso :
    (homotopyOpEquivalence (C := A)).functor ⋙
        F.op.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).op ⋙
        (derivedOpEquivalence (C := B)).functor :=
  letI _h₁ : Localization.Lifting (opQuotient (C := A))
      (HomologicalComplex.homotopyEquivalences Aᵒᵖ (ComplexShape.up ℤ))
      (F.op.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      ((homotopyOpEquivalence (C := A)).functor ⋙
        F.op.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
    ⟨Functor.isoWhiskerRight (opQuotientCompHomotopyOpEquivalenceFunctorIso (C := A))
        (F.op.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ≪≫
      Functor.isoWhiskerRight (F.op.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
        DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft (F.op.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.quotientCompQhIso Bᵒᵖ)⟩
  letI _h₂ : Localization.Lifting (opQuotient (C := A))
      (HomologicalComplex.homotopyEquivalences Aᵒᵖ (ComplexShape.up ℤ))
      (F.op.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).op ⋙
        (derivedOpEquivalence (C := B)).functor) :=
    ⟨Functor.isoWhiskerLeft (CochainComplex.opEquivalence A).inverse
        (Functor.isoWhiskerRight
          ((NatIso.op (Functor.isoWhiskerRight
              (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) DerivedCategory.Qh)).symm ≪≫
            (NatIso.op (Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
              (DerivedCategory.quotientCompQhIso B))).symm)
          (derivedOpEquivalence (C := B)).functor) ≪≫
      Functor.isoWhiskerLeft (F.op.mapHomologicalComplex (ComplexShape.up ℤ))
        (opQCompDerivedOpEquivalenceFunctorIso (C := B))⟩
  Localization.liftNatIso (opQuotient (C := A))
    (HomologicalComplex.homotopyEquivalences Aᵒᵖ (ComplexShape.up ℤ))
    (F.op.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (F.op.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) _ _ (Iso.refl _)

end DualityComparison

section Transport

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory Aᵒᵖ] [HasDerivedCategory Bᵒᵖ]

attribute [local instance] isLocalization_opQ isLocalization_opQuotient

/-- The two dualities `K(𝒜)ᵒᵖ ≌ K(𝒜ᵒᵖ)` and `D(𝒜)ᵒᵖ ≌ D(𝒜ᵒᵖ)` read from the side of the
inverse functors: `Qh.op` precomposed with `K(𝒜ᵒᵖ) ⥤ K(𝒜)ᵒᵖ` is `Qh` followed by
`D(𝒜ᵒᵖ) ⥤ D(𝒜)ᵒᵖ`. This is `homotopyOpEquivalenceFunctorCompQhIso` transported across the two
equivalences. -/
public noncomputable def inverseCompQhOpIso :
    (homotopyOpEquivalence (C := A)).inverse ⋙ DerivedCategory.Qh.op ≅
      DerivedCategory.Qh ⋙ (derivedOpEquivalence (C := A)).inverse :=
  Functor.isoWhiskerLeft (homotopyOpEquivalence (C := A)).inverse
      (((Functor.associator (homotopyOpEquivalence (C := A)).functor DerivedCategory.Qh
            (derivedOpEquivalence (C := A)).inverse).symm ≪≫
          Functor.isoWhiskerRight (homotopyOpEquivalenceFunctorCompQhIso (A := A))
            (derivedOpEquivalence (C := A)).inverse ≪≫
          Functor.associator DerivedCategory.Qh.op (derivedOpEquivalence (C := A)).functor
            (derivedOpEquivalence (C := A)).inverse ≪≫
          Functor.isoWhiskerLeft DerivedCategory.Qh.op
            (derivedOpEquivalence (C := A)).unitIso.symm ≪≫
          DerivedCategory.Qh.op.rightUnitor).symm) ≪≫
    (homotopyOpEquivalence (C := A)).invFunIdAssoc
      (DerivedCategory.Qh ⋙ (derivedOpEquivalence (C := A)).inverse)

variable (F : A ⥤ B) [F.Additive]

/-- The duality `K(𝒜ᵒᵖ) ⥤ K(𝒜)ᵒᵖ` carries `K ↦ F.op(K)` followed by `Qh` to `K ↦ F(K)` followed
by `Qh`, read in the opposite categories and transported to `D(ℬᵒᵖ)`. This is
`homotopyOpEquivalenceFunctorCompMapQhIso` read from the side of the inverse functor. -/
public noncomputable def inverseCompMapQhOpIso :
    F.op.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      (homotopyOpEquivalence (C := A)).inverse ⋙
        (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).op ⋙
          (derivedOpEquivalence (C := B)).functor :=
  ((homotopyOpEquivalence (C := A)).invFunIdAssoc
      (F.op.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)).symm ≪≫
    Functor.isoWhiskerLeft (homotopyOpEquivalence (C := A)).inverse
      (homotopyOpEquivalenceFunctorCompMapQhIso F)

variable (LF : DerivedCategory A ⥤ DerivedCategory B)
  (α : DerivedCategory.Qh ⋙ LF ⟶
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)

/-- A left derived functor `LF : D(𝒜) ⥤ D(ℬ)` of `F` read on the opposite side: the functor
`D(𝒜ᵒᵖ) ⥤ D(ℬᵒᵖ)` obtained from `LF.op` by the dualities `D(𝒜)ᵒᵖ ≌ D(𝒜ᵒᵖ)` and
`D(ℬ)ᵒᵖ ≌ D(ℬᵒᵖ)`. -/
public noncomputable def opLF : DerivedCategory Aᵒᵖ ⥤ DerivedCategory Bᵒᵖ :=
  (derivedOpEquivalence (C := A)).inverse ⋙ LF.op ⋙ (derivedOpEquivalence (C := B)).functor

/-- The counit `α` of a left derived functor, read as the unit of `LF.op` and transported to
`D(ℬᵒᵖ)`; it is a unit for `opLF` over `D(𝒜ᵒᵖ)` once the source is compared along
`inverseCompQhOpIso`. -/
public noncomputable def opAlpha :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).op ⋙
        (derivedOpEquivalence (C := B)).functor ⟶
      DerivedCategory.Qh.op ⋙ LF.op ⋙ (derivedOpEquivalence (C := B)).functor :=
  Functor.whiskerRight (opCounit LF α) (derivedOpEquivalence (C := B)).functor ≫
    (Functor.associator _ _ _).hom

/-- The unit of the transported functor `opLF`: the natural transformation making `opLF` a right
derived functor of `F.op` along `Qh : K(𝒜ᵒᵖ) ⥤ D(𝒜ᵒᵖ)`. Its shape is dictated by
`CategoryTheory.Functor.isLeftKanExtension_iff_precomp_equivalence`, so that the compatibility
that lemma asks for holds by definition. -/
public noncomputable def opAlphaTransport :
    F.op.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ opLF LF :=
  (inverseCompMapQhOpIso F).hom ≫
    Functor.whiskerLeft (homotopyOpEquivalence (C := A)).inverse (opAlpha F LF α) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (inverseCompQhOpIso (A := A)).hom
      (LF.op ⋙ (derivedOpEquivalence (C := B)).functor) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft DerivedCategory.Qh (Iso.refl (opLF LF)).hom

variable [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- The opposite of a left derived functor of `F` on `D(𝒜)` is a right derived functor of `F.op`
on `D(𝒜ᵒᵖ)`. Only the universal property enters: `LF.op` is a left Kan extension of the opposite
functor along `Qh.op` (`isLeftKanExtension_op`), postcomposing with the equivalence
`D(ℬ)ᵒᵖ ≌ D(ℬᵒᵖ)` preserves that, and the two equivalences `K(𝒜)ᵒᵖ ≌ K(𝒜ᵒᵖ)`,
`D(𝒜)ᵒᵖ ≌ D(𝒜ᵒᵖ)` move it to a left Kan extension along `Qh : K(𝒜ᵒᵖ) ⥤ D(𝒜ᵒᵖ)`. -/
public lemma isRightDerivedFunctor_opLF :
    (opLF LF).IsRightDerivedFunctor (opAlphaTransport F LF α)
      (HomotopyCategory.quasiIso Aᵒᵖ (ComplexShape.up ℤ)) := by
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension LF α
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension,
    ← Functor.isLeftKanExtension_iff_precomp_equivalence (opAlphaTransport F LF α)
      (opAlpha F LF α) (inverseCompQhOpIso (A := A)) (inverseCompMapQhOpIso F)
      (Iso.refl (opLF LF)) rfl]
  exact (Functor.isLeftKanExtension_postcompose₂_iff _ _ _).2 (isLeftKanExtension_op LF α)

omit [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] in
/-- Invertibility of the transported unit `opAlphaTransport` at an object of `K(𝒜ᵒᵖ)` is
invertibility of the counit `α` at the corresponding object of `K(𝒜)`: the two differ by the
comparison isomorphisms of the dualities and by the equivalence `D(ℬ)ᵒᵖ ≌ D(ℬᵒᵖ)`, which
reflects isomorphisms. -/
public lemma isIso_opAlphaTransport_app_iff (X : HomotopyCategory Aᵒᵖ (ComplexShape.up ℤ)) :
    IsIso ((opAlphaTransport F LF α).app X) ↔
      IsIso (α.app ((homotopyOpEquivalence (C := A)).inverse.obj X).unop) := by
  refine Iff.trans (isIso_iff_of_eq_comp ((inverseCompMapQhOpIso F).app X)
      ((derivedOpEquivalence (C := B)).functor.map
        ((opCounit LF α).app ((homotopyOpEquivalence (C := A)).inverse.obj X)))
      ((LF.op ⋙ (derivedOpEquivalence (C := B)).functor).mapIso
        ((inverseCompQhOpIso (A := A)).app X))
      ((opAlphaTransport F LF α).app X) ?_) ?_
  · simp [opAlphaTransport, opAlpha, opLF, Functor.whiskerLeft, Iso.refl]
  rw [opCounit_app]
  constructor
  · intro h
    rw [← isIso_op_iff]
    have := h
    exact isIso_of_reflects_iso _ (derivedOpEquivalence (C := B)).functor
  · intro h
    have : IsIso ((α.app ((homotopyOpEquivalence (C := A)).inverse.obj X).unop).op) :=
      (isIso_op_iff _).2 h
    infer_instance

/-- The complex `Lᵒᵖ` of `𝒜ᵒᵖ` opposite to a complex `L` of `𝒜`, viewed in `K(𝒜ᵒᵖ)` and carried
back along the duality `K(𝒜)ᵒᵖ ≌ K(𝒜ᵒᵖ)`, is the opposite of `L` viewed in `K(𝒜)`. -/
public noncomputable def unopInverseObjQuotientIso (L : CochainComplex A ℤ) :
    ((homotopyOpEquivalence (C := A)).inverse.obj
        ((HomotopyCategory.quotient Aᵒᵖ (ComplexShape.up ℤ)).obj
          ((CochainComplex.opEquivalence A).functor.obj (Opposite.op L)))).unop ≅
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L :=
  Iso.symm (Iso.unop
    ((homotopyOpEquivalence (C := A)).inverse.mapIso
        ((opQuotientCompHomotopyOpEquivalenceFunctorIso (C := A)).app
          ((CochainComplex.opEquivalence A).functor.obj (Opposite.op L))).symm ≪≫
      ((homotopyOpEquivalence (C := A)).unitIso.app
        (opQuotient.obj ((CochainComplex.opEquivalence A).functor.obj (Opposite.op L)))).symm ≪≫
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).op.mapIso
        (((CochainComplex.opEquivalence A).unitIso.app (Opposite.op L)).symm)))

omit [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] in
/-- **Invertibility transported.** `H ^ (-i)` of the map that `opLF LF` induces from the transport
of `f` is invertible exactly when `H ^ i (LF f)` is.

Three reassociations and two isomorphisms: `opLF LF` is by definition
`D(𝒜ᵒᵖ) ⥤ D(𝒜)ᵒᵖ ⥤ D(ℬ)ᵒᵖ ⥤ D(ℬᵒᵖ)`, so the outer homology functor may be absorbed into the last
step and exchanged for `H ^ i` of `ℬ` by `derivedHomologyOpNatIso'`; the first step then undoes
the transport of `f` up to the unit isomorphism
(`isIso_map_inverse_map_functor_map_iff`); and invertibility in `ℬᵒᵖ` is invertibility in `ℬ`. -/
public lemma isIso_homologyFunctor_map_opLF_map_iff (i : ℤ) {X Y : DerivedCategory A}
    (f : X ⟶ Y) :
    IsIso ((DerivedCategory.homologyFunctor Bᵒᵖ (-i)).map
        ((opLF LF).map ((derivedOpEquivalence (C := A)).functor.map f.op))) ↔
      IsIso ((DerivedCategory.homologyFunctor B i).map (LF.map f)) :=
  -- each reassociation is an equality of functors, so `Iff.rfl` bridges it; rewriting instead
  -- strands the goal on a type that is not correct under `implicit` transparency
  Iff.trans
    (show _ ↔ IsIso (((derivedOpEquivalence (C := B)).functor ⋙
        DerivedCategory.homologyFunctor Bᵒᵖ (-i)).map
        (LF.op.map ((derivedOpEquivalence (C := A)).inverse.map
          ((derivedOpEquivalence (C := A)).functor.map f.op)))) from Iff.rfl) <|
  Iff.trans (NatIso.isIso_map_iff (derivedHomologyOpNatIso' (-i) i (by omega)) _) <|
  Iff.trans
    (show _ ↔ IsIso ((LF.op ⋙ (DerivedCategory.homologyFunctor B i).op).map
        ((derivedOpEquivalence (C := A)).inverse.map
          ((derivedOpEquivalence (C := A)).functor.map f.op))) from Iff.rfl) <|
  Iff.trans
    (isIso_map_inverse_map_functor_map_iff (derivedOpEquivalence (C := A))
      (LF.op ⋙ (DerivedCategory.homologyFunctor B i).op) f.op) <|
  isIso_op_iff _

end Transport

end CategoryTheory.Functor

end
