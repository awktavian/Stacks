module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
# The Koszul symmetric monoidal structure on cochain complexes

Let `C` be a symmetric monoidal preadditive category with enough coproducts for Mathlib's
monoidal structure on `CochainComplex C ℤ` to exist, the tensor product being the total
complex of the degreewise tensor product. This file equips that monoidal structure with its
commutativity constraint: on the summand of bidegree `(p, q)` the braiding is the symmetry of
`C` multiplied by the Koszul sign `(-1)^(p*q)`. The resulting braiding is a symmetry.

## Main definitions

* `CochainComplex.koszulBraiding`: the Koszul braiding `K ⊗ L ≅ L ⊗ K`.
* `CochainComplex.symmetricCategory` and `CochainComplex.braidedCategory`: the resulting
  symmetric and braided monoidal structures on `CochainComplex C ℤ`, as data.

## Main results

* `CochainComplex.ιTensorObj_koszulBraiding`: the braiding on the homogeneous summand
  `K^p ⊗ L^q`.
* `CochainComplex.symmetricCategory_braiding`: the braiding of the structure is
  `CochainComplex.koszulBraiding`, on the nose.

## References

* [The Stacks Project, Tag 0FNI](https://stacks.math.columbia.edu/tag/0FNI)
* [The Stacks Project, Tag 0GWR](https://stacks.math.columbia.edu/tag/0GWR)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C]

/-! ## Whiskering and integral units -/

/-- Whiskering on the right is `ℤ`-linear, in the form needed for `ℤˣ`-scalars. -/
lemma units_smul_whiskerRight (s : ℤˣ) {X Y Z : C} (f : X ⟶ Y) :
    (s • f) ▷ Z = s • (f ▷ Z) := by
  show (tensorRight Z).map (s • f) = s • (tensorRight Z).map f
  exact Functor.map_units_smul (tensorRight Z) s f

/-- Whiskering on the left is `ℤ`-linear, in the form needed for `ℤˣ`-scalars. -/
lemma units_smul_whiskerLeft (s : ℤˣ) {X Y Z : C} (f : X ⟶ Y) :
    Z ◁ (s • f) = s • (Z ◁ f) := by
  show (tensorLeft Z).map (s • f) = s • (tensorLeft Z).map f
  exact Functor.map_units_smul (tensorLeft Z) s f

variable [HasZeroObject C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-! ## The homogeneous summands of a tensor product of complexes -/

/-- Restricted to the summand `K^i ⊗ M^j`, whiskering a map of complexes on the right is the
whiskering of its degree-`i` component. -/
@[reassoc]
lemma ιTensorObj_whiskerRight {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (M : CochainComplex C ℤ) (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιTensorObj K M i j n h ≫ (f ▷ M).f n =
      f.f i ▷ M.X j ≫ HomologicalComplex.ιTensorObj L M i j n h := by
  show HomologicalComplex.ιTensorObj K M i j n h ≫
    (HomologicalComplex.tensorHom f (𝟙 M)).f n = _
  rw [HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, Category.id_comp, curriedTensor_map_app]

/-- Restricted to the summand `K^i ⊗ L^j`, whiskering a map of complexes on the left is the
whiskering of its degree-`j` component. -/
@[reassoc]
lemma ιTensorObj_whiskerLeft (K : CochainComplex C ℤ) {L M : CochainComplex C ℤ}
    (f : L ⟶ M) (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιTensorObj K L i j n h ≫ (K ◁ f).f n =
      K.X i ◁ f.f j ≫ HomologicalComplex.ιTensorObj K M i j n h := by
  show HomologicalComplex.ιTensorObj K L i j n h ≫
    (HomologicalComplex.tensorHom (𝟙 K) f).f n = _
  rw [HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, curriedTensor_obj_map]

open ComplexShape in
/-- The inclusion of the summand `K^p ⊗ L^q ⊗ M^r` of `(K ⊗ L) ⊗ M`, written with the monoidal
notation of `CochainComplex C ℤ`. -/
@[reassoc]
lemma mapBifunctor₁₂_ι_eq (K L M : CochainComplex C ℤ) (p q r m n : ℤ) (hm : p + q = m)
    (hn : m + r = n) (h : ComplexShape.r (up ℤ) (up ℤ) (up ℤ) (up ℤ) (up ℤ) (p, q, r) = n) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor C) (curriedTensor C) K L M
        (up ℤ) (up ℤ) p q r n h =
      HomologicalComplex.ιTensorObj K L p q m hm ▷ M.X r ≫
        HomologicalComplex.ιTensorObj (K ⊗ L) M m r n hn :=
  HomologicalComplex.mapBifunctor₁₂.ι_eq (F₁₂ := curriedTensor C) (G := curriedTensor C)
    K L M (up ℤ) (up ℤ) p q r m n hm hn

open ComplexShape in
/-- The inclusion of the summand `K^p ⊗ L^q ⊗ M^r` of `K ⊗ (L ⊗ M)`, written with the monoidal
notation of `CochainComplex C ℤ`. -/
@[reassoc]
lemma mapBifunctor₂₃_ι_eq (K L M : CochainComplex C ℤ) (p q r m n : ℤ) (hm : q + r = m)
    (hn : p + m = n) (h : ComplexShape.r (up ℤ) (up ℤ) (up ℤ) (up ℤ) (up ℤ) (p, q, r) = n) :
    HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor C) (curriedTensor C) K L M
        (up ℤ) (up ℤ) (up ℤ) p q r n h =
      K.X p ◁ HomologicalComplex.ιTensorObj L M q r m hm ≫
        HomologicalComplex.ιTensorObj K (L ⊗ M) p m n hn :=
  HomologicalComplex.mapBifunctor₂₃.ι_eq (F := curriedTensor C) (G₂₃ := curriedTensor C)
    K L M (up ℤ) (up ℤ) (up ℤ) p q r m n hm hn

open ComplexShape in
/-- On the summand of tridegree `(p, q, r)`, the associator of `CochainComplex C ℤ` is the
associator of `C`. -/
@[reassoc]
lemma mapBifunctor₁₂_ι_comp_associator (K L M : CochainComplex C ℤ) (p q r n : ℤ)
    (h : ComplexShape.r (up ℤ) (up ℤ) (up ℤ) (up ℤ) (up ℤ) (p, q, r) = n) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor C) (curriedTensor C) K L M
        (up ℤ) (up ℤ) p q r n h ≫ (α_ K L M).hom.f n =
      (α_ (K.X p) (L.X q) (M.X r)).hom ≫
        HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor C) (curriedTensor C) K L M
          (up ℤ) (up ℤ) (up ℤ) p q r n h := by
  have hα : (α_ K L M).hom.f n =
      (HomologicalComplex.mapBifunctorAssociatorX (curriedAssociatorNatIso C) K L M
        (up ℤ) (up ℤ) (up ℤ) n).hom := rfl
  rw [hα, HomologicalComplex.ι_mapBifunctorAssociatorX_hom]
  simp only [CategoryTheory.MonoidalCategory.curriedAssociatorNatIso_hom_app_app_app]

variable [SymmetricCategory C]

/-! ## The Koszul braiding -/

/-- The Koszul signs of integers `a` and `b` multiply to the sign of `c` when `a + b = c`. -/
private lemma negOnePow_mul_eq {a b c : ℤ} (h : a + b = c) :
    (a.negOnePow : ℤˣ) * b.negOnePow = c.negOnePow := by
  rw [← Int.negOnePow_add, h]

/-- The degree-`n` component of the Koszul braiding: on the summand `K^p ⊗ L^q` it is the
symmetry of `C` scaled by the Koszul sign `(-1)^(p*q)`. -/
noncomputable def koszulBraidingX (K L : CochainComplex C ℤ) (n : ℤ) :
    (K ⊗ L).X n ≅ (L ⊗ K).X n where
  hom := HomologicalComplex.mapBifunctorDesc (fun p q h =>
    ((p * q).negOnePow : ℤˣ) • ((β_ (K.X p) (L.X q)).hom ≫
      HomologicalComplex.ιTensorObj L K q p n (by simpa [add_comm] using h)))
  inv := HomologicalComplex.mapBifunctorDesc (fun q p h =>
    ((p * q).negOnePow : ℤˣ) • ((β_ (L.X q) (K.X p)).hom ≫
      HomologicalComplex.ιTensorObj K L p q n (by simpa [add_comm] using h)))
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    simp only [HomologicalComplex.ι_mapBifunctorDesc_assoc, Linear.units_smul_comp,
      Category.assoc, HomologicalComplex.ι_mapBifunctorDesc, Linear.comp_units_smul,
      smul_smul, SymmetricCategory.symmetry_assoc]
    rw [← Int.negOnePow_add, show p * q + p * q = 2 * (p * q) by ring,
      Int.negOnePow_two_mul, one_smul]
    exact (Category.comp_id _).symm
  inv_hom_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro q p h
    simp only [HomologicalComplex.ι_mapBifunctorDesc_assoc, Linear.units_smul_comp,
      Category.assoc, HomologicalComplex.ι_mapBifunctorDesc, Linear.comp_units_smul,
      smul_smul, SymmetricCategory.symmetry_assoc]
    rw [← Int.negOnePow_add, show p * q + p * q = 2 * (p * q) by ring,
      Int.negOnePow_two_mul, one_smul]
    exact (Category.comp_id _).symm

/-- Swapping the two factors of `koszulBraidingX` inverts it. -/
lemma koszulBraidingX_symm (K L : CochainComplex C ℤ) (n : ℤ) :
    (koszulBraidingX L K n).hom = (koszulBraidingX K L n).inv := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro q p h
  simp only [koszulBraidingX, HomologicalComplex.ι_mapBifunctorDesc]
  rw [mul_comm q p]

/-- The degreewise Koszul braiding commutes with the total differentials. -/
lemma koszulBraidingX_hom_comm (K L : CochainComplex C ℤ) (n m : ℤ)
    (hnm : (ComplexShape.up ℤ).Rel n m) :
    (koszulBraidingX K L n).hom ≫ (L ⊗ K).d n m =
      (K ⊗ L).d n m ≫ (koszulBraidingX K L m).hom := by
  show (koszulBraidingX K L n).hom ≫
      (HomologicalComplex.mapBifunctor L K (curriedTensor C) (ComplexShape.up ℤ)).d n m =
    (HomologicalComplex.mapBifunctor K L (curriedTensor C) (ComplexShape.up ℤ)).d n m ≫
      (koszulBraidingX K L m).hom
  simp only [HomologicalComplex.mapBifunctor.d_eq]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hsum : p + q = n := h
  have hm : n + 1 = m := hnm
  have hp : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
  have hq : (ComplexShape.up ℤ).Rel q (q + 1) := rfl
  have hA : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p + 1, q) = m :=
    show p + 1 + q = m by omega
  have hB : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q + 1) = m :=
    show p + (q + 1) = m by omega
  have hL₁ : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (q + 1, p) = m :=
    show q + 1 + p = m by omega
  have hL₂ : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (q, p + 1) = m :=
    show q + (p + 1) = m by omega
  simp only [Preadditive.comp_add, Preadditive.add_comp,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  simp only [koszulBraidingX, HomologicalComplex.ι_mapBifunctorDesc_assoc,
    Linear.units_smul_comp, Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq (K₁ := L) (K₂ := K)
    (F := curriedTensor C) (c := ComplexShape.up ℤ) (i₁' := q + 1) hq p m hL₁,
    HomologicalComplex.mapBifunctor.d₂_eq (K₁ := L) (K₂ := K)
    (F := curriedTensor C) (c := ComplexShape.up ℤ) q (i₂' := p + 1) hp m hL₂,
    HomologicalComplex.mapBifunctor.d₁_eq (K₁ := K) (K₂ := L)
    (F := curriedTensor C) (c := ComplexShape.up ℤ) (i₁' := p + 1) hp q m hA,
    HomologicalComplex.mapBifunctor.d₂_eq (K₁ := K) (K₂ := L)
    (F := curriedTensor C) (c := ComplexShape.up ℤ) p (i₂' := q + 1) hq m hB]
  simp only [curriedTensor_obj_obj, ComplexShape.ε₁_def, curriedTensor_map_app, one_smul,
    ComplexShape.ε₂_def, ComplexShape.ε_up_ℤ, curriedTensor_obj_map, Linear.comp_units_smul,
    ComplexShape.π_def, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc,
    BraidedCategory.braiding_naturality_left_assoc, Linear.units_smul_comp,
    BraidedCategory.braiding_naturality_right_assoc]
  simp only [smul_smul]
  have hsign₁ : (p * q).negOnePow * q.negOnePow = ((p + 1) * q).negOnePow :=
    negOnePow_mul_eq (by ring)
  have hsign₂ : (p * q).negOnePow = p.negOnePow * (p * (q + 1)).negOnePow := by
    rw [mul_comm p.negOnePow, ← Int.negOnePow_sub]
    congr 1
    ring
  rw [hsign₁, hsign₂]
  abel

/-- The Koszul braiding `K ⊗ L ≅ L ⊗ K`, assembled from its degreewise components. -/
noncomputable def koszulBraiding (K L : CochainComplex C ℤ) : K ⊗ L ≅ L ⊗ K :=
  HomologicalComplex.Hom.isoOfComponents (koszulBraidingX K L) (koszulBraidingX_hom_comm K L)

/-- The Koszul braiding on homogeneous summands: restricted to the summand `K^p ⊗ L^q` of
`(K ⊗ L)^n`, it is the symmetry `K^p ⊗ L^q ≅ L^q ⊗ K^p` of `C`, multiplied by the Koszul sign
`(-1)^(p*q)` and followed by the inclusion of the summand `L^q ⊗ K^p` of `(L ⊗ K)^n`. -/
@[reassoc]
lemma ιTensorObj_koszulBraiding (K L : CochainComplex C ℤ) (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫ (koszulBraiding K L).hom.f n =
      ((p * q).negOnePow : ℤˣ) • ((β_ (K.X p) (L.X q)).hom ≫
        HomologicalComplex.ιTensorObj L K q p n (by simpa [add_comm] using h)) := by
  simp [koszulBraiding, koszulBraidingX]

/-- Naturality of the symmetry of `C` against the inclusion of a summand of `L ⊗ M`. -/
@[reassoc]
lemma whiskerLeft_ιTensorObj_comp_braiding (K L M : CochainComplex C ℤ) (p q r m : ℤ)
    (hm : q + r = m) :
    K.X p ◁ HomologicalComplex.ιTensorObj L M q r m hm ≫
        (β_ (K.X p) ((L ⊗ M).X m)).hom =
      (β_ (K.X p) (L.X q ⊗ M.X r)).hom ≫
        HomologicalComplex.ιTensorObj L M q r m hm ▷ K.X p :=
  BraidedCategory.braiding_naturality_right _ _

/-- The Koszul braiding of `K` and `L` on the summand `K^p ⊗ L^q`, whiskered on the right by
`M^r`. -/
@[reassoc]
lemma whiskerRight_ιTensorObj_comp_braiding (K L M : CochainComplex C ℤ) (p q r m : ℤ)
    (hm : p + q = m) :
    HomologicalComplex.ιTensorObj K L p q m hm ▷ M.X r ≫
        (koszulBraiding K L).hom.f m ▷ M.X r =
      ((p * q).negOnePow : ℤˣ) • ((β_ (K.X p) (L.X q)).hom ▷ M.X r ≫
        HomologicalComplex.ιTensorObj L K q p m (by omega) ▷ M.X r) := by
  rw [← MonoidalCategory.comp_whiskerRight, ιTensorObj_koszulBraiding,
    units_smul_whiskerRight, MonoidalCategory.comp_whiskerRight]

/-- The Koszul braiding of `K` and `M` on the summand `K^p ⊗ M^r`, whiskered on the left by
`L^q`. -/
@[reassoc]
lemma ιTensorObj_comp_whiskerLeft_braiding (K L M : CochainComplex C ℤ) (p q r m : ℤ)
    (hm : p + r = m) :
    L.X q ◁ HomologicalComplex.ιTensorObj K M p r m hm ≫
        L.X q ◁ (koszulBraiding K M).hom.f m =
      ((p * r).negOnePow : ℤˣ) • (L.X q ◁ (β_ (K.X p) (M.X r)).hom ≫
        L.X q ◁ HomologicalComplex.ιTensorObj M K r p m (by omega)) := by
  rw [← MonoidalCategory.whiskerLeft_comp, ιTensorObj_koszulBraiding,
    units_smul_whiskerLeft, MonoidalCategory.whiskerLeft_comp]

/-! ## The hexagon identities and the symmetry -/

open ComplexShape in
/-- The left-hand side of the forward hexagon, evaluated on the summand of tridegree
`(p, q, r)`. -/
lemma koszulBraiding_hexagon_forward_lhs (K L M : CochainComplex C ℤ) (p q r n : ℤ)
    (hn : p + q + r = n)
    (h : ComplexShape.r (up ℤ) (up ℤ) (up ℤ) (up ℤ) (up ℤ) (p, q, r) = n)
    (hqpr : ComplexShape.r (up ℤ) (up ℤ) (up ℤ) (up ℤ) (up ℤ) (q, r, p) = n) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor C) (curriedTensor C) K L M
        (up ℤ) (up ℤ) p q r n h ≫
      ((α_ K L M).hom ≫ (koszulBraiding K (L ⊗ M)).hom ≫ (α_ L M K).hom).f n =
    ((p * (q + r)).negOnePow : ℤˣ) • ((α_ (K.X p) (L.X q) (M.X r)).hom ≫
      (β_ (K.X p) (L.X q ⊗ M.X r)).hom ≫ (α_ (L.X q) (M.X r) (K.X p)).hom ≫
        HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor C) (curriedTensor C) L M K
          (up ℤ) (up ℤ) (up ℤ) q r p n hqpr) := by
  simp only [HomologicalComplex.comp_f]
  rw [mapBifunctor₁₂_ι_comp_associator_assoc,
    mapBifunctor₂₃_ι_eq_assoc K L M p q r (q + r) n rfl (by omega) h,
    ιTensorObj_koszulBraiding_assoc]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc]
  rw [whiskerLeft_ιTensorObj_comp_braiding_assoc,
    ← mapBifunctor₁₂_ι_eq_assoc L M K q r p (q + r) n rfl (by omega) hqpr,
    mapBifunctor₁₂_ι_comp_associator]

open ComplexShape in
/-- The right-hand side of the forward hexagon, evaluated on the summand of tridegree
`(p, q, r)`. -/
lemma koszulBraiding_hexagon_forward_rhs (K L M : CochainComplex C ℤ) (p q r n : ℤ)
    (hn : p + q + r = n)
    (h : ComplexShape.r (up ℤ) (up ℤ) (up ℤ) (up ℤ) (up ℤ) (p, q, r) = n)
    (hqpr : ComplexShape.r (up ℤ) (up ℤ) (up ℤ) (up ℤ) (up ℤ) (q, r, p) = n) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor C) (curriedTensor C) K L M
        (up ℤ) (up ℤ) p q r n h ≫
      ((koszulBraiding K L).hom ▷ M ≫ (α_ L K M).hom ≫ L ◁ (koszulBraiding K M).hom).f n =
    ((p * q).negOnePow * (p * r).negOnePow : ℤˣ) •
      ((β_ (K.X p) (L.X q)).hom ▷ M.X r ≫ (α_ (L.X q) (K.X p) (M.X r)).hom ≫
        L.X q ◁ (β_ (K.X p) (M.X r)).hom ≫
          HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor C) (curriedTensor C) L M K
            (up ℤ) (up ℤ) (up ℤ) q r p n hqpr) := by
  have hqpn : ComplexShape.r (up ℤ) (up ℤ) (up ℤ) (up ℤ) (up ℤ) (q, p, r) = n :=
    show q + p + r = n by omega
  simp only [HomologicalComplex.comp_f]
  rw [mapBifunctor₁₂_ι_eq_assoc K L M p q r (p + q) n rfl (by omega) h,
    ιTensorObj_whiskerRight_assoc, whiskerRight_ιTensorObj_comp_braiding_assoc]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [← mapBifunctor₁₂_ι_eq_assoc L K M q p r (p + q) n (by omega) hn hqpn,
    mapBifunctor₁₂_ι_comp_associator_assoc,
    mapBifunctor₂₃_ι_eq_assoc L K M q p r (p + r) n (by omega) (by omega) hqpn,
    ιTensorObj_whiskerLeft, ιTensorObj_comp_whiskerLeft_braiding_assoc]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc, smul_smul]
  rw [← mapBifunctor₂₃_ι_eq L M K q r p (p + r) n (by omega) (by omega) hqpr]

open ComplexShape in
/-- The forward hexagon identity for the Koszul braiding. -/
lemma koszulBraiding_hexagon_forward (K L M : CochainComplex C ℤ) :
    (α_ K L M).hom ≫ (koszulBraiding K (L ⊗ M)).hom ≫ (α_ L M K).hom =
      (koszulBraiding K L).hom ▷ M ≫ (α_ L K M).hom ≫ L ◁ (koszulBraiding K M).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  have hn : p + q + r = n := h
  have hqpr : ComplexShape.r (up ℤ) (up ℤ) (up ℤ) (up ℤ) (up ℤ) (q, r, p) = n :=
    show q + r + p = n by omega
  rw [koszulBraiding_hexagon_forward_lhs K L M p q r n hn h hqpr,
    koszulBraiding_hexagon_forward_rhs K L M p q r n hn h hqpr,
    (negOnePow_mul_eq (by ring) : (p * q).negOnePow * (p * r).negOnePow =
      (p * (q + r)).negOnePow).symm,
    reassoc_of% (BraidedCategory.hexagon_forward (K.X p) (L.X q) (M.X r))]

/-- Naturality of the Koszul braiding in its first variable. -/
lemma koszulBraiding_naturality_left {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (M : CochainComplex C ℤ) :
    f ▷ M ≫ (koszulBraiding L M).hom = (koszulBraiding K M).hom ≫ M ◁ f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f]
  rw [ιTensorObj_whiskerRight_assoc, ιTensorObj_koszulBraiding,
    ιTensorObj_koszulBraiding_assoc]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc]
  rw [ιTensorObj_whiskerLeft, BraidedCategory.braiding_naturality_left_assoc]

/-- Naturality of the Koszul braiding in its second variable. -/
lemma koszulBraiding_naturality_right (K : CochainComplex C ℤ)
    {L M : CochainComplex C ℤ} (f : L ⟶ M) :
    K ◁ f ≫ (koszulBraiding K M).hom = (koszulBraiding K L).hom ≫ f ▷ K := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f]
  rw [ιTensorObj_whiskerLeft_assoc, ιTensorObj_koszulBraiding,
    ιTensorObj_koszulBraiding_assoc]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc]
  rw [ιTensorObj_whiskerRight, BraidedCategory.braiding_naturality_right_assoc]

/-- The Koszul braiding is a symmetry. -/
lemma koszulBraiding_symmetry (K L : CochainComplex C ℤ) :
    (koszulBraiding K L).hom ≫ (koszulBraiding L K).hom = 𝟙 (K ⊗ L) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  rw [ιTensorObj_koszulBraiding_assoc, Linear.units_smul_comp, Category.assoc,
    ιTensorObj_koszulBraiding, Linear.comp_units_smul, smul_smul,
    SymmetricCategory.symmetry_assoc, ← Int.negOnePow_add,
    show p * q + q * p = 2 * (p * q) by ring, Int.negOnePow_two_mul, one_smul]
  exact (Category.comp_id _).symm

/-- The inverse of the Koszul braiding is the Koszul braiding of the swapped arguments. -/
lemma koszulBraiding_symm (K L : CochainComplex C ℤ) :
    (koszulBraiding K L).symm = koszulBraiding L K := by
  have h : koszulBraiding K L = (koszulBraiding L K).symm :=
    Iso.ext ((koszulBraiding L K).hom_comp_eq_id.mp (koszulBraiding_symmetry L K))
  simpa using congrArg Iso.symm h

variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- The reverse hexagon identity for the Koszul braiding. -/
lemma koszulBraiding_hexagon_reverse (K L M : CochainComplex C ℤ) :
    (α_ K L M).inv ≫ (koszulBraiding (K ⊗ L) M).hom ≫ (α_ M K L).inv =
      K ◁ (koszulBraiding L M).hom ≫ (α_ K M L).inv ≫ (koszulBraiding K M).hom ▷ L := by
  have hf : (α_ M K L) ≪≫ koszulBraiding M (K ⊗ L) ≪≫ (α_ K L M) =
      whiskerRightIso (koszulBraiding M K) L ≪≫ (α_ K M L) ≪≫
        whiskerLeftIso K (koszulBraiding M L) :=
    Iso.ext (koszulBraiding_hexagon_forward M K L)
  have hr : (α_ K L M).symm ≪≫ koszulBraiding (K ⊗ L) M ≪≫ (α_ M K L).symm =
      whiskerLeftIso K (koszulBraiding L M) ≪≫ (α_ K M L).symm ≪≫
        whiskerRightIso (koszulBraiding K M) L := by
    simpa only [Iso.trans_assoc, Iso.trans_symm, koszulBraiding_symm, whiskerLeftIso_symm,
      whiskerRightIso_symm] using congrArg Iso.symm hf
  exact congrArg Iso.hom hr

/-! ## The symmetric monoidal structure -/

/-- Cochain complexes in a symmetric monoidal preadditive category are symmetric monoidal, with
braiding the base symmetry times the Koszul sign `(-1)^(p*q)` on the summand of bidegree
`(p, q)`. -/
@[instance_reducible]
noncomputable def symmetricCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [Preadditive C] [MonoidalPreadditive C] [SymmetricCategory C] [HasZeroObject C]
    [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
    [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
    [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] :
    SymmetricCategory (CochainComplex C ℤ) where
  braiding := koszulBraiding
  braiding_naturality_left := koszulBraiding_naturality_left
  braiding_naturality_right := koszulBraiding_naturality_right
  hexagon_forward := koszulBraiding_hexagon_forward
  hexagon_reverse := koszulBraiding_hexagon_reverse
  symmetry := koszulBraiding_symmetry

/-- The braided monoidal structure underlying `CochainComplex.symmetricCategory`. -/
@[instance_reducible]
noncomputable def braidedCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [Preadditive C] [MonoidalPreadditive C] [SymmetricCategory C] [HasZeroObject C]
    [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
    [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
    [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] :
    BraidedCategory (CochainComplex C ℤ) :=
  (symmetricCategory C).toBraidedCategory

/-- The braiding of `CochainComplex.symmetricCategory` is `CochainComplex.koszulBraiding`. -/
lemma symmetricCategory_braiding (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [Preadditive C] [MonoidalPreadditive C] [SymmetricCategory C] [HasZeroObject C]
    [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
    [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
    [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (K L : CochainComplex C ℤ) :
    BraidedCategory.braiding (self := braidedCategory C) K L = koszulBraiding K L := rfl

end CochainComplex

end
