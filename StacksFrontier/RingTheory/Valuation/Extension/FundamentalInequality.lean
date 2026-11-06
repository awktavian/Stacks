module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import StacksCore.LinearAlgebra.Matrix.CommSemiring

/-!
# The fundamental inequality for extensions of valuation rings

Let `A ⊆ B` be an extension of valuation rings with fraction fields `K ⊆ L` such that `L/K` is
finite. Then the residue field extension `κ_B/κ_A` is finite, the value group `Γ_A` has finite
index in `Γ_B`, and `[Γ_B : Γ_A] · [κ_B : κ_A] ≤ [L : K]`.

## Main definitions

* `ValuationRing.valueGroupHom`: the homomorphism `Kˣ → (ValueGroup B L)ˣ` sending `x` to the
  valuation of its image in `L`; its range is `Γ_A` viewed as a subgroup of `Γ_B`.

## Main results

* `ValuationRing.card_mul_card_le_finrank`: if `rs ⊆ κ_B` is linearly independent over `κ_A` and
  `vs ⊆ Γ_B` meets each coset of `Γ_A` at most once, then `|rs| · |vs| ≤ [L : K]`.
* `ValuationRing.index_mul_finrank_residueField_le_finrank`: the residue field extension is
  finite, the index `[Γ_B : Γ_A]` is finite, and `[Γ_B : Γ_A] · [κ_B : κ_A] ≤ [L : K]`.
* `ext_valuation_rings_degree_ineq`: the same, with the residue field algebra structure induced
  by `IsLocalRing.ResidueField.map (algebraMap A B)`.

## References

* [Stacks Project, Tag 0ASH](https://stacks.math.columbia.edu/tag/0ASH)
-/

@[expose] public section

open ValuationRing IsLocalRing

/-- The homomorphism `Kˣ → Γ_B = (ValueGroup B L)ˣ` for an extension `A ⊆ B` of valuation rings
with fraction fields `K ⊆ L`, sending a unit `x : Kˣ` to the valuation of `algebraMap K L x`.
Its range is `Γ_A` viewed as a subgroup of `Γ_B`, and its index is the degree `[Γ_B : Γ_A]`. -/
noncomputable def ValuationRing.valueGroupHom (B K L : Type*)
    [CommRing B] [IsDomain B] [ValuationRing B]
    [Field K] [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] :
    Kˣ →* (ValueGroup B L)ˣ :=
  Units.map (((valuation B L).toMonoidWithZeroHom.comp
    (algebraMap K L).toMonoidWithZeroHom).toMonoidHom)


/-- Every nonzero element of the residue field of a local ring `B` is the residue of a unit
of `B`. -/
theorem IsLocalRing.exists_unit_residue_eq {B : Type*} [CommRing B] [IsLocalRing B]
    (r : ResidueField B) (hr : r ≠ 0) :
    ∃ u : Bˣ, residue B (u : B) = r := by
  obtain ⟨x, rfl⟩ := residue_surjective r
  exact ⟨((residue_ne_zero_iff_isUnit x).mp hr).unit, by simp [IsUnit.unit_spec]⟩

/-- If `k ∈ K` has image in `L` lying in the image of `B`, then `k` lies in the image of `A`. -/
theorem ValuationRing.exists_algebraMap_eq_of_algebraMap_eq (A B K L : Type*)
    [CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing B] [IsDomain B] [ValuationRing B] [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsLocalHom (algebraMap A B)]
    (b : B) (k : K) (hb : (algebraMap B L) b = (algebraMap K L) k) :
    ∃ a : A, algebraMap A K a = k := by
  by_contra h
  push Not at h
  have hk0 : k ≠ 0 := by rintro rfl; exact h 0 (by simp)
  rcases ValuationRing.isInteger_or_isInteger A k with ⟨a, ha⟩ | ⟨a', ha'⟩
  · exact h a ha
  have ha'_nonunit : ¬ IsUnit a' := by
    rintro ⟨v, rfl⟩
    apply h ((v⁻¹ : Aˣ) : A)
    rw [map_units_inv, ha']; simp
  have haL : algebraMap A L a' = (algebraMap B L b)⁻¹ := by
    rw [IsScalarTower.algebraMap_apply A K L, ha', hb, map_inv₀]
  have hAL : algebraMap A L a' = algebraMap B L (algebraMap A B a') := by
    rw [IsScalarTower.algebraMap_apply A B L]
  have hbne : algebraMap B L b ≠ 0 := by
    rw [hb, ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective K L)]; exact hk0
  have hmul1 : algebraMap B L (algebraMap A B a' * b) = 1 := by
    rw [map_mul, ← hAL, haL]; field_simp
  have heq : algebraMap A B a' * b = 1 :=
    FaithfulSMul.algebraMap_injective B L (by rw [hmul1, map_one])
  have hu : IsUnit (algebraMap A B a') := IsUnit.of_mul_eq_one b heq
  exact ha'_nonunit (isUnit_of_map_unit (algebraMap A B) a' hu)

/-- Let `bb : ι → Bˣ` be units whose residues are linearly independent over `κ_A`, and let
`a : ι → K` be not identically zero. Then `∑ i, a i * bb i` is nonzero in `L`, and its valuation
equals the valuation of the image of some `x : Kˣ`. -/
theorem ValuationRing.sum_ne_zero_and_exists_valuation_eq (A B K L : Type*)
    [CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing B] [IsDomain B] [ValuationRing B] [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsLocalHom (algebraMap A B)]
    (ι : Type*) [Fintype ι]
    (bb : ι → Bˣ) (a : ι → K)
    (hli : LinearIndependent (ResidueField A) (fun i => residue B (bb i : B)))
    (hne : ∃ i, a i ≠ 0) :
    (∑ i, algebraMap K L (a i) * algebraMap B L (bb i : B)) ≠ 0 ∧
    ∃ x : Kˣ, (valuation B L) (∑ i, algebraMap K L (a i) * algebraMap B L (bb i : B))
              = (valuation B L) (algebraMap K L (x : K)) := by
  classical
  set v := valuation B L with hv
  have hSne : (Finset.univ.filter (fun i => a i ≠ 0)).Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by simp [hi]⟩
  obtain ⟨i₀, hi₀mem, hi₀max⟩ :=
    (Finset.univ.filter (fun i => a i ≠ 0)).exists_max_image
      (fun i => v (algebraMap K L (a i))) hSne
  have ha0 : a i₀ ≠ 0 := by simpa using (Finset.mem_filter.mp hi₀mem).2
  have hL0 : algebraMap K L (a i₀) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective K L)).mpr ha0
  set M := v (algebraMap K L (a i₀)) with hM
  have hMpos : 0 < M := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hL0)
  set ac : ι → K := fun i => a i / a i₀ with hac
  have hac_le : ∀ i, v (algebraMap K L (ac i)) ≤ 1 := by
    intro i
    by_cases hai : a i = 0
    · simp [hac, hai, hv]
    · rw [hac, map_div₀, map_div₀, div_le_one₀ hMpos]
      exact hi₀max i (by simp [hai])
  have hlift : ∀ i, ∃ t : A, algebraMap A K t = ac i := by
    intro i
    have hmemint : (valuation B L) (algebraMap K L (ac i)) ≤ 1 := hac_le i
    rw [← Valuation.mem_integer_iff, ValuationRing.mem_integer_iff] at hmemint
    obtain ⟨bb', hbb'⟩ := hmemint
    exact exists_algebraMap_eq_of_algebraMap_eq A B K L bb' (ac i) hbb'
  choose t ht using hlift
  set w : B := ∑ i, algebraMap A B (t i) * (bb i : B) with hw
  have he : algebraMap B L w = ∑ i, algebraMap K L (ac i) * algebraMap B L (bb i : B) := by
    rw [hw, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, ← ht i, ← IsScalarTower.algebraMap_apply A K L,
        IsScalarTower.algebraMap_apply A B L]
  have hres : residue B w ≠ 0 := by
    have hcomb : residue B w
        = ∑ i, (residue A (t i)) • (residue B (bb i : B)) := by
      rw [hw, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, Algebra.smul_def, ResidueField.algebraMap_residue]
    intro hw0
    have hzero : ∑ i, (residue A (t i)) • (residue B (bb i : B)) = 0 := hcomb.symm.trans hw0
    have hti0 : t i₀ = 1 := by
      have h1 : algebraMap A K (t i₀) = algebraMap A K 1 := by
        rw [ht i₀, map_one]; simp [hac, ha0]
      exact FaithfulSMul.algebraMap_injective A K h1
    have hcoeff0 : residue A (t i₀) ≠ 0 := by simp [hti0]
    exact hcoeff0 ((Fintype.linearIndependent_iff.mp hli) (fun i => residue A (t i)) hzero i₀)
  have hwunit : IsUnit w := by
    rw [← notMem_maximalIdeal]
    exact fun hmem => hres ((IsLocalRing.residue_eq_zero_iff w).mpr hmem)
  have hve : v (algebraMap B L w) = 1 := by
    rw [hv, ← hwunit.unit_spec]
    exact (ValuationRing.integers B L).valuation_unit _
  have hsum_eq : (∑ i, algebraMap K L (a i) * algebraMap B L (bb i : B))
      = algebraMap K L (a i₀) * algebraMap B L w := by
    rw [he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hac, map_div₀]
    field_simp
  refine ⟨?_, ⟨Units.mk0 (a i₀) ha0, ?_⟩⟩
  · rw [hsum_eq]
    apply mul_ne_zero
    · exact hL0
    · rw [ne_eq, ← Valuation.zero_iff (valuation B L), ← hv, hve]; exact one_ne_zero
  · simp only [Units.val_mk0]
    rw [hsum_eq, hv, Valuation.map_mul, ← hv, hve, mul_one]

/-- A sum over a nonempty finset of nonzero elements of `L` with pairwise distinct valuations is
nonzero. -/
theorem Valuation.sum_ne_zero_of_injOn {L Γ : Type*} [DivisionRing L]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) {ι : Type*} (S : Finset ι) (f : ι → L)
    (hSne : S.Nonempty) (hfne : ∀ i ∈ S, f i ≠ 0)
    (hinj : Set.InjOn (fun i => v (f i)) ↑S) :
    ∑ i ∈ S, f i ≠ 0 := by
  classical
  obtain ⟨i₀, hi₀, hi₀max⟩ := S.exists_max_image (fun i => v (f i)) hSne
  rw [← Finset.add_sum_erase S f hi₀]
  have hlt : v (∑ i ∈ S.erase i₀, f i) < v (f i₀) := by
    apply Valuation.map_sum_lt'
    · exact zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr (hfne i₀ hi₀))
    · intro j hj
      have hjS : j ∈ S := Finset.mem_of_mem_erase hj
      have hjne : j ≠ i₀ := Finset.ne_of_mem_erase hj
      have hle : v (f j) ≤ v (f i₀) := hi₀max j hjS
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exact absurd (hinj (Finset.mem_coe.mpr hjS) (Finset.mem_coe.mpr hi₀) h) hjne
  rw [add_comm, ne_eq, ← Valuation.zero_iff v, Valuation.map_add_eq_of_lt_right v hlt]
  exact (Valuation.ne_zero_iff v).mpr (hfne i₀ hi₀)

/-- The canonical valuation of a valuation ring on its fraction field is surjective onto the
value group. -/
theorem ValuationRing.valuation_surjective (B L : Type*) [CommRing B] [IsDomain B]
    [ValuationRing B] [Field L] [Algebra B L] [IsFractionRing B L] :
    Function.Surjective (valuation B L) := by
  exact Quotient.mk_surjective

/-- The value of `valueGroupHom B K L x` is the valuation of the image of `x` in `L`. -/
@[simp]
theorem ValuationRing.coe_valueGroupHom_apply (B K L : Type*)
    [CommRing B] [IsDomain B] [ValuationRing B]
    [Field K] [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
    (x : Kˣ) : ((valueGroupHom B K L x : (ValueGroup B L)ˣ) : ValueGroup B L)
      = (valuation B L) (algebraMap K L (x:K)) :=
  rfl

/-- Let `rs ⊆ κ_B` be linearly independent over `κ_A`, and let `vs ⊆ Γ_B` be a finset whose
elements lie in pairwise distinct cosets of `Γ_A`. Then `|rs| · |vs| ≤ [L : K]`. -/
theorem ValuationRing.card_mul_card_le_finrank (A B K L : Type*)
    [CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing B] [IsDomain B] [ValuationRing B] [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsLocalHom (algebraMap A B)] [Module.Finite K L]
    (rs : Finset (ResidueField B)) (vs : Finset ((ValueGroup B L)ˣ))
    (hrs : LinearIndependent (ResidueField A) (fun x : rs => (x : ResidueField B)))
    (hvs : Set.InjOn (QuotientGroup.mk (s := (valueGroupHom B K L).range)) (↑vs)) :
    rs.card * vs.card ≤ Module.finrank K L := by
  classical
  set v := valuation B L with hv
  set H : Subgroup ((ValueGroup B L)ˣ) := (valueGroupHom B K L).range with hH
  have hlift_b : ∀ x : rs, ∃ u : Bˣ, residue B (u : B) = (x : ResidueField B) := fun x =>
    exists_unit_residue_eq _ (by simpa using hrs.ne_zero x)
  choose bb hbb using hlift_b
  have hlift_c : ∀ y : vs, ∃ c : L, c ≠ 0 ∧ v c = ((y : (ValueGroup B L)ˣ) : ValueGroup B L) := by
    intro y
    obtain ⟨c, hc⟩ := valuation_surjective B L ((y : (ValueGroup B L)ˣ) : ValueGroup B L)
    rw [hv]
    refine ⟨c, ?_, hc⟩
    rintro rfl
    rw [map_zero] at hc
    exact (y : (ValueGroup B L)ˣ).ne_zero hc.symm
  choose cc hcc_ne hcc_val using hlift_c
  set g : rs × vs → L := fun p => algebraMap B L (bb p.1 : B) * cc p.2 with hg
  have hLI : LinearIndependent K g := by
    have hbres : LinearIndependent (ResidueField A) (fun i : rs => residue B (bb i : B)) := by
      rwa [funext hbb]
    rw [Fintype.linearIndependent_iff]
    intro α hα p₀
    by_contra hcontra
    set D : vs → L := fun y =>
      ∑ x : rs, algebraMap K L (α (x, y)) * algebraMap B L (bb x : B) with hD
    have hreorg : ∑ p : rs × vs, α p • g p = ∑ y : vs, D y * cc y := by
      rw [Fintype.sum_prod_type_right]
      apply Finset.sum_congr rfl
      intro y _
      rw [hD, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [hg, Algebra.smul_def, IsScalarTower.algebraMap_apply K L L]
      ring
    rw [hreorg] at hα
    have hDp0 : D p₀.2 ≠ 0 :=
      (sum_ne_zero_and_exists_valuation_eq A B K L rs bb (fun x => α (x, p₀.2)) hbres
        ⟨p₀.1, hcontra⟩).1
    have hcolval : ∀ y : vs, D y ≠ 0 →
        ∃ x : Kˣ, v (D y) = v (algebraMap K L (x : K)) := by
      intro y hy
      have hexists : ∃ x : rs, α (x, y) ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hy
        rw [hD]
        apply Finset.sum_eq_zero
        intro x _
        rw [hall x, map_zero, zero_mul]
      exact (sum_ne_zero_and_exists_valuation_eq A B K L rs bb (fun x => α (x, y)) hbres hexists).2
    choose xx hxx using hcolval
    set S : Finset vs := Finset.univ.filter (fun y => D y ≠ 0) with hS
    have hSsum : ∑ y ∈ S, D y * cc y = 0 := by
      have hsub : ∑ y ∈ S, D y * cc y = ∑ y : vs, D y * cc y := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro y _ hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hy
        rw [hy, zero_mul]
      rw [hsub, hα]
    have hp0S : p₀.2 ∈ S := by rw [hS]; simp [hDp0]
    have hSne : S.Nonempty := ⟨p₀.2, hp0S⟩
    have hfne : ∀ y ∈ S, D y * cc y ≠ 0 := by
      intro y hy
      rw [hS, Finset.mem_filter] at hy
      exact mul_ne_zero hy.2 (hcc_ne y)
    have hinj : Set.InjOn (fun y => v (D y * cc y)) (↑S : Set vs) := by
      intro y₁ hy₁ y₂ hy₂ heq
      replace heq : v (D y₁ * cc y₁) = v (D y₂ * cc y₂) := heq
      rw [Finset.mem_coe, hS, Finset.mem_filter] at hy₁ hy₂
      rw [hv, Valuation.map_mul, Valuation.map_mul, ← hv, hxx y₁ hy₁.2, hxx y₂ hy₂.2,
        hcc_val y₁, hcc_val y₂, hv, ← coe_valueGroupHom_apply B K L (xx y₁ hy₁.2),
        ← coe_valueGroupHom_apply B K L (xx y₂ hy₂.2)] at heq
      have hequnit : (valueGroupHom B K L (xx y₁ hy₁.2)) * (y₁ : (ValueGroup B L)ˣ)
          = (valueGroupHom B K L (xx y₂ hy₂.2)) * (y₂ : (ValueGroup B L)ˣ) :=
        Units.ext (by push_cast; exact heq)
      have hmem : (y₁ : (ValueGroup B L)ˣ) * (y₂ : (ValueGroup B L)ˣ)⁻¹ ∈ H := by
        rw [hH]
        refine ⟨(xx y₁ hy₁.2)⁻¹ * (xx y₂ hy₂.2), ?_⟩
        rw [map_mul, map_inv,
          mul_comm ((valueGroupHom B K L) (xx y₁ hy₁.2))⁻¹ ((valueGroupHom B K L) (xx y₂ hy₂.2)),
          ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul,
          mul_comm (y₁ : (ValueGroup B L)ˣ), mul_comm ((valueGroupHom B K L) (xx y₂ hy₂.2)),
          mul_comm (y₂ : (ValueGroup B L)ˣ)]
        exact hequnit.symm
      have hqmk : QuotientGroup.mk (s := H) (y₁ : (ValueGroup B L)ˣ)
          = QuotientGroup.mk (y₂ : (ValueGroup B L)ˣ) := by
        rw [QuotientGroup.eq]
        simpa [mul_comm] using H.inv_mem hmem
      exact Subtype.ext (hvs y₁.2 y₂.2 hqmk)
    exact Valuation.sum_ne_zero_of_injOn v S (fun y => D y * cc y) hSne hfne hinj hSsum
  simpa using hLI.fintype_card_le_finrank

/-- Every finset in the codomain of a surjection lifts to a finset of representatives of the same
cardinality on which the surjection is injective. -/
theorem Function.Surjective.exists_finset_card_eq_injOn {α β : Type*} {f : α → β}
    (hf : Function.Surjective f) (t : Finset β) :
    ∃ s : Finset α, s.card = t.card ∧ Set.InjOn f ↑s := by
  classical
  refine ⟨t.image (Function.surjInv hf),
    Finset.card_image_of_injective _ (Function.injective_surjInv hf), ?_⟩
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_image] at ha hb
  obtain ⟨a', -, rfl⟩ := ha
  obtain ⟨b', -, rfl⟩ := hb
  exact congrArg _ ((Function.surjInv_eq hf a').symm.trans (hab.trans (Function.surjInv_eq hf b')))

/-- The degree inequality `[Γ_B : Γ_A] · [κ_B : κ_A] ≤ [L : K]` for an extension of valuation
rings with `L/K` finite, together with the finiteness of `κ_B/κ_A` and of `[Γ_B : Γ_A]`. -/
theorem ValuationRing.index_mul_finrank_residueField_le_finrank
    (A B K L : Type*)
    [CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing B] [IsDomain B] [ValuationRing B] [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsLocalHom (algebraMap A B)] [Module.Finite K L] :
    Module.Finite (ResidueField A) (ResidueField B) ∧
    (valueGroupHom B K L).range.index ≠ 0 ∧
    (valueGroupHom B K L).range.index * Module.finrank (ResidueField A) (ResidueField B)
      ≤ Module.finrank K L := by
  set H : Subgroup ((ValueGroup B L)ˣ) := (valueGroupHom B K L).range
  have hrank : Module.rank (ResidueField A) (ResidueField B) ≤ (Module.finrank K L : ℕ) :=
    rank_le fun s hs => by
      simpa using card_mul_card_le_finrank A B K L s {1} hs (by intro a _ b _ _; simp_all)
  have hres_fin : Module.Finite (ResidueField A) (ResidueField B) :=
    Module.rank_lt_aleph0_iff.mp (hrank.trans_lt Cardinal.natCast_lt_aleph0)
  have hcoset_bound : ∀ vs : Finset ((ValueGroup B L)ˣ),
      Set.InjOn (QuotientGroup.mk (s := H)) ↑vs → vs.card ≤ Module.finrank K L := by
    intro vs hvs
    have h1 : LinearIndependent (ResidueField A)
        (fun x : ({1} : Finset (ResidueField B)) => (x : ResidueField B)) := by
      rw [linearIndependent_unique_iff]
      simp
    simpa using card_mul_card_le_finrank A B K L {1} vs h1 hvs
  have hindex : H.index ≠ 0 := by
    intro hzero
    rw [Subgroup.index_eq_card, Nat.card_eq_zero] at hzero
    have : Infinite ((ValueGroup B L)ˣ ⧸ H) := hzero.resolve_left (not_isEmpty_of_nonempty _)
    obtain ⟨t, ht⟩ :=
      Infinite.exists_subset_card_eq ((ValueGroup B L)ˣ ⧸ H) (Module.finrank K L + 1)
    obtain ⟨vs, hvs, hinj⟩ := (QuotientGroup.mk_surjective (s := H)).exists_finset_card_eq_injOn t
    have := hcoset_bound vs hinj
    omega
  have hprod : H.index * Module.finrank (ResidueField A) (ResidueField B) ≤
      Module.finrank K L := by
    obtain ⟨rs, hrs_card, hrs_ind⟩ :=
      exists_finset_linearIndependent_of_le_finrank (R := ResidueField A) (M := ResidueField B)
        le_rfl
    have : Finite ((ValueGroup B L)ˣ ⧸ H) :=
      Nat.finite_of_card_ne_zero (by rwa [← Subgroup.index_eq_card])
    have := Fintype.ofFinite ((ValueGroup B L)ˣ ⧸ H)
    obtain ⟨vs, hvs_card, hvs_inj⟩ :=
      (QuotientGroup.mk_surjective (s := H)).exists_finset_card_eq_injOn Finset.univ
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card] at hvs_card
    rw [mul_comm, ← hrs_card, ← hvs_card]
    exact card_mul_card_le_finrank A B K L rs vs hrs_ind hvs_inj
  exact ⟨hres_fin, hindex, hprod⟩

/-- Let `A ⊆ B` be an extension of valuation rings with fraction fields `K ⊆ L`, and assume the
field extension `L/K` is finite. Then:

1. the residue field extension `κ_A ⊆ κ_B` is finite (`Module.Finite`, i.e.
   `[κ_B : κ_A] < ∞`);
2. the value group `Γ_A` has finite index in `Γ_B`
   (`(valueGroupHom B K L).range.index ≠ 0`, i.e. `[Γ_B : Γ_A] < ∞`); and
3. `[Γ_B : Γ_A] · [κ_B : κ_A] ≤ [L : K]`.

The residue field degree `[κ_B : κ_A]` is computed with respect to the algebra structure on
`κ_B` over `κ_A` induced by Mathlib's `IsLocalRing.ResidueField.map (algebraMap A B)`. -/
@[stacks 0ASH]
theorem ext_valuation_rings_degree_ineq
    (A B K L : Type*)
    [CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing B] [IsDomain B] [ValuationRing B] [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsLocalHom (algebraMap A B)]
    (hfin : Module.Finite K L) :
    letI : Algebra (ResidueField A) (ResidueField B) :=
      (ResidueField.map (algebraMap A B)).toAlgebra
    Module.Finite (ResidueField A) (ResidueField B) ∧
    (valueGroupHom B K L).range.index ≠ 0 ∧
    (valueGroupHom B K L).range.index * Module.finrank (ResidueField A) (ResidueField B)
      ≤ Module.finrank K L := by
  have := hfin
  exact ValuationRing.index_mul_finrank_residueField_le_finrank A B K L
