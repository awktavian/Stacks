module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Lattice.Defs
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm.OrdIntBasics
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm.CokerLenDevissage


@[expose] public section


open Ring

/-- STEP 2 (Route γ).  Clearing scalar.  Given a full-rank free submodule `range j ⊆ M` (with `j`
the embedding from `exists_fullRank_free_submodule`) and any `A`-linear `φ : M →ₗ M`, there is a
nonzero `a ∈ A` such that `a • φ` carries `range j` into `range j`, i.e.
`∀ x, (a • φ) (j x) ∈ range j`.  (Each `φ (j x_i)` is a `K`-combination of the basis `j x_i` in
`M ⊗ K`; clear the finitely many denominators by a single nonzero `a ∈ A`; torsion-freeness pushes
the relation back into `M`.) -/
theorem exists_clearing_scalar
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M]
    (j : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A] M)
    (hjinj : Function.Injective j)
    (hjlen : Module.length A (M ⧸ LinearMap.range j) ≠ ⊤)
    (φ : M →ₗ[A] M) :
    ∃ a : A, a ≠ 0 ∧ ∀ x, (a • φ) (j x) ∈ LinearMap.range j := by
  set R := LinearMap.range j with hRdef
  have hQfl : IsFiniteLength A (M ⧸ R) := Module.length_ne_top_iff.mp hjlen
  by_cases hf : IsField A
  · -- Field case: `range j` is a full-rank subspace of the finite-dimensional `A`-space `M`,
    -- so `range j = ⊤` and any scalar (e.g. `a = 1`) works.
    refine ⟨1, one_ne_zero, fun x => ?_⟩
    have htop : R = ⊤ := by
      let : Field A := hf.toField
      have : Module.Free A M := inferInstance
      have : FiniteDimensional A M := inferInstance
      have hn : Module.finrank K (TensorProduct A K M) = Module.finrank A M :=
        Module.finrank_baseChange
      have hdom : Module.finrank A (Fin (Module.finrank K (TensorProduct A K M)) → A)
          = Module.finrank A M := by
        rw [Module.finrank_fin_fun, hn]
      rw [hRdef, LinearMap.range_eq_top]
      exact (LinearMap.linearEquivOfInjective j hjinj hdom).surjective
    rw [htop]; exact Submodule.mem_top
  · -- Non-field case: `Q := M ⧸ range j` has finite length over the `1`-dimensional Noetherian
    -- local domain `A`, hence is torsion: each element is killed by a nonzero `a ∈ A` (otherwise a
    -- copy of `A` would have finite length, forcing `A` Artinian, hence a field — contradiction).
    set g : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A] (M ⧸ R) :=
      R.mkQ ∘ₗ φ ∘ₗ j with hgdef
    have key : ∀ y : (M ⧸ R), ∃ a : A, a ≠ 0 ∧ a • y = 0 := by
      intro y
      by_contra h
      push Not at h
      have hker : (LinearMap.toSpanSingleton A (M ⧸ R) y).ker = ⊥ := by
        rw [LinearMap.ker_eq_bot']
        intro a ha; by_contra hne; exact h a hne ha
      have hinj : Function.Injective (LinearMap.toSpanSingleton A (M ⧸ R) y) := by
        rw [← LinearMap.ker_eq_bot]; exact hker
      have hfl : IsFiniteLength A A := by
        have hle : Module.length A A ≤ Module.length A (M ⧸ R) :=
          Module.length_le_of_injective _ hinj
        rw [← Module.length_ne_top_iff] at hQfl ⊢
        intro htop; rw [htop] at hle; exact hQfl (top_le_iff.mp hle)
      have : IsArtinianRing A := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).right
      exact hf (IsArtinianRing.isField_of_isDomain A)
    -- Choose a nonzero annihilator `c i` for each generator `g eᵢ` and take their product `a`.
    choose c hc0 hc using fun i => key (g (Pi.single i 1))
    set a : A := ∏ i, c i with hadef
    have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hc0 i)
    have hgen : ∀ i, a • g (Pi.single i 1) = 0 := by
      intro i
      rw [hadef, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul, hc i, smul_zero]
    -- `x ↦ a • g x` is `A`-linear and vanishes on the standard basis, hence is identically zero.
    have hzero : ∀ x, a • g x = 0 := by
      have hlin : (a • g) = 0 := by
        apply (Pi.basisFun A (Fin (Module.finrank K (TensorProduct A K M)))).ext
        intro i
        simp only [LinearMap.smul_apply, Pi.basisFun_apply, LinearMap.zero_apply]
        exact hgen i
      intro x
      have := LinearMap.congr_fun hlin x
      simpa using this
    refine ⟨a, ha0, fun x => ?_⟩
    have hx : a • g x = 0 := hzero x
    rw [hgdef] at hx
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hx ⊢
    rw [← map_smul] at hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    exact hx

/-- DET HELPER (Route γ).  The `K`-base change of `a • φ` has determinant
`a ^ r · det (φ.baseChange K)` where `r = finrank K (M ⊗ K)`.  (`(a•φ).baseChange K =
(algebraMap A K a) • (φ.baseChange K)`, and `det (c • L) = c ^ (finrank) · det L` for an
endomorphism
`L` of a `finrank`-dimensional space.)  Used in the kernel assembly. -/
@[ega "II 6.4.9" "special case"]
theorem det_baseChange_smul
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a : A) (φ : M →ₗ[A] M) :
    LinearMap.det ((a • φ).baseChange K) =
      (algebraMap A K a) ^ (Module.finrank K (TensorProduct A K M)) *
        LinearMap.det (φ.baseChange K) := by
  have h : (a • φ).baseChange K = (algebraMap A K a) • (φ.baseChange K) := by
    rw [LinearMap.baseChange_smul, algebraMap_smul]
  rw [h, LinearMap.det_smul]

/-- SCALAR IDENTITY (Route γ).  For multiplication-by-`a` (`a ≠ 0`) on a finite torsion-free module
`M` over a 1-dim Noetherian local domain `A`, the cokernel length equals `r · ord_A(a)` where
`r = finrank K (M ⊗ K)`. -/
@[ega "IV 21.10.13" "special case"]
theorem length_quot_smul_eq_rank_mul_ord
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M]
    (a : A) (ha : a ≠ 0) (haK : algebraMap A K a ≠ 0) :
    ((Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M a))).toNat : ℤ) =
      (Module.finrank K (TensorProduct A K M) : ℤ) * ordInt A (algebraMap A K a) haK := by
  -- cusp k[[t²,t³]] match)
  classical
  -- Proof-irrelevance helper for `ordInt` in its nonzero-witness argument, plus value congruence.
  have ordA_congr : ∀ (x y : K) (hx : x ≠ 0) (hy : y ≠ 0), x = y →
      ordInt A x hx = ordInt A y hy := by
    intro x y hx hy h; subst h; rfl
  set r := Module.finrank K (TensorProduct A K M) with hr
  -- Step 1: full-rank free submodule.
  obtain ⟨j, hjinj, hjlen⟩ := exists_fullRank_free_submodule A K M
  -- abbreviation: ψ = multiplication-by-a on M.
  set ψ : M →ₗ[A] M := LinearMap.lsmul A M a with hψ
  -- `ψ = a • id`
  have hψsmul : ψ = a • (LinearMap.id : M →ₗ[A] M) := by
    ext x; simp [hψ, LinearMap.lsmul_apply]
  -- `ψ` injective (torsion-free, `a ≠ 0`)
  have hψinj : Function.Injective ψ := by
    intro x y h
    simp only [hψ, LinearMap.lsmul_apply] at h
    exact smul_right_injective M ha h
  -- `ψ` preserves `range j`
  have hpres : ∀ x, ψ (j x) ∈ LinearMap.range j := by
    intro x
    have : ψ (j x) = j (a • x) := by
      simp [hψ, LinearMap.lsmul_apply, map_smul]
    rw [this]
    exact LinearMap.mem_range_self j (a • x)
  -- determinant of base change of `ψ = a • id`
  have hdetψeq : LinearMap.det (ψ.baseChange K) = (algebraMap A K a) ^ r := by
    rw [hψsmul, det_baseChange_smul A K M a (LinearMap.id : M →ₗ[A] M)]
    have : LinearMap.det ((LinearMap.id : M →ₗ[A] M).baseChange K) = 1 := by
      rw [LinearMap.baseChange_id]; exact LinearMap.det_id
    rw [this, mul_one]
  have hdetψ : LinearMap.det (ψ.baseChange K) ≠ 0 := by
    rw [hdetψeq]; exact pow_ne_zero _ haK
  -- Step 3: defect dévissage for `ψ`.
  have hdev :
      ordInt A (LinearMap.det (ψ.baseChange K)) hdetψ =
        ((Module.length A (M ⧸ LinearMap.range ψ)).toNat : ℤ) :=
    defect_devissage_free A K M ψ hψinj j hjinj hjlen hpres hdetψ
  -- ord of a power: `ordInt A (x^k) = k * ordInt A x`.
  have hpow : ∀ k : ℕ, ∀ (h : (algebraMap A K a) ^ k ≠ 0),
      ordInt A ((algebraMap A K a) ^ k) h = (k : ℤ) * ordInt A (algebraMap A K a) haK := by
    intro k
    induction k with
    | zero =>
        intro h
        simp only [Nat.cast_zero, zero_mul]
        have h1 : ordInt A ((algebraMap A K a) ^ 0) h = ordInt A (1 : K) (by norm_num) :=
          ordA_congr _ _ _ _ (by rw [pow_zero])
        rw [h1]
        have hval : ordInt A ((1 : K) * 1) (by norm_num : (1 : K) * 1 ≠ 0) =
            ordInt A (1 : K) (by norm_num) + ordInt A (1 : K) (by norm_num) :=
          ordInt_mul A (1 : K) (1 : K) (by norm_num) (by norm_num)
        simp only [mul_one] at hval
        omega
    | succ n ih =>
        intro h
        have hpn : (algebraMap A K a) ^ n ≠ 0 := pow_ne_zero _ haK
        have hsplit :
            ordInt A ((algebraMap A K a) ^ n * algebraMap A K a)
              (mul_ne_zero hpn haK) =
              ordInt A ((algebraMap A K a) ^ n) hpn +
                ordInt A (algebraMap A K a) haK :=
          ordInt_mul A _ _ hpn haK
        have hcong : ordInt A ((algebraMap A K a) ^ (n + 1)) h =
            ordInt A ((algebraMap A K a) ^ n * algebraMap A K a) (mul_ne_zero hpn haK) :=
          ordA_congr _ _ _ _ (by rw [pow_succ])
        rw [hcong, hsplit, ih hpn]
        push_cast
        ring
  -- Assemble: ordInt(det ψ⊗K) = ordInt((alg a)^r) = r * ordInt(alg a) = length.
  have hpowne : (algebraMap A K a) ^ r ≠ 0 := pow_ne_zero _ haK
  have e1 : ordInt A (LinearMap.det (ψ.baseChange K)) hdetψ =
      ordInt A ((algebraMap A K a) ^ r) hpowne :=
    ordA_congr _ _ _ _ hdetψeq
  rw [hdev] at e1
  rw [e1, hpow r hpowne]

/-- If the `K`-base change of `φ : M →ₗ M`, for a finite `A`-module `M`, has
nonzero determinant — equivalently `φ.baseChange K` is a `K`-automorphism — then the cokernel
`M ⧸ range φ` has finite `A`-length.  (`(M ⧸ range φ) ⊗ K = coker (φ.baseChange K) = 0` since the
base change is onto; a finite `A`-module killed by `⊗ K` is torsion, supported on `{𝔪}`, hence of
finite length over the 1-dim Noetherian local ring `A`.) -/
@[ega "IV 21.10.13" "(i)"]
theorem cokerLen_ne_top_of_baseChangeDet_ne_zero
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (φ : M →ₗ[A] M) (hdet : LinearMap.det (φ.baseChange K) ≠ 0) :
    Module.length A (M ⧸ LinearMap.range φ) ≠ ⊤ := by
  classical
  have : FiniteDimensional K (TensorProduct A K M) := inferInstance
  -- Surjectivity of `φ.baseChange K` (nonzero det ⟹ unit ⟹ bijective on a fin-dim space).
  have hsurj : Function.Surjective (φ.baseChange K) := by
    have hd : IsUnit (LinearMap.det (φ.baseChange K)) := isUnit_iff_ne_zero.mpr hdet
    have hu : IsUnit (φ.baseChange K) := (LinearMap.isUnit_iff_isUnit_det _).mpr hd
    obtain ⟨u, hu⟩ := hu
    intro v
    refine ⟨u.inv v, ?_⟩
    have h2 : (↑u : TensorProduct A K M →ₗ[K] TensorProduct A K M) (u.inv v) = v := by
      calc (↑u : TensorProduct A K M →ₗ[K] TensorProduct A K M) (u.inv v)
            = (↑u * u.inv) v := rfl
        _ = v := by rw [u.val_inv]; rfl
    rw [hu] at h2; exact h2
  -- Tensoring the exact sequence `M --φ--> M --mkQ--> N → 0` with `K` (right-exactness).
  have hexact : Function.Exact φ (LinearMap.range φ).mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ]
  have hsmkQ : Function.Surjective (LinearMap.range φ).mkQ := Submodule.mkQ_surjective _
  have hTexact := lTensor_exact K hexact hsmkQ
  have hTsurj : Function.Surjective (LinearMap.lTensor K (LinearMap.range φ).mkQ) :=
    LinearMap.lTensor_surjective K hsmkQ
  have hsurjT : Function.Surjective (LinearMap.lTensor K φ) := by
    rw [← LinearMap.baseChange_eq_ltensor]; exact hsurj
  -- `lTensor K mkQ = 0` (its kernel is `range (lTensor K φ) = ⊤`), and it is surjective, so
  -- `K ⊗ N = 0`.
  have hKN : ∀ z : TensorProduct A K (M ⧸ LinearMap.range φ), z = 0 := by
    intro z
    obtain ⟨y, rfl⟩ := hTsurj z
    rw [hTexact y]; exact hsurjT y
  -- Hence `N = M ⧸ range φ` is torsion: each element is killed by a nonzero scalar.
  have htorQ : ∀ q : M ⧸ LinearMap.range φ, ∃ a : A, a ≠ 0 ∧ a • q = 0 := by
    intro q
    set ιN : (M ⧸ LinearMap.range φ) →ₗ[A] TensorProduct A K (M ⧸ LinearMap.range φ) :=
      (TensorProduct.mk A K (M ⧸ LinearMap.range φ)) 1 with hιdef
    have : IsLocalizedModule (nonZeroDivisors A) ιN := by
      rw [hιdef, isLocalizedModule_iff_isBaseChange (nonZeroDivisors A) K]
      exact TensorProduct.isBaseChange A (M ⧸ LinearMap.range φ) K
    have h0 : ιN q = 0 := hKN _
    rw [IsLocalizedModule.eq_zero_iff (nonZeroDivisors A)] at h0
    obtain ⟨s, hs⟩ := h0
    exact ⟨(s : A), nonZeroDivisors.ne_zero s.property, hs⟩
  -- Artinian helper: `A/(a)` is Artinian for `a ≠ 0` (`dim A/(a) ≤ dim A - 1 = 0`).
  have hArt : ∀ (a : A), a ≠ 0 → IsArtinianRing (A ⧸ Ideal.span {a}) := by
    intro a ha
    rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
    refine ⟨inferInstance, ?_⟩
    rw [Ring.krullDimLE_iff]
    have hmem : a ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero ha
    have hq := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hmem
    have hA : ringKrullDim A ≤ ((1:ℕ):WithBot ℕ∞) := Ring.krullDimLE_iff.mp inferInstance
    have h : ringKrullDim (A ⧸ Ideal.span {a}) + 1 ≤ ((1:ℕ):WithBot ℕ∞) := le_trans hq hA
    set d := ringKrullDim (A ⧸ Ideal.span {a}) with hd
    have h' : d + 1 ≤ ((1:ℕ∞):WithBot ℕ∞) := by rw [← WithBot.coe_natCast] at h; exact_mod_cast h
    change d ≤ ((0:ℕ):WithBot ℕ∞)
    rw [show ((0:ℕ):WithBot ℕ∞) = ((0:ℕ∞):WithBot ℕ∞) by norm_cast]
    rw [WithBot.le_coe_iff]
    intro a' hda
    rw [hda] at h'
    have h2 : a' + 1 ≤ 1 := by exact_mod_cast h'
    cases a' with
    | top => simp at h2
    | coe n =>
      rw [← ENat.natCast_one, ← ENat.natCast_add, ENat.natCast_le_natCast] at h2
      have : n = 0 := by omega
      subst this; simp
  -- `N` is finitely generated and torsion, hence annihilated by a single nonzero `a`.
  obtain ⟨a, ha0, hann⟩ : ∃ a : A, a ≠ 0 ∧ ∀ q : M ⧸ LinearMap.range φ, a • q = 0 := by
    obtain ⟨s, hs⟩ := (Module.finite_def.mp (by infer_instance) :
      (⊤ : Submodule A (M ⧸ LinearMap.range φ)).FG)
    choose f hf0 hf using htorQ
    set a : A := ∏ g ∈ s, f g with ha
    have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun g _ => hf0 g)
    refine ⟨a, ha0, ?_⟩
    have hgen : ∀ g ∈ s, a • g = 0 := by
      intro g hg
      rw [ha, ← Finset.prod_erase_mul _ _ hg, mul_smul, hf g, smul_zero]
    intro q
    have hq : q ∈ (⊤ : Submodule A (M ⧸ LinearMap.range φ)) := Submodule.mem_top
    rw [← hs] at hq
    induction hq using Submodule.span_induction with
    | mem y hy => exact hgen y hy
    | zero => exact smul_zero a
    | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul c y _ hy => rw [smul_comm, hy, smul_zero]
  -- `N` is a finite module over the Artinian ring `A/(a)`, hence Artinian over `A`.
  have hArtQ : IsArtinian A (M ⧸ LinearMap.range φ) := by
    set I : Ideal A := Ideal.span {a} with hI
    have htor : Module.IsTorsionBySet A (M ⧸ LinearMap.range φ) (I : Set A) := by
      intro q r
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp r.property
      rw [← hc, mul_smul, hann]; simp
    let : Module (A ⧸ I) (M ⧸ LinearMap.range φ) := htor.module
    have : IsScalarTower A (A ⧸ I) (M ⧸ LinearMap.range φ) := htor.isScalarTower
    have : Module.Finite (A ⧸ I) (M ⧸ LinearMap.range φ) :=
      Module.Finite.of_restrictScalars_finite A (A ⧸ I) (M ⧸ LinearMap.range φ)
    have : IsArtinianRing (A ⧸ I) := hArt a ha0
    have : IsArtinian (A ⧸ I) (M ⧸ LinearMap.range φ) := isArtinian_of_fg_of_artinian'
    exact isArtinian_of_surjective_algebraMap (S := A) (R := A ⧸ I)
      (M := M ⧸ LinearMap.range φ) Ideal.Quotient.mk_surjective
  -- Noetherian + Artinian = finite length, so the length is not `⊤`.
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance, hArtQ⟩

/-- KERNEL (Stacks Tag 02QH).  For a finite **torsion-free** `A`-module `M` over a `1`-dimensional
Noetherian local domain `A` with fraction field `K`, and an INJECTIVE `A`-linear endomorphism `φ`
of `M` whose base change to `K` has nonzero determinant, the order of vanishing of that determinant
equals the `A`-length of the cokernel `M ⧸ range φ`.

This is the genuine analytic content of Stacks 02MI.  Carries `[NoZeroSMulDivisors A M]`
(torsion-free `M`); the use site `M = B` (a domain over `A`) supplies it.

*Proof.* Pick a full-rank free submodule
`F ≅ Aʳ ⊆ M` with finite-length quotient (`exists_fullRank_free_submodule`).  `φ` need not preserve
`F`, but a scalar multiple `ψ = a·φ = μ_a ∘ φ` (`a ≠ 0`) does; then `Δ(M,ψ) = 0`
(`defect_devissage_free`: snake additivity over `0→F→M→Q→0`, matrix base case on `F`, finite-length
on `Q`).  Undo the scalar via the scalar identity `Δ(M, μ_a) = 0`
(`length_quot_smul_eq_rank_mul_ord`) and the composition additivity `Δ(M, μ_a ∘ φ) = Δ(M, μ_a) +
Δ(M, φ)` (`defect_comp`), giving `Δ(M,φ) = 0`. -/
@[ega "IV 21.10.17.3" "special case"]
theorem ordInt_baseChangeDet_eq_length_cokernel
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M]
    (φ : M →ₗ[A] M)
    (hφinj : Function.Injective φ)
    (hdet : LinearMap.det (φ.baseChange K) ≠ 0) :
    ordInt A (LinearMap.det (φ.baseChange K)) hdet =
      ((Module.length A (M ⧸ LinearMap.range φ)).toNat : ℤ) := by
  classical
  -- Proof-irrelevance helper for `ordInt` in its nonzero-witness argument, plus value congruence.
  have ordA_congr : ∀ (x y : K) (hx : x ≠ 0) (hy : y ≠ 0), x = y →
      ordInt A x hx = ordInt A y hy := by
    intro x y hx hy h; subst h; rfl
  set r := Module.finrank K (TensorProduct A K M) with hr
  -- Step 1: full-rank free submodule.
  obtain ⟨j, hjinj, hjlen⟩ := exists_fullRank_free_submodule A K M
  -- Step 2: clearing scalar.
  obtain ⟨a, ha, hpres⟩ := exists_clearing_scalar A K M j hjinj hjlen φ
  -- abbreviations
  set μ : M →ₗ[A] M := LinearMap.lsmul A M a with hμ
  -- `a • φ = μ ∘ₗ φ`
  have hψeq : a • φ = μ ∘ₗ φ := by
    ext x; simp [hμ, LinearMap.lsmul_apply]
  -- `μ` injective (torsion-free, `a ≠ 0`)
  have hμinj : Function.Injective μ := by
    intro x y h
    simp only [hμ, LinearMap.lsmul_apply] at h
    exact smul_right_injective M ha h
  -- `ψ := a • φ` injective
  have hψinj : Function.Injective (a • φ) := by
    rw [hψeq]; exact hμinj.comp hφinj
  -- `algebraMap A K a ≠ 0`
  have haK : algebraMap A K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha
  -- determinant of base change of `a • φ`
  have hdetsmul : LinearMap.det ((a • φ).baseChange K) =
      (algebraMap A K a) ^ r * LinearMap.det (φ.baseChange K) :=
    det_baseChange_smul A K M a φ
  -- nonzero determinant of `(a•φ).baseChange K`
  have hdetψ : LinearMap.det ((a • φ).baseChange K) ≠ 0 := by
    rw [hdetsmul]
    exact mul_ne_zero (pow_ne_zero _ haK) hdet
  -- determinant of base change of `μ` (= scalar `a • id`)
  have hμsmul : μ = a • (LinearMap.id : M →ₗ[A] M) := by
    ext x; simp [hμ, LinearMap.lsmul_apply]
  have hdetμeq : LinearMap.det (μ.baseChange K) = (algebraMap A K a) ^ r := by
    rw [hμsmul, det_baseChange_smul A K M a (LinearMap.id : M →ₗ[A] M)]
    have : LinearMap.det ((LinearMap.id : M →ₗ[A] M).baseChange K) = 1 := by
      rw [LinearMap.baseChange_id]; exact LinearMap.det_id
    rw [this, mul_one]
  have hdetμ : LinearMap.det (μ.baseChange K) ≠ 0 := by
    rw [hdetμeq]; exact pow_ne_zero _ haK
  -- Step 3: defect dévissage for `ψ = a • φ`.
  have hdev :
      ordInt A (LinearMap.det ((a • φ).baseChange K)) hdetψ =
        ((Module.length A (M ⧸ LinearMap.range (a • φ))).toNat : ℤ) :=
    defect_devissage_free A K M (a • φ) hψinj j hjinj hjlen hpres hdetψ
  -- finiteness of cokernels
  have hcfφ : Module.length A (M ⧸ LinearMap.range φ) ≠ ⊤ :=
    cokerLen_ne_top_of_baseChangeDet_ne_zero A K M φ hdet
  have hcfμ : Module.length A (M ⧸ LinearMap.range μ) ≠ ⊤ :=
    cokerLen_ne_top_of_baseChangeDet_ne_zero A K M μ hdetμ
  -- Step 8: composition additivity of cokernel length, in ℕ∞.
  have hcomp :
      Module.length A (M ⧸ LinearMap.range (a • φ)) =
        Module.length A (M ⧸ LinearMap.range φ) +
          Module.length A (M ⧸ LinearMap.range μ) := by
    rw [hψeq]
    exact cokerLen_comp_add A M φ μ hμinj
  -- Step 9: `.toNat` is additive on the two finite summands.
  have htoNat :
      (Module.length A (M ⧸ LinearMap.range (a • φ))).toNat =
        (Module.length A (M ⧸ LinearMap.range φ)).toNat +
          (Module.length A (M ⧸ LinearMap.range μ)).toNat := by
    rw [hcomp, ENat.toNat_add hcfφ hcfμ]
  -- Step 11: scalar identity gives the length of `M ⧸ range μ`.
  have hscalar :
      ((Module.length A (M ⧸ LinearMap.range μ)).toNat : ℤ) =
        (r : ℤ) * ordInt A (algebraMap A K a) haK :=
    length_quot_smul_eq_rank_mul_ord A K M a ha haK
  -- ord of a power: `ordInt A (x^k) = k * ordInt A x`.
  have hpow : ∀ k : ℕ, ∀ (h : (algebraMap A K a) ^ k ≠ 0),
      ordInt A ((algebraMap A K a) ^ k) h = (k : ℤ) * ordInt A (algebraMap A K a) haK := by
    intro k
    induction k with
    | zero =>
        intro h
        simp only [Nat.cast_zero, zero_mul]
        have h1 : ordInt A ((algebraMap A K a) ^ 0) h = ordInt A (1 : K) (by norm_num) :=
          ordA_congr _ _ _ _ (by rw [pow_zero])
        rw [h1]
        have hval : ordInt A ((1 : K) * 1) (by norm_num : (1 : K) * 1 ≠ 0) =
            ordInt A (1 : K) (by norm_num) + ordInt A (1 : K) (by norm_num) :=
          ordInt_mul A (1 : K) (1 : K) (by norm_num) (by norm_num)
        simp only [mul_one] at hval
        omega
    | succ n ih =>
        intro h
        have hpn : (algebraMap A K a) ^ n ≠ 0 := pow_ne_zero _ haK
        have hsplit :
            ordInt A ((algebraMap A K a) ^ n * algebraMap A K a)
              (mul_ne_zero hpn haK) =
              ordInt A ((algebraMap A K a) ^ n) hpn +
                ordInt A (algebraMap A K a) haK :=
          ordInt_mul A _ _ hpn haK
        have hcong : ordInt A ((algebraMap A K a) ^ (n + 1)) h =
            ordInt A ((algebraMap A K a) ^ n * algebraMap A K a) (mul_ne_zero hpn haK) :=
          ordA_congr _ _ _ _ (by rw [pow_succ])
        rw [hcong, hsplit, ih hpn]
        push_cast
        ring
  -- Step 10: ord of `det (ψ.baseChange K)` splits via `det_baseChange_smul` + `ordInt_mul`.
  have hordψ :
      ordInt A (LinearMap.det ((a • φ).baseChange K)) hdetψ =
        (r : ℤ) * ordInt A (algebraMap A K a) haK +
          ordInt A (LinearMap.det (φ.baseChange K)) hdet := by
    have hpowne : (algebraMap A K a) ^ r ≠ 0 := pow_ne_zero _ haK
    -- rewrite the value inside ordInt via congruence (proof-irrelevant witness)
    have e1 : ordInt A (LinearMap.det ((a • φ).baseChange K)) hdetψ =
        ordInt A ((algebraMap A K a) ^ r * LinearMap.det (φ.baseChange K))
          (mul_ne_zero hpowne hdet) :=
      ordA_congr _ _ _ _ hdetsmul
    rw [e1, ordInt_mul A _ _ hpowne hdet, hpow r hpowne]
  -- Assemble.
  -- From hdev + hordψ : r*c + D = (length (M ⧸ range (a•φ))).toNat
  -- From htoNat + hscalar : (length (M ⧸ range (a•φ))).toNat = Lφ + r*c
  have key1 :
      (r : ℤ) * ordInt A (algebraMap A K a) haK +
          ordInt A (LinearMap.det (φ.baseChange K)) hdet =
        ((Module.length A (M ⧸ LinearMap.range (a • φ))).toNat : ℤ) := by
    rw [← hordψ, hdev]
  have key2 :
      ((Module.length A (M ⧸ LinearMap.range (a • φ))).toNat : ℤ) =
        ((Module.length A (M ⧸ LinearMap.range φ)).toNat : ℤ) +
          (r : ℤ) * ordInt A (algebraMap A K a) haK := by
    rw [htoNat]
    push_cast
    rw [hscalar]
  rw [key2] at key1
  -- key1 : r*c + D = Lφ + r*c
  linarith [key1]

/-- BRIDGE.  The determinant of the `K`-base change of `A`-linear multiplication-by-`b` on `B`
equals the field norm `Nm_{L/K}(algebraMap B L b)`.

Uses the canonical `K`-algebra isomorphism `B ⊗[A] K ≅ L` (`B` is finite over `A`, `L = Frac B`,
`K = Frac A`), under which `(lmul_A b).baseChange K` corresponds to multiplication-by-`b` on `L`
as a `K`-vector space, whose `K`-determinant is by definition `Algebra.norm K`.  Candidate hooks:
`IsLocalization` / `FractionRing` tensor-product identification, `Algebra.norm` as `LinearMap.det`
of `lmul`, `LinearMap.det_baseChange` / `LinearMap.baseChange` naturality.  Its own subtask. -/
theorem baseChangeDet_lmul_eq_norm
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    (K L : Type*) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    (b : B) :
    LinearMap.det ((Algebra.lmul A B b).baseChange K) = Algebra.norm K (algebraMap B L b) := by
  -- once FiniteDimensional K L, which is forced by Module.Finite A B + L=Frac B/K=Frac A).
  classical
  -- B is integral over A (module-finite), hence the image of A∖{0} lies in B∖{0} and every
  -- nonzero element of B divides a nonzero element of A; so inverting A∖{0} in B yields L.
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  -- `A → B` is injective: A is a domain and B is a nonzero A-algebra (a domain), and any
  -- finite faithful... actually we get it from `NoZeroSMulDivisors`/integrality is not needed;
  -- use that nonzero divisors map to nonzero divisors via algebra being injective on Frac data.
  have hAB : Function.Injective (algebraMap A B) := by
    have h1 : Function.Injective (algebraMap A L) :=
      (IsScalarTower.algebraMap_eq A K L ▸ (FaithfulSMul.algebraMap_injective K L).comp
        (IsFractionRing.injective A K))
    have h2 : (algebraMap A L) = (algebraMap B L).comp (algebraMap A B) :=
      IsScalarTower.algebraMap_eq A B L
    intro x y hxy
    apply h1
    rw [h2]
    simp only [RingHom.comp_apply]
    rw [hxy]
  have hMN : Algebra.algebraMapSubmonoid B (nonZeroDivisors A) ≤ nonZeroDivisors B := by
    rintro x ⟨a, ha, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    have : a ≠ 0 := nonZeroDivisors.ne_zero ha
    rw [ne_eq, ← (algebraMap A B).map_zero]
    exact fun h => this (hAB h)
  have hdvd : ∀ n ∈ nonZeroDivisors B,
      ∃ m ∈ Algebra.algebraMapSubmonoid B (nonZeroDivisors A), n ∣ m := by
    intro n hn
    obtain ⟨c, d, hd, hdc⟩ :=
      Algebra.IsAlgebraic.exists_smul_eq_mul A (1 : B) (b := n) (nonZeroDivisors.ne_zero hn)
    refine ⟨algebraMap A B d, ?_, ?_⟩
    · rw [Algebra.algebraMapSubmonoid, Submonoid.mem_map]
      exact ⟨d, mem_nonZeroDivisors_of_ne_zero hd, rfl⟩
    · rw [Algebra.smul_def, mul_one] at hdc
      exact ⟨c, hdc⟩
  have hLocB : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    (IsLocalization.iff_of_le_of_exists_dvd (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
      (nonZeroDivisors B) hMN hdvd).mpr inferInstance
  -- L is the localization of the A-module B at A∖{0}.
  have hLM : IsLocalizedModule (nonZeroDivisors A)
      (IsScalarTower.toAlgHom A B L).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr hLocB
  -- Base change: K ⊗[A] B ≃ₗ[K] L.
  have hbc : IsBaseChange K (IsScalarTower.toAlgHom A B L).toLinearMap :=
    IsLocalizedModule.isBaseChange (nonZeroDivisors A) K (IsScalarTower.toAlgHom A B L).toLinearMap
  set e : (TensorProduct A K B) ≃ₗ[K] L := hbc.equiv with he
  -- The conjugation identity: e ∘ (lmul b).baseChange = (lmul (algMap b)) ∘ e.
  have hconj : (Algebra.lmul A B b).baseChange K
      = (e.symm : L →ₗ[K] (TensorProduct A K B)) ∘ₗ
          (Algebra.lmul K L (algebraMap B L b)) ∘ₗ (e : (TensorProduct A K B) →ₗ[K] L) := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext k
    simp only [ TensorProduct.AlgebraTensorModule.curry_apply,
      TensorProduct.curry_apply, LinearMap.coe_restrictScalars, LinearMap.baseChange_tmul,
      LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, he]
    rw [LinearEquiv.eq_symm_apply, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul]
    simp only [one_smul, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom']
    change algebraMap B L ((Algebra.lmul A B b) k) = (Algebra.lmul K L (algebraMap B L b))
        (algebraMap B L k)
    have h1 : (Algebra.lmul A B b) k = b * k := by simp [Algebra.lmul]
    have h2 : (Algebra.lmul K L (algebraMap B L b)) (algebraMap B L k)
        = algebraMap B L b * algebraMap B L k := by simp [Algebra.lmul]
    rw [h1, h2, map_mul]
  rw [Algebra.norm_apply, hconj]
  have := LinearMap.det_conj (Algebra.lmul K L (algebraMap B L b)) e.symm
  simp only [LinearEquiv.symm_symm] at this
  rw [this]

/-- The order of vanishing of the norm of `b` equals the length of `B ⧸ bB` over `A`. -/
theorem ordInt_norm_eq_length_quotient
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (K L : Type*) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    (hAB : Function.Injective (algebraMap A B))
    (b : B) (hb : b ≠ 0)
    (hx0 : Algebra.norm K (algebraMap B L b) ≠ 0) :
    ordInt A (Algebra.norm K (algebraMap B L b)) hx0 =
      ((Module.length A (B ⧸ Ideal.span {b})).toNat : ℤ) := by
  -- Reduce to the 02QH kernel with M = B, φ = A-linear multiplication-by-b.
  -- ordInt is proof-irrelevant in its nonzero proof; transport along equalities of values.
  have ordA_congr : ∀ (a a' : K) (ha : a ≠ 0) (ha' : a' ≠ 0),
      a = a' → ordInt A a ha = ordInt A a' ha' := by
    intro a a' ha ha' h; subst h; rfl
  set φ : B →ₗ[A] B := Algebra.lmul A B b with hφ
  -- BRIDGE 1 (det = norm): cited as `baseChangeDet_lmul_eq_norm`.
  have hbridgeDet : LinearMap.det (φ.baseChange K) = Algebra.norm K (algebraMap B L b) :=
    baseChangeDet_lmul_eq_norm A B K L b
  -- BRIDGE 2 (cokernel = B/bB): range of multiplication-by-b is the ideal span {b} (PROVEN).
  have hbridgeCoker :
      Module.length A (B ⧸ LinearMap.range φ) = Module.length A (B ⧸ Ideal.span {b}) := by
    have hrange : LinearMap.range φ = (Ideal.span {b}).restrictScalars A := by
      ext x
      simp only [hφ, LinearMap.mem_range, Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
      constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, by simp [Algebra.lmul]⟩
    rw [hrange]
    rfl
  -- Combine via the 02QH kernel.
  have hdet : LinearMap.det (φ.baseChange K) ≠ 0 := by rwa [hbridgeDet]
  have hφinj : Function.Injective φ := by
    rw [hφ]
    exact fun u v huv => mul_left_cancel₀ hb (by simpa [Algebra.lmul] using huv)
  have : NoZeroSMulDivisors A B := by
    refine ⟨fun {a c} hac => ?_⟩
    rw [Algebra.smul_def] at hac
    rcases mul_eq_zero.mp hac with h | h
    · left; exact hAB (by simpa using h)
    · right; exact h
  rw [← ordA_congr _ _ hdet hx0 hbridgeDet,
    ordInt_baseChangeDet_eq_length_cokernel A K B φ hφinj hdet, hbridgeCoker]

