module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent of finiteness to a finite stage of a directed colimit

Let `A = colim_i Aᵢ` be a directed colimit of commutative rings, `A₀` a base stage and
`φ₀ : B₀ → C₀` a map of `A₀`-algebras. Several properties of the base change
`id_A ⊗ φ₀ : A ⊗_{A₀} B₀ → A ⊗_{A₀} C₀` descend to `id_{Aᵢ} ⊗ φ₀` for some stage `i`. This
file treats finiteness.

## Main results

* `Stacks.DirectLimit.FiniteDescent.finite_baseChange_of_colimit_finite`: if `id_A ⊗ φ₀` is
  finite and `φ₀` is of finite type, then some `id_{Aᵢ} ⊗ φ₀` is finite.

## Implementation notes

The colimit is described concretely by the predicate `IsDirectedColimit`, with the base ring `R`
playing the role of the base stage and the index set restricted to the stages above it.

## References

* [Stacks Project, Tag 07RG](https://stacks.math.columbia.edu/tag/07RG)
-/

@[expose] public section

/-- `IsDirectedColimit A f L g` asserts that the ring `L`, together with the
`R`-algebra structure maps `g i : A i →ₐ[R] L`, is the directed colimit of the
directed system of `R`-algebras `(A i)` with transition maps `f`: `f` is functorial, `g` is a
cocone over `f`, the structure maps are jointly surjective, and an element of `A i` vanishes in
`L` if and only if it vanishes at a later stage. -/
structure IsDirectedColimit
    {R : Type*} [CommRing R]
    {ι : Type*} [Preorder ι]
    (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (f : ∀ ⦃i j⦄, i ≤ j → A i →ₐ[R] A j)
    (L : Type*) [CommRing L] [Algebra R L]
    (g : ∀ i, A i →ₐ[R] L) : Prop where
  /-- The transition maps respect composition. -/
  map_comp : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) (x : A i),
    f hjk (f hij x) = f (le_trans hij hjk) x
  /-- The transition map along `i ≤ i` is the identity. -/
  map_id : ∀ i (x : A i), f (le_refl i) x = x
  /-- The structure maps form a cocone: `g j ∘ f_{ji} = g i`. -/
  comp : ∀ ⦃i j⦄ (hij : i ≤ j) (x : A i), g j (f hij x) = g i x
  /-- Every element of `L` comes from some stage. -/
  jointly_surjective : ∀ x : L, ∃ i, ∃ a : A i, g i a = x
  /-- If `a : A i` maps to `0` in `L`, then it already maps to `0` at some later
  stage `j ≥ i`. -/
  exists_eq_zero : ∀ ⦃i⦄ (a : A i), g i a = 0 → ∃ j, ∃ hij : i ≤ j, f hij a = 0


namespace Stacks.DirectLimit.FiniteDescent

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable {B C : Type*} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

/-- Base change of `φ : B →ₐ[R] C` along the structure map `R → S`, where `S` is
any `R`-algebra, i.e. `id_S ⊗ φ : S ⊗_R B → S ⊗_R C`. -/
noncomputable def baseChange (S : Type*) [CommRing S] [Algebra R S] (φ : B →ₐ[R] C) :
    TensorProduct R S B →ₐ[R] TensorProduct R S C :=
  Algebra.TensorProduct.map (AlgHom.id R S) φ

/-- The structure map `g i : A i →ₐ[R] L` tensored on the right by an `R`-algebra `S`,
`g i ⊗ id : A i ⊗_R S → L ⊗_R S`. -/
noncomputable def tensorG (S : Type*) [CommRing S] [Algebra R S]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {L : Type*} [CommRing L] [Algebra R L]
    (g : ∀ i, A i →ₐ[R] L) (i : ι) :
    TensorProduct R (A i) S →ₐ[R] TensorProduct R L S :=
  Algebra.TensorProduct.map (g i) (AlgHom.id R S)

/-- Tensoring a transition map `f hij : A i →ₐ[R] A j` on the right by `S`. -/
noncomputable def tensorF (S : Type*) [CommRing S] [Algebra R S]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (f : ∀ ⦃i j⦄, i ≤ j → A i →ₐ[R] A j) ⦃i j : ι⦄ (hij : i ≤ j) :
    TensorProduct R (A i) S →ₐ[R] TensorProduct R (A j) S :=
  Algebra.TensorProduct.map (f hij) (AlgHom.id R S)

/-! ### Tensoring commutes with directed colimits -/

/-- If `L = colim A_i` as `R`-algebras, then `L ⊗_R S = colim (A_i ⊗_R S)`, with structure
maps `tensorG S g = g i ⊗ id` and transition maps `tensorF S f = f ⊗ id`. -/
theorem IsDirectedColimit.tensor_right (S : Type*) [CommRing S] [Algebra R S]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {f : ∀ ⦃i j⦄, i ≤ j → A i →ₐ[R] A j}
    {L : Type*} [CommRing L] [Algebra R L]
    {g : ∀ i, A i →ₐ[R] L}
    (hcolim : IsDirectedColimit A f L g) :
    IsDirectedColimit (fun i => TensorProduct R (A i) S) (tensorF S f)
      (TensorProduct R L S) (tensorG S g) := by
  classical
  have hcompP : ∀ ⦃i j⦄ (hij : i ≤ j) (z : TensorProduct R (A i) S),
      tensorG S g j (tensorF S f hij z) = tensorG S g i z := by
    intro i j hij z
    induction z using TensorProduct.inductionOn with
    | tmul a s => simp [tensorF, tensorG, Algebra.TensorProduct.map_tmul, hcolim.comp]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hmapR : ∀ {A' : Type _} [CommRing A'] [Algebra R A'] (h : A' →ₐ[R] L)
      (w : TensorProduct R A' S),
      (Algebra.TensorProduct.map h (AlgHom.id R S)) w = LinearMap.rTensor S h.toLinearMap w := by
    intro A' _ _ h w
    induction w using TensorProduct.inductionOn with
    | tmul a s => simp [Algebra.TensorProduct.map_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hmapRf : ∀ {A' A'' : Type _} [CommRing A'] [Algebra R A'] [CommRing A''] [Algebra R A'']
      (h : A' →ₐ[R] A'') (w : TensorProduct R A' S),
      (Algebra.TensorProduct.map h (AlgHom.id R S)) w = LinearMap.rTensor S h.toLinearMap w := by
    intro A' A'' _ _ _ _ h w
    induction w using TensorProduct.inductionOn with
    | tmul a s => simp [Algebra.TensorProduct.map_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j k hij hjk x
    induction x using TensorProduct.inductionOn with
    | tmul a s => simp [tensorF, Algebra.TensorProduct.map_tmul, hcolim.map_comp]
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro i x
    induction x using TensorProduct.inductionOn with
    | tmul a s => simp [tensorF, Algebra.TensorProduct.map_tmul, hcolim.map_id]
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro i j hij x
    exact hcompP hij x
  · intro y
    induction y using TensorProduct.inductionOn with
    | tmul l s =>
        obtain ⟨i, a, ha⟩ := hcolim.jointly_surjective l
        refine ⟨i, a ⊗ₜ[R] s, ?_⟩
        simp [tensorG, Algebra.TensorProduct.map_tmul, ha]
    | add y₁ y₂ h₁ h₂ =>
        obtain ⟨i₁, z₁, hz₁⟩ := h₁
        obtain ⟨i₂, z₂, hz₂⟩ := h₂
        obtain ⟨k, hik₁, hik₂⟩ := directed_of (· ≤ ·) i₁ i₂
        refine ⟨k, tensorF S f hik₁ z₁ + tensorF S f hik₂ z₂, ?_⟩
        rw [map_add, hcompP hik₁ z₁, hcompP hik₂ z₂, hz₁, hz₂]
  · set Gf : (i j : ι) → i ≤ j → A i →ₗ[R] A j := fun i j hij => (f hij).toLinearMap with hGf
    have hds : DirectedSystem A (fun i j hij => ⇑(Gf i j hij)) := by
      refine ⟨?_, ?_⟩
      · intro i x; exact hcolim.map_id i x
      · intro i j k hij hjk x; exact hcolim.map_comp hij hjk x
    set M := Module.DirectLimit A Gf with hM
    set liftG : M →ₗ[R] L :=
      Module.DirectLimit.lift R ι A Gf (fun i => (g i).toLinearMap)
        (fun i j hij a => by
          rw [hGf, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply]
          exact hcolim.comp hij a) with hliftG
    have hsurj : Function.Surjective liftG := by
      intro x
      obtain ⟨i, a, ha⟩ := hcolim.jointly_surjective x
      refine ⟨Module.DirectLimit.of R ι A Gf i a, ?_⟩
      rwa [hliftG, Module.DirectLimit.lift_of]
    have hinj : Function.Injective liftG := by
      rw [injective_iff_map_eq_zero]
      intro m hm
      obtain ⟨i, a, rfl⟩ := Module.DirectLimit.exists_of m
      rw [hliftG, Module.DirectLimit.lift_of] at hm
      obtain ⟨j, hij, hfa⟩ := hcolim.exists_eq_zero a hm
      rw [← Module.DirectLimit.of_f (hij := hij)]
      show (Module.DirectLimit.of R ι A Gf j) (f hij a) = 0
      rw [hfa, map_zero]
    set e : M ≃ₗ[R] L := LinearEquiv.ofBijective liftG ⟨hinj, hsurj⟩ with he
    have hkey : ∀ i, (e.symm.toLinearMap).comp (g i).toLinearMap
        = Module.DirectLimit.of R ι A Gf i := by
      intro i
      apply LinearMap.ext
      intro a
      simp only [LinearMap.comp_apply]
      rw [show (g i).toLinearMap a = liftG (Module.DirectLimit.of R ι A Gf i a) from
        (by rw [hliftG, Module.DirectLimit.lift_of])]
      show e.symm (e (Module.DirectLimit.of R ι A Gf i a)) = _
      rw [e.symm_apply_apply]
    intro i z hz
    have hzg : tensorG S g i z = LinearMap.rTensor S (g i).toLinearMap z := by
      show (Algebra.TensorProduct.map (g i) (AlgHom.id R S)) z = _
      exact hmapR (g i) z
    have hstep : (TensorProduct.directLimitLeft Gf S)
        (LinearMap.rTensor S e.symm.toLinearMap (tensorG S g i z))
        = Module.DirectLimit.of R ι (fun i => TensorProduct R (A i) S)
            (fun i j h => LinearMap.rTensor S (Gf i j h)) i z := by
      rw [hzg, ← LinearMap.rTensor_comp_apply, hkey i,
        TensorProduct.directLimitLeft_rTensor_of]
    rw [hz] at hstep
    simp only [map_zero] at hstep
    obtain ⟨j, hij, hfz⟩ := Module.DirectLimit.of.zero_exact hstep.symm
    refine ⟨j, hij, ?_⟩
    show (Algebra.TensorProduct.map (f hij) (AlgHom.id R S)) z = 0
    rw [hmapRf (f hij) z]
    rwa [hGf] at hfz

/-! ### Each stage map is of finite type -/

/-- If `t` generates `C` as a `B`-algebra via `φ`, then the elements `1 ⊗ c`, `c ∈ t`, generate
`S ⊗_R C` over `S ⊗_R B` for every `R`-algebra `S`. -/
private theorem adjoin_one_tmul_image_baseChange_eq_top (S : Type*) [CommRing S] [Algebra R S]
    (φ : B →ₐ[R] C) (t : Finset C) (ht' : @Algebra.adjoin B C _ _ φ.toAlgebra (↑t : Set C) = ⊤) :
    letI := (baseChange S φ).toRingHom.toAlgebra
    Algebra.adjoin (TensorProduct R S B) ((fun c => (1 : S) ⊗ₜ[R] c) '' (↑t : Set C)) = ⊤ := by

  let algBC : Algebra B C := φ.toAlgebra
  have tower1 : IsScalarTower R B C :=
    IsScalarTower.of_algebraMap_eq (fun r => (φ.commutes r).symm)
  let algBSB : Algebra B (TensorProduct R S B) :=
    (Algebra.TensorProduct.includeRight).toRingHom.toAlgebra
  have tower2 : IsScalarTower R B (TensorProduct R S B) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      rw [RingHom.algebraMap_toAlgebra]
      show algebraMap R (TensorProduct R S B) r =
        Algebra.TensorProduct.includeRight (algebraMap R B r)
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        ← TensorProduct.smul_tmul])
  let algSBSC : Algebra (TensorProduct R S B) (TensorProduct R S C) :=
    (Algebra.TensorProduct.map (AlgHom.id R S) φ).toRingHom.toAlgebra
  let algBSC : Algebra B (TensorProduct R S C) :=
    ((algebraMap (TensorProduct R S B) (TensorProduct R S C)).comp
      (algebraMap B (TensorProduct R S B))).toAlgebra
  have towerBSB : IsScalarTower B (TensorProduct R S B) (TensorProduct R S C) :=
    IsScalarTower.of_algebraMap_eq (fun b => by rw [RingHom.algebraMap_toAlgebra]; rfl)
  have galg : ∀ b : B, Algebra.TensorProduct.includeRight (R := R) (A := S) (algebraMap B C b)
      = algebraMap B (TensorProduct R S C) b := by
    intro b
    rw [IsScalarTower.algebraMap_apply B (TensorProduct R S B) (TensorProduct R S C),
        RingHom.algebraMap_toAlgebra (R := B) (S := TensorProduct R S B)]
    show Algebra.TensorProduct.includeRight (algebraMap B C b) =
      (Algebra.TensorProduct.map (AlgHom.id R S) φ) (Algebra.TensorProduct.includeRight b)
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  let gC : C →ₐ[B] TensorProduct R S C :=
    { Algebra.TensorProduct.includeRight (R := R) (A := S) (B := C) with
      commutes' := galg }
  have hcomm : ∀ (x : TensorProduct R S B) (y : C),
      Commute ((Algebra.ofId (TensorProduct R S B) (TensorProduct R S C)) x) (gC y) :=
    fun x y => mul_comm _ _
  let L : TensorProduct B (TensorProduct R S B) C →ₐ[TensorProduct R S B]
      TensorProduct R S C :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) gC hcomm
  have hLsurj : Function.Surjective L := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul s c =>
        refine ⟨(s ⊗ₜ[R] (1:B)) ⊗ₜ[B] c, ?_⟩
        show L ((s ⊗ₜ[R] (1:B)) ⊗ₜ[B] c) = s ⊗ₜ[R] c
        rw [Algebra.TensorProduct.lift_tmul]
        show (algebraMap (TensorProduct R S B) (TensorProduct R S C)) (s ⊗ₜ[R] (1:B)) *
          ((1:S) ⊗ₜ[R] c) = s ⊗ₜ[R] c
        have hsc : (algebraMap (TensorProduct R S B) (TensorProduct R S C)) (s ⊗ₜ[R] (1:B)) =
            s ⊗ₜ[R] (1:C) := by
          rw [RingHom.algebraMap_toAlgebra]
          show (Algebra.TensorProduct.map (AlgHom.id R S) φ) (s ⊗ₜ[R] (1:B)) = s ⊗ₜ[R] (1:C)
          rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
        rw [hsc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    | add x z hx hz =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hz
        exact ⟨a + b, by rw [map_add, ha, hb]⟩
  have hadjBSB : Algebra.adjoin (TensorProduct R S B)
      ((fun x => (1 : TensorProduct R S B) ⊗ₜ[B] x) '' (↑t : Set C)) = ⊤ :=
    Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (R := B) (A := TensorProduct R S B)
      (B := C) (↑t : Set C) ht'
  have himg : L '' ((fun x => (1 : TensorProduct R S B) ⊗ₜ[B] x) '' (↑t : Set C))
      = (fun c => (1 : S) ⊗ₜ[R] c) '' (↑t : Set C) := by
    rw [Set.image_image]
    apply Set.image_congr
    intro c _
    show L ((1 : TensorProduct R S B) ⊗ₜ[B] c) = (1 : S) ⊗ₜ[R] c
    rw [Algebra.TensorProduct.lift_tmul]
    show (algebraMap (TensorProduct R S B) (TensorProduct R S C)) (1 : TensorProduct R S B) *
      ((1:S) ⊗ₜ[R] c) = (1:S) ⊗ₜ[R] c
    rw [map_one, one_mul]
  have hmap := AlgHom.map_adjoin L
    ((fun x => (1 : TensorProduct R S B) ⊗ₜ[B] x) '' (↑t : Set C))
  rw [hadjBSB, Algebra.map_top, himg] at hmap
  have hLrange : L.range = ⊤ := by
    rwa [AlgHom.range_eq_top]
  rw [hLrange] at hmap
  exact hmap.symm

/-- If `φ : B →ₐ[R] C` is of finite type, then for every `R`-algebra `S` the base change
`baseChange S φ : S ⊗_R B → S ⊗_R C` is of finite type. -/
theorem baseChange_finiteType (S : Type*) [CommRing S] [Algebra R S]
    (φ : B →ₐ[R] C) (hfin_type : φ.FiniteType) :
    (baseChange S φ).FiniteType := by
  classical
  let algBC : Algebra B C := φ.toAlgebra
  have : Algebra.FiniteType B C := hfin_type
  obtain ⟨t, ht⟩ := this.out
  let := (baseChange S φ).toRingHom.toAlgebra
  exact ⟨⟨t.image fun c => (1 : S) ⊗ₜ[R] c, by
    rw [Finset.coe_image]; exact adjoin_one_tmul_image_baseChange_eq_top S φ t ht⟩⟩

/-! ### Finiteness descent over a directed colimit -/

/-- If the colimit map `ψL` makes `gT i₀ y` integral over `SL`, then at some later stage
`i ≥ i₀` the element `fT y` is integral over `S i` via `ψ i`. -/
theorem descend_isIntegralElem
    {S T : ι → Type*}
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    {fS : ∀ ⦃i j⦄, i ≤ j → S i →ₐ[R] S j} {fT : ∀ ⦃i j⦄, i ≤ j → T i →ₐ[R] T j}
    {SL : Type*} [CommRing SL] [Algebra R SL]
    {TL : Type*} [CommRing TL] [Algebra R TL]
    {gS : ∀ i, S i →ₐ[R] SL} {gT : ∀ i, T i →ₐ[R] TL}
    (hS : IsDirectedColimit S fS SL gS) (hT : IsDirectedColimit T fT TL gT)
    (ψ : ∀ i, S i →ₐ[R] T i) (ψL : SL →ₐ[R] TL)
    (hψf : ∀ ⦃i j⦄ (hij : i ≤ j) (x : S i), ψ j (fS hij x) = fT hij (ψ i x))
    (hψcomp : ∀ i (x : S i), ψL (gS i x) = gT i (ψ i x))
    (i₀ : ι) (y : T i₀)
    (hy : ψL.toRingHom.IsIntegralElem (gT i₀ y)) :
    ∃ i, ∃ hi : i₀ ≤ i, (ψ i).toRingHom.IsIntegralElem (fT hi y) := by
  classical
  obtain ⟨P, hPmonic, hPeval⟩ := hy
  choose jc ac hac using fun n => hS.jointly_surjective (P.coeff n)
  set stages : Finset ι := insert i₀ (P.support.image jc) with hstages
  obtain ⟨i₁, hi₁⟩ := stages.exists_le
  have hi₀i₁ : i₀ ≤ i₁ := hi₁ i₀ (Finset.mem_insert_self _ _)
  have hjci₁ : ∀ n ∈ P.support, jc n ≤ i₁ := by
    intro n hn
    exact hi₁ (jc n) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem jc hn))
  have hPlift : ∀ n, ∃ s : S i₁, gS i₁ s = P.coeff n := by
    intro n
    by_cases hn : n ∈ P.support
    · refine ⟨fS (hjci₁ n hn) (ac n), ?_⟩
      show gS i₁ (fS (hjci₁ n hn) (ac n)) = P.coeff n
      rw [hS.comp]; exact hac n
    · refine ⟨0, ?_⟩
      show gS i₁ 0 = P.coeff n
      rw [Polynomial.mem_support_iff, not_not] at hn
      rw [hn, map_zero]
  choose b hb using hPlift
  have hb' : ∀ n, (gS i₁ : S i₁ →+* SL) (b n) = P.coeff n := hb
  set d : ℕ := P.natDegree with hd
  set Qlow : Polynomial (S i₁) := ∑ n ∈ Finset.range d, Polynomial.C (b n) * Polynomial.X ^ n
    with hQlow
  set Q : Polynomial (S i₁) := Polynomial.X ^ d + Qlow with hQ
  have hQlowdeg : Qlow.degree < (d : WithBot ℕ) := by
    rw [hQlow]
    apply lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr
    intro n hn
    rw [Finset.mem_range] at hn
    calc (Polynomial.C (b n) * Polynomial.X ^ n).degree
        ≤ (Polynomial.C (b n)).degree + (Polynomial.X ^ n).degree := Polynomial.degree_mul_le _ _
      _ ≤ 0 + n := by
            gcongr
            · exact Polynomial.degree_C_le
            · exact Polynomial.degree_X_pow_le n
      _ < (d : WithBot ℕ) := by
            rw [zero_add]
            exact_mod_cast hn
  have hQmonic : Q.Monic := by
    rw [hQ]
    exact Polynomial.monic_X_pow_add hQlowdeg
  have hQmap : Q.map (gS i₁ : S i₁ →+* SL) = P := by
    rw [hQ, hQlow, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
    rw [hPmonic.as_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, hb' n]
  have hcompS : ∀ k : ι, (↑(gT k) : T k →+* TL).comp (↑(ψ k) : S k →+* T k)
      = (↑ψL : SL →+* TL).comp (↑(gS k) : S k →+* SL) := by
    intro k
    apply RingHom.ext
    intro x
    show gT k (ψ k x) = ψL (gS k x)
    rw [hψcomp]
  set e : T i₁ := Polynomial.eval₂ (ψ i₁).toRingHom (fT hi₀i₁ y) Q with he
  have hge : gT i₁ e = 0 := by
    rw [he]
    show (gT i₁ : T i₁ →+* TL) (Polynomial.eval₂ (ψ i₁).toRingHom (fT hi₀i₁ y) Q) = 0
    rw [Polynomial.hom_eval₂]
    simp only [AlgHom.toRingHom_eq_coe]
    rw [hcompS i₁]
    have hpt : (↑(gT i₁) : T i₁ →+* TL) (fT hi₀i₁ y) = gT i₀ y := hT.comp hi₀i₁ y
    rw [hpt, ← Polynomial.eval₂_map, hQmap]
    exact hPeval
  obtain ⟨i, hi₁i, hfe⟩ := hT.exists_eq_zero e hge
  refine ⟨i, le_trans hi₀i₁ hi₁i, Q.map (fS hi₁i), hQmonic.map _, ?_⟩
  have hcompF : (↑(fT hi₁i) : T i₁ →+* T i).comp (↑(ψ i₁) : S i₁ →+* T i₁)
      = (↑(ψ i) : S i →+* T i).comp (↑(fS hi₁i) : S i₁ →+* S i) := by
    apply RingHom.ext
    intro x
    show fT hi₁i (ψ i₁ x) = ψ i (fS hi₁i x)
    rw [hψf hi₁i x]
  have hfTy : (↑(fT hi₁i) : T i₁ →+* T i) (fT hi₀i₁ y) = fT (le_trans hi₀i₁ hi₁i) y :=
    hT.map_comp hi₀i₁ hi₁i y
  have hfinal : Polynomial.eval₂ (ψ i).toRingHom (fT (le_trans hi₀i₁ hi₁i) y) (Q.map (fS
      hi₁i)) = 0 := by
    rw [Polynomial.eval₂_map]
    simp only [AlgHom.toRingHom_eq_coe]
    rw [← hcompF, ← hfTy]
    have h0 : (fT hi₁i : T i₁ →+* T i) (Polynomial.eval₂ (ψ i₁).toRingHom (fT hi₀i₁ y) Q) = 0 := hfe
    rw [Polynomial.hom_eval₂] at h0
    simp only [AlgHom.toRingHom_eq_coe] at h0
    exact h0
  exact hfinal

omit [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
/-- If `z : T i₁` is integral over `S i₁` via `ψ i₁`, then for any `i ≥ i₁` the image
`fT z : T i` is integral over `S i` via `ψ i`. -/
theorem map_isIntegralElem
    {S T : ι → Type*}
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    {fS : ∀ ⦃i j⦄, i ≤ j → S i →ₐ[R] S j} {fT : ∀ ⦃i j⦄, i ≤ j → T i →ₐ[R] T j}
    (ψ : ∀ i, S i →ₐ[R] T i)
    (hψf : ∀ ⦃i j⦄ (hij : i ≤ j) (x : S i), ψ j (fS hij x) = fT hij (ψ i x))
    {i₁ i : ι} (hi : i₁ ≤ i) (z : T i₁)
    (hz : (ψ i₁).toRingHom.IsIntegralElem z) :
    (ψ i).toRingHom.IsIntegralElem (fT hi z) := by
  obtain ⟨P, hPmonic, hPeval⟩ := hz
  refine ⟨P.map (fS hi : S i₁ →+* S i), hPmonic.map _, ?_⟩
  have hcompF : (↑(fT hi) : T i₁ →+* T i).comp (↑(ψ i₁) : S i₁ →+* T i₁)
      = (↑(ψ i) : S i →+* T i).comp (↑(fS hi) : S i₁ →+* S i) := by
    apply RingHom.ext
    intro x
    show fT hi (ψ i₁ x) = ψ i (fS hi x)
    rw [hψf hi x]
  rw [Polynomial.eval₂_map]
  simp only [AlgHom.toRingHom_eq_coe]
  rw [← hcompF]
  have h0 : (fT hi : T i₁ →+* T i)
      (Polynomial.eval₂ (ψ i₁).toRingHom z P) = 0 := by
    rw [hPeval]; exact map_zero _
  rw [Polynomial.hom_eval₂] at h0
  simp only [AlgHom.toRingHom_eq_coe] at h0
  exact h0

/-- If `ψL` is finite and a finite family `gen` at a base stage `i₀` has `fT`-images
generating `T i` over `S i` at every stage `i ≥ i₀`, then some `ψ i` is integral. -/
theorem exists_stage_isIntegral
    {S T : ι → Type*}
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    {fS : ∀ ⦃i j⦄, i ≤ j → S i →ₐ[R] S j} {fT : ∀ ⦃i j⦄, i ≤ j → T i →ₐ[R] T j}
    {SL : Type*} [CommRing SL] [Algebra R SL]
    {TL : Type*} [CommRing TL] [Algebra R TL]
    {gS : ∀ i, S i →ₐ[R] SL} {gT : ∀ i, T i →ₐ[R] TL}
    (hS : IsDirectedColimit S fS SL gS) (hT : IsDirectedColimit T fT TL gT)
    (ψ : ∀ i, S i →ₐ[R] T i) (ψL : SL →ₐ[R] TL)
    (hψf : ∀ ⦃i j⦄ (hij : i ≤ j) (x : S i), ψ j (fS hij x) = fT hij (ψ i x))
    (hψcomp : ∀ i (x : S i), ψL (gS i x) = gT i (ψ i x))
    (hψLfin : ψL.toRingHom.Finite)
    (i₀ : ι) (gen : Finset (T i₀))
    (hgen : ∀ i (hi : i₀ ≤ i),
        letI := (ψ i).toRingHom.toAlgebra
        Algebra.adjoin (S i) (fT hi '' (↑gen : Set (T i₀))) = ⊤) :
    ∃ i : ι, (ψ i).toRingHom.IsIntegral := by
  classical
  have hLint : ∀ x : TL, ψL.toRingHom.IsIntegralElem x := hψLfin.to_isIntegral
  have hdesc : ∀ x : T i₀, ∃ i, ∃ hi : i₀ ≤ i, (ψ i).toRingHom.IsIntegralElem (fT hi x) := by
    intro x
    exact descend_isIntegralElem hS hT ψ ψL hψf hψcomp i₀ x (hLint (gT i₀ x))
  choose ix hix hintx using hdesc
  set stages : Finset ι := insert i₀ (gen.image ix) with hstages
  obtain ⟨i, hi⟩ := stages.exists_le
  have hi₀i : i₀ ≤ i := hi i₀ (Finset.mem_insert_self _ _)
  refine ⟨i, ?_⟩
  have hgenint : ∀ x ∈ gen, (ψ i).toRingHom.IsIntegralElem (fT hi₀i x) := by
    intro x hx
    have hixi : ix x ≤ i := hi (ix x) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem ix hx))
    have hcomp : fT hixi (fT (hix x) x) = fT hi₀i x := hT.map_comp (hix x) hixi x
    have := map_isIntegralElem ψ hψf hixi (fT (hix x) x) (hintx x)
    rwa [hcomp] at this
  let := (ψ i).toRingHom.toAlgebra
  have htop : Algebra.adjoin (S i) (fT hi₀i '' (↑gen : Set (T i₀))) = ⊤ := hgen i hi₀i
  have hsint : ∀ z ∈ (fT hi₀i '' (↑gen : Set (T i₀))), IsIntegral (S i) z := by
    rintro z ⟨x, hx, rfl⟩
    exact hgenint x (by exact_mod_cast hx)
  have hadj := Algebra.IsIntegral.adjoin hsint
  rw [htop] at hadj
  have hAll : Algebra.IsIntegral (S i) (T i) := by
    rw [Algebra.isIntegral_def]
    intro z
    have hz : z ∈ (⊤ : Subalgebra (S i) (T i)) := Algebra.mem_top
    have hh := (Algebra.isIntegral_def.mp hadj) ⟨z, hz⟩
    simpa using hh.map (⊤ : Subalgebra (S i) (T i)).val
  exact hAll.isIntegral

/-- Suppose `SL = colim S_i` and `TL = colim T_i` are directed colimits of `R`-algebras,
related by a family of `R`-algebra maps `ψ i : S_i →ₐ[R] T_i` compatible with the structure
maps (`ψL ∘ gS i = gT i ∘ ψ i` where `ψL : SL →ₐ TL` is the colimit map). If every `ψ i` is of
finite type, `ψL` is finite, and there is a finite family `gen` at a base stage `i₀` whose
`fT`-images generate `T i` over `S i` at every stage `i ≥ i₀`, then some `ψ i` is finite. -/
theorem finite_descend_of_colimit
    {S T : ι → Type*}
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    {fS : ∀ ⦃i j⦄, i ≤ j → S i →ₐ[R] S j} {fT : ∀ ⦃i j⦄, i ≤ j → T i →ₐ[R] T j}
    {SL : Type*} [CommRing SL] [Algebra R SL]
    {TL : Type*} [CommRing TL] [Algebra R TL]
    {gS : ∀ i, S i →ₐ[R] SL} {gT : ∀ i, T i →ₐ[R] TL}
    (hS : IsDirectedColimit S fS SL gS) (hT : IsDirectedColimit T fT TL gT)
    (ψ : ∀ i, S i →ₐ[R] T i) (ψL : SL →ₐ[R] TL)
    (hψf : ∀ ⦃i j⦄ (hij : i ≤ j) (x : S i), ψ j (fS hij x) = fT hij (ψ i x))
    (hψcomp : ∀ i (x : S i), ψL (gS i x) = gT i (ψ i x))
    (hψtype : ∀ i, (ψ i).FiniteType)
    (hψLfin : ψL.toRingHom.Finite)
    (i₀ : ι) (gen : Finset (T i₀))
    (hgen : ∀ i (hi : i₀ ≤ i),
        letI := (ψ i).toRingHom.toAlgebra
        Algebra.adjoin (S i) (fT hi '' (↑gen : Set (T i₀))) = ⊤) :
    ∃ i : ι, (ψ i).toRingHom.Finite := by
  obtain ⟨i, hint⟩ := exists_stage_isIntegral hS hT ψ ψL hψf hψcomp hψLfin i₀ gen hgen
  refine ⟨i, ?_⟩
  rw [RingHom.finite_iff_isIntegral_and_finiteType]
  exact ⟨hint, hψtype i⟩


/-- Let `L` be the directed colimit of a directed system of `R`-algebras `(A i)`, and let
`φ : B →ₐ[R] C` be a map of `R`-algebras of finite type. If the base change
`id_L ⊗ φ : L ⊗_R B → L ⊗_R C` is a finite ring map, then there is an index `i` such that the
base change `id_{A i} ⊗ φ : A i ⊗_R B → A i ⊗_R C` is a finite ring map. -/
@[stacks 07RG]
theorem finite_baseChange_of_colimit_finite
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {f : ∀ ⦃i j⦄, i ≤ j → A i →ₐ[R] A j}
    {L : Type*} [CommRing L] [Algebra R L]
    {g : ∀ i, A i →ₐ[R] L}
    (φ : B →ₐ[R] C)
    (hcolim : IsDirectedColimit A f L g)
    (hfin_type : φ.FiniteType)
    (hfin : (baseChange L φ).toRingHom.Finite) :
    ∃ i : ι, (baseChange (A i) φ).toRingHom.Finite := by
  have hSB := IsDirectedColimit.tensor_right B hcolim
  have hTC := IsDirectedColimit.tensor_right C hcolim
  have hcompat_f : ∀ ⦃i j⦄ (hij : i ≤ j) (x : TensorProduct R (A i) B),
      baseChange (A j) φ (tensorF B f hij x) = tensorF C f hij (baseChange (A i) φ x) := by
    intro i j hij x
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp [baseChange, tensorF, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => simp [map_add, hx, hy]
  have hcompat_g : ∀ i (x : TensorProduct R (A i) B),
      baseChange L φ (tensorG B g i x) = tensorG C g i (baseChange (A i) φ x) := by
    intro i x
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp [baseChange, tensorG, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => simp [map_add, hx, hy]
  have htype : ∀ i, (baseChange (A i) φ).FiniteType :=
    fun i => baseChange_finiteType (A i) φ hfin_type
  classical
  obtain ⟨i₀, gen, hgen⟩ :
      ∃ (i₀ : ι) (gen : Finset (TensorProduct R (A i₀) C)),
        ∀ i (hi : i₀ ≤ i),
          let := (baseChange (A i) φ).toRingHom.toAlgebra
          Algebra.adjoin (TensorProduct R (A i) B)
            (tensorF C f hi '' (↑gen : Set (TensorProduct R (A i₀) C))) = ⊤ := by
    let algBC0 : Algebra B C := φ.toAlgebra
    have hft : Algebra.FiniteType B C := hfin_type
    obtain ⟨t, ht⟩ := hft.out
    have ht' : @Algebra.adjoin B C _ _ φ.toAlgebra (↑t : Set C) = ⊤ := ht
    refine ⟨Classical.arbitrary ι, t.image (fun c => (1 : A (Classical.arbitrary ι)) ⊗ₜ[R] c),
      fun i hi => ?_⟩
    have hsetimg : tensorF C f hi ''
        (↑(t.image (fun c => (1 : A (Classical.arbitrary ι)) ⊗ₜ[R] c)) :
          Set (TensorProduct R (A (Classical.arbitrary ι)) C))
        = (fun c => (1 : A i) ⊗ₜ[R] c) '' (↑t : Set C) := by
      rw [Finset.coe_image, Set.image_image]
      apply Set.image_congr
      intro c _
      show tensorF C f hi ((1 : A (Classical.arbitrary ι)) ⊗ₜ[R] c) = (1 : A i) ⊗ₜ[R] c
      rw [tensorF, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
    rw [hsetimg]
    exact adjoin_one_tmul_image_baseChange_eq_top (A i) φ t ht'
  exact finite_descend_of_colimit hSB hTC (fun i => baseChange (A i) φ)
    (baseChange L φ) hcompat_f hcompat_g htype hfin i₀ gen hgen

end Stacks.DirectLimit.FiniteDescent

end
