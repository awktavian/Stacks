module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.SetTheory.Cardinal.Order
import StacksCore.Tactic.StacksAttribute

/-!
# Small acyclic complexes in a Grothendieck abelian category

Let `C` be a Grothendieck abelian category. Tag 079K produces a single cardinal
`acyclicComplexSizeBound C`, built from the size of a separator of `C` by iterating the
source's cardinal function, such that

* every nonzero acyclic cochain complex contains a nonzero bounded-above acyclic subcomplex all
  of whose terms have size at most that cardinal, and
* every acyclic cochain complex is an epimorphic image of a coproduct of such small
  bounded-above acyclic complexes.

## Main definitions

* `Stacks.Injectives.acyclicComplexSizeBound`: the uniform cardinal bound of the source.

## Main results

* `Stacks.Injectives.exists_small_boundedAbove_acyclic_subcomplex`: every nonzero acyclic complex
  contains a nonzero small bounded-above acyclic subcomplex.
* `Stacks.Injectives.exists_epi_coproduct_small_boundedAbove_acyclic`: every acyclic complex is an
  epimorphic image of a coproduct of small bounded-above acyclic complexes.

## Implementation notes

The size of an object is the cardinality of its type of subobjects, shrunk to the independent
Grothendieck universe `w` in which `C` has colimits; well-poweredness of a Grothendieck abelian
category is what makes this a cardinal in `w`. A subcomplex is a monomorphism of cochain
complexes, and "bounded above" is stated as vanishing of the terms above some integer rather
than through a boundedness class.

## References

* [Stacks Project, Tag 079K](https://stacks.math.columbia.edu/tag/079K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.Injectives

variable {C : Type u} [Category.{v} C] [Abelian C]
  [IsGrothendieckAbelian.{w} C]

/-- A cardinal which uniformly bounds the sizes of the terms of the small bounded-above acyclic
complexes: the supremum over `n` of the `(n + 1)`-st iterate of `κ ↦ #(Subobject (∐_κ U))` at
`#(Subobject U)`, where `U` is the separator of `C`. -/
@[stacks 079K "the cardinal"]
noncomputable def acyclicComplexSizeBound (C : Type u) [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] : Cardinal.{w} :=
  let U := separator C
  let c : Cardinal.{w} → Cardinal.{w} := fun κ ↦
    Cardinal.mk (Shrink.{w} (Subobject (∐ fun (_ : κ.out) ↦ U)))
  ⨆ n : ℕ, c^[n + 1] (Cardinal.mk (Shrink.{w} (Subobject U)))

-- Sizes are taken in the universe of small colimits, using well-poweredness.
private noncomputable def size (X : C) : Cardinal.{w} :=
  Cardinal.mk (Shrink.{w} (Subobject X))

private noncomputable def cardFn (κ : Cardinal.{w}) : Cardinal.{w} :=
  size (∐ fun (_ : κ.out) ↦ separator C)

private lemma size_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    size X ≤ size Y := by
  apply Cardinal.mk_le_of_injective
    ((equivShrink.{w} (Subobject Y)).injective.comp
      ((Subobject.map_obj_injective f).comp
        (equivShrink.{w} (Subobject X)).symm.injective))

private lemma size_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    size Y ≤ size X := by
  let eX := Abelian.subobjectIsoSubobjectOp X
  let eY := Abelian.subobjectIsoSubobjectOp Y
  exact Cardinal.mk_le_of_injective
    ((equivShrink.{w} (Subobject X)).injective.comp
      (eX.symm.injective.comp ((Subobject.map_obj_injective f.op).comp
        (eY.injective.comp (equivShrink.{w} (Subobject Y)).symm.injective))))

private lemma cardFn_mono : Monotone (cardFn (C := C)) := by
  classical
  intro κ μ h
  obtain ⟨f⟩ : Nonempty (κ.out ↪ μ.out) := (Cardinal.le_def _ _).mp (by simpa using h)
  let g : (∐ fun (_ : κ.out) ↦ separator C) ⟶
      (∐ fun (_ : μ.out) ↦ separator C) :=
    Sigma.desc (fun i ↦ Sigma.ι (fun (_ : μ.out) ↦ separator C) (f i))
  have : IsSplitMono g := by
    refine ⟨⟨Sigma.desc (fun j ↦ if h : ∃ i, f i = j then
      Sigma.ι (fun (_ : κ.out) ↦ separator C) h.choose else 0), ?_⟩⟩
    apply Sigma.hom_ext
    intro i
    simp only [g, Sigma.ι_desc_assoc, Sigma.ι_desc, Category.comp_id]
    have hi : ∃ a, f a = f i := ⟨i, rfl⟩
    rw [dite_eq_left hi]
    congr 1
    exact f.injective hi.choose_spec
  exact size_mono g

private lemma size_le_cardFn : size (separator C) ≤ cardFn (C := C) (size (separator C)) := by
  let i : (size (separator C)).out := Cardinal.outMkEquiv.symm
    ((equivShrink.{w} _) (⊥ : Subobject (separator C)))
  exact size_mono (Sigma.ι (fun (_ : (size (separator C)).out) ↦ separator C) i)

private theorem hasCoproduct_hom (U X : C) :
    HasCoproduct (fun (_ : U ⟶ X) ↦ U) := by
  have : HasCoproduct (fun (_ : Shrink.{w} (U ⟶ X)) ↦ U) := inferInstance
  exact hasCoproduct_of_equiv_of_iso
    (fun (_ : Shrink.{w} (U ⟶ X)) ↦ U) (fun (_ : U ⟶ X) ↦ U)
    (equivShrink _) (fun _ ↦ Iso.refl U)

-- An epimorphism onto `N` restricts to an epimorphism on a subobject of size at most
-- `cardFn (size N)` (Tag 079J).
private theorem exists_small_epi {M N : C} (π : M ⟶ N) [Epi π] :
    ∃ S : Subobject M, Epi (S.arrow ≫ π) ∧ size (S : C) ≤ cardFn (C := C) (size N) := by
  classical
  let U := separator C
  let I := Shrink.{w} (Subobject N)
  have (X : C) : HasCoproduct (fun (_ : U ⟶ X) ↦ U) := hasCoproduct_hom U X
  let e : (∐ fun (_ : U ⟶ M) ↦ U) ⟶ M := Sigma.desc (fun f ↦ f)
  have : Epi e := (isSeparator_iff_epi U).1 (isSeparator_separator C) M
  have hchoose : ∀ S : Subobject N, S ≠ ⊤ →
      ∃ f : U ⟶ M, ¬ S.Factors (f ≫ π) := by
    intro S hS
    by_contra h
    push Not at h
    let l : (∐ fun (_ : U ⟶ M) ↦ U) ⟶ (S : C) :=
      Sigma.desc (fun f ↦ S.factorThru (f ≫ π) (h f))
    have hl : e ≫ π = l ≫ S.arrow := by
      apply Sigma.hom_ext
      intro f
      simp [e, l]
    have hE : Epi (e ≫ π) := inferInstance
    rw [hl] at hE
    have : Epi S.arrow := epi_of_epi l S.arrow
    have : IsIso S.arrow := isIso_of_mono_of_epi _
    exact hS ((Subobject.isIso_arrow_iff_eq_top S).1 this)
  let φ : I → (U ⟶ M) := fun i ↦
    if hS : (equivShrink.{w} (Subobject N)).symm i = ⊤ then 0
    else (hchoose _ hS).choose
  have hφ (S : Subobject N) (hS : S ≠ ⊤) :
      ¬ S.Factors (φ ((equivShrink.{w} _) S) ≫ π) := by
    simpa only [φ, Equiv.symm_apply_apply, dite_eq_right hS] using (hchoose S hS).choose_spec
  let q : (∐ fun (_ : I) ↦ U) ⟶ M := Sigma.desc φ
  have hqπ : Epi (q ≫ π) := by
    have htop : imageSubobject (q ≫ π) = ⊤ := by
      by_contra htop
      let S := imageSubobject (q ≫ π)
      apply hφ S htop
      have hs : S.Factors (q ≫ π) := by
        dsimp [S]
        simpa using imageSubobject_factors_comp_self (q ≫ π)
          (𝟙 (∐ fun (_ : I) ↦ U))
      obtain ⟨k, hk⟩ := hs
      refine ⟨Sigma.ι (fun (_ : I) ↦ U) ((equivShrink.{w} _) S) ≫ k, ?_⟩
      rw [Category.assoc, hk, ← Category.assoc, Sigma.ι_desc]
    have : IsIso (imageSubobject (q ≫ π)).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2 htop
    rw [← imageSubobject_arrow_comp (q ≫ π)]
    infer_instance
  refine ⟨imageSubobject q, ?_, ?_⟩
  · have hfac : q ≫ π = factorThruImageSubobject q ≫
        ((imageSubobject q).arrow ≫ π) := by
      rw [← Category.assoc, imageSubobject_arrow_comp]
    rw [hfac] at hqπ
    exact epi_of_epi (factorThruImageSubobject q) _
  · refine (size_epi (factorThruImageSubobject q)).trans ?_
    let α : (size N).out ≃ I := Cardinal.outMkEquiv
    exact size_mono ((Sigma.reindex α (fun (_ : I) ↦ U)).symm.hom)

private lemma exists_small_extension (T : ShortComplex C) (hT : T.Exact)
    {Y Z : C} (d : Y ⟶ Z) (i : Y ⟶ T.X₂) (j : Z ⟶ T.X₃) [Mono i] [Mono j]
    (comm : i ≫ T.g = d ≫ j) :
    ∃ (X : C) (δ : X ⟶ Y) (a : X ⟶ T.X₁) (hδ : δ ≫ d = 0),
      Mono a ∧ a ≫ T.f = δ ≫ i ∧ (ShortComplex.mk δ d hδ).Exact ∧
      size X ≤ cardFn (C := C) (size Y) := by
  let p := kernel.lift T.g T.f T.zero
  have : Epi p := hT.epi_kernelLift
  let q := kernel.lift T.g (kernel.ι d ≫ i) (by
    rw [Category.assoc, comm, ← Category.assoc, kernel.condition, zero_comp])
  have : Mono q := inferInstance
  let e := pullback.snd p q
  let m := pullback.fst p q
  have : Epi e := inferInstance
  have : Mono m := inferInstance
  obtain ⟨S, hS, hsize⟩ := exists_small_epi e
  let δ := S.arrow ≫ e ≫ kernel.ι d
  let a := S.arrow ≫ m
  have hδ : δ ≫ d = 0 := by simp [δ]
  refine ⟨(S : C), δ, a, hδ, inferInstance, ?_, ?_, ?_⟩
  · have h := (pullback.condition (f := p) (g := q)) =≫ kernel.ι T.g
    dsimp [p, q] at h
    simpa [a, δ, m, e] using congrArg (S.arrow ≫ ·) h
  · apply (ShortComplex.exact_iff_epi_kernel_lift _).2
    have h : kernel.lift d δ hδ = S.arrow ≫ e := by
      apply (cancel_mono (kernel.ι d)).1
      simp [δ]
    show Epi (kernel.lift d δ hδ)
    rw [h]
    exact hS
  · exact hsize.trans (cardFn_mono (size_mono (kernel.ι d)))

-- Two adjacent terms of the subcomplex, with their inclusions and an iterative size bound.
private structure Stage (K : ChainComplex C ℕ) (n : ℕ) where
  X₀ : C
  X₁ : C
  d : X₁ ⟶ X₀
  i₀ : X₀ ⟶ K.X n
  i₁ : X₁ ⟶ K.X (n + 1)
  [mono_i₀ : Mono i₀]
  [mono_i₁ : Mono i₁]
  comm : i₁ ≫ K.d (n + 1) n = d ≫ i₀
  bound : size X₁ ≤ (cardFn (C := C))^[n + 1] (size (separator C))

attribute [instance] Stage.mono_i₀ Stage.mono_i₁

private structure Extension {K : ChainComplex C ℕ} {n : ℕ} (S : Stage K n) where
  X : C
  d : X ⟶ S.X₁
  i : X ⟶ K.X (n + 2)
  [mono_i : Mono i]
  comm : i ≫ K.d (n + 2) (n + 1) = d ≫ S.i₁
  zero : d ≫ S.d = 0
  exact : (ShortComplex.mk d S.d zero).Exact
  bound : size X ≤ (cardFn (C := C))^[n + 1 + 1] (size (separator C))

attribute [instance] Extension.mono_i

private noncomputable def extendStage {K : ChainComplex C ℕ} (hK : K.Acyclic)
    {n : ℕ} (S : Stage K n) : Extension S := Classical.choice (by
  have hT : (K.sc' (n + 2) (n + 1) n).Exact :=
    (K.exactAt_iff' (n + 2) (n + 1) n (by simp) (by simp)).1 (hK (n + 1))
  obtain ⟨X, d, i, hz, hm, hc, he, hb⟩ :=
    @exists_small_extension C _ _ _ (K.sc' (n + 2) (n + 1) n) hT
      S.X₁ S.X₀ S.d S.i₁ S.i₀ S.mono_i₁ S.mono_i₀ S.comm
  refine ⟨{
    X := X
    d := d
    i := i
    mono_i := hm
    comm := hc
    zero := hz
    exact := he
    bound := ?_ }⟩
  exact hb.trans (by
    simpa only [Function.iterate_succ_apply'] using cardFn_mono S.bound))

private noncomputable abbrev nextStage {K : ChainComplex C ℕ} (hK : K.Acyclic)
    {n : ℕ} (S : Stage K n) : Stage K (n + 1) where
  X₀ := S.X₁
  X₁ := (extendStage hK S).X
  d := (extendStage hK S).d
  i₀ := S.i₁
  i₁ := (extendStage hK S).i
  comm := (extendStage hK S).comm
  bound := (extendStage hK S).bound

private noncomputable abbrev stages {K : ChainComplex C ℕ} (hK : K.Acyclic)
    (S : Stage K 0) : (n : ℕ) → Stage K n
  | 0 => S
  | n + 1 => nextStage hK (stages hK S n)

private noncomputable def smallChain {K : ChainComplex C ℕ} (hK : K.Acyclic)
    (S : Stage K 0) : ChainComplex C ℕ :=
  ChainComplex.of (fun n ↦ (stages hK S n).X₀) (fun n ↦ (stages hK S n).d)
    (fun n ↦ (extendStage hK (stages hK S n)).zero)

private noncomputable def smallChainι {K : ChainComplex C ℕ} (hK : K.Acyclic)
    (S : Stage K 0) : smallChain hK S ⟶ K :=
  ChainComplex.ofHom (fun n ↦ (stages hK S n).i₀) (fun n ↦ by
    change (stages hK S n).i₁ ≫ _ =
      ChainComplex.of.d (fun m ↦ (stages hK S m).X₀)
        (fun m ↦ (stages hK S m).d) (n + 1) n ≫ _
    rw [ChainComplex.of_d]
    exact (stages hK S n).comm)

private lemma smallChainι_mono {K : ChainComplex C ℕ} (hK : K.Acyclic)
    (S : Stage K 0) : Mono (smallChainι hK S) :=
  HomologicalComplex.mono_of_mono_f (smallChainι hK S) (fun n ↦ (stages hK S n).mono_i₀)

private lemma smallChain_d {K : ChainComplex C ℕ} (hK : K.Acyclic)
    (S : Stage K 0) (n : ℕ) :
    (smallChain hK S).d (n + 1) n = (stages hK S n).d :=
  ChainComplex.of_d (fun n ↦ (stages hK S n).X₀) (fun n ↦ (stages hK S n).d) n

private lemma smallChain_acyclic {K : ChainComplex C ℕ} (hK : K.Acyclic)
    (S : Stage K 0) [Epi S.d] : (smallChain hK S).Acyclic := by
  intro n
  cases n with
  | zero =>
    apply ((smallChain hK S).exactAt_iff' 1 0 0 (by simp) (by simp)).2
    apply (ShortComplex.exact_iff_epi _ (by simp [HomologicalComplex.sc'])).2
    show Epi ((smallChain hK S).d (0 + 1) 0)
    simpa only [smallChain_d] using (inferInstanceAs (Epi S.d))
  | succ n =>
    apply ((smallChain hK S).exactAt_iff' (n + 2) (n + 1) n (by simp) (by simp)).2
    show (ShortComplex.mk ((smallChain hK S).d ((n + 1) + 1) (n + 1))
      ((smallChain hK S).d (n + 1) n) _).Exact
    simp only [smallChain_d]
    exact (extendStage hK (stages hK S n)).exact

private noncomputable def initialStage (K : ChainComplex C ℕ)
    (ψ : separator C ⟶ K.X 1) : Stage K 0 where
  X₀ := image (ψ ≫ K.d 1 0)
  X₁ := image ψ
  d := image.map (Arrow.homMk' (f := ψ) (g := ψ ≫ K.d 1 0) (𝟙 _) (K.d 1 0) (by simp))
  i₀ := image.ι (ψ ≫ K.d 1 0)
  i₁ := image.ι ψ
  comm := by
    simpa using (image.map_ι (Arrow.homMk' (f := ψ) (g := ψ ≫ K.d 1 0)
      (𝟙 _) (K.d 1 0) (by simp))).symm
  bound := (size_epi (factorThruImage ψ)).trans (by
    simpa using (size_le_cardFn (C := C)))

private lemma initialStage_epi (K : ChainComplex C ℕ) (ψ : separator C ⟶ K.X 1) :
    Epi (initialStage K ψ).d := by
  show Epi (image.map (Arrow.homMk' (f := ψ) (g := ψ ≫ K.d 1 0)
    (𝟙 _) (K.d 1 0) (by simp)))
  let sq := Arrow.homMk' (f := ψ) (g := ψ ≫ K.d 1 0) (𝟙 _) (K.d 1 0) (by simp)
  have h : factorThruImage ψ ≫ image.map sq = factorThruImage (ψ ≫ K.d 1 0) := by
    have h := image.factor_map sq
    change factorThruImage ψ ≫ image.map sq =
      (𝟙 (separator C)) ≫ factorThruImage (ψ ≫ K.d 1 0) at h
    simpa only [Category.id_comp] using h
  have : Epi (factorThruImage ψ ≫ image.map sq) := h.symm ▸ inferInstance
  exact epi_of_epi (factorThruImage ψ) (image.map sq)

private lemma iterate_le_bound (n : ℕ) :
    (cardFn (C := C))^[n + 1] (size (separator C)) ≤ acyclicComplexSizeBound C :=
  le_ciSup Cardinal.bddAbove_of_small n

private lemma generator_size_le_bound : size (separator C) ≤ acyclicComplexSizeBound C :=
  size_le_cardFn.trans (by simpa using (iterate_le_bound (C := C) 0))

private lemma zero_size_le_bound {X : C} (hX : IsZero X) :
    size X ≤ acyclicComplexSizeBound C := by
  have : Mono (0 : X ⟶ separator C) := hX.mono _
  exact (size_mono (0 : X ⟶ separator C)).trans generator_size_le_bound

private lemma exists_small_chain (K : ChainComplex C ℕ) (hK : K.Acyclic)
    (ψ : separator C ⟶ K.X 1) :
    ∃ (L : ChainComplex C ℕ) (f : L ⟶ K) (g : separator C ⟶ L.X 1),
      Mono f ∧ L.Acyclic ∧ g ≫ f.f 1 = ψ ∧
      ∀ n : ℕ, size (L.X n) ≤ acyclicComplexSizeBound C := by
  let S := initialStage K ψ
  have : Epi S.d := initialStage_epi K ψ
  refine ⟨smallChain hK S, smallChainι hK S, factorThruImage ψ,
    smallChainι_mono hK S, smallChain_acyclic hK S, ?_, ?_⟩
  · exact image.fac ψ
  · intro n
    cases n with
    | zero =>
      exact (size_epi (factorThruImage (ψ ≫ K.d 1 0))).trans generator_size_le_bound
    | succ n => exact (stages hK S n).bound.trans (iterate_le_bound n)

omit [IsGrothendieckAbelian.{w} C] in
private lemma isIso_ιTruncLE_f (M : CochainComplex C ℤ) (n : ℤ) :
    IsIso ((M.ιTruncLE (n + 1)).f n) := by
  show IsIso ((((HomologicalComplex.op M).πTruncGE
    (ComplexShape.embeddingUpIntLE (n + 1)).op).f n).unop)
  have hj : (ComplexShape.embeddingUpIntLE (n + 1)).op.f 1 = n := by simp
  have : IsIso (((HomologicalComplex.op M).πTruncGE
      (ComplexShape.embeddingUpIntLE (n + 1)).op).f n) := by
    dsimp only [HomologicalComplex.πTruncGE]
    refine ((ComplexShape.embeddingUpIntLE (n + 1)).op.isIso_liftExtend_f_iff
      _ ((HomologicalComplex.op M).restrictionToTruncGE'_hasLift _) hj).2 ?_
    apply HomologicalComplex.isIso_restrictionToTruncGE'
    simp only [ComplexShape.Embedding.op_boundaryGE_iff,
      ComplexShape.boundaryLE_embeddingUpIntLE_iff]
    decide
  infer_instance

private lemma exists_small_factorization (M : CochainComplex C ℤ) (hM : M.Acyclic)
    (n : ℤ) (ψ : separator C ⟶ M.X n) :
    ∃ (N : CochainComplex C ℤ) (f : N ⟶ M) (g : separator C ⟶ N.X n),
      Mono f ∧ N.Acyclic ∧ g ≫ f.f n = ψ ∧
      (∃ a : ℤ, ∀ i : ℤ, a < i → IsZero (N.X i)) ∧
      ∀ i : ℤ, size (N.X i) ≤ acyclicComplexSizeBound C := by
  classical
  let e := ComplexShape.embeddingUpIntLE (n + 1)
  let K := HomologicalComplex.truncLE' M e
  have hn : e.f 1 = n := by simp [e]
  have hK : K.Acyclic := fun i => (K.extend_exactAt_iff e (rfl : e.f i = e.f i)).1
    (((HomologicalComplex.Acyclic.truncLE hM e) (e.f i)).of_iso (M.truncLEIso e))
  let t : K.extend e ⟶ M := (M.truncLEIso e).inv ≫ HomologicalComplex.ιTruncLE M e
  have : Mono t := by dsimp [t]; infer_instance
  have : IsIso (t.f n) := by
    have : IsIso ((HomologicalComplex.ιTruncLE M e).f n) := isIso_ιTruncLE_f M n
    show IsIso ((M.truncLEIso e).inv.f n ≫ (HomologicalComplex.ιTruncLE M e).f n)
    infer_instance
  let r : K.X 1 ⟶ M.X n := (K.extendXIso e hn).inv ≫ t.f n
  have : IsIso r := by dsimp [r]; infer_instance
  obtain ⟨L, f, g, hf, hL, hg, hb⟩ := exists_small_chain K hK (ψ ≫ inv r)
  let F : L.extend e ⟶ M := HomologicalComplex.extendMap f e ≫ t
  let G : separator C ⟶ (L.extend e).X n := g ≫ (L.extendXIso e hn).inv
  have hfm : Mono (HomologicalComplex.extendMap f e) := by
    apply HomologicalComplex.mono_of_mono_f
    intro i
    by_cases hi : ∃ j, e.f j = i
    · obtain ⟨j, hj⟩ := hi
      rw [HomologicalComplex.extendMap_f f e hj]
      infer_instance
    · exact (L.isZero_extend_X e i (by simpa using hi)).mono _
  refine ⟨L.extend e, F, G, inferInstance, ?_, ?_, ⟨n + 1, ?_⟩, ?_⟩
  · intro i
    by_cases hi : ∃ j, e.f j = i
    · obtain ⟨j, hj⟩ := hi
      exact (L.extend_exactAt_iff e hj).2 (hL j)
    · exact L.extend_exactAt e i (by simpa using hi)
  · show (g ≫ (L.extendXIso e hn).inv) ≫
      ((HomologicalComplex.extendMap f e).f n ≫ t.f n) = ψ
    rw [HomologicalComplex.extendMap_f f e hn]
    calc
      _ = (g ≫ f.f 1) ≫ r := by simp [r, Category.assoc]
      _ = ψ := by rw [hg]; simp
  · exact fun i hi =>
      L.isZero_extend_X e i ((ComplexShape.notMem_range_embeddingUpIntLE_iff (n + 1) i).2 hi)
  · intro i
    by_cases hi : ∃ j, e.f j = i
    · obtain ⟨j, hj⟩ := hi
      exact (size_mono (L.extendXIso e hj).hom).trans (hb j)
    · exact zero_size_le_bound (L.isZero_extend_X e i (by simpa using hi))

omit [IsGrothendieckAbelian.{w} C] in
private lemma exists_not_isZero_X (M : CochainComplex C ℤ) (hM₀ : ¬ IsZero M) :
    ∃ n : ℤ, ¬ IsZero (M.X n) := by
  by_contra! h
  apply hM₀
  rw [IsZero.iff_id_eq_zero]
  ext n
  exact (h n).eq_of_src _ _

/-- Every nonzero acyclic complex contains a nonzero bounded-above acyclic subcomplex
whose terms have uniformly bounded size. -/
@[stacks 079K "part (1)"]
theorem exists_small_boundedAbove_acyclic_subcomplex
    (M : CochainComplex C ℤ) (hM : M.Acyclic) (hM₀ : ¬ IsZero M) :
    ∃ (N : CochainComplex C ℤ) (f : N ⟶ M),
      Mono f ∧
      ¬ IsZero N ∧
      N.Acyclic ∧
      (∃ a : ℤ, ∀ n : ℤ, a < n → IsZero (N.X n)) ∧
      ∀ n : ℤ, Cardinal.mk (Shrink.{w} (Subobject (N.X n))) ≤
        acyclicComplexSizeBound (C := C) := by
  obtain ⟨n, hn⟩ := exists_not_isZero_X M hM₀
  obtain ⟨ψ, hψ⟩ : ∃ ψ : separator C ⟶ M.X n, ψ ≠ 0 := by
    by_contra! h
    apply hn
    rw [IsZero.iff_id_eq_zero]
    apply (isSeparator_separator C).def
    intro ψ
    simp [h ψ]
  obtain ⟨N, f, g, hf, hN, hg, hba, hb⟩ := exists_small_factorization M hM n ψ
  refine ⟨N, f, hf, ?_, hN, hba, hb⟩
  intro hz
  apply hψ
  have hg₀ : g = 0 :=
    (Functor.map_isZero (HomologicalComplex.eval C (.up ℤ) n) hz).eq_of_tgt _ _
  simpa [hg₀] using hg.symm

/-- Every acyclic complex is an epimorphic image of a coproduct of bounded-above
acyclic complexes whose terms have uniformly bounded size. -/
@[stacks 079K "part (2)"]
theorem exists_epi_coproduct_small_boundedAbove_acyclic
    (M : CochainComplex C ℤ) (hM : M.Acyclic) :
    ∃ (I : Type w) (N : I → CochainComplex C ℤ)
      (f : (∐ fun i ↦ N i) ⟶ M),
      Epi f ∧
      ∀ i : I,
        (N i).Acyclic ∧
        (∃ a : ℤ, ∀ n : ℤ, a < n → IsZero ((N i).X n)) ∧
        ∀ n : ℤ,
          Cardinal.mk (Shrink.{w} (Subobject ((N i).X n))) ≤
            acyclicComplexSizeBound (C := C) := by
  classical
  let I := Σ n : ULift.{w} ℤ, Shrink.{w} (separator C ⟶ M.X n.down)
  let ψ (i : I) : separator C ⟶ M.X i.1.down := (equivShrink _).symm i.2
  choose N f g hf hN hg hba hb using
    (fun i : I ↦ exists_small_factorization M hM i.1.down (ψ i))
  let F : (∐ N) ⟶ M := Sigma.desc f
  refine ⟨I, N, F, ?_, fun i ↦ ⟨hN i, hba i, hb i⟩⟩
  apply HomologicalComplex.epi_of_epi_f
  intro n
  constructor
  intro Y a b hab
  apply (isSeparator_separator C).def
  intro φ
  let i : I := ⟨⟨n⟩, (equivShrink _) φ⟩
  have hi : ψ i = φ := by simp [ψ, i]
  have hfac : (g i ≫ (Sigma.ι N i).f n) ≫ F.f n = φ := by
    rw [Category.assoc, ← HomologicalComplex.comp_f]
    show g i ≫ (Sigma.ι N i ≫ Sigma.desc f).f n = φ
    rw [Sigma.ι_desc]
    exact (hg i).trans hi
  rw [← hfac, Category.assoc, hab, Category.assoc]
  simp only [Category.assoc]

end Stacks.Injectives
