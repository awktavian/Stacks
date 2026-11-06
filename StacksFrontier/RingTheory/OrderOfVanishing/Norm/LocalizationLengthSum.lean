module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Lattice.Defs
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm.OrdIntBasics
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm.CokerLenDevissage
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm.BaseChangeDetNorm


@[expose] public section


open Ring

/-
## Sub-lemma (Step D = Stacks Tag 02M0, Lemma 10.52.12): localization decomposition of length.

For a nonzero `b : B`, the residue-degree-weighted sum of the local orders equals the `A`-length
of `B / bB`:

    Σ_v [κ(m_v):κ(m_A)] · ord_{B_v}(b) = length_A (B / bB).

INFORMAL ARGUMENT. Two ingredients:
(a) For each maximal ideal `m_v` of `B`, `ord_{B_v}(b) = length_{B_v}((B/bB)_{m_v})` by definition
    of `ord` (Definition 1) applied to the 1-dim Noetherian local domain `B_v = B_{m_v}` with
    fraction field `L`: indeed `ord_{B_v}(algebraMap B_v L b) = length_{B_v}(B_v / b·B_v)`
    (`ordInt_algebraMap` for `R = B_v`), and `(B/bB)_{m_v} ≅ B_v / b·B_v`.
(b) Change of rings for length along the residue field: if `M` is a finite-length module over the
    local ring `B_v` with residue field `κ(m_v)`, then `length_A(M) = [κ(m_v):κ(m_A)] ·
    length_{B_v}(M)` — because `A → B_v` is local with residue extension `κ(m_A) → κ(m_v)` of
    degree `[κ(m_v):κ(m_A)] = inertiaDeg`, and length multiplies by the residue degree under such
    a finite local extension (Jordan–Hölder: each `B_v`-composition factor `κ(m_v)` has
    `A`-length `[κ(m_v):κ(m_A)]`). Applied to `M = (B/bB)_{m_v}`:
        length_A((B/bB)_{m_v}) = [κ(m_v):κ(m_A)] · length_{B_v}((B/bB)_{m_v}).
(c) Tag 02M0 (Lemma 10.52.12): a finite-length module over the semilocal `B` is the (finite)
    direct sum of its localizations at the maximal ideals, so length is additive:
        length_A (B/bB) = Σ_v length_A((B/bB)_{m_v}).
    (`B/bB` is Artinian — finite `A`-length, killed by a power of `m_A` — hence its support is the
     finite set of maximal ideals of `B`, and `M ≅ ⊕_v M_{m_v}`.)
Combining (a)+(b)+(c):
    length_A(B/bB) = Σ_v length_A((B/bB)_{m_v}) = Σ_v [κ(m_v):κ(m_A)] · length_{B_v}((B/bB)_{m_v})
                   = Σ_v [κ(m_v):κ(m_A)] · ord_{B_v}(b).
This is a substantial, separable lemma (its own subtree); the chief Mathlib gap is the
finite-direct-sum-of-localizations decomposition (02M0) and the residue-degree length change (b).
-/

/-- **Ingredient (a)** (localization-quotient iso). For each maximal ideal `m_v` of `B`, the
localization of `B/bB` at `m_v` is `B_v`-isomorphic to `B_v / b·B_v`, so they have the same
`B_v`-length. Proof route: localization is exact, so applying `LocalizedModule v.primeCompl (-)`
to the cokernel presentation `B --·b--> B → B/bB → 0` yields `B_v --·b--> B_v → (B/bB)_{m_v} → 0`,
i.e. `(B/bB)_{m_v} ≅ B_v / (algebraMap B B_v b)·B_v`. Mathlib hooks to explore:
`LocalizedModule`/`IsLocalizedModule` flatness, `Localization.quotientEquiv`-style isos, or build
the
`B_v`-linear equiv by hand from `IsLocalizedModule.mk'`/`LinearEquiv` on the cokernel. -/
theorem length_localizedModule_quot_eq
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (v : MaximalSpectrum B) (b : B) :
    Module.length (Localization.AtPrime v.asIdeal)
        (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b})) =
      Module.length (Localization.AtPrime v.asIdeal)
        ((Localization.AtPrime v.asIdeal) ⧸
          Ideal.span {algebraMap B (Localization.AtPrime v.asIdeal) b}) := by
  set p := v.asIdeal.primeCompl with hp
  set Bv := Localization.AtPrime v.asIdeal with hBv
  have hsub : Submodule.localized' Bv p (Algebra.linearMap B Bv) (Ideal.span {b})
      = Ideal.span {algebraMap B Bv b} := by
    rw [Submodule.localized'_span]
    simp [Algebra.linearMap_apply, Ideal.span]
  have e : LocalizedModule p (B ⧸ Ideal.span {b}) ≃ₗ[B]
      (Bv ⧸ Submodule.localized' Bv p (Algebra.linearMap B Bv) (Ideal.span {b})) :=
    IsLocalizedModule.iso p
      (Submodule.toLocalizedQuotient' Bv p (Algebra.linearMap B Bv) (Ideal.span {b}))
  have e' : LocalizedModule p (B ⧸ Ideal.span {b}) ≃ₗ[Bv]
      (Bv ⧸ Submodule.localized' Bv p (Algebra.linearMap B Bv) (Ideal.span {b})) :=
    LinearEquiv.extendScalarsOfIsLocalization p Bv e
  rw [LinearEquiv.length_eq e', hsub]

-- `Ideal.inertiaDeg'` has no semantics-preserving replacement here: `Ideal.inertiaDeg` is a
-- different definition (residue fields of localizations), equal only under `LiesOver` plus
-- maximality, so migrating would change this statement.
set_option linter.deprecated false in
/-- **Ingredient (b)** (residue-degree change of rings for length). For a module `N` over
`B_v = Localization.AtPrime m_v` which is also an `A`-module compatibly (`IsScalarTower`), the
`A`-length is `[κ(m_v):κ(m_A)]` times the `B_v`-length. Proof route (Jordan–Hölder): the residue
field `κ(m_v) = B_v/m_vB_v ≅ B/m_v` is a finite extension of `κ(m_A) = A/m_A` of degree
`inertiaDeg(m_A, m_v) = finrank_{κ(m_A)}(B/m_v)`; the unique simple `B_v`-module `κ(m_v)` has
`A`-length `= finrank_{κ(m_A)}(κ(m_v))` (length of a vector space = `finrank`, since `m_A` kills
`κ(m_v)`); then `length_A` is additive (`Module.length_eq_add_of_exact`) along a `B_v`-composition
series of `N`, each factor contributing `inertiaDeg`. Likely needs its own subtree (composition
series / `Module.length` induction). NOTE: the statement is unconditional in `N`; for `N = ⊤`
(length
`⊤`) both sides are `⊤` (if `inertiaDeg ≠ 0`) — the genuine content is the finite-length case. -/
@[sga "2 IV 5.2" "special case"]
theorem length_restrictScalars_eq_inertiaDeg_mul
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (v : MaximalSpectrum B)
    (N : Type*) [AddCommGroup N]
    [Module (Localization.AtPrime v.asIdeal) N] [Module A N]
    [IsScalarTower A (Localization.AtPrime v.asIdeal) N]
    (hN : Module.length (Localization.AtPrime v.asIdeal) N ≠ ⊤) :
    Module.length A N =
      (Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) v.asIdeal : ℕ∞) *
        Module.length (Localization.AtPrime v.asIdeal) N := by
  -- finrank_{κ(m_A)}(B/m_v))
  set Bv := Localization.AtPrime v.asIdeal with hBv
  have hvmax : v.asIdeal.IsMaximal := v.isMaximal
  have : IsLocalRing Bv := Localization.AtPrime.isLocalRing v.asIdeal
  -- generic length-over-restriction lemma: if `A → K` is a surjective ring map and `M` is a
  -- `K`-module (compatible `A`-action), then the `A`- and `K`-submodule lattices coincide,
  -- hence the lengths agree.
  have len_eq_aux : ∀ (A K : Type _) [CommRing A] [CommRing K] [Algebra A K]
      (_ : Function.Surjective (algebraMap A K))
      (M : Type _) [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower A K M],
      Module.length A M = Module.length K M := by
    intro A K _ _ _ hsurj M _ _ _ _
    let toK : Submodule A M → Submodule K M := fun N =>
    { carrier := N, add_mem' := N.add_mem, zero_mem' := N.zero_mem
      smul_mem' := fun k m hm => by
        obtain ⟨a, rfl⟩ := hsurj k; rw [algebraMap_smul]; exact N.smul_mem a hm }
    let e : Submodule K M ≃o Submodule A M :=
    { toFun := fun N => N.restrictScalars A, invFun := toK
      left_inv := fun N => by ext x; simp [toK]
      right_inv := fun N => by ext x; simp [toK]
      map_rel_iff' := by intro N₁ N₂; exact Iff.rfl }
    unfold Module.length; congr 1; exact (Order.krullDim_eq_of_orderIso e).symm
  -- key induction (Jordan–Hölder): for finite-length `Bv`-modules `M`,
  -- `length_A M = length_A(κ(m_v)) * length_{Bv} M`.
  have key : ∀ (M : Type _) [AddCommGroup M] [Module Bv M] (_ : IsFiniteLength Bv M)
      [Module A M] [IsScalarTower A Bv M],
      Module.length A M
        = Module.length A (Bv ⧸ IsLocalRing.maximalIdeal Bv) * Module.length Bv M := by
    set c := Module.length A (Bv ⧸ IsLocalRing.maximalIdeal Bv) with hc
    -- `A`-length is additive along the canonical SES `0 → N → M → M/N → 0`.
    have addA : ∀ (M : Type _) [AddCommGroup M] [Module Bv M] [Module A M] [IsScalarTower A Bv M]
        (N : Submodule Bv M),
        Module.length A M = Module.length A N + Module.length A (M ⧸ N) := by
      intro M _ _ _ _ N
      have hex : Function.Exact (N.subtype) (N.mkQ) := by
        rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype]
      exact Module.length_eq_add_of_exact
        ((N.subtype).restrictScalars A) ((N.mkQ).restrictScalars A)
        N.subtype_injective N.mkQ_surjective hex
    -- a simple `Bv`-module is `≅ κ(m_v)` (since `Bv` is local), so has `A`-length `c`.
    have simpleA : ∀ (Q : Type _) [AddCommGroup Q] [Module Bv Q] [Module A Q] [IsScalarTower A Bv
        Q],
        IsSimpleModule Bv Q → Module.length A Q = c := by
      intro Q _ _ _ _ hQ
      obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hQ
      have hImax : I = IsLocalRing.maximalIdeal Bv := IsLocalRing.eq_maximalIdeal hI
      subst hImax
      exact (e.restrictScalars A).length_eq
    intro M _ _ h
    induction h with
    | @of_subsingleton M _ _ _ =>
        intro instA _
        have h1 : Module.length A M = 0 := Module.length_eq_zero_iff.mpr ‹_›
        have h2 : Module.length Bv M = 0 := Module.length_eq_zero_iff.mpr ‹_›
        rw [h1, h2, mul_zero]
    | @of_simple_quotient M _ _ N hsimp a ih =>
        intro instA _
        have hAadd := addA M N
        have hBadd : Module.length Bv M = Module.length Bv N + Module.length Bv (M ⧸ N) := by
          have hex : Function.Exact (N.subtype) (N.mkQ) := by
            rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype]
          exact Module.length_eq_add_of_exact N.subtype N.mkQ
            N.subtype_injective N.mkQ_surjective hex
        have hQlen : Module.length A (M ⧸ N) = c := simpleA (M ⧸ N) hsimp
        have hQBlen : Module.length Bv (M ⧸ N) = 1 := Module.length_eq_one_iff.mpr hsimp
        have hIH : Module.length A N = c * Module.length Bv N := ih
        rw [hAadd, hIH, hQlen, hBadd, hQBlen, mul_add, mul_one]
  -- the per-step constant equals the residue degree `inertiaDeg`.
  have hconst : Module.length A (Bv ⧸ IsLocalRing.maximalIdeal Bv)
      = (Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) v.asIdeal : ℕ∞) := by
    have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
    have hlo : v.asIdeal.LiesOver (IsLocalRing.maximalIdeal A) :=
      have hmax : (Ideal.comap (algebraMap A B) v.asIdeal).IsMaximal :=
        Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal
      ⟨(IsLocalRing.eq_maximalIdeal hmax).symm⟩
    change Module.length A v.asIdeal.ResidueField = _
    have : IsScalarTower A (B ⧸ v.asIdeal) v.asIdeal.ResidueField :=
      IsScalarTower.of_algebraMap_eq (fun x => by
        rw [IsScalarTower.algebraMap_apply A B (B ⧸ v.asIdeal)]; rfl)
    -- `κ(m_v) ≅ B/m_v` as `A`-modules, since `m_v` is maximal.
    let alg : (B ⧸ v.asIdeal) ≃ₐ[B ⧸ v.asIdeal] v.asIdeal.ResidueField :=
      AlgEquiv.ofBijective (Algebra.ofId (B ⧸ v.asIdeal) v.asIdeal.ResidueField)
        (Ideal.bijective_algebraMap_quotient_residueField v.asIdeal)
    have hlen1 : Module.length A v.asIdeal.ResidueField = Module.length A (B ⧸ v.asIdeal) :=
      ((alg.symm.toLinearEquiv.restrictScalars A)).length_eq
    rw [hlen1]
    have hmaxA : (IsLocalRing.maximalIdeal A).IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
    have : Module.Finite A (B ⧸ v.asIdeal) := Module.Finite.of_surjective
      ((Submodule.mkQ v.asIdeal).restrictScalars A) (Submodule.mkQ_surjective v.asIdeal)
    have : Module.Finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ v.asIdeal) :=
      Module.Finite.of_restrictScalars_finite A _ _
    have hsurj : Function.Surjective (algebraMap A (A ⧸ IsLocalRing.maximalIdeal A)) := by
      rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective
    -- `length_A (B/m_v) = length_{κ(m_A)} (B/m_v) = finrank_{κ(m_A)} (B/m_v) = inertiaDeg`.
    rw [len_eq_aux A (A ⧸ IsLocalRing.maximalIdeal A) hsurj (B ⧸ v.asIdeal)]
    rw [Ideal.inertiaDeg'_algebraMap]
    let fld : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
    exact Module.length_eq_finrank (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ v.asIdeal)
  -- combine: `N` is finite length over `Bv`, then apply `key` and `hconst`.
  have hfl : IsFiniteLength Bv N := Module.length_ne_top_iff.mp hN
  rw [key N hfl, hconst]

/-- **(c) sub-lemma 1.** `M = B/bB` is an Artinian `B`-module for `b ≠ 0`. It has finite
`A`-length (it is a quotient of `B/aB` for a nonzero `a ∈ A` with `aB ⊆ bB`, and `B/aB` is finite
over the Artinian ring `A/aA`), hence is Artinian over `A`, hence Artinian over `B` (the `B`-
submodule lattice embeds in the `A`-submodule lattice since `A → B` is module-finite — use
`isArtinian_of_tower` / `IsArtinian` transfer). Used to compute the support of `M` (a finite set of
maximal ideals) for the localization decomposition. -/
theorem isArtinian_quot_span_of_ne_zero
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (b : B) (hb : b ≠ 0) :
    IsArtinian B (B ⧸ Ideal.span {b}) := by
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  -- Step 1: B has Krull dimension ≤ 1 (nonzero primes are maximal, via going-up over A).
  have hB1 : Ring.KrullDimLE 1 B := by
    rw [Ring.krullDimLE_one_iff_of_noZeroDivisors]
    intro I hIne hIp
    have hcomap_ne : Ideal.comap (algebraMap A B) I ≠ ⊥ :=
      Ideal.IsIntegral.comap_ne_bot A hIne
    have hmax : (Ideal.comap (algebraMap A B) I).IsMaximal :=
      Ideal.isMaximal_of_isPrime_of_ne_bot _ hcomap_ne
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap I hmax
  -- Step 2: B is a Noetherian ring (finite over Noetherian A).
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  -- Step 3: B ⧸ (b) has Krull dimension 0.
  have hk0 : Ring.KrullDimLE 0 (B ⧸ Ideal.span {b}) := by
    rw [Ring.krullDimLE_iff]
    have hmem : b ∈ nonZeroDivisors B := mem_nonZeroDivisors_of_ne_zero hb
    have hq := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hmem
    have hB : ringKrullDim B ≤ ((1:ℕ):WithBot ℕ∞) := Ring.krullDimLE_iff.mp inferInstance
    have h : ringKrullDim (B ⧸ Ideal.span {b}) + 1 ≤ ((1:ℕ):WithBot ℕ∞) := le_trans hq hB
    set d := ringKrullDim (B ⧸ Ideal.span {b}) with hd
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
  -- Step 4: a Noetherian ring of dimension 0 is Artinian.
  have : IsArtinianRing (B ⧸ Ideal.span {b}) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  -- Step 5: restrict scalars from (B ⧸ (b)) to B.
  exact isArtinian_of_surjective_algebraMap (S := B) (R := B ⧸ Ideal.span {b})
    Ideal.Quotient.mk_surjective

-- needed: `localizedModule_offdiag_subsingleton`'s `simpa` produces an `(Submodule B M)ᵒᵈ`
-- equality that only typechecks once `OrderDual` unfolds at `default` transparency
set_option backward.isDefEq.respectTransparency false in
/-- **(c) sub-lemma 2** (off-diagonal vanishing of double localization). For distinct maximal
ideals `v ≠ w` of `B`, the localization at `m_w` of the localization at `m_v` of the Artinian
module `M = B/bB` vanishes. Reason: `M_{m_v}` is supported only at `m_v` (it is Artinian with
support `⊆ {m_v}`), so localizing it further at `m_w ≠ m_v` kills it (the localization of a module
whose support misses `m_w` is `0`). Mathlib hooks: `Module.support`, `LocalizedModule`,
`LocalizedModule.subsingleton_iff` / support-disjointness; uses `isArtinian_quot_span_of_ne_zero`.
-/
theorem localizedModule_offdiag_subsingleton
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (b : B) (hb : b ≠ 0)
    (v w : MaximalSpectrum B) (hvw : v ≠ w) :
    Subsingleton (LocalizedModule w.asIdeal.primeCompl
      (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b}))) := by
  classical
  set M := B ⧸ Ideal.span {b} with hM
  have : IsArtinian B M := isArtinian_quot_span_of_ne_zero A B b hb
  -- choose `s ∈ m_v` with `s ∉ m_w` (distinct maximal ideals are incomparable)
  have hsExists : ∃ s ∈ v.asIdeal, s ∉ w.asIdeal := SetLike.not_le_iff_exists.mp fun hle =>
    hvw (MaximalSpectrum.ext (v.isMaximal.eq_of_le w.isMaximal.ne_top hle))
  obtain ⟨s, hsv, hsw⟩ := hsExists
  rw [LocalizedModule.subsingleton_iff]
  intro n
  -- write `n = mk c u`
  induction n using LocalizedModule.induction_on with
  | _ c u =>
    -- Artinian stabilization of the descending cyclic chain `B ∙ sᵐ • c`:
    -- ∃ k β, sᵏ • c = β • (sᵏ⁺¹ • c)
    have hstab : ∃ (k : ℕ) (β : B), s^k • c = β • (s^(k+1) • c) := by
      set g : ℕ → Submodule B M := fun m => Submodule.span B {s^m • c} with hg
      have hanti : Antitone g := by
        intro a c' hac
        rw [hg]; simp only
        rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hac
        rw [pow_add, mul_smul, smul_comm]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      let f : ℕ →o (Submodule B M)ᵒᵈ :=
        ⟨fun m => OrderDual.toDual (g m), fun a c' hac => hanti hac⟩
      obtain ⟨k, hk⟩ := IsArtinian.monotone_stabilizes f
      have key : g k = g (k+1) := by simpa [f] using hk (k+1) (Nat.le_succ k)
      have hmem : s^k • c ∈ g (k+1) := by
        rw [← key]; exact Submodule.mem_span_singleton_self _
      simp only [hg, Submodule.mem_span_singleton] at hmem
      obtain ⟨β, hβ⟩ := hmem
      exact ⟨k, β, hβ.symm⟩
    obtain ⟨k, β, hβ⟩ := hstab
    -- the scalar `sᵏ ∈ w.primeCompl` annihilates `n`; the witness `(1 - β·s) ∈ v.primeCompl`
    refine ⟨s^k, ?_, ?_⟩
    · -- `sᵏ ∈ w.asIdeal.primeCompl` since `s ∉ w.asIdeal` and `w.asIdeal` is prime
      have hwp : w.asIdeal.IsPrime := w.isMaximal.isPrime
      simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
        SetLike.mem_coe]
      intro hpow
      exact hsw (hwp.mem_of_pow_mem k hpow)
    · -- `sᵏ • (mk c u) = mk (sᵏ • c) u = 0`, witnessed by `(1 - β·s) ∈ v.primeCompl`
      rw [LocalizedModule.smul'_mk]
      have hkill : (1 - β * s) • (s^k • c) = 0 := by
        rw [sub_smul, one_smul, mul_smul]
        have hss : s • (s^k • c) = s^(k+1) • c := by rw [← mul_smul, ← pow_succ']
        rw [hss, ← hβ, sub_self]
      have hv : (1 - β * s) ∈ v.asIdeal.primeCompl := by
        simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
          SetLike.mem_coe]
        intro hmem
        have hone : (1 : B) ∈ v.asIdeal := by
          have hbs : β * s ∈ v.asIdeal := Ideal.mul_mem_left _ _ hsv
          have := Ideal.add_mem _ hmem hbs
          simpa using this
        exact v.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)
      rw [show (0 : LocalizedModule v.asIdeal.primeCompl M) =
          LocalizedModule.mk 0 u from (LocalizedModule.zero_mk u).symm]
      rw [LocalizedModule.mk_eq]
      refine ⟨⟨1 - β*s, hv⟩, ?_⟩
      simp only [Submonoid.mk_smul, smul_zero]
      rw [smul_comm, hkill, smul_zero]

/-- **(c) sub-lemma 3** (the localization-decomposition iso, Stacks Tag 02M0 core). The canonical
`B`-linear map `M → ∏_v M_{m_v}` from the finite-length `B`-module `M = B/bB` to the (finite)
product of its localizations at the maximal ideals is an isomorphism. Proof route (closer-verified
reduction): apply `bijective_of_isLocalized_maximal` over the base ring `B` to the natural map
`LinearMap.pi (fun v => LocalizedModule.mkLinearMap v.asIdeal.primeCompl M)`; the resulting per-
maximal stalk goal at `P = m_w` is bijectivity of `M_{m_w} → ∏_v (M_{m_v})_{m_w}`, which holds
componentwise: the diagonal `v = w` component is `isLocalizedModule_id` (re-localizing a module
already local at `m_w`), and the off-diagonal `v ≠ w` components vanish by
`localizedModule_offdiag_subsingleton`. -/
theorem quot_span_nonempty_equiv_pi_localized
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    [Finite (MaximalSpectrum B)]
    (b : B) (hb : b ≠ 0) :
    Nonempty ((B ⧸ Ideal.span {b}) ≃ₗ[B]
      (∀ v : MaximalSpectrum B,
        LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b}))) := by
  classical
  have := Fintype.ofFinite (MaximalSpectrum B)
  refine ⟨LinearEquiv.ofBijective
    (LinearMap.pi (fun v =>
      LocalizedModule.mkLinearMap v.asIdeal.primeCompl (B ⧸ Ideal.span {b}))) ?_⟩
  apply bijective_of_isLocalized_maximal
    (fun P _ => LocalizedModule P.primeCompl (B ⧸ Ideal.span {b}))
    (fun P _ => LocalizedModule.mkLinearMap P.primeCompl (B ⧸ Ideal.span {b}))
    (fun P _ => ∀ v : MaximalSpectrum B,
       LocalizedModule P.primeCompl (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b})))
    (fun P _ => LinearMap.pi (fun v =>
       (LocalizedModule.mkLinearMap P.primeCompl _).comp (LinearMap.proj v)))
    _
  intro P hP
  -- The composite `g ∘ F : M → ∏_v (M_v)_{m_P}` is a localization of `M` at `m_P`: off-diagonal
  -- factors vanish (`localizedModule_offdiag_subsingleton`), so the product is iso to the diagonal
  -- factor `(M_w)_{m_w} ≅ M_{m_w}` (re-localizing the already-local `M_w`, via
  -- `isLocalizedModule_id`).
  have hcomp : IsLocalizedModule P.primeCompl
      ((LinearMap.pi (fun v : MaximalSpectrum B =>
          (LocalizedModule.mkLinearMap P.primeCompl
            (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b}))).comp
          (LinearMap.proj v))).comp
        (LinearMap.pi (fun v : MaximalSpectrum B =>
          LocalizedModule.mkLinearMap v.asIdeal.primeCompl (B ⧸ Ideal.span {b})))) := by
    set M := B ⧸ Ideal.span {b} with hM
    set w : MaximalSpectrum B := ⟨P, hP⟩ with hw
    set l := (LinearMap.pi (fun v : MaximalSpectrum B =>
            (LocalizedModule.mkLinearMap P.primeCompl
              (LocalizedModule v.asIdeal.primeCompl M)).comp
            (LinearMap.proj v))).comp
          (LinearMap.pi (fun v : MaximalSpectrum B =>
            LocalizedModule.mkLinearMap v.asIdeal.primeCompl M)) with hl
    let mkw := LocalizedModule.mkLinearMap w.asIdeal.primeCompl M
    let mkP := LocalizedModule.mkLinearMap P.primeCompl (LocalizedModule w.asIdeal.primeCompl M)
    have hid : IsLocalizedModule P.primeCompl
        (LinearMap.id (R := B) (M := LocalizedModule w.asIdeal.primeCompl M)) :=
      isLocalizedModule_id P.primeCompl (LocalizedModule w.asIdeal.primeCompl M)
        (Localization P.primeCompl)
    have hmkP_bij : Function.Bijective mkP := by
      have hcoe : ⇑mkP = ⇑(IsLocalizedModule.linearEquiv P.primeCompl
            (LinearMap.id (R := B) (M := LocalizedModule w.asIdeal.primeCompl M)) mkP) := by
        funext x
        simpa only [LinearMap.id_coe, id_eq] using (IsLocalizedModule.linearEquiv_apply P.primeCompl
          (LinearMap.id (R := B) (M := LocalizedModule w.asIdeal.primeCompl M)) mkP x).symm
      rw [hcoe]
      exact (IsLocalizedModule.linearEquiv P.primeCompl
        (LinearMap.id (R := B) (M := LocalizedModule w.asIdeal.primeCompl M)) mkP).bijective
    let mkPe : LocalizedModule w.asIdeal.primeCompl M ≃ₗ[B]
        LocalizedModule P.primeCompl (LocalizedModule w.asIdeal.primeCompl M) :=
      LinearEquiv.ofBijective mkP hmkP_bij
    have hd : IsLocalizedModule P.primeCompl (mkPe.toLinearMap.comp mkw) :=
      IsLocalizedModule.of_linearEquiv P.primeCompl mkw mkPe
    have hproj : Function.Bijective
        (LinearMap.proj w : (∀ v : MaximalSpectrum B,
            LocalizedModule P.primeCompl (LocalizedModule v.asIdeal.primeCompl M))
          →ₗ[B] LocalizedModule P.primeCompl (LocalizedModule w.asIdeal.primeCompl M)) := by
      refine ⟨fun y₁ y₂ hyy => funext fun v => ?_, fun z => ⟨Pi.single w z, by simp⟩⟩
      by_cases hv : v = w
      · subst hv; exact hyy
      · exact (localizedModule_offdiag_subsingleton A B b hb v w hv).allEq _ _
    let pe := LinearEquiv.ofBijective (LinearMap.proj w : (∀ v : MaximalSpectrum B,
            LocalizedModule P.primeCompl (LocalizedModule v.asIdeal.primeCompl M))
          →ₗ[B] LocalizedModule P.primeCompl (LocalizedModule w.asIdeal.primeCompl M)) hproj
    have hkey : l = (pe.symm.toLinearMap.comp (mkPe.toLinearMap.comp mkw)) := by
      refine LinearMap.ext fun m => ?_
      apply pe.injective
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]
      change (l m) w = _
      simp only [hl, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply]
      rfl
    rw [hkey]
    exact IsLocalizedModule.of_linearEquiv P.primeCompl (mkPe.toLinearMap.comp mkw) pe.symm
  -- The induced localization map is bijective because `g ∘ F` is itself a localization (`hcomp`):
  -- it then agrees with the canonical iso between the two localizations of `M`.
  set f := LocalizedModule.mkLinearMap P.primeCompl (B ⧸ Ideal.span {b}) with hf
  set g := LinearMap.pi (fun v : MaximalSpectrum B =>
      (LocalizedModule.mkLinearMap P.primeCompl
        (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b}))).comp
      (LinearMap.proj v)) with hg
  set F := LinearMap.pi (fun v : MaximalSpectrum B =>
      LocalizedModule.mkLinearMap v.asIdeal.primeCompl (B ⧸ Ideal.span {b})) with hFdef
  have key : (IsLocalizedModule.map P.primeCompl f g F)
      = ((IsLocalizedModule.iso P.primeCompl (g.comp F)).toLinearMap.comp
          (IsLocalizedModule.iso P.primeCompl f).symm.toLinearMap) := by
    apply IsLocalizedModule.ext P.primeCompl f
      (fun x => IsLocalizedModule.map_units (g.comp F) x)
    rw [IsLocalizedModule.map_comp]
    refine LinearMap.ext fun m => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [show (IsLocalizedModule.iso P.primeCompl f).symm (f m) = LocalizedModule.mk m 1 from ?_]
    · rw [IsLocalizedModule.iso_apply_mk]; simp
    · rw [IsLocalizedModule.iso_symm_apply' P.primeCompl f (f m) m 1 (by simp)]
  rw [key, LinearMap.coe_comp]
  exact (IsLocalizedModule.iso P.primeCompl (g.comp F)).bijective.comp
    (IsLocalizedModule.iso P.primeCompl f).symm.bijective

/-- **Ingredient (c)** (finite-direct-sum-of-localizations decomposition, Stacks Tag 02M0 core).
For nonzero `b`, the finite-`A`-length module `M = B/bB` over the semilocal ring `B` is the finite
direct sum of its localizations at the maximal ideals, so `A`-length is additive:
`length_A(B/bB) = Σ_v length_A((B/bB)_{m_v})`. Proof (closer-verified): the `B`-linear iso
`M ≃ₗ[B] ∏_v M_{m_v}` (`quot_span_nonempty_equiv_pi_localized`) restricts to an `A`-linear iso,
and `Module.length_pi_of_fintype` turns the product length into the sum. -/
theorem length_quot_eq_sum_localizations
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    [Fintype (MaximalSpectrum B)]
    (b : B) (hb : b ≠ 0) :
    Module.length A (B ⧸ Ideal.span {b}) =
      ∑ v : MaximalSpectrum B,
        Module.length A (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b})) := by
  -- The B-linear iso `M ≃ₗ[B] ∏_v M_{m_v}` restricts to an A-linear iso;
  -- `Module.length_pi_of_fintype`
  -- turns the product length into the sum.
  obtain ⟨e⟩ := quot_span_nonempty_equiv_pi_localized A B b hb
  rw [(e.restrictScalars A).length_eq, Module.length_pi_of_fintype]

/-- **Finiteness** of each localized factor: `(B/bB)_{m_v}` has finite `B_v`-length for `b ≠ 0`.
Used to push `.toNat`/casts through the finite sum/product in the assembly. Route: it is
`B_v`-isomorphic to `B_v / b·B_v` (ingredient (a)) whose length is finite because `B_v` is a
1-dim Noetherian local domain and `algebraMap B B_v b ≠ 0` (so `ordInt_algebraMap`/`spanLen_ne_top`
machinery applies), or directly because `(B/bB)_{m_v}` is a localization of the finite-`A`-length
`B/bB`. -/
theorem length_localizedModule_ne_top
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    [∀ v : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime v.asIdeal)]
    [∀ v : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime v.asIdeal)]
    (v : MaximalSpectrum B) (b : B)
    (hbv : algebraMap B (Localization.AtPrime v.asIdeal) b ≠ 0) :
    Module.length (Localization.AtPrime v.asIdeal)
        (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b})) ≠ ⊤ := by
  -- Ingredient (a): the localized factor has the same B_v-length as B_v/span{algebraMap b}.
  rw [length_localizedModule_quot_eq A B v b]
  -- B_v is a 1-dim Noetherian local domain and `algebraMap B B_v b ≠ 0`, so `spanLen_ne_top`.
  exact spanLen_ne_top (Localization.AtPrime v.asIdeal) _ hbv

-- `Ideal.inertiaDeg'` has no semantics-preserving replacement here: `Ideal.inertiaDeg` is a
-- different definition (residue fields of localizations), equal only under `LiesOver` plus
-- maximality, so migrating would change this statement.
set_option linter.deprecated false in
/-- The length of `B ⧸ bB` over `A` is the sum, over the maximal ideals `v` of `B`, of the
inertia degree of `v` times the order of vanishing of `b` in `B_v`. -/
theorem sum_inertiaDeg_ordInt_eq_length_quotient
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (L : Type*) [Field L]
    [Algebra B L] [IsFractionRing B L]
    [Fintype (MaximalSpectrum B)]
    [∀ v : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime v.asIdeal)]
    [∀ v : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime v.asIdeal)]
    [∀ v : MaximalSpectrum B, Algebra (Localization.AtPrime v.asIdeal) L]
    [∀ v : MaximalSpectrum B, IsScalarTower B (Localization.AtPrime v.asIdeal) L]
    [∀ v : MaximalSpectrum B, IsFractionRing (Localization.AtPrime v.asIdeal) L]
    (b : B) (hb : b ≠ 0)
    (hbL : ∀ _ : MaximalSpectrum B, (algebraMap B L b) ≠ 0) :
    ∑ v : MaximalSpectrum B,
        (Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) v.asIdeal : ℤ) *
          ordInt (Localization.AtPrime v.asIdeal) (algebraMap B L b) (hbL v) =
      ((Module.length A (B ⧸ Ideal.span {b})).toNat : ℤ) := by
  -- Stacks 02M0)
  -- image of `b` in each `B_v` is nonzero.
  have hbv : ∀ v : MaximalSpectrum B,
      algebraMap B (Localization.AtPrime v.asIdeal) b ≠ 0 := by
    intro v
    have h := hbL v
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime v.asIdeal) L b] at h
    intro hz; apply h; rw [hz]; simp
  -- finiteness of each `B_v`-length.
  have hfin : ∀ v : MaximalSpectrum B,
      Module.length (Localization.AtPrime v.asIdeal)
        (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b})) ≠ ⊤ := fun v =>
    length_localizedModule_ne_top A B v b (hbv v)
  -- Step (a)+def: each local order equals the `B_v`-length of `(B/bB)_{m_v}`, as a `.toNat`.
  have hord : ∀ v : MaximalSpectrum B,
      ordInt (Localization.AtPrime v.asIdeal) (algebraMap B L b) (hbL v) =
        ((Module.length (Localization.AtPrime v.asIdeal)
          (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b}))).toNat : ℤ) := by
    intro v
    have key := ordInt_algebraMap (Localization.AtPrime v.asIdeal)
      (K := L) (algebraMap B (Localization.AtPrime v.asIdeal) b) (hbv v)
      (by rw [← IsScalarTower.algebraMap_apply B (Localization.AtPrime v.asIdeal) L b];
          exact hbL v)
    rw [length_localizedModule_quot_eq A B v b, ← key]
    congr 1
    exact (IsScalarTower.algebraMap_apply B (Localization.AtPrime v.asIdeal) L b)
  -- Reduce the LHS sum to integer casts of the `B_v`-lengths.
  rw [Finset.sum_congr rfl (fun v _ => by rw [hord v])]
  -- Step (c): `length_A(B/bB) = Σ_v length_A((B/bB)_{m_v})` (in ℕ∞).
  rw [length_quot_eq_sum_localizations A B b hb]
  -- Step (b): `length_A((B/bB)_{m_v}) = inertiaDeg_v * length_{B_v}(...)` (in ℕ∞).
  rw [Finset.sum_congr rfl (fun v _ =>
    length_restrictScalars_eq_inertiaDeg_mul A B v _ (hfin v))]
  -- Now both sides are finite; push `.toNat` through the finite sum and product.
  have hprodfin : ∀ v ∈ (Finset.univ : Finset (MaximalSpectrum B)),
      (Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) v.asIdeal : ℕ∞) *
        Module.length (Localization.AtPrime v.asIdeal)
          (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b})) ≠ ⊤ := by
    intro v _
    exact WithTop.mul_ne_top (ENat.natCast_ne_top _) (hfin v)
  rw [ENat.toNat_sum hprodfin]
  push_cast
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [ENat.toNat_mul, ENat.toNat_natCast]
  push_cast [ENat.natCast_toNat (hfin v)]
  ring

