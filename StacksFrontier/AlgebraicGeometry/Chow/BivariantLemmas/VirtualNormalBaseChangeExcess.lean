module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalSubbundle

/-!
# Restriction of a virtual normal Gysin class to a base change, with excess

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let

```
Z' --i'--→ X'
|          |
g          f
↓          ↓
Z  --i---→ X
```

be a cartesian square of schemes locally of finite type over `S` whose horizontal arrows are
closed immersions, let `𝒩` be a virtual normal sheaf for `Z ⊂ X` and `𝒩'` one for `Z' ⟶ X'`, and
let

  `0 ⟶ 𝒩' ⟶ g^*𝒩 ⟶ ℰ ⟶ 0`

be a short exact sequence of finite locally free `𝒪_{Z'}`-modules such that the square

```
g^*𝒩^∨ -----→ (𝒩')^∨
|               |
g^*σ            σ'
↓               ↓
g^*𝒞_{Z/X} --→ 𝒞_{Z'/X'}
```

commutes. **Stacks 0FV7** asserts that then

  `res(c(Z ⟶ X, 𝒩)) = c_top(ℰ) ∘ c(Z' ⟶ X', 𝒩')`

in `A^*(Z' ⟶ X')^∧`.

The source's proof is two steps: Stacks 0FBK identifies `res(c(Z ⟶ X, 𝒩))` with
`c(Z' ⟶ X', g^*𝒩)`, and Stacks 0FBL, applied to the short exact sequence on `Z'`, rewrites that
as `c_top(ℰ) ∘ c(Z' ⟶ X', 𝒩')`. Here Stacks 0FBL is
`Stacks.Chow.virtualNormalGysinCap_eq_topChernCap_comp`, the pullback `g^*𝒩` is the virtual
normal sheaf of Stacks 0FBJ (`Stacks.Chow.VirtualNormalBundle.baseChange`), and the commuting
square above is the factorization hypothesis of Stacks 0FBL for `g^*𝒩`.

## Main definitions

* `Stacks.Chow.baseChangeVirtualNormalProjection` — the geometric input of Stacks 0FBK at the
  base change: the virtual normal sheaf `g^*𝒩` of Stacks 0FBJ, of the same constant rank as
  `𝒩`, together with the projection of its vector bundle.

## Main results

* `Stacks.Chow.isFiniteLocallyFreeOfRank_modulePullback` — the pullback of a module that is
  finite locally free of rank `r` is finite locally free of rank `r`.
* `Stacks.Chow.dualMap_comp_surjection_eq_baseChange_surjection` — the commuting square of
  Stacks 0FV7 is the factorization hypothesis of Stacks 0FBL for the pulled-back virtual normal
  sheaf.
* `Stacks.Chow.virtualNormalGysinRestrictionCap_eq_topChernCap_comp` — **Stacks 0FV7**, on cap
  operations.
* `Stacks.Chow.virtualNormalGysinRestriction_eq_of_isTopChernComposition` — **Stacks 0FV7**, as
  an equality of bivariant classes.

## Implementation notes

### The square is the chosen fibre product

`Stacks.Chow.bivariantRestriction`, this repository's Stacks 0F9Z, produces a bivariant class
for `pullback.snd i f : Z ×_X X' ⟶ X'`, the *chosen* categorical fibre product: the cap
operation of a bivariant class lands in chosen pullbacks, so the restriction cannot be typed
anywhere else. Accordingly the cartesian square of the tag is taken here to be the chosen one,
`Stacks.Chow.isPullback_pullbackSnd`, with `Z' = Z ×_X X'`, `i' = pullback.snd i f` and
`g = pullback.fst i f`. This is no loss: every cartesian square with the same two bottom and
right arrows is canonically isomorphic to this one, and it is where `res` exists.

### What is carried, and why

The hypothesis `hbase` is the base-change clause of Stacks 0FBK, the source's first proof step:
that `res(c(Z ⟶ X, 𝒩))` satisfies the relation `p^* ∘ c = ι_* ∘ j^* ∘ C` of the construction for
the pulled-back sheaf `g^*𝒩`, that is, that it *is* `c(Z' ⟶ X', g^*𝒩)` in the sense in which
this repository has that class. The clause is no longer absent from the repository: read on the
completed class `Stacks.Chow.completedVirtualNormalGysinClass` it is the theorem
`Stacks.Chow.completedBivariantRestriction_completedVirtualNormalGysinClass`, registered as the
`@[stacks 0FBK "base change: the restriction of c(Z → X, 𝒩) ∈ A^*(Z → X)^∧ along X' → X is c(Z ×_X X' → X', g^*𝒩), for 𝒩 of arbitrary rank"]`
of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedVirtualNormalBundleClassBaseChange`.
The inputs this section once recorded as absent are registered too: the normal cone of Stacks 0637
(`Stacks.Conormal.normalConeToNormalBundle`), the deformation space of Stacks 0FBH
(`Stacks.Chow.normalConeToExceptionalDivisor_spec`) and the class of Stacks 0F9J
(`Stacks.Chow.gysinAtInfinityClass` and its companions in the `GysinAtInfinity` family). The
binder remains nonetheless, because the statements below abstract over the class: `c` and `c'`
are arbitrary bivariant classes of degrees `m` and `m'`, and `hbase` is exactly the hypothesis
tying `res(c)` to the pulled-back sheaf `g^*𝒩`; discharging it from the theorem above would mean
instantiating `c` at `completedVirtualNormalGysinClass` and rewriting the cap data along
`Stacks.Chow.completedVirtualNormalGysinClass_cap_baseChange` — a change of these signatures, not
a gap in this repository. `Stacks.Chow.IsVirtualNormalGysinClass` is the repository's
characterization of the class for an abstract bivariant class, and it is in that form that the
clause enters below. Everything else the tag needs is proved or applied: the factorization
hypothesis of Stacks 0FBL for `g^*𝒩` is derived from the tag's commuting square by
`Stacks.Chow.dualMap_comp_surjection_eq_baseChange_surjection`, and the conclusion is Stacks 0FBL
(`Stacks.Chow.virtualNormalGysinCap_eq_topChernCap_comp` of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalSubbundle`).

The remaining hypotheses are those of Stacks 0FBL, unchanged and for the same reasons; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalSubbundle` for `hfactor`,
`hstep` and `hinj`. As there, the tag's sheaf-level commuting square enters only as the
factorization hypothesis of Stacks 0FBL, which that lemma's proof does not consume, running
instead on the carried geometric consequence `hfactor`.

### Closed immersions

The horizontal arrows are closed immersions, as the tag has them; that is what `i` is assumed to
be, and `pullback.snd i f` is then one too. The argument uses only that they are immersions,
which is how Stacks 0FBJ and Stacks 0FBL are stated here.

### The rank of the pulled-back sheaf is not assumed

`Stacks.Chow.VirtualNormalBundleProjection` asks the virtual normal sheaf for a constant rank,
the case Stacks 0FBK reduces to. For `g^*𝒩` that rank is the rank of `𝒩`, and this is proved
here rather than assumed, by `Stacks.Chow.isFiniteLocallyFreeOfRank_modulePullback`: local free
presentations transport through a pullback with the same basis-indexing types, which is
`Stacks.AlgebraicGeometry.ComponentDegrees.rankPullbackData`.

## References

* [Stacks Project, Tag 0FV7](https://stacks.math.columbia.edu/tag/0FV7)
* [Stacks Project, Tag 0FBI](https://stacks.math.columbia.edu/tag/0FBI)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBL](https://stacks.math.columbia.edu/tag/0FBL)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

/-! ### The pulled-back virtual normal sheaf -/

/-- The pullback of a module that is finite locally free of rank `r` is finite locally free of
rank `r`: the local free presentations transport with the same basis-indexing types. -/
theorem isFiniteLocallyFreeOfRank_modulePullback {Z Z' : Scheme.{u}} (g : Z' ⟶ Z)
    (M : Z.Modules) (r : ℕ)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((modulePullback g.toLRSHom.toShHom).obj M) r :=
  Stacks.AlgebraicGeometry.ComponentDegrees.rankPullbackData _
    (structureSheafHom g.toLRSHom.toShHom) M r h

/-- The module of the virtual normal sheaf of Stacks 0FBJ is the pullback `g^*𝒩`. -/
theorem VirtualNormalBundle.baseChange_bundle {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsImmersion i] [IsImmersion i'] (g : Z' ⟶ Z) (f : X' ⟶ X) (sq : IsPullback i' g f i)
    (N : VirtualNormalBundle i) :
    (VirtualNormalBundle.baseChange i i' g f sq N).bundle =
      (modulePullback g.toLRSHom.toShHom).obj N.bundle :=
  rfl

/-- The conormal surjection of the virtual normal sheaf of Stacks 0FBJ is the composite of the
inverse of the dual base-change isomorphism, the pullback of `σ`, and the conormal comparison
map of Stacks 0473. -/
theorem VirtualNormalBundle.baseChange_surjection {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X)
    (i' : Z' ⟶ X') [IsImmersion i] [IsImmersion i'] (g : Z' ⟶ Z) (f : X' ⟶ X)
    (sq : IsPullback i' g f i) (N : VirtualNormalBundle i) :
    (VirtualNormalBundle.baseChange i i' g f sq N).surjection =
      (@asIso _ _ _ _ (pullbackDualMap g N.bundle)
          (pullbackDualMap_isIso g N.bundle N.isFiniteLocallyFree)).inv ≫
        (modulePullback g.toLRSHom.toShHom).map N.surjection ≫
          Stacks.Immersion.immersionConormalSheafMap i' i g f
            (Stacks.Immersion.toShHom_square sq.w) :=
  rfl

/-- **The commuting square of Stacks 0FV7 is the factorization hypothesis of Stacks 0FBL.** If
the square

```
g^*𝒩^∨ -----→ (𝒩')^∨
|               |
g^*σ            σ'
↓               ↓
g^*𝒞_{Z/X} --→ 𝒞_{Z'/X'}
```

commutes, whose top arrow is the dual base-change isomorphism followed by the dual of
`𝒩' ⟶ g^*𝒩`, then the conormal surjection of the virtual normal sheaf `g^*𝒩` of Stacks 0FBJ
factors through that of `𝒩'` along that dual. -/
theorem dualMap_comp_surjection_eq_baseChange_surjection {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X)
    (i' : Z' ⟶ X') [IsImmersion i] [IsImmersion i'] (g : Z' ⟶ Z) (f : X' ⟶ X)
    (sq : IsPullback i' g f i) (N : VirtualNormalBundle i) (N' : VirtualNormalBundle i')
    (inc : N'.bundle ⟶ (modulePullback g.toLRSHom.toShHom).obj N.bundle)
    (hcomm : pullbackDualMap g N.bundle ≫ dualMap inc ≫ N'.surjection =
      (modulePullback g.toLRSHom.toShHom).map N.surjection ≫
        Stacks.Immersion.immersionConormalSheafMap i' i g f
          (Stacks.Immersion.toShHom_square sq.w)) :
    dualMap inc ≫ N'.surjection =
      (VirtualNormalBundle.baseChange i i' g f sq N).surjection := by
  rw [VirtualNormalBundle.baseChange_surjection, ← hcomm]
  exact (Iso.inv_hom_id_assoc (@asIso _ _ _ _ (pullbackDualMap g N.bundle)
    (pullbackDualMap_isIso g N.bundle N.isFiniteLocallyFree)) _).symm

/-! ### The chosen cartesian square -/

/-- The chosen fibre product `Z ×_X X'` as a cartesian square with `i` on the bottom and `f` on
the right, the square Stacks 0FV7 is stated at here. -/
theorem isPullback_pullbackSnd {Z X X' : Scheme.{u}} (i : Z ⟶ X) (f : X' ⟶ X) :
    IsPullback (pullback.snd i f) (pullback.fst i f) f i :=
  (IsPullback.of_hasPullback i f).flip

/-- **The geometric input of Stacks 0FBK at the base change.** The virtual normal sheaf
`g^*𝒩` of Stacks 0FBJ for `Z ×_X X' ⟶ X'`, which has the same constant rank `m` as `𝒩`,
together with a flat projection of relative dimension `m` for its vector bundle. -/
def baseChangeVirtualNormalProjection {Z X X' Nbig : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (f : X' ⟶ X) (N : VirtualNormalBundle i) (m : ℕ)
    (hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N.bundle m)
    (q : Nbig ⟶ pullback i f) [LocallyOfFiniteType q] (hflat : AlgebraicGeometry.Flat q)
    (hrd : AlgebraicGeometry.RelativeDimension q m) :
    VirtualNormalBundleProjection (pullback.snd i f) q m where
  normalBundle :=
    VirtualNormalBundle.baseChange i (pullback.snd i f) (pullback.fst i f) f
      (isPullback_pullbackSnd i f) N
  rank := isFiniteLocallyFreeOfRank_modulePullback (pullback.fst i f) N.bundle m hrank
  flat := hflat
  relativeDimension := hrd

/-! ### Stacks 0FV7 -/

section Main

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X X' Nbig Nsub : Scheme.{u}}
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFiniteType i] (hi : i ≫ sX = sZ)
  (f : X' ⟶ X) [LocallyOfFiniteType f]
  (sNbig : Nbig ⟶ C.S) [LocallyOfFiniteType sNbig]
  (sNsub : Nsub ⟶ C.S) [LocallyOfFiniteType sNsub]
  (q : Nbig ⟶ pullback i f) [LocallyOfFiniteType q]
  (q' : Nsub ⟶ pullback i f) [LocallyOfFiniteType q']
  (hq : q ≫ (pullback.fst i f ≫ sZ) = sNbig)
  (hq' : q' ≫ (pullback.fst i f ≫ sZ) = sNsub)
  (j : Nsub ⟶ Nbig) [IsClosedImmersion j] (hj : j ≫ q = q')
  (m m' e : ℕ) (N : VirtualNormalBundle i)
  (hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N.bundle m)
  (hflat : AlgebraicGeometry.Flat q) (hrd : AlgebraicGeometry.RelativeDimension q m)
  (P' : VirtualNormalBundleProjection (pullback.snd i f) q' m')
  (Eb : (pullback i f).Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Eb e]
  (cap : HigherChernCapRule C e) (hdesc : FlatPullbackDescends C)
  (E : BivariantClass C G sNbig (f ≫ sX) (q ≫ pullback.snd i f)
    (comp_comp_structureMorphism_eq hq (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f)) 0)
  (E' : BivariantClass C G sNsub (f ≫ sX) (q' ≫ pullback.snd i f)
    (comp_comp_structureMorphism_eq hq' (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f)) 0)
  (inc : P'.normalBundle.bundle ⟶
    (modulePullback (pullback.fst i f).toLRSHom.toShHom).obj N.bundle)
  (pr : (modulePullback (pullback.fst i f).toLRSHom.toShHom).obj N.bundle ⟶ Eb)
  (hgys : G.IsNaturalUnderBaseChangeIso)

/-- **Stacks 0FV7**, on cap operations. Let `(S, δ)` be the base situation of chapter 42, let

```
Z' --i'--→ X'
|          |
g          f
↓          ↓
Z  --i---→ X
```

be the cartesian square of the chosen fibre product `Z' = Z ×_X X'` of a closed immersion
`i : Z ⟶ X` along `f : X' ⟶ X`, both locally of finite type over `S`. Let `𝒩` be a virtual
normal sheaf for `Z ⊂ X` of constant rank `m`, let `𝒩'` be one for `Z' ⟶ X'` of constant rank
`m'`, and let

  `0 ⟶ 𝒩' ⟶ g^*𝒩 ⟶ ℰ ⟶ 0`

be a short exact sequence of finite locally free `𝒪_{Z'}`-modules with `ℰ` of constant rank `e`,
such that the square of `hcomm` commutes. Then, for `c = c(Z ⟶ X, 𝒩)` and
`c' = c(Z' ⟶ X', 𝒩')` the classes of Stacks 0FBK,

  `res(c) ∩ α = c_top(ℰ) ∩ (c' ∩ α)`

on every test scheme `g₀ : T ⟶ X'`, in every degree and for every `α ∈ A_k(T)`.

The identification of `res(c)` with `c(Z' ⟶ X', g^*𝒩)` by Stacks 0FBK is the hypothesis
`hbase`. -/
@[stacks 0FV7 "res(c(Z -> X, N)) = c_top(E) composed with c(Z' -> X', N') for a cartesian \
square of closed immersions and a short exact sequence 0 -> N' -> g^*N -> E -> 0 of finite \
locally free O_{Z'}-modules of constant ranks m', m, e whose dual square against the conormal \
sheaves commutes. The square is the CHOSEN fibre product, which is where Stacks 0F9Z lives in \
this repository (`bivariantRestriction`), every cartesian square being canonically isomorphic \
to it. The commuting square IS consumed: it yields the factorization hypothesis of Stacks 0FBL \
for g^*N, which is `dualMap_comp_surjection_eq_baseChange_surjection`. The pulled-back sheaf is \
the virtual normal sheaf of Stacks 0FBJ, and its constant rank is PROVED, not assumed. CARRIED: \
the Stacks 0FBJ base-change clause of Stacks 0FBK as `hbase` -- that res(c) satisfies the \
characterizing relation for g^*N, the source's first proof step; the clause is proved in this \
repository for the completed class at \
`completedBivariantRestriction_completedVirtualNormalGysinClass` (stacks 0FBK), and the binder is \
retained because this theorem abstracts over the class c; and the hypotheses of \
Stacks 0FBL, unchanged (Stacks 0FAA at the base-changed bundle projections as `hstep`, the \
geometric consequence of the factorization as `hfactor`, Stacks 02TY injectivity as `hinj`, \
Stacks 0B7G as this directory's cap-rule parameter)"]
theorem virtualNormalGysinRestrictionCap_eq_topChernCap_comp
    (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)
    (hcomm : pullbackDualMap (pullback.fst i f) N.bundle ≫
        dualMap inc ≫ P'.normalBundle.surjection =
      (modulePullback (pullback.fst i f).toLRSHom.toShHom).map N.surjection ≫
        Stacks.Immersion.immersionConormalSheafMap (pullback.snd i f) i (pullback.fst i f) f
          (Stacks.Immersion.toShHom_square (isPullback_pullbackSnd i f).w))
    (x : ↥(pullback i f))
    (hinj : ∀ {T : Scheme.{u}} (g₀ : T ⟶ X') [LocallyOfFiniteType g₀] (k : ℤ),
      Function.Injective
        (bundleFlatPullback C (pullback.fst i f ≫ sZ) sNbig (pullback.snd i f) q hq m hflat hrd
          hdesc g₀ k))
    (hfactor : SubbundleGysinFactorization C G (pullback.fst i f ≫ sZ) (f ≫ sX) sNbig sNsub
      (pullback.snd i f) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) q q' hq hq' j hj
      E E')
    (hstep : SubbundleGysinTopChernStep C (pullback.fst i f ≫ sZ) sNbig sNsub (pullback.snd i f)
      q q' hq hq' j hj m m' e Eb cap hdesc
      (baseChangeVirtualNormalProjection i f N m hrank q hflat hrd) P')
    {c : BivariantClass C G sZ sX i hi (m : ℤ)}
    {c' : BivariantClass C G (pullback.fst i f ≫ sZ) (f ≫ sX) (pullback.snd i f)
      (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) (m' : ℤ)}
    (hbase : IsVirtualNormalGysinClass C G (pullback.fst i f ≫ sZ) (f ≫ sX) sNbig
      (pullback.snd i f) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) q hq m 0 E
      (bundleFlatPullback C (pullback.fst i f ≫ sZ) sNbig (pullback.snd i f) q hq m hflat hrd
        hdesc)
      (baseChangeVirtualNormalProjection i f N m hrank q hflat hrd)
      (bivariantRestriction C G sZ sX i hi f (m : ℤ) hgys c))
    (hbase' : IsVirtualNormalGysinClass C G (pullback.fst i f ≫ sZ) (f ≫ sX) sNsub
      (pullback.snd i f) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) q' hq' m' 0 E'
      (bundleFlatPullback C (pullback.fst i f ≫ sZ) sNsub (pullback.snd i f) q' hq' m' P'.flat
        P'.relativeDimension hdesc)
      P' c')
    {T : Scheme.{u}} (g₀ : T ⟶ X') [LocallyOfFiniteType g₀] (k : ℤ)
    (α : chowGroup C (g₀ ≫ (f ≫ sX)) k) :
    (bivariantRestriction C G sZ sX i hi f (m : ℤ) hgys c).cap g₀ k α =
      chowGroupDegreeEquiv C (pullback.fst (pullback.snd i f) g₀ ≫ (pullback.fst i f ≫ sZ))
        (subbundleVirtualNormalDegree_eq
          (baseChangeVirtualNormalProjection i f N m hrank q hflat hrd) P' Eb inc pr w hseq x k)
        (subbundleTopChernCap C (pullback.fst i f ≫ sZ) (pullback.snd i f) m' e Eb cap g₀ k
          (c'.cap g₀ k α)) :=
  virtualNormalGysinCap_eq_topChernCap_comp C G (pullback.fst i f ≫ sZ) (f ≫ sX) sNbig sNsub
    (pullback.snd i f) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) q q' hq hq' j hj
    m m' e Eb cap hdesc E E'
    (baseChangeVirtualNormalProjection i f N m hrank q hflat hrd) P' inc pr w hseq
    (dualMap_comp_surjection_eq_baseChange_surjection i (pullback.snd i f) (pullback.fst i f) f
      (isPullback_pullbackSnd i f) N P'.normalBundle inc hcomm)
    x hinj hfactor hstep hbase hbase' g₀ k α

/-- **Stacks 0FV7**, as an equality in `A^m(Z' ⟶ X')`. If `d` is a bivariant class of degree `m`
for `Z' ⟶ X'` whose cap operation is cap with `c(Z' ⟶ X', 𝒩')` followed by `c_top(ℰ)`, that is
if `d` is the composite `c_top(ℰ) ∘ c(Z' ⟶ X', 𝒩')`, then `d = res(c(Z ⟶ X, 𝒩))`.

The composite is described by its cap operation, in the idiom of
`Stacks.Chow.IsBivariantClassComposition`. -/
@[stacks 0FV7 "res(c(Z -> X, N)) = c_top(E) composed with c(Z' -> X', N'), read as an equality \
of classes in A^m(Z' -> X') via `BivariantClass.ext`, for a cartesian square of closed \
immersions and a short exact sequence 0 -> N' -> g^*N -> E -> 0 of finite locally free \
O_{Z'}-modules of constant ranks m', m, e whose dual square against the conormal sheaves \
commutes. The square is the CHOSEN fibre product, which is where Stacks 0F9Z lives in this \
repository (`bivariantRestriction`), every cartesian square being canonically isomorphic to it. \
The commuting square IS consumed: it yields the factorization hypothesis of Stacks 0FBL for \
g^*N. The pulled-back sheaf is the virtual normal sheaf of Stacks 0FBJ, and its constant rank \
is PROVED, not assumed. CARRIED: the Stacks 0FBJ base-change clause of Stacks 0FBK as `hbase`, \
the source's first proof step, the clause being proved in this repository for the completed class \
at `completedBivariantRestriction_completedVirtualNormalGysinClass` (stacks 0FBK) and the binder \
retained because this theorem abstracts over the class c; and the hypotheses of Stacks 0FBL, \
unchanged (Stacks 0FAA at the \
base-changed bundle projections as `hstep`, the geometric consequence of the factorization as \
`hfactor`, Stacks 02TY injectivity as `hinj`, Stacks 0B7G as this directory's cap-rule \
parameter)"]
theorem virtualNormalGysinRestriction_eq_of_isTopChernComposition
    (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)
    (hcomm : pullbackDualMap (pullback.fst i f) N.bundle ≫
        dualMap inc ≫ P'.normalBundle.surjection =
      (modulePullback (pullback.fst i f).toLRSHom.toShHom).map N.surjection ≫
        Stacks.Immersion.immersionConormalSheafMap (pullback.snd i f) i (pullback.fst i f) f
          (Stacks.Immersion.toShHom_square (isPullback_pullbackSnd i f).w))
    (x : ↥(pullback i f))
    (hinj : ∀ {T : Scheme.{u}} (g₀ : T ⟶ X') [LocallyOfFiniteType g₀] (k : ℤ),
      Function.Injective
        (bundleFlatPullback C (pullback.fst i f ≫ sZ) sNbig (pullback.snd i f) q hq m hflat hrd
          hdesc g₀ k))
    (hfactor : SubbundleGysinFactorization C G (pullback.fst i f ≫ sZ) (f ≫ sX) sNbig sNsub
      (pullback.snd i f) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) q q' hq hq' j hj
      E E')
    (hstep : SubbundleGysinTopChernStep C (pullback.fst i f ≫ sZ) sNbig sNsub (pullback.snd i f)
      q q' hq hq' j hj m m' e Eb cap hdesc
      (baseChangeVirtualNormalProjection i f N m hrank q hflat hrd) P')
    {c : BivariantClass C G sZ sX i hi (m : ℤ)}
    {c' : BivariantClass C G (pullback.fst i f ≫ sZ) (f ≫ sX) (pullback.snd i f)
      (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) (m' : ℤ)}
    {d : BivariantClass C G (pullback.fst i f ≫ sZ) (f ≫ sX) (pullback.snd i f)
      (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) (m : ℤ)}
    (hbase : IsVirtualNormalGysinClass C G (pullback.fst i f ≫ sZ) (f ≫ sX) sNbig
      (pullback.snd i f) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) q hq m 0 E
      (bundleFlatPullback C (pullback.fst i f ≫ sZ) sNbig (pullback.snd i f) q hq m hflat hrd
        hdesc)
      (baseChangeVirtualNormalProjection i f N m hrank q hflat hrd)
      (bivariantRestriction C G sZ sX i hi f (m : ℤ) hgys c))
    (hbase' : IsVirtualNormalGysinClass C G (pullback.fst i f ≫ sZ) (f ≫ sX) sNsub
      (pullback.snd i f) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) q' hq' m' 0 E'
      (bundleFlatPullback C (pullback.fst i f ≫ sZ) sNsub (pullback.snd i f) q' hq' m' P'.flat
        P'.relativeDimension hdesc)
      P' c')
    (hd : ∀ {T : Scheme.{u}} (g₀ : T ⟶ X') [LocallyOfFiniteType g₀] (k : ℤ)
      (α : chowGroup C (g₀ ≫ (f ≫ sX)) k),
      d.cap g₀ k α =
        chowGroupDegreeEquiv C (pullback.fst (pullback.snd i f) g₀ ≫ (pullback.fst i f ≫ sZ))
          (subbundleVirtualNormalDegree_eq
            (baseChangeVirtualNormalProjection i f N m hrank q hflat hrd) P' Eb inc pr w hseq x k)
          (subbundleTopChernCap C (pullback.fst i f ≫ sZ) (pullback.snd i f) m' e Eb cap g₀ k
            (c'.cap g₀ k α))) :
    d = bivariantRestriction C G sZ sX i hi f (m : ℤ) hgys c := by
  refine BivariantClass.ext C G (pullback.fst i f ≫ sZ) (f ≫ sX) (pullback.snd i f)
    (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) (m : ℤ) ?_
  intro T g₀ _ k α
  rw [hd g₀ k α]
  exact (virtualNormalGysinRestrictionCap_eq_topChernCap_comp C G sZ sX i hi f sNbig sNsub q q'
    hq hq' j hj m m' e N hrank hflat hrd P' Eb cap hdesc E E' inc pr hgys w hseq hcomm x hinj
    hfactor hstep hbase hbase' g₀ k α).symm

end Main

end Stacks.Chow

end
