module

public import Mathlib.RingTheory.Extension.Cotangent.BaseChange

/-!
# Flat base change for `H₁` of the naive cotangent complex

If `S'` is the base change of `S` along a flat ring map `R → R'`, then the canonical map
`H₁(L_{S/R}) → H₁(L_{S'/R'})` exhibits its target as the base change of its source, both along
`R → R'` and along `S → S'`.

## Main results

* `h1Cotangent_map_map`: functoriality of `Algebra.H1Cotangent.map` in the algebra.
* `isBaseChange_of_isBaseChange_of_isPushout`: for a module over a pushout square, a base change
  along `R → R'` is a base change along `S → S'`.
* `isBaseChange_restrictScalars_h1Cotangent_map`, `isBaseChange_h1Cotangent_map`: flat base
  change for `H₁` of the naive cotangent complex, along `R → R'` and along `S → S'` respectively.

## References

* [StacksProject 00S4](https://stacks.math.columbia.edu/tag/00S4)
-/

@[expose] public section

universe u v w x y

open scoped TensorProduct

namespace Stacks.Cotangent.H1BaseChange

/-- In a pushout square of commutative rings
```
R  →  R'
↓     ↓
S  →  S'
```
an `S'`-module `N` is the base change of an `S`-module `M` along `S → S'` as soon as it is the base
change of `M` along `R → R'`. -/
lemma isBaseChange_of_isBaseChange_of_isPushout
    {R R' S S' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R R'] [Algebra R S] [Algebra R S'] [Algebra R' S'] [Algebra S S']
    [IsScalarTower R R' S'] [IsScalarTower R S S'] [Algebra.IsPushout R R' S S']
    {M N : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup N] [Module R N] [Module R' N] [Module S N] [Module S' N]
    [IsScalarTower R R' N] [IsScalarTower R S N] [IsScalarTower R' S' N] [IsScalarTower S S' N]
    (f : M →ₗ[S] N) (hf : IsBaseChange R' (f.restrictScalars R)) :
    IsBaseChange S' f := by
  set e := Algebra.IsPushout.cancelBaseChange R R' S S' M with he
  have key : ∀ x : R' ⊗[R] M, f.liftBaseChange S' (e.symm x) = hf.equiv x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul r' m =>
        rw [he, Algebra.IsPushout.cancelBaseChange_symm_tmul, hf.equiv_tmul]
        simp [algebraMap_smul]
    | add x y hx hy => simp [hx, hy]
  have hcomp : (f.liftBaseChange S' : S' ⊗[S] M → N) = hf.equiv ∘ e := by
    funext x; simpa using key (e x)
  exact .of_equiv (LinearEquiv.ofBijective (f.liftBaseChange S')
    (hcomp ▸ hf.equiv.bijective.comp e.bijective)) (by simp)

/-- **Functoriality of `Algebra.H1Cotangent.map`** along a stack of two squares of rings
```
R  →  S
↓     ↓
R' →  S'
↓     ↓
R''→  S''
```
the map `H₁(L_{S/R}) → H₁(L_{S''/R''})` is the composite of the maps of the two squares. -/
lemma h1Cotangent_map_map (R S R' S' R'' S'' : Type*) [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [CommRing R''] [CommRing S'']
    [Algebra R S] [Algebra R' S'] [Algebra R'' S'']
    [Algebra R R'] [Algebra R' R''] [Algebra R R''] [IsScalarTower R R' R'']
    [Algebra S S'] [Algebra S' S''] [Algebra S S''] [IsScalarTower S S' S'']
    [Algebra R S'] [Algebra R S''] [Algebra R' S'']
    [IsScalarTower R R' S'] [IsScalarTower R S S'] [IsScalarTower R' R'' S'']
    [IsScalarTower R' S' S''] [IsScalarTower R R'' S''] [IsScalarTower R S S'']
    (x : Algebra.H1Cotangent R S) :
    Algebra.H1Cotangent.map R' R'' S' S'' (Algebra.H1Cotangent.map R R' S S' x)
      = Algebra.H1Cotangent.map R R'' S S'' x := by
  simp only [Algebra.H1Cotangent.map, ← Algebra.Extension.H1Cotangent.map_comp_apply]
  rw [Algebra.Extension.H1Cotangent.map_eq]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Flat base change for `H₁` of the naive cotangent complex**, along the base ring. If `S'` is
the base change of `S` along a flat ring map `R → R'`, then `H₁(L_{S'/R'})` is the base change of
`H₁(L_{S/R})` along `R → R'`. -/
lemma isBaseChange_restrictScalars_h1Cotangent_map (R S R' S' : Type*) [CommRing R]
    [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra S S']
    [Algebra R' S'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    [Algebra.IsPushout R R' S S'] [Module.Flat R R'] :
    IsBaseChange R' ((Algebra.H1Cotangent.map R R' S S').restrictScalars R) := by
  set e := Algebra.IsPushout.equiv R R' S S' with he
  let _ : Algebra (R' ⊗[R] S) S' := e.toRingHom.toAlgebra
  have : IsScalarTower R' (R' ⊗[R] S) S' := .of_algebraMap_eq' e.toAlgHom.comp_algebraMap.symm
  have : IsScalarTower S (R' ⊗[R] S) S' := .of_algebraMap_eq fun s => by
    rw [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.right_algebraMap_apply]
    simp [he, Algebra.IsPushout.equiv_tmul]
  refine .of_equiv (Algebra.tensorH1CotangentOfFlat R S R' ≪≫ₗ
    Algebra.H1Cotangent.mapEquiv R' _ _ e) fun x => ?_
  rw [LinearEquiv.trans_apply, Algebra.tensorH1CotangentOfFlat_tmul, one_smul]
  exact h1Cotangent_map_map R S R' (R' ⊗[R] S) R' S' x

/-- **Flat base change for `H₁` of the naive cotangent complex.** If `S'` is the base change of
`S` along a flat ring map `R → R'`, then the canonical map `H₁(L_{S/R}) → H₁(L_{S'/R'})` exhibits
its target as the base change of its source along `S → S'`. -/
lemma isBaseChange_h1Cotangent_map (R S R' S' : Type*) [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    [Algebra.IsPushout R R' S S'] [Module.Flat R R'] :
    IsBaseChange S' (Algebra.H1Cotangent.map R R' S S') :=
  isBaseChange_of_isBaseChange_of_isPushout _
    (isBaseChange_restrictScalars_h1Cotangent_map R S R' S')

end Stacks.Cotangent.H1BaseChange

end
