module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksCore.Tactic.StacksAttribute

/-!
# Stalks of a change-of-rings tensor product

Let `X` be a topological space, `α : O ⟶ O'` a morphism of presheaves (resp. sheaves) of
commutative rings on `X`, and `F` a presheaf (resp. sheaf) of `O`-modules.

The stalk at `x` of the change-of-rings tensor product presheaf `F ⊗_{p,O} O'` (Stacks Tag 006P)
is `F_x ⊗_{O_x} O'_x` (Stacks Tag 007K, Lemma 6.20.2); no sheaf condition is needed. For `O, O'`
sheaves of commutative rings and `F` a sheaf of `O`-modules, the same holds for the tensor product
sheaf `F ⊗_O O'`, the sheafification of `F ⊗_{p,O} O'`, a sheaf of `O'`-modules (Stacks Tag 0089):
`F_x ⊗_{O_x} O'_x ≅ (F ⊗_O O')_x` (Stacks Tag 008B, Lemma 6.20.3).

## Main definitions

* `rightTensorModule`: the `A`-module structure on `M ⊗[R] A` with `A` acting on the right factor.
* `tensorPresheafOfModules`: the tensor product presheaf `F ⊗_{p,O} O'` of `O'`-modules.
* `tensorSheaf`: the tensor product sheaf `F ⊗_O O'` of `O'`-modules.

## Main results

* `tensorPresheafStalkIso`: the `O'_x`-linear equivalence `F_x ⊗_{O_x} O'_x ≃ₗ (F ⊗_{p,O} O')_x`.
* `tensorSheafStalkIso`: the `O'_x`-linear equivalence `(F ⊗_{p,O} O')_x ≃ₗ (F ⊗_O O')_x`.
* `mainIso`: the `O'_x`-linear equivalence `F_x ⊗_{O_x} O'_x ≃ₗ (F ⊗_O O')_x`.

## Implementation notes

The Stacks Project writes `=` for these canonical identifications, which are formalized here as
`O'_x`-linear equivalences `≃ₗ`. The tags write `F ⊗_O O'` with the algebra on the right, whereas
Mathlib's canonical module structure is on `A ⊗[R] M` with the algebra on the left; so
`rightTensorModule` supplies the `A`-module structure on `M ⊗[R] A` given by
`a • (m ⊗ b) = m ⊗ (a * b)`, while the tensor presheaf itself is built in the equivalent
orientation `U ↦ O'(U) ⊗_{O(U)} F(U)`. The resulting use of `TensorProduct.comm` is absorbed into
the comparison isomorphisms, whose stated orientation is the tags'.

**Universes.** Outside the `RightModule` section (which is plain algebra and is polymorphic
in three independent universes) everything is stated at a single universe `u` carrying the
space, the rings and the module sections together.  That single universe is forced, not
chosen: Mathlib's module structure on a stalk (`PresheafOfModules.germ_smul`,
`PresheafOfModules.germ_ringCat_smul`) is stated for
`{X : TopCat.{u}} {R : X.Presheaf RingCat.{u}} (M : PresheafOfModules.{u} R)`, the filtered
colimit computing the stalk being indexed by the opens of `X` and taken in `Ab.{u}`.  The
`CommRingCat`, `RingCat`, `Ab`, `PresheafOfModules` and `SheafOfModules` arguments must be
written `.{u}`: left implicit they default to `0` and silently collapse every universe in the
statement.  This includes the `forget₂ CommRingCat.{u} RingCat.{u}` in `ringPresheaf` and
`ringSheaf`, where the bare spelling pins the whole file at `0`.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopCat TensorProduct

universe u

namespace Stacks.Sheafify.ModuleStalkTensor

/-! ## The right-factor module structure on `M ⊗[R] A`

Mathlib only provides a canonical `A`-module structure on `A ⊗[R] M` (algebra on the left).
Here `A` acts on `M ⊗[R] A` through the right factor, by `a • (m ⊗ b) = m ⊗ (a * b)`. -/

section RightModule

variable (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- The right-factor scalar multiplication of `A` on `M ⊗[R] A`:
`a • x = (id_M ⊗ (· * a)) x`. -/
@[reducible] noncomputable def rSMul : SMul A (TensorProduct R M A) where
  smul a x := LinearMap.lTensor M (LinearMap.mulLeft R a) x

attribute [local instance] rSMul

/-- The right `A`-action `rSMul` on `M ⊗[R] A` is multiplication by `a` on the right factor,
tensored with the identity on `M`. -/
theorem rSMul_def (a : A) (x : TensorProduct R M A) :
    a • x = LinearMap.lTensor M (LinearMap.mulLeft R a) x := rfl

/-- The right `A`-action of `rSMul` on a pure tensor multiplies the right factor. -/
theorem rSMul_tmul (a : A) (m : M) (b : A) :
    a • (m ⊗ₜ[R] b) = m ⊗ₜ[R] (a * b) := by
  rw [rSMul_def]; simp [LinearMap.lTensor_tmul]

/-- The canonical `A`-module structure on `M ⊗[R] A`, with `A` acting on the right factor. -/
@[reducible] noncomputable def rightTensorModule : Module A (TensorProduct R M A) where
  one_smul x := by rw [rSMul_def]; simp
  mul_smul a b x := by
    rw [rSMul_def, rSMul_def, rSMul_def, ← LinearMap.lTensor_comp_apply]
    congr 1; ext y; simp
  smul_zero a := by rw [rSMul_def]; simp
  smul_add a x y := by rw [rSMul_def, rSMul_def, rSMul_def]; simp
  add_smul a b x := by
    rw [rSMul_def, rSMul_def, rSMul_def]
    have h : LinearMap.mulLeft R (a + b) = LinearMap.mulLeft R a + LinearMap.mulLeft R b := by
      ext y; simp [add_mul]
    rw [h]; simp [LinearMap.lTensor_add]
  zero_smul x := by rw [rSMul_def]; simp

/-- The action of `A` on a pure tensor for the `rightTensorModule` structure:
`a • (m ⊗ b) = m ⊗ (a * b)`. -/
theorem rightTensorModule_smul_tmul (a : A) (m : M) (b : A) :
    letI := rightTensorModule R A M
    a • (m ⊗ₜ[R] b) = m ⊗ₜ[R] (a * b) := by
  let := rightTensorModule R A M
  exact rSMul_tmul R A M a m b

end RightModule

/-- The presheaf of (not necessarily commutative) rings (`RingCat`-valued) underlying a presheaf
of commutative rings, obtained by composing with the forgetful functor `CommRingCat ⥤ RingCat`. -/
abbrev ringPresheaf {X : TopCat.{u}} (O : TopCat.Presheaf CommRingCat.{u} X) :
    (TopologicalSpace.Opens X)ᵒᵖ ⥤ RingCat.{u} :=
  O ⋙ forget₂ CommRingCat.{u} RingCat.{u}

/-- The sheaf of (not necessarily commutative) rings (`RingCat`-valued) underlying a sheaf of
commutative rings, obtained by composing with the forgetful functor `CommRingCat ⥤ RingCat`. -/
abbrev ringSheaf {X : TopCat.{u}} (O : TopCat.Sheaf CommRingCat.{u} X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  (CategoryTheory.sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj O

section Construction

variable {X : TopCat.{u}}
variable (O O' : TopCat.Presheaf CommRingCat.{u} X) (α : O ⟶ O')
  (F : PresheafOfModules.{u} (ringPresheaf O))

/-- The restriction map of `F` packaged as an `(O.map i)`-semilinear map `F(U) → F(V)`. -/
noncomputable def fSemilin (U V : (TopologicalSpace.Opens X)ᵒᵖ) (i : U ⟶ V) :
    F.obj U →ₛₗ[(O.map i).hom] F.obj V where
  toFun := fun m => F.map i m
  map_add' := by intro a b; exact map_add _ a b
  map_smul' := by intro r m; exact PresheafOfModules.map_smul F i r m

/-- `fSemilin` is the restriction map of `F`. -/
@[simp]
theorem fSemilin_apply (U V : (TopologicalSpace.Opens X)ᵒᵖ) (i : U ⟶ V) (m : F.obj U) :
    fSemilin O F U V i m = F.map i m := rfl

/-- The restriction map of `O'` packaged as an `(O.map i)`-semilinear map `O'(U) → O'(V)`,
where `O'(U)` is regarded as an `O(U)`-module via `α`. -/
noncomputable def o'Semilin (U V : (TopologicalSpace.Opens X)ᵒᵖ) (i : U ⟶ V) :
    letI := (α.app U).hom.toAlgebra
    letI := (α.app V).hom.toAlgebra
    O'.obj U →ₛₗ[(O.map i).hom] O'.obj V :=
  letI := (α.app U).hom.toAlgebra
  letI := (α.app V).hom.toAlgebra
  { toFun := fun s => (O'.map i).hom s
    map_add' := by intro a b; exact map_add _ a b
    map_smul' := by
      intro r s
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra,
        RingHom.algebraMap_toAlgebra]
      congr 1
      have h := congrArg
        (fun (g : O.obj U ⟶ O'.obj V) => g.hom r) (α.naturality i)
      simp only [CommRingCat.comp_apply] at h
      exact h.symm }

/-- `o'Semilin` is the restriction map of `O'`. -/
@[simp]
theorem o'Semilin_apply (U V : (TopologicalSpace.Opens X)ᵒᵖ) (i : U ⟶ V) (s : O'.obj U) :
    letI := (α.app U).hom.toAlgebra
    letI := (α.app V).hom.toAlgebra
    o'Semilin O O' α U V i s = (O'.map i).hom s := rfl

/-- The underlying abelian-group-valued presheaf of the tensor product presheaf, built in the
auxiliary orientation `U ↦ O'(U) ⊗_{O(U)} F(U)` (canonically isomorphic to the tags'
`F(U) ⊗_{O(U)} O'(U)` via `TensorProduct.comm`), with restriction maps
`TensorProduct.map (O'.map i) (F.map i)`. -/
@[implicit_reducible]
noncomputable def tensorAbPresheaf : (TopologicalSpace.Opens X)ᵒᵖ ⥤ Ab.{u} where
  obj U :=
    letI := (α.app U).hom.toAlgebra
    AddCommGrpCat.of (TensorProduct (O.obj U) (O'.obj U) (F.obj U))
  map {U V} i :=
    letI := (α.app U).hom.toAlgebra
    letI := (α.app V).hom.toAlgebra
    AddCommGrpCat.ofHom
      (TensorProduct.map (o'Semilin O O' α U V i) (fSemilin O F U V i)).toAddMonoidHom
  map_id U := by
    let := (α.app U).hom.toAlgebra
    apply AddCommGrpCat.hom_ext
    refine AddMonoidHom.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      simp only [AddCommGrpCat.hom_ofHom, AddCommGrpCat.hom_id, LinearMap.toAddMonoidHom_coe,
        AddMonoidHom.id_apply, TensorProduct.map_tmul, o'Semilin_apply, fSemilin_apply, O'.map_id,
        ← PresheafOfModules.presheaf_map_apply_coe, F.presheaf.map_id]
      simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  map_comp {U V W} i j := by
    let := (α.app U).hom.toAlgebra
    let := (α.app V).hom.toAlgebra
    let := (α.app W).hom.toAlgebra
    apply AddCommGrpCat.hom_ext
    refine AddMonoidHom.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      simp only [AddCommGrpCat.hom_ofHom, AddCommGrpCat.hom_comp, LinearMap.toAddMonoidHom_coe,
        AddMonoidHom.comp_apply, TensorProduct.map_tmul, o'Semilin_apply, fSemilin_apply,
        O'.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]
      rw [PresheafOfModules.map_comp_apply]
    | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- The restriction maps of `tensorAbPresheaf` are `TensorProduct.map` of the restriction maps
of `O'` and `F`. -/
@[simp]
theorem tensorAbPresheaf_map_apply {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V)
    (t : (tensorAbPresheaf O O' α F).obj U) :
    letI := (α.app U).hom.toAlgebra
    letI := (α.app V).hom.toAlgebra
    (tensorAbPresheaf O O' α F).map i t
      = TensorProduct.map (o'Semilin O O' α U V i) (fSemilin O F U V i) t := rfl

/-- The natural `O'(U)`-module structure on the value `O'(U) ⊗_{O(U)} F(U)` of the tensor
product presheaf (acting through the left/`O'(U)` factor). -/
noncomputable instance tensorAbModule (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    Module ((ringPresheaf O').obj U) ((tensorAbPresheaf O O' α F).obj U) :=
  letI := (α.app U).hom.toAlgebra
  (inferInstance : Module (O'.obj U) (TensorProduct (O.obj U) (O'.obj U) (F.obj U)))

/-- The restriction map of the tensor product presheaf as an `(O'.map i)`-semilinear map
between the `O'(U)`- and `O'(V)`-modules `O'(U) ⊗_{O(U)} F(U)` and `O'(V) ⊗_{O(V)} F(V)`. -/
noncomputable def tensorSemilin (U V : (TopologicalSpace.Opens X)ᵒᵖ) (i : U ⟶ V) :
    letI := (α.app U).hom.toAlgebra
    letI := (α.app V).hom.toAlgebra
    (TensorProduct (O.obj U) (O'.obj U) (F.obj U))
      →ₛₗ[(O'.map i).hom]
        (TensorProduct (O.obj V) (O'.obj V) (F.obj V)) :=
  letI := (α.app U).hom.toAlgebra
  letI := (α.app V).hom.toAlgebra
  { toFun := fun x => TensorProduct.map (o'Semilin O O' α U V i) (fSemilin O F U V i) x
    map_add' := by intro a b; exact map_add _ a b
    map_smul' := by
      intro r x
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | tmul s m =>
        rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
            TensorProduct.smul_tmul']
        congr 1
        rw [o'Semilin_apply, o'Semilin_apply, smul_eq_mul, smul_eq_mul, map_mul]
      | add a b ha hb => rw [smul_add, map_add, map_add, smul_add, ha, hb] }

/-- `tensorSemilin` is `TensorProduct.map` of the restriction maps of `O'` and `F`. -/
@[simp]
theorem tensorSemilin_apply (U V : (TopologicalSpace.Opens X)ᵒᵖ) (i : U ⟶ V) :
    letI := (α.app U).hom.toAlgebra
    letI := (α.app V).hom.toAlgebra
    ∀ t : TensorProduct (O.obj U) (O'.obj U) (F.obj U),
      tensorSemilin O O' α F U V i t
        = TensorProduct.map (o'Semilin O O' α U V i) (fSemilin O F U V i) t := fun _ => rfl

/-- **The tensor product presheaf `F ⊗_{p,O} O'`.**  The presheaf of `O'`-modules modeling
`U ↦ F(U) ⊗_{O(U)} O'(U)` (Stacks Tag 006P), implemented in the canonically isomorphic
orientation `U ↦ O'(U) ⊗_{O(U)} F(U)`. -/
noncomputable def tensorPresheafOfModules : PresheafOfModules.{u} (ringPresheaf O') :=
  @PresheafOfModules.ofPresheaf _ _ (ringPresheaf O') (tensorAbPresheaf O O' α F)
    (tensorAbModule O O' α F)
    (fun {U V} i r x => (tensorSemilin O O' α F U V i).map_smul' r x)

end Construction

section Statements

variable {X : TopCat.{u}}
variable (O O' : TopCat.Presheaf CommRingCat.{u} X) (α : O ⟶ O')
  (F : PresheafOfModules.{u} (ringPresheaf O)) (x : X)

/-- The ring homomorphism `O_x → O'_x` on stalks at `x` induced by `α`. -/
noncomputable def stalkHom : O.stalk x ⟶ O'.stalk x :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map α

/-- Three stalk elements, of an `Ab`-presheaf and of two ring presheaves, are germs of sections
over a common open neighbourhood of `x`. -/
private theorem exists_germ_eq_triple (P : TopCat.Presheaf Ab.{u} X)
    (Q R : TopCat.Presheaf CommRingCat.{u} X) (p : P.stalk x) (q : Q.stalk x) (r : R.stalk x) :
    ∃ (W : TopologicalSpace.Opens X) (hx : x ∈ W) (p' : P.obj (Opposite.op W))
      (q' : Q.obj (Opposite.op W)) (r' : R.obj (Opposite.op W)),
      P.germ W x hx p' = p ∧ Q.germ W x hx q' = q ∧ R.germ W x hx r' = r := by
  obtain ⟨U, hU, p', rfl⟩ := P.exists_germ_eq p
  obtain ⟨V, hV, q', rfl⟩ := Q.exists_germ_eq q
  obtain ⟨T, hT, r', rfl⟩ := R.exists_germ_eq r
  exact ⟨U ⊓ V ⊓ T, ⟨⟨hU, hV⟩, hT⟩, P.map (homOfLE (inf_le_left.trans inf_le_left)).op p',
    Q.map (homOfLE (inf_le_left.trans inf_le_right)).op q', R.map (homOfLE inf_le_right).op r',
    by simp, by simp, by simp⟩

/-! ### The presheaf comparison isomorphism (Stacks Tag 007K)

The `O'_x`-linear equivalence `F_x ⊗_{O_x} O'_x ≃ₗ (F ⊗_{p,O} O')_x`: filtered colimits commute
with tensor products of modules. -/

/-- The germ map `O'(W) ⊗_{O(W)} F(W) → (F ⊗_{p,O} O')_x` at an open `W ∋ x` of the abelian group
presheaf underlying `tensorPresheafOfModules`. -/
noncomputable abbrev tensorPresheafGerm (W : TopologicalSpace.Opens X) (hx : x ∈ W) :
    (tensorPresheafOfModules O O' α F).presheaf.obj (Opposite.op W) →
      TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x :=
  fun t => TopCat.Presheaf.germ (tensorPresheafOfModules O O' α F).presheaf W x hx t

section Helpers

/-- The germ of a pure tensor `s ⊗ₜ m` over an open `W ∋ x`, as an element of the stalk
`(tensorPresheafOfModules)_x`. -/
noncomputable def germTmul (W : TopologicalSpace.Opens X) (hx : x ∈ W)
    (s : O'.obj (Opposite.op W)) (m : F.obj (Opposite.op W)) :
    TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x :=
  letI := (α.app (Opposite.op W)).hom.toAlgebra
  TopCat.Presheaf.germ (tensorPresheafOfModules O O' α F).presheaf W x hx
    (s ⊗ₜ[O.obj (Opposite.op W)] m)

set_option backward.isDefEq.respectTransparency true in
/-- Restriction on a pure tensor in the tensor presheaf. -/
theorem tensorPresheaf_map_tmul (W W' : TopologicalSpace.Opens X)
    (j : W' ⟶ W)
    (s : O'.obj (Opposite.op W)) (m : F.obj (Opposite.op W)) :
    letI := (α.app (Opposite.op W)).hom.toAlgebra
    letI := (α.app (Opposite.op W')).hom.toAlgebra
    (tensorPresheafOfModules O O' α F).presheaf.map j.op (s ⊗ₜ[O.obj (Opposite.op W)] m)
      = (O'.map j.op).hom s ⊗ₜ[O.obj (Opposite.op W')] (F.map j.op m) := by
  let := (α.app (Opposite.op W)).hom.toAlgebra
  let := (α.app (Opposite.op W')).hom.toAlgebra
  simp [tensorPresheafOfModules]
  rfl

/-- `germTmul` is invariant under restricting both representatives to a smaller open. -/
theorem germTmul_res (W W' : TopologicalSpace.Opens X) (hx : x ∈ W) (hx' : x ∈ W')
    (j : W' ⟶ W)
    (s : O'.obj (Opposite.op W)) (m : F.obj (Opposite.op W)) :
    germTmul O O' α F x W' hx' ((O'.map j.op).hom s) (F.map j.op m)
      = germTmul O O' α F x W hx s m := by
  let := (α.app (Opposite.op W)).hom.toAlgebra
  let := (α.app (Opposite.op W')).hom.toAlgebra
  unfold germTmul
  rw [← tensorPresheaf_map_tmul O O' α F W W' j s m]
  exact TopCat.Presheaf.germ_res_apply (tensorPresheafOfModules O O' α F).presheaf j x hx'
    (s ⊗ₜ[O.obj (Opposite.op W)] m)

/-- The germ `germTmul` of a pure tensor depends only on the germs of its factors, given by
representatives over the opens `W` resp. `W'`. -/
theorem germTmul_wd (W W' : TopologicalSpace.Opens X)
    (hxW : x ∈ W) (hxW' : x ∈ W')
    (s : O'.obj (Opposite.op W)) (s' : O'.obj (Opposite.op W'))
    (m : F.obj (Opposite.op W)) (m' : F.obj (Opposite.op W'))
    (hs : TopCat.Presheaf.germ O' W x hxW s
      = TopCat.Presheaf.germ O' W' x hxW' s')
    (hm : TopCat.Presheaf.germ F.presheaf W x hxW m
        = TopCat.Presheaf.germ F.presheaf W' x hxW' m') :
    germTmul O O' α F x W hxW s m = germTmul O O' α F x W' hxW' s' m' := by
  obtain ⟨A, hxA, jWA, jW'A, hsA⟩ := TopCat.Presheaf.germ_eq O' x hxW hxW' s s' hs
  obtain ⟨B, hxB, kWB, kW'B, hmB⟩ := TopCat.Presheaf.germ_eq F.presheaf x hxW hxW' m m' hm
  set Z : TopologicalSpace.Opens X := A ⊓ B with hZ
  have hxZ : x ∈ Z := ⟨hxA, hxB⟩
  set pA : Z ⟶ A := homOfLE inf_le_left
  set pB : Z ⟶ B := homOfLE inf_le_right
  have hZW : Z ≤ W := le_trans inf_le_left (leOfHom jWA)
  have hZW' : Z ≤ W' := le_trans inf_le_left (leOfHom jW'A)
  set jZW : Z ⟶ W := homOfLE hZW
  set jZW' : Z ⟶ W' := homOfLE hZW'
  rw [← germTmul_res O O' α F x W Z hxW hxZ jZW s m,
      ← germTmul_res O O' α F x W' Z hxW' hxZ jZW' s' m']
  congr 1
  · have e : ∀ {V} (k : Z ⟶ V) (l : A ⟶ V) (t : O'.obj (Opposite.op V)),
        (O'.map k.op).hom t = (O'.map pA.op).hom ((O'.map l.op).hom t) := fun k l t => by
      rw [← CommRingCat.comp_apply, ← O'.map_comp]
      congr 1
    rw [e jZW jWA, e jZW' jW'A, hsA]
  · have e : ∀ {V} (k : Z ⟶ V) (l : B ⟶ V) (t : F.obj (Opposite.op V)),
        F.map k.op t = F.presheaf.map pB.op (F.presheaf.map l.op t) := fun k l t => by
      change F.presheaf.map k.op t = _
      rw [show k.op = l.op ≫ pB.op from Subsingleton.elim _ _, F.presheaf.map_comp]; rfl
    rw [e jZW kWB, e jZW' kW'B, hmB]

end Helpers

section RawB

/-- The function `F_x → O'_x → (F ⊗_{p,O} O')_x` sending `germ_x m` and `germ_x s` to the germ of
`s ⊗ m`, computed on chosen representatives (`exists_germ_eq`) restricted to the intersection of
their opens. -/
noncomputable def rawB
    (mx : TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    (sx : O'.stalk x) :
    TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x :=
  germTmul O O' α F x
    ((TopCat.Presheaf.exists_germ_eq F.presheaf mx).choose ⊓
     (TopCat.Presheaf.exists_germ_eq O' sx).choose)
    ⟨(TopCat.Presheaf.exists_germ_eq F.presheaf mx).choose_spec.choose,
     (TopCat.Presheaf.exists_germ_eq O' sx).choose_spec.choose⟩
    ((O'.map (homOfLE inf_le_right).op).hom
      (TopCat.Presheaf.exists_germ_eq O' sx).choose_spec.choose_spec.choose)
    (F.map (homOfLE inf_le_left).op
      (TopCat.Presheaf.exists_germ_eq F.presheaf mx).choose_spec.choose_spec.choose)

/-- The defining reduction of `rawB`: over any common open `W` with representatives, `rawB`
of the germs equals `germTmul`. -/
theorem rawB_germ (W : TopologicalSpace.Opens X) (hxW : x ∈ W)
    (s : O'.obj (Opposite.op W)) (m : F.obj (Opposite.op W)) :
    rawB O O' α F x (TopCat.Presheaf.germ F.presheaf W x hxW m)
        (TopCat.Presheaf.germ O' W x hxW s)
      = germTmul O O' α F x W hxW s m := by
  set mx := TopCat.Presheaf.germ F.presheaf W x hxW m with hmx
  set sx := TopCat.Presheaf.germ O' W x hxW s with hsx
  have specU :=
    (TopCat.Presheaf.exists_germ_eq F.presheaf mx).choose_spec.choose_spec.choose_spec
  have specV := (TopCat.Presheaf.exists_germ_eq O' sx).choose_spec.choose_spec.choose_spec
  unfold rawB
  apply germTmul_wd O O' α F x _ W _ hxW
  · rw [TopCat.Presheaf.germ_res_apply O' (homOfLE inf_le_right) x _
      (TopCat.Presheaf.exists_germ_eq O' sx).choose_spec.choose_spec.choose]
    rw [specV, hsx]
  · erw [TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE inf_le_left) x _
      (TopCat.Presheaf.exists_germ_eq F.presheaf mx).choose_spec.choose_spec.choose]
    rw [specU, hmx]

/-- `germTmul` is additive in the `O'`-argument. -/
theorem germTmul_add_s (W : TopologicalSpace.Opens X) (hx : x ∈ W)
    (s s' : O'.obj (Opposite.op W)) (m : F.obj (Opposite.op W)) :
    germTmul O O' α F x W hx (s + s') m
      = germTmul O O' α F x W hx s m + germTmul O O' α F x W hx s' m := by
  let := (α.app (Opposite.op W)).hom.toAlgebra
  unfold germTmul
  rw [TensorProduct.add_tmul, map_add]

/-- `germTmul` is additive in the `F`-argument. -/
theorem germTmul_add_m (W : TopologicalSpace.Opens X) (hx : x ∈ W)
    (s : O'.obj (Opposite.op W)) (m m' : F.obj (Opposite.op W)) :
    germTmul O O' α F x W hx s (m + m')
      = germTmul O O' α F x W hx s m + germTmul O O' α F x W hx s m' := by
  let := (α.app (Opposite.op W)).hom.toAlgebra
  unfold germTmul
  rw [TensorProduct.tmul_add, map_add]

/-- `germTmul` of a zero `O'`-section is zero. -/
theorem germTmul_zero_s (W : TopologicalSpace.Opens X) (hx : x ∈ W)
    (m : F.obj (Opposite.op W)) :
    germTmul O O' α F x W hx 0 m = 0 := by
  let := (α.app (Opposite.op W)).hom.toAlgebra
  unfold germTmul
  rw [TensorProduct.zero_tmul, map_zero]

/-- `germTmul` of a zero `F`-section is zero. -/
theorem germTmul_zero_m (W : TopologicalSpace.Opens X) (hx : x ∈ W)
    (s : O'.obj (Opposite.op W)) :
    germTmul O O' α F x W hx s 0 = 0 := by
  let := (α.app (Opposite.op W)).hom.toAlgebra
  unfold germTmul
  rw [TensorProduct.tmul_zero, map_zero]

/-- Stalk-hom commutes with germs: `stalkHom (germ r) = germ (αW r)`. -/
theorem stalkHom_germ (W : TopologicalSpace.Opens X) (hx : x ∈ W)
    (r : O.obj (Opposite.op W)) :
    (stalkHom O O' α x).hom (TopCat.Presheaf.germ O W x hx r)
      = TopCat.Presheaf.germ O' W x hx ((α.app (Opposite.op W)).hom r) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply W x hx α r

/-- The `O'(W)`-action on the tensor presheaf value acts on the left factor. -/
theorem o'_smul_tmul (W : TopologicalSpace.Opens X)
    (a s : O'.obj (Opposite.op W)) (m : F.obj (Opposite.op W)) :
    letI := (α.app (Opposite.op W)).hom.toAlgebra
    a • (s ⊗ₜ[O.obj (Opposite.op W)] m)
      = (a * s) ⊗ₜ[O.obj (Opposite.op W)] m := by
  let := (α.app (Opposite.op W)).hom.toAlgebra
  exact TensorProduct.smul_tmul' a s m

/-- The `O'_x`-action on the germ of a pure tensor multiplies into the left factor. -/
theorem germTmul_smul (W : TopologicalSpace.Opens X) (hx : x ∈ W)
    (a s : O'.obj (Opposite.op W)) (m : F.obj (Opposite.op W)) :
    (TopCat.Presheaf.germ O' W x hx a) • germTmul O O' α F x W hx s m
      = germTmul O O' α F x W hx (a * s) m := by
  let := (α.app (Opposite.op W)).hom.toAlgebra
  unfold germTmul
  rw [← PresheafOfModules.germ_smul (R := O') (tensorPresheafOfModules O O' α F) x W hx a
        (s ⊗ₜ[O.obj (Opposite.op W)] m)]
  rw [o'_smul_tmul O O' α F W a s m]

/-- An `O(W)`-scalar moves across the tensor in `germTmul`. -/
theorem germTmul_balance (W : TopologicalSpace.Opens X) (hx : x ∈ W)
    (r0 : O.obj (Opposite.op W)) (s : O'.obj (Opposite.op W))
    (m : F.obj (Opposite.op W)) :
    letI := (α.app (Opposite.op W)).hom.toAlgebra
    germTmul O O' α F x W hx ((α.app (Opposite.op W)).hom r0 * s) m
      = germTmul O O' α F x W hx s (r0 • m) := by
  let := (α.app (Opposite.op W)).hom.toAlgebra
  unfold germTmul
  congr 1
  rw [← (α.app (Opposite.op W)).hom.smul_toAlgebra r0 s, TensorProduct.smul_tmul]

/-- `rawB` is additive in its `O'_x`-argument. -/
theorem rawB_add_right (mx : TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    (sx sx' : O'.stalk x) :
    rawB O O' α F x mx (sx + sx')
      = rawB O O' α F x mx sx + rawB O O' α F x mx sx' := by
  obtain ⟨W, hxW, m, s, s', rfl, rfl, rfl⟩ := exists_germ_eq_triple x F.presheaf O' O' mx sx sx'
  rw [← map_add (ConcreteCategory.hom (TopCat.Presheaf.germ O' W x hxW)),
      rawB_germ, rawB_germ, rawB_germ, germTmul_add_s]

/-- `rawB` is additive in its `F_x`-argument. -/
theorem rawB_add_left (mx mx' : TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    (sx : O'.stalk x) :
    rawB O O' α F x (mx + mx') sx
      = rawB O O' α F x mx sx + rawB O O' α F x mx' sx := by
  obtain ⟨U, hU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf mx
  obtain ⟨U', hU', m', rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf mx'
  obtain ⟨V, hV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq O' sx
  set W : TopologicalSpace.Opens X := U ⊓ U' ⊓ V
  have hxW : x ∈ W := ⟨⟨hU, hU'⟩, hV⟩
  have jU : W ⟶ U := homOfLE (le_trans inf_le_left inf_le_left)
  have jU' : W ⟶ U' := homOfLE (le_trans inf_le_left inf_le_right)
  have jV : W ⟶ V := homOfLE inf_le_right
  rw [← TopCat.Presheaf.germ_res_apply F.presheaf jU x hxW m,
      ← TopCat.Presheaf.germ_res_apply F.presheaf jU' x hxW m',
      ← TopCat.Presheaf.germ_res_apply O' jV x hxW s,
      ← map_add (ConcreteCategory.hom (TopCat.Presheaf.germ F.presheaf W x hxW)),
      rawB_germ, rawB_germ, rawB_germ, germTmul_add_m]

/-- An `O'_x`-scalar in the `O'_x`-argument of `rawB` becomes the `O'_x`-action on the value. -/
theorem rawB_mul_right (mx : TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    (t sx : O'.stalk x) :
    rawB O O' α F x mx (t * sx) = t • rawB O O' α F x mx sx := by
  obtain ⟨W, hxW, m, a, s, rfl, rfl, rfl⟩ := exists_germ_eq_triple x F.presheaf O' O' mx t sx
  rw [← map_mul (ConcreteCategory.hom (TopCat.Presheaf.germ O' W x hxW)),
      rawB_germ, rawB_germ, germTmul_smul]

/-- An `O_x`-scalar in the `F_x`-argument of `rawB` becomes the `O'_x`-action along `stalkHom`. -/
theorem rawB_smul_left (r : O.stalk x)
    (mx : TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x) (sx : O'.stalk x) :
    rawB O O' α F x (r • mx) sx
      = (stalkHom O O' α x).hom r • rawB O O' α F x mx sx := by
  obtain ⟨W, hxW, m, r0, s, rfl, rfl, rfl⟩ := exists_germ_eq_triple x F.presheaf O O' mx r sx
  erw [← PresheafOfModules.germ_smul (R := O) F x W hxW r0 m]
  rw [rawB_germ, rawB_germ, stalkHom_germ O O' α x W hxW r0, germTmul_smul, germTmul_balance]

end RawB

/-- The `O_x`-bilinear map `F_x → O'_x → (F ⊗_{p,O} O')_x` sending `(germ_x m, germ_x s)` to
`germ_x (s|_W ⊗ m|_W)` for a common neighborhood `W` of `x`. -/
noncomputable def tensorPresheafStalk_bilinMap :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI : Module (O.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x) :=
      Module.compHom _ (stalkHom O O' α x).hom
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x) →ₗ[O.stalk x]
      (O'.stalk x) →ₗ[O.stalk x]
        (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x) := by
  letI := (stalkHom O O' α x).hom.toAlgebra
  letI : Module (O.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x) :=
    Module.compHom _ (stalkHom O O' α x).hom
  exact
    { toFun := fun mx =>
        { toFun := rawB O O' α F x mx
          map_add' := rawB_add_right O O' α F x mx
          map_smul' := fun r sx =>
            rawB_mul_right O O' α F x mx ((stalkHom O O' α x).hom r) sx }
      map_add' := fun mx mx' => LinearMap.ext (rawB_add_left O O' α F x mx mx')
      map_smul' := fun r mx => LinearMap.ext (rawB_smul_left O O' α F x r mx) }

/-- `tensorPresheafStalk_bilinMap` evaluates to `rawB`. -/
theorem tensorPresheafStalk_bilinMap_apply (mx : TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    (sx : O'.stalk x) :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI : Module (O.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x) :=
      Module.compHom _ (stalkHom O O' α x).hom
    tensorPresheafStalk_bilinMap O O' α F x mx sx = rawB O O' α F x mx sx := rfl

/-- For an open `W ∋ x`, `m ∈ F(W)` and `s ∈ O'(W)`, `tensorPresheafStalk_bilinMap` sends the
two germs to the germ of the pure tensor `s ⊗ₜ m ∈ O'(W) ⊗_{O(W)} F(W)`. -/
theorem tensorPresheafStalk_bilinMap_tmul
    (W : TopologicalSpace.Opens X) (hx : x ∈ W)
    (m : F.obj (Opposite.op W)) (s : O'.obj (Opposite.op W)) :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI : Module (O.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x) :=
      Module.compHom _ (stalkHom O O' α x).hom
    letI := (α.app (Opposite.op W)).hom.toAlgebra
    tensorPresheafStalk_bilinMap O O' α F x
        (TopCat.Presheaf.germ F.presheaf W x hx m)
        (TopCat.Presheaf.germ O' W x hx s)
      = tensorPresheafGerm O O' α F x W hx (s ⊗ₜ[O.obj (Opposite.op W)] m) := by
  rw [tensorPresheafStalk_bilinMap_apply, rawB_germ, germTmul]

/-- The lift of `tensorPresheafStalk_bilinMap` is `O'_x`-linear for the right-factor action on
`F_x ⊗_{O_x} O'_x`. -/
theorem lift_bilinMap_smul :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI := rightTensorModule (O.stalk x) (O'.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    letI : Module (O.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x) :=
      Module.compHom _ (stalkHom O O' α x).hom
    ∀ (a : O'.stalk x) (z : TensorProduct (O.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x) (O'.stalk x)),
      TensorProduct.lift (tensorPresheafStalk_bilinMap O O' α F x) (a • z)
        = a • TensorProduct.lift (tensorPresheafStalk_bilinMap O O' α F x) z := by
  let := (stalkHom O O' α x).hom.toAlgebra
  let := rightTensorModule (O.stalk x) (O'.stalk x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
  let : Module (O.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x) :=
    Module.compHom _ (stalkHom O O' α x).hom
  intro a z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => rw [smul_add, map_add, map_add, smul_add, hz, hz']
  | tmul mx sx =>
      rw [rightTensorModule_smul_tmul, TensorProduct.lift.tmul, TensorProduct.lift.tmul]
      exact rawB_mul_right O O' α F x mx a sx

/-- The `O'_x`-linear map `F_x ⊗_{O_x} O'_x → (F ⊗_{p,O} O')_x`, the map
`TensorProduct.lift (tensorPresheafStalk_bilinMap …)`, linear for the right-factor action. -/
noncomputable def tensorPresheafStalk_fwdMap :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI := rightTensorModule (O.stalk x) (O'.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    (TensorProduct (O.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
        (O'.stalk x))
      →ₗ[O'.stalk x]
        (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x) :=
  letI := (stalkHom O O' α x).hom.toAlgebra
  letI := rightTensorModule (O.stalk x) (O'.stalk x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
  letI : Module (O.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x) :=
    Module.compHom _ (stalkHom O O' α x).hom
  let Φ₀ := TensorProduct.lift (tensorPresheafStalk_bilinMap O O' α F x)
  { toFun := Φ₀
    map_add' := Φ₀.map_add
    map_smul' := lift_bilinMap_smul O O' α F x }

/-- `tensorPresheafStalk_fwdMap` is `TensorProduct.lift` of `tensorPresheafStalk_bilinMap`. -/
theorem tensorPresheafStalk_fwdMap_apply :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI := rightTensorModule (O.stalk x) (O'.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    letI : Module (O.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x) :=
      Module.compHom _ (stalkHom O O' α x).hom
    ∀ z : TensorProduct (O.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x) (O'.stalk x),
      tensorPresheafStalk_fwdMap O O' α F x z
        = TensorProduct.lift (tensorPresheafStalk_bilinMap O O' α F x) z := fun _ => rfl

/-- There is an `O'_x`-linear map `F_x ⊗_{O_x} O'_x → (F ⊗_{p,O} O')_x`. -/
theorem tensorPresheafStalk_toFun :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI := rightTensorModule (O.stalk x) (O'.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    Nonempty
      ((TensorProduct (O.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
          (O'.stalk x))
        →ₗ[O'.stalk x]
          (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x)) :=
  ⟨tensorPresheafStalk_fwdMap O O' α F x⟩

section InvMap

/-- The pure tensor `germ_x m ⊗ germ_x s` in `F_x ⊗_{O_x} O'_x` (the factors in the order
opposite to `germTmul`). -/
noncomputable def germTmulC (W : TopologicalSpace.Opens X) (hx : x ∈ W)
    (s : O'.obj (Opposite.op W)) (m : F.obj (Opposite.op W)) :
    letI := (stalkHom O O' α x).hom.toAlgebra
    TensorProduct (O.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
      (O'.stalk x) :=
  letI := (stalkHom O O' α x).hom.toAlgebra
  (TopCat.Presheaf.germ F.presheaf W x hx m)
    ⊗ₜ[O.stalk x] (TopCat.Presheaf.germ O' W x hx s)

/-- The germ of `O'`-sections is semilinear: `germ_x (r • s) = (germ_x r) • (germ_x s)` where
`r • s` uses the `O(W)`-action on `O'(W)` (through `α`) and `(germ_x r) • (germ_x s)` uses the
`O_x`-algebra action on `O'_x` (through `stalkHom`). -/
theorem germ_o'_smul (W : TopologicalSpace.Opens X) (hx : x ∈ W)
    (r : O.obj (Opposite.op W)) (s : O'.obj (Opposite.op W)) :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI := (α.app (Opposite.op W)).hom.toAlgebra
    TopCat.Presheaf.germ O' W x hx (r • s)
      = (TopCat.Presheaf.germ O W x hx r)
        • (TopCat.Presheaf.germ O' W x hx s) := by
  let := (stalkHom O O' α x).hom.toAlgebra
  let := (α.app (Opposite.op W)).hom.toAlgebra
  rw [(α.app (Opposite.op W)).hom.smul_toAlgebra, (stalkHom O O' α x).hom.smul_toAlgebra,
    stalkHom_germ O O' α x W hx r, map_mul]

/-- The `O(W)`-balancing identity for `germTmulC`: moving an `O(W)`-scalar across the tensor. -/
theorem germTmulC_balance (W : TopologicalSpace.Opens X) (hx : x ∈ W)
    (r : O.obj (Opposite.op W)) (s : O'.obj (Opposite.op W))
    (m : F.obj (Opposite.op W)) :
    letI := (α.app (Opposite.op W)).hom.toAlgebra
    germTmulC O O' α F x W hx (r • s) m
      = germTmulC O O' α F x W hx s (r • m) := by
  let := (stalkHom O O' α x).hom.toAlgebra
  let := (α.app (Opposite.op W)).hom.toAlgebra
  unfold germTmulC
  rw [germ_o'_smul O O' α x W hx r s]
  rw [PresheafOfModules.germ_smul (R := O) F x W hx r m]
  rw [TensorProduct.smul_tmul]

/-- The biadditive map `O'(W) →+ F(W) →+ (F_x ⊗ O'_x)` sending `s, m ↦ germ_x m ⊗ germ_x s`. -/
noncomputable def bCAddHom (W : TopologicalSpace.Opens X) (hx : x ∈ W) :
    letI := (stalkHom O O' α x).hom.toAlgebra
    O'.obj (Opposite.op W) →+ F.obj (Opposite.op W) →+
      (TensorProduct (O.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
        (O'.stalk x)) :=
  letI := (stalkHom O O' α x).hom.toAlgebra
  AddMonoidHom.mk'
    (fun s => AddMonoidHom.mk' (fun m => germTmulC O O' α F x W hx s m) (by
      intro m m'
      unfold germTmulC
      rw [map_add, TensorProduct.add_tmul]))
    (by
      intro s s'
      apply AddMonoidHom.ext
      intro m
      simp only [AddMonoidHom.add_apply, AddMonoidHom.mk'_apply]
      unfold germTmulC
      rw [map_add, TensorProduct.tmul_add])

/-- The additive map `O'(W) ⊗_{O(W)} F(W) →+ (F_x ⊗ O'_x)`, `s ⊗ m ↦ germ_x m ⊗ germ_x s`,
induced by `bCAddHom`. -/
noncomputable def liftC (W : TopologicalSpace.Opens X) (hx : x ∈ W) :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI := (α.app (Opposite.op W)).hom.toAlgebra
    (TensorProduct (O.obj (Opposite.op W)) (O'.obj (Opposite.op W))
      (F.obj (Opposite.op W))) →+
      (TensorProduct (O.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
        (O'.stalk x)) :=
  letI := (stalkHom O O' α x).hom.toAlgebra
  letI := (α.app (Opposite.op W)).hom.toAlgebra
  TensorProduct.liftAddHom (bCAddHom O O' α F x W hx)
    (by
      intro r s m
      exact germTmulC_balance O O' α F x W hx r s m)

/-- Computation rule for `liftC` on a pure tensor. -/
theorem liftC_tmul (W : TopologicalSpace.Opens X) (hx : x ∈ W)
    (s : O'.obj (Opposite.op W)) (m : F.obj (Opposite.op W)) :
    letI := (α.app (Opposite.op W)).hom.toAlgebra
    liftC O O' α F x W hx (s ⊗ₜ[O.obj (Opposite.op W)] m)
      = germTmulC O O' α F x W hx s m := by
  let := (stalkHom O O' α x).hom.toAlgebra
  let := (α.app (Opposite.op W)).hom.toAlgebra
  rfl

/-- `liftC` is compatible with restriction: restricting the section and reapplying `liftC`
over a smaller open gives the same value. -/
theorem liftC_res (W W' : TopologicalSpace.Opens X) (hx : x ∈ W) (hx' : x ∈ W')
    (j : W' ⟶ W) (p : (tensorPresheafOfModules O O' α F).presheaf.obj (Opposite.op W)) :
    liftC O O' α F x W' hx' ((tensorPresheafOfModules O O' α F).presheaf.map j.op p)
      = liftC O O' α F x W hx p := by
  let := (stalkHom O O' α x).hom.toAlgebra
  let := (α.app (Opposite.op W)).hom.toAlgebra
  let := (α.app (Opposite.op W')).hom.toAlgebra
  induction p using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul s m =>
    rw [tensorPresheaf_map_tmul O O' α F W W' j s m]
    rw [liftC_tmul, liftC_tmul]
    unfold germTmulC
    erw [TopCat.Presheaf.germ_res_apply O' j x hx' s,
        TopCat.Presheaf.germ_res_apply F.presheaf j x hx' m]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

/-- The function `(F ⊗_{p,O} O')_x → F_x ⊗_{O_x} O'_x` applying `liftC` to a chosen
representative (`exists_germ_eq`) of a stalk element. -/
noncomputable def rawC
    (t : TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x) :
    letI := (stalkHom O O' α x).hom.toAlgebra
    TensorProduct (O.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
      (O'.stalk x) :=
  letI := (stalkHom O O' α x).hom.toAlgebra
  let h := TopCat.Presheaf.exists_germ_eq (tensorPresheafOfModules O O' α F).presheaf t
  liftC O O' α F x h.choose h.choose_spec.choose h.choose_spec.choose_spec.choose

/-- Over any open `W ∋ x` with representative `p`, `rawC` of the germ of `p` is `liftC` of
`p`. -/
theorem rawC_germ (W : TopologicalSpace.Opens X) (hxW : x ∈ W)
    (p : (tensorPresheafOfModules O O' α F).presheaf.obj (Opposite.op W)) :
    rawC O O' α F x
        (TopCat.Presheaf.germ (tensorPresheafOfModules O O' α F).presheaf W x hxW p)
      = liftC O O' α F x W hxW p := by
  unfold rawC
  dsimp only
  set t := TopCat.Presheaf.germ (tensorPresheafOfModules O O' α F).presheaf W x hxW p with ht
  set W₀ := (TopCat.Presheaf.exists_germ_eq (tensorPresheafOfModules O O' α F).presheaf t).choose
      with hW₀
  set hxW₀ := (TopCat.Presheaf.exists_germ_eq (tensorPresheafOfModules O O' α F).presheaf
      t).choose_spec.choose
    with hxW₀def
  set p₀ := (TopCat.Presheaf.exists_germ_eq (tensorPresheafOfModules O O' α F).presheaf
      t).choose_spec.choose_spec.choose
    with hp₀
  have hspec :
      TopCat.Presheaf.germ (tensorPresheafOfModules O O' α F).presheaf W₀ x hxW₀ p₀ = t :=
    (TopCat.Presheaf.exists_germ_eq (tensorPresheafOfModules O O' α F).presheaf
        t).choose_spec.choose_spec.choose_spec
  obtain ⟨Z, hxZ, jZW₀, jZW, hZ⟩ :=
    TopCat.Presheaf.germ_eq (tensorPresheafOfModules O O' α F).presheaf x hxW₀ hxW p₀ p (by
      rw [hspec, ht])
  rw [← liftC_res O O' α F x W₀ Z hxW₀ hxZ jZW₀ p₀,
      ← liftC_res O O' α F x W Z hxW hxZ jZW p]
  rw [hZ]

/-- `liftC` intertwines the `O'(W)`-action with the `O'_x`-action through the germ map:
`liftC (a • p) = (germ_x a) • liftC p`. -/
theorem liftC_smul (W : TopologicalSpace.Opens X) (hx : x ∈ W)
    (a : O'.obj (Opposite.op W))
    (p : (tensorPresheafOfModules O O' α F).obj (Opposite.op W)) :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI := rightTensorModule (O.stalk x) (O'.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    liftC O O' α F x W hx (a • p)
      = (TopCat.Presheaf.germ O' W x hx a) • liftC O O' α F x W hx p := by
  let := (stalkHom O O' α x).hom.toAlgebra
  let := rightTensorModule (O.stalk x) (O'.stalk x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
  let := (α.app (Opposite.op W)).hom.toAlgebra
  induction p using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul s m =>
    rw [o'_smul_tmul O O' α F W a s m]
    rw [liftC_tmul, liftC_tmul]
    unfold germTmulC
    rw [rightTensorModule_smul_tmul]
    rw [map_mul (ConcreteCategory.hom (TopCat.Presheaf.germ O' W x hx))]
  | add b c hb hc =>
    rw [smul_add, map_add, map_add, smul_add, hb, hc]

/-- The `O'_x`-linear map `(F ⊗_{p,O} O')_x → F_x ⊗_{O_x} O'_x` given by `rawC`. -/
noncomputable def tensorPresheafStalk_invMap :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI := rightTensorModule (O.stalk x) (O'.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x)
      →ₗ[O'.stalk x]
        (TensorProduct (O.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
          (O'.stalk x)) :=
  letI := (stalkHom O O' α x).hom.toAlgebra
  letI := rightTensorModule (O.stalk x) (O'.stalk x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
  { toFun := fun t => rawC O O' α F x t
    map_add' := by
      intro t t'
      obtain ⟨U, hU, p, rfl⟩ := TopCat.Presheaf.exists_germ_eq (tensorPresheafOfModules O O' α
          F).presheaf t
      obtain ⟨V, hV, q, rfl⟩ := TopCat.Presheaf.exists_germ_eq (tensorPresheafOfModules O O' α
          F).presheaf t'
      set W : TopologicalSpace.Opens X := U ⊓ V with hWdef
      have hxW : x ∈ W := ⟨hU, hV⟩
      have jU : W ⟶ U := homOfLE inf_le_left
      have jV : W ⟶ V := homOfLE inf_le_right
      rw [← TopCat.Presheaf.germ_res_apply (tensorPresheafOfModules O O' α F).presheaf jU x hxW p,
          ← TopCat.Presheaf.germ_res_apply (tensorPresheafOfModules O O' α F).presheaf jV x hxW q]
      rw [← map_add (ConcreteCategory.hom
            (TopCat.Presheaf.germ (tensorPresheafOfModules O O' α F).presheaf W x hxW))]
      rw [rawC_germ, rawC_germ, rawC_germ, map_add]
    map_smul' := by
      intro a t
      simp only [RingHom.id_apply]
      obtain ⟨U, hU, p, rfl⟩ := TopCat.Presheaf.exists_germ_eq (tensorPresheafOfModules O O' α
          F).presheaf t
      obtain ⟨V, hV, a0, rfl⟩ := TopCat.Presheaf.exists_germ_eq O' a
      set W : TopologicalSpace.Opens X := U ⊓ V with hWdef
      have hxW : x ∈ W := ⟨hU, hV⟩
      have jU : W ⟶ U := homOfLE inf_le_left
      have jV : W ⟶ V := homOfLE inf_le_right
      rw [← TopCat.Presheaf.germ_res_apply (tensorPresheafOfModules O O' α F).presheaf jU x hxW p]
      rw [← TopCat.Presheaf.germ_res_apply O' jV x hxW a0]
      let := (α.app (Opposite.op W)).hom.toAlgebra
      rw [← PresheafOfModules.germ_smul (R := O')
            (tensorPresheafOfModules O O' α F) x W hxW (O'.map jV.op a0)
            ((tensorPresheafOfModules O O' α F).presheaf.map jU.op p)]
      rw [rawC_germ, rawC_germ]
      exact liftC_smul O O' α F x W hxW ((O'.map jV.op).hom a0)
        ((tensorPresheafOfModules O O' α F).presheaf.map jU.op p) }

/-- `tensorPresheafStalk_invMap` evaluates to `rawC`. -/
theorem tensorPresheafStalk_invMap_apply
    (t : TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x) :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI := rightTensorModule (O.stalk x) (O'.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    tensorPresheafStalk_invMap O O' α F x t = rawC O O' α F x t := rfl

/-- Computation rule for `tensorPresheafStalk_invMap` on a germ of a pure tensor:
`germ_x (s ⊗ₜ m) ↦ germ_x m ⊗ germ_x s`. -/
theorem tensorPresheafStalk_invMap_germTmul (W : TopologicalSpace.Opens X) (hx : x ∈ W)
    (s : O'.obj (Opposite.op W)) (m : F.obj (Opposite.op W)) :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI := rightTensorModule (O.stalk x) (O'.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    tensorPresheafStalk_invMap O O' α F x (germTmul O O' α F x W hx s m)
      = (TopCat.Presheaf.germ F.presheaf W x hx m)
          ⊗ₜ[O.stalk x] (TopCat.Presheaf.germ O' W x hx s) := by
  let := (stalkHom O O' α x).hom.toAlgebra
  let := (α.app (Opposite.op W)).hom.toAlgebra
  rw [tensorPresheafStalk_invMap_apply, germTmul, rawC_germ, liftC_tmul, germTmulC]

end InvMap

/-- There is an `O'_x`-linear map `(F ⊗_{p,O} O')_x → F_x ⊗_{O_x} O'_x`. -/
theorem tensorPresheafStalk_invFun :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI := rightTensorModule (O.stalk x) (O'.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    Nonempty
      ((TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x)
        →ₗ[O'.stalk x]
          (TensorProduct (O.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
            (O'.stalk x))) :=
  let := (stalkHom O O' α x).hom.toAlgebra
  let := rightTensorModule (O.stalk x) (O'.stalk x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
  ⟨tensorPresheafStalk_invMap O O' α F x⟩

/-- Computation rule for the forward map on `germ_x m ⊗ germ_x s`: it returns `germTmul s m`. -/
theorem tensorPresheafStalk_fwdMap_tmul (W : TopologicalSpace.Opens X) (hx : x ∈ W)
    (s : O'.obj (Opposite.op W)) (m : F.obj (Opposite.op W)) :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI := rightTensorModule (O.stalk x) (O'.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    tensorPresheafStalk_fwdMap O O' α F x
        ((TopCat.Presheaf.germ F.presheaf W x hx m)
          ⊗ₜ[O.stalk x] (TopCat.Presheaf.germ O' W x hx s))
      = germTmul O O' α F x W hx s m := by
  let := (stalkHom O O' α x).hom.toAlgebra
  let := rightTensorModule (O.stalk x) (O'.stalk x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
  let : Module (O.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x) :=
    Module.compHom _ (stalkHom O O' α x).hom
  rw [tensorPresheafStalk_fwdMap_apply, TensorProduct.lift.tmul, tensorPresheafStalk_bilinMap_tmul,
    germTmul]

/-- `tensorPresheafStalk_fwdMap` is a left inverse of `tensorPresheafStalk_invMap`. -/
theorem tensorPresheafStalk_fwdMap_invMap
    (t : TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x) :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI := rightTensorModule (O.stalk x) (O'.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    tensorPresheafStalk_fwdMap O O' α F x (tensorPresheafStalk_invMap O O' α F x t) = t := by
  let := (stalkHom O O' α x).hom.toAlgebra
  let := rightTensorModule (O.stalk x) (O'.stalk x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
  obtain ⟨U, hU, p, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (tensorPresheafOfModules O O' α F).presheaf t
  let := (α.app (Opposite.op U)).hom.toAlgebra
  induction p using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul s m =>
      have hgt : TopCat.Presheaf.germ (tensorPresheafOfModules O O' α F).presheaf U x hU
          (s ⊗ₜ[O.obj (Opposite.op U)] m) = germTmul O O' α F x U hU s m := rfl
      rw [hgt, tensorPresheafStalk_invMap_germTmul, tensorPresheafStalk_fwdMap_tmul]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]

/-- `tensorPresheafStalk_invMap` is a left inverse of `tensorPresheafStalk_fwdMap`. -/
theorem tensorPresheafStalk_invMap_fwdMap :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI := rightTensorModule (O.stalk x) (O'.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    ∀ z : TensorProduct (O.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x) (O'.stalk x),
      tensorPresheafStalk_invMap O O' α F x (tensorPresheafStalk_fwdMap O O' α F x z) = z := by
  let := (stalkHom O O' α x).hom.toAlgebra
  let := rightTensorModule (O.stalk x) (O'.stalk x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul mx sx =>
      obtain ⟨U, hU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf mx
      obtain ⟨V, hV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq O' sx
      set W : TopologicalSpace.Opens X := U ⊓ V
      have hxW : x ∈ W := ⟨hU, hV⟩
      have jU : W ⟶ U := homOfLE inf_le_left
      have jV : W ⟶ V := homOfLE inf_le_right
      rw [← TopCat.Presheaf.germ_res_apply F.presheaf jU x hxW m,
          ← TopCat.Presheaf.germ_res_apply O' jV x hxW s,
          tensorPresheafStalk_fwdMap_tmul, tensorPresheafStalk_invMap_germTmul]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

/-- The canonical isomorphism of `O'_x`-modules
`F_x ⊗_{O_x} O'_x ≃ₗ (F ⊗_{p,O} O')_x`, for a morphism `α : O ⟶ O'` of *presheaves* of
commutative rings on `X` and a *presheaf* `F` of `O`-modules.  The left-hand side is the tensor
product of the `O_x`-module `F_x` with the `O_x`-algebra `O'_x`, carrying the `O'_x`-module
structure of `rightTensorModule` in which `O'_x` acts on the right factor; the right-hand side is
the stalk at `x` of the tensor product presheaf. -/
@[stacks 007K]
noncomputable def tensorPresheafStalkIso :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI := rightTensorModule (O.stalk x) (O'.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    (TensorProduct (O.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
        (O'.stalk x))
      ≃ₗ[O'.stalk x]
        (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x) :=
  letI := (stalkHom O O' α x).hom.toAlgebra
  letI := rightTensorModule (O.stalk x) (O'.stalk x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
  letI : Module (O.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x) :=
    Module.compHom _ (stalkHom O O' α x).hom
  LinearEquiv.ofLinearMap
    (tensorPresheafStalk_fwdMap O O' α F x)
    (tensorPresheafStalk_invMap O O' α F x)
    (LinearMap.ext (tensorPresheafStalk_fwdMap_invMap O O' α F x))
    (LinearMap.ext (tensorPresheafStalk_invMap_fwdMap O O' α F x))

/-- Existence form of `tensorPresheafStalkIso` (Stacks Tag 007K): the stalk of the tensor
product *presheaf* is `O'_x`-linearly isomorphic to `F_x ⊗_{O_x} O'_x`. -/
theorem nonempty_tensorPresheafStalkIso :
    letI := (stalkHom O O' α x).hom.toAlgebra
    letI := rightTensorModule (O.stalk x) (O'.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
    Nonempty
      ((TensorProduct (O.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x)
          (O'.stalk x))
        ≃ₗ[O'.stalk x]
          (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfModules O O' α F).presheaf x)) :=
  ⟨tensorPresheafStalkIso O O' α F x⟩

/-- A morphism `φ : M ⟶ N` of presheaves of `O'`-modules induces an `O'.stalk x`-linear map on
the `Ab`-stalks of the underlying presheaves, with underlying additive map
`(stalkFunctor Ab.{u} x).map φ.presheaf`. -/
@[ega "0 3.1.6" "special case"]
noncomputable def stalkLinearMapOfHom
    {M N : PresheafOfModules.{u} (ringPresheaf O')}
    (φ : M ⟶ N) :
    (TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x)
      →ₗ[O'.stalk x] (TopCat.Presheaf.stalk (C := Ab.{u}) N.presheaf x) where
  toFun := (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
    ((PresheafOfModules.toPresheaf _).map φ)))
  map_add' a b := map_add _ a b
  map_smul' r m := by
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
    obtain ⟨V, hV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq O' r
    simp only [RingHom.id_apply]
    set W : TopologicalSpace.Opens X := U ⊓ V with hWdef
    have hW : x ∈ W := ⟨hU, hV⟩
    set iU : W ⟶ U := homOfLE inf_le_left with hiU
    set iV : W ⟶ V := homOfLE inf_le_right with hiV
    rw [← TopCat.Presheaf.germ_res_apply M.presheaf iU x hW s,
        ← TopCat.Presheaf.germ_res_apply O' iV x hW t]
    rw [← PresheafOfModules.germ_smul (R := O') M x W hW
          (O'.map iV.op t) (M.presheaf.map iU.op s)]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply W x hW
          ((PresheafOfModules.toPresheaf _).map φ)]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply W x hW
          ((PresheafOfModules.toPresheaf _).map φ) (M.presheaf.map iU.op s)]
    erw [PresheafOfModules.toPresheaf_map_app_apply φ (Opposite.op W),
        PresheafOfModules.toPresheaf_map_app_apply φ (Opposite.op W),
        map_smul (φ.app (Opposite.op W)).hom ((ringPresheaf O').map iV.op t)
          (M.presheaf.map iU.op s)]
    erw [PresheafOfModules.germ_smul (R := O') N x W hW
          (O'.map iV.op t)
          ((φ.app (Opposite.op W)).hom (M.presheaf.map iU.op s))]
    rw [TopCat.Presheaf.germ_res_apply O' iV x hW t]
    rfl

end Statements

/-! ## Specialisation to sheaves (Stacks Tag 008B)

Here `O, O'` are sheaves of commutative rings and `F` is a sheaf of `O`-modules, and the presheaf
constructions are applied to the underlying presheaf data. -/

section SheafStatements

variable {X : TopCat.{u}}
variable (O O' : TopCat.Sheaf CommRingCat.{u} X) (α : O ⟶ O')
  (F : SheafOfModules.{u} (ringSheaf O)) (x : X)

/-- `α` as a morphism of the underlying presheaves of commutative rings. -/
abbrev αp : O.presheaf ⟶ O'.presheaf :=
  (sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{u}).map α

/-- The tensor product presheaf `F ⊗_{p,O} O'` of the underlying presheaf data of `α` and `F`,
in the sheaf situation. -/
noncomputable abbrev tensorPresheafOfSheaves : PresheafOfModules.{u} ((ringSheaf O').obj) :=
  tensorPresheafOfModules O.presheaf O'.presheaf (αp O O' α) F.val

/-- The ring homomorphism `O_x → O'_x` on stalks at `x` induced by a morphism of sheaves of
commutative rings. -/
noncomputable abbrev stalkHomOfSheaves : O.presheaf.stalk x ⟶ O'.presheaf.stalk x :=
  stalkHom O.presheaf O'.presheaf (αp O O' α) x

/-- **The tensor product sheaf `F ⊗_O O'`.**  The sheafification of the tensor product presheaf,
as a *sheaf of `O'`-modules* on `X` (Stacks Tag 0089).  It is obtained by applying
`PresheafOfModules.sheafification` along the identity, `O'` being already a sheaf of rings, so
its stalks carry the canonical `O'_x`-module structure. -/
noncomputable def tensorSheaf : SheafOfModules.{u} (ringSheaf O') :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf O').obj)).obj (tensorPresheafOfSheaves O O' α F)

/-! ### Sheafification commutes with stalks

The stalk at `x` of the unit of the sheafification adjunction for presheaves of `O'`-modules,
taken at the tensor product presheaf, is an `O'_x`-linear equivalence
`(F ⊗_{p,O} O')_x ≃ₗ (F ⊗_O O')_x`. -/

/-- The `O'_x`-linear comparison map `(F ⊗_{p,O} O')_x → (F ⊗_O O')_x`: the stalk at `x` of the
unit of the `PresheafOfModules` sheafification adjunction, evaluated at the tensor product
presheaf. -/
noncomputable def tensorSheafStalk_map :
    (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfSheaves O O' α F).presheaf x)
      →ₗ[O'.presheaf.stalk x]
        (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorSheaf O O' α F).val.presheaf x) :=
  stalkLinearMapOfHom O'.presheaf x
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O').obj)).unit.app
      (tensorPresheafOfSheaves O O' α F))

/-- Existence form of `tensorSheafStalk_map`: there is an `O'_x`-linear map from the stalk of
the tensor product presheaf to the stalk of its sheafification. -/
theorem nonempty_tensorSheafStalk_linearMap :
    Nonempty
      ((TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfSheaves O O' α F).presheaf x)
        →ₗ[O'.presheaf.stalk x]
          (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorSheaf O O' α F).val.presheaf x)) :=
  ⟨tensorSheafStalk_map O O' α F x⟩

/-- The comparison map `tensorSheafStalk_map` is bijective. -/
theorem tensorSheafStalk_bijective :
    Function.Bijective (tensorSheafStalk_map O O' α F x) := by
  set η := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O').obj)).unit.app
      (tensorPresheafOfSheaves O O' α F) with hη
  have hiso : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      ((PresheafOfModules.toPresheaf _).map η)) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x Ab _
  show Function.Bijective ⇑(ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      ((PresheafOfModules.toPresheaf _).map η)))
  exact CategoryTheory.ConcreteCategory.bijective_of_isIso _

/-- **Sheafification commutes with stalks.**  The canonical comparison from the stalk of the
tensor product presheaf to the stalk of the tensor product sheaf (its sheafification) is an
`O'_x`-linear isomorphism, given by `tensorSheafStalk_map`. -/
noncomputable def tensorSheafStalkIso :
    (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfSheaves O O' α F).presheaf x)
      ≃ₗ[O'.presheaf.stalk x]
        (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorSheaf O O' α F).val.presheaf x) :=
  LinearEquiv.ofBijective (tensorSheafStalk_map O O' α F x)
    (tensorSheafStalk_bijective O O' α F x)

/-- Existence form of `tensorSheafStalkIso`: sheafification does not change stalks, so the
stalk of the tensor product presheaf is `O'_x`-linearly isomorphic to the stalk of the tensor
product sheaf. -/
theorem nonempty_tensorSheafStalkIso :
    Nonempty
      ((TopCat.Presheaf.stalk (C := Ab.{u}) (tensorPresheafOfSheaves O O' α F).presheaf x)
        ≃ₗ[O'.presheaf.stalk x]
          (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorSheaf O O' α F).val.presheaf x)) :=
  ⟨tensorSheafStalkIso O O' α F x⟩

/-- The canonical isomorphism of `O'_x`-modules
`F_x ⊗_{O_x} O'_x ≃ₗ (F ⊗_O O')_x`, in the orientation of the tag.  The left-hand side is the
tensor product of the `O_x`-module `F_x` with the `O_x`-algebra `O'_x`, carrying the
`O'_x`-module structure of `rightTensorModule` in which `O'_x` acts on the right factor; the
right-hand side is the stalk at `x` of the tensor product *sheaf* with its canonical
`O'_x`-module structure.  The equivalence is the composite of the presheaf comparison
(`tensorPresheafStalkIso`, Tag 007K) with the fact that sheafification commutes with stalks
(`tensorSheafStalkIso`). -/
@[stacks 008B, ega "0 4.1.5" "special case"]
noncomputable def mainIso :
    letI := (stalkHomOfSheaves O O' α x).hom.toAlgebra
    letI := rightTensorModule (O.presheaf.stalk x) (O'.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)
    (TensorProduct (O.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)
        (O'.presheaf.stalk x))
      ≃ₗ[O'.presheaf.stalk x]
        (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorSheaf O O' α F).val.presheaf x) :=
  letI := (stalkHomOfSheaves O O' α x).hom.toAlgebra
  letI := rightTensorModule (O.presheaf.stalk x) (O'.presheaf.stalk x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)
  (tensorPresheafStalkIso O.presheaf O'.presheaf (αp O O' α) F.val x).trans
    (tensorSheafStalkIso O O' α F x)

/-- Existence form of Stacks 008B: there is an `O'_x`-linear isomorphism
`F_x ⊗_{O_x} O'_x ≅ (F ⊗_O O')_x`, in the orientation of the tag. -/
theorem nonempty_tensor_stalk_iso :
    letI := (stalkHomOfSheaves O O' α x).hom.toAlgebra
    letI := rightTensorModule (O.presheaf.stalk x) (O'.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)
    Nonempty
      ((TensorProduct (O.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)
          (O'.presheaf.stalk x))
        ≃ₗ[O'.presheaf.stalk x]
          (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorSheaf O O' α F).val.presheaf x)) :=
  ⟨mainIso O O' α F x⟩

/-- The canonical `O'_x`-module structure on the stalk of the tensor product sheaf `F ⊗_O O'`. -/
noncomputable instance tensorSheafStalkModule :
    Module (O'.presheaf.stalk x)
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (tensorSheaf O O' α F).val.presheaf x)) :=
  inferInstanceAs (Module (O'.presheaf.stalk x)
    (ToType (TopCat.Presheaf.stalk (C := Ab.{u})
      (show PresheafOfModules.{u} (ringPresheaf O'.presheaf) from
        (tensorSheaf O O' α F).val).presheaf x)))

end SheafStatements

end Stacks.Sheafify.ModuleStalkTensor
