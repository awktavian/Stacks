module
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaves on the site of `G`-sets are `G`-sets

Let `G` be a monoid. The site `𝒯_G` has as underlying category a full subcategory of the category
`Action (Type u) G` of `G`-sets, and a family `{Uᵢ → U}` is a covering exactly when it is jointly
surjective. Evaluating a presheaf `F` on `𝒯_G` at the left regular `G`-set `Action.leftRegular G`
(the source's `{}_G G`) produces a `G`-set: right multiplications give an isomorphism of monoids
`Hom_G({}_G G, {}_G G) ≅ Gᵒᵖ`, `φ ↦ φ 1`, and `g` acts on `F({}_G G)` as `F(R_g)`. Conversely a
`G`-set `S` produces the presheaf `F_S : U ↦ Hom_G(U, S)`, the Yoneda embedding of `S` restricted
along the inclusion of `𝒯_G` into `G`-sets; it is a sheaf because a covering of `U` is a jointly
surjective family, so a compatible family of `G`-maps `Uᵢ → S` glues uniquely. The two
constructions are quasi-inverse equivalences between the category of sheaves of sets on `𝒯_G` and
the category of `G`-sets.

## Main results

* `Action.exists_equivalence_sheaf`: restricted Yoneda `S ↦ (U ↦ Hom_G(ι U, S))` takes values in
  sheaves and is one half of an equivalence between `G`-sets and the sheaves of sets on `(T, J)`;
  the quasi-inverse is `F ↦ F({}_G G)`.

## Implementation notes

The source's `𝒯_G` depends on set-theoretic choices (a cardinal bound cutting the class of all
`G`-sets down to a small category), and the source observes that the resulting category of sheaves
does not: the only properties of `𝒯_G` used are that it is a full subcategory `ι` of `G`-sets (a)
containing `{}_G G` (b), that it has fibre products, computed as in `G`-sets (c), that it contains
an object isomorphic to every `G`-invariant subset of each of its objects (d), and that a family of
maps between its objects is a covering exactly when it is surjective (e). Three of those five are
the hypotheses below — (c) and (d) are not, see the paragraphs on fibre products and on invariant
subsets — so the statement is about every such site rather than about one choice of `𝒯_G`.
Property (b) is phrased with `Functor.essImage`: `{}_G G` lies in the essential image of `ι`.

Joint surjectivity of a sieve `S` on `U` is phrased as: every `G`-map `{}_G G → ι U` factors
through an arrow of `S`. The points of a `G`-set `U` are exactly the `G`-maps `{}_G G → U`
(evaluation at `1`), so this says that the arrows of `S` cover `U`; the source states (e) in one
direction only, coverings being surjective by the construction of `𝒯_G`, whereas here `J` is
otherwise unconstrained, and both directions are needed — for the discrete topology, in which every
sieve covers, the sheaves form the terminal category. `CategoryTheory.typesGrothendieckTopology`
says the same with `PUnit` in place of `{}_G G`, and the statement below is the `G`-equivariant
form of `CategoryTheory.typeEquiv` together with `CategoryTheory.yoneda'_comp`.

Fibre products, the source's (c), are not needed. The source works with covering families
`{Uᵢ → U}` and reads compatibility of a family of sections off the fibre products `Uᵢ ×_U Uⱼ`,
which is why it asks for them. Compatibility of a family indexed by a *sieve* is
`Presieve.FamilyOfElements.SieveCompatible`, `x (g ≫ f) = P.map g (x f)`, so the sieve-theoretic
sheaf condition quantifies over commuting squares, and a square is available wherever the source
takes a fibre product. That `U ↦ Hom_G(ι U, S)` is a sheaf comes down to well-definedness of the
amalgamation at a point `a` of `ι U`, which compares two factorizations `b ≫ ι f = b' ≫ ι f'` of
`a`; fullness and faithfulness of `ι` make this a commuting square in `T` with vertex the object
supplied by (b). Dropping (c) enlarges the class of sites covered: for `G = ℤ/2` and `T` the
full subcategory of `G`-sets on the empty `G`-set, the one-point `G`-set `*` and `{}_G G`, the
hypotheses below hold and the conclusion holds, while `T` has no fibre product of the two copies of
`{}_G G → *`, that fibre product being two free orbits in `G`-sets.

Closure under `G`-invariant subsets, the source's (d), is not needed either, and for a similar
reason: what it buys the source is that the orbits of `U = ∐ᵢ Oᵢ` are *objects*, so that `U` may be
covered by `{Oᵢ → U}` and a single orbit with stabiliser `H` by `{{}_G G → U}`, `g ↦ gu`, whose
fibre product `({}_G G) ×_U ({}_G G) ≅ ∐_{h ∈ H} {}_G G` produces the pair of maps differing by
`h ∈ H`. The sieve `R_U` generated by *all* arrows `u₀ → U`, for a `u₀` with `ι u₀ ≅ {}_G G`,
does the same work while creating no new objects: its members are arrows of `T` by construction, it
covers `U` by (e) because every point of `ι U` is `ι` of an arrow out of `u₀` by fullness, and
separatedness of a sheaf on `R_U` — which the sheaf condition hands over for free — replaces both
the orbit decomposition and the stabiliser computation. So (d) too excludes sites for which the
conclusion holds: for any `G`, let `T` be the full subcategory of `G`-sets on the single object
`{}_G G` and let `J = GrothendieckTopology.trivial T`. A sieve on that object is a left ideal
`I ⊆ G` read through `End({}_G G) ≅ Gᵒᵖ`, and it is jointly surjective exactly when `1 ∈ I`, that
is exactly when it is `⊤`, so `hJ` holds, as does `hreg`; every presheaf is a sheaf for the trivial
topology, `Tᵒᵖ` is `SingleObj G`, and so `PSh(T) ≌ Action (Type u) G` by
`Action.functorCategoryEquivalence`, the equivalence being restricted Yoneda. Yet the empty `G`-set
is a subobject of `{}_G G` — monomorphisms of `G`-sets are the injective maps — and is isomorphic
to no object of `T`, so (d) fails.

The source's `G` is a group, and the statement below asks only for a monoid. What needs inverses
is the source's own proof, which decomposes an object into `G`-orbits and computes the stabiliser
of a point; the argument through `R_U` above needs none, and each ingredient it uses holds over a
monoid: `{}_G G` corepresents the underlying set, `Hom_G({}_G G, X) ≅ X` by evaluation at `1`
since `φ g = g · φ 1`, right multiplications give `End({}_G G) ≅ Gᵒᵖ` by `g ↦ R_g`, and the
`G`-set structure on a presheaf's value at `{}_G G` is `g ↦ F(R_g)`.

## References

* [Stacks 00W0](https://stacks.math.columbia.edu/tag/00W0)
-/

namespace CategoryTheory.Sites.Sheaf

section

universe w v u
open CategoryTheory
open CategoryTheory Opposite

namespace Stacks.Sites.GSetSheaves

section LeftRegular

variable {G : Type u} [Monoid G]

/-- A morphism of `G`-sets is equivariant, elementwise. -/
private lemma hom_apply_ρ {X Y : Action (Type u) G} (φ : X ⟶ Y) (g : G) (x : X.V) :
    φ.hom (X.ρ g x) = Y.ρ g (φ.hom x) :=
  ConcreteCategory.congr_hom (φ.comm g) x

private lemma leftRegular_ρ_one (g : G) : ((Action.leftRegular G).ρ g) (1 : G) = g :=
  (Action.ofMulAction_apply g (1 : G)).trans (mul_one g)

/-- A `G`-map out of the left regular `G`-set satisfies `φ g = g • φ 1`. -/
private lemma leftRegular_hom_apply {X : Action (Type u) G} (φ : Action.leftRegular G ⟶ X)
    (g : G) : φ.hom g = X.ρ g (φ.hom (1 : G)) := by
  have h := hom_apply_ρ φ g (1 : G)
  rw [leftRegular_ρ_one] at h
  exact h

/-- Evaluation at `1` identifies the `G`-maps out of the left regular `G`-set `{}_G G` with the
underlying set of the target: a `G`-map `φ` out of `{}_G G` satisfies `φ g = g • φ 1`. -/
private def leftRegularHomEquiv (X : Action (Type u) G) : (Action.leftRegular G ⟶ X) ≃ X.V where
  toFun φ := φ.hom (1 : G)
  invFun x :=
    { hom := ↾fun g => X.ρ g x
      comm := fun g =>
        ConcreteCategory.hom_ext _ _ fun (h : G) => by
          change X.ρ (g * h) x = X.ρ g (X.ρ h x)
          rw [map_mul, End.mul_def, types_comp_apply] }
  left_inv φ :=
    Action.hom_ext _ _
      (ConcreteCategory.hom_ext _ _ fun (g : G) => by
        exact (leftRegular_hom_apply φ g).symm)
  right_inv x := by
    simp [map_one, End.one_def]

end LeftRegular

/-! ### The points of an object of the site -/

section Site

variable {T : Type w} [Category.{v} T] {G : Type u} [Monoid G] (ι : T ⥤ Action (Type u) G) [ι.Full]
  [ι.Faithful] {u₀ : T} (α : ι.obj u₀ ≅ Action.leftRegular G)

/-- The point of `ι u₀` corresponding to `1 ∈ {}_G G`. -/
private def basePt : (ι.obj u₀).V :=
  α.inv.hom (1 : G)

omit [ι.Full] [ι.Faithful] in
private lemma inv_hom_apply (y : (ι.obj u₀).V) : α.inv.hom (α.hom.hom y) = y :=
  ConcreteCategory.congr_hom (Action.hom_inv_hom α) y

/-- Evaluation at the base point identifies the `G`-maps out of `ι u₀` with the underlying set of
the target. -/
private def basePtEquiv (X : Action (Type u) G) : (ι.obj u₀ ⟶ X) ≃ X.V :=
  (α.homCongr (Iso.refl X)).trans (leftRegularHomEquiv X)

omit [ι.Full] [ι.Faithful] in
private lemma basePtEquiv_apply {X : Action (Type u) G} (φ : ι.obj u₀ ⟶ X) :
    basePtEquiv ι α X φ = φ.hom (basePt ι α) :=
  rfl

omit [ι.Full] [ι.Faithful] in
private lemma basePtEquiv_comp {X Y : Action (Type u) G} (φ : ι.obj u₀ ⟶ X) (f : X ⟶ Y) :
    basePtEquiv ι α Y (φ ≫ f) = f.hom (basePtEquiv ι α X φ) :=
  rfl

/-- **The points of `ι V` are the arrows `u₀ ⟶ V`.** -/
private noncomputable def ptEquiv (V : T) : (u₀ ⟶ V) ≃ (ι.obj V).V :=
  (Functor.FullyFaithful.ofFullyFaithful ι).homEquiv.trans (basePtEquiv ι α (ι.obj V))

private lemma ptEquiv_apply {V : T} (h : u₀ ⟶ V) : ptEquiv ι α V h = (ι.map h).hom (basePt ι α) :=
  rfl

private lemma ptEquiv_comp {V W : T} (h : u₀ ⟶ V) (f : V ⟶ W) :
    ptEquiv ι α W (h ≫ f) = (ι.map f).hom (ptEquiv ι α V h) := by
  rw [ptEquiv_apply, ptEquiv_apply, ι.map_comp]
  rfl

private lemma basePtEquiv_precomp_map {V : T} {X : Action (Type u) G} (k : u₀ ⟶ V)
    (χ : ι.obj V ⟶ X) : basePtEquiv ι α X (ι.map k ≫ χ) = χ.hom (ptEquiv ι α V k) :=
  rfl

/-- A `G`-map out of `ι V` is determined by its values on the points of `ι V`. -/
private lemma hom_ext_pt {V : T} {X : Action (Type u) G} {χ χ' : ι.obj V ⟶ X}
    (h : ∀ k : u₀ ⟶ V, χ.hom (ptEquiv ι α V k) = χ'.hom (ptEquiv ι α V k)) : χ = χ' := by
  refine Action.hom_ext _ _ (ConcreteCategory.hom_ext _ _ fun y => ?_)
  obtain ⟨k, rfl⟩ := (ptEquiv ι α V).surjective y
  exact h k

/-- The endomorphism of `u₀` corresponding to right multiplication by `g` on `{}_G G`. -/
private noncomputable def rAct (g : G) : u₀ ⟶ u₀ :=
  (ptEquiv ι α u₀).symm ((ι.obj u₀).ρ g (basePt ι α))

private lemma ptEquiv_rAct (g : G) : ptEquiv ι α u₀ (rAct ι α g) = (ι.obj u₀).ρ g (basePt ι α) :=
  (ptEquiv ι α u₀).apply_symm_apply _

/-- Under `basePtEquiv`, precomposing with the right translation `rAct g` is the action of `g`. -/
private lemma basePtEquiv_rAct_comp {X : Action (Type u) G} (g : G) (φ : ι.obj u₀ ⟶ X) :
    basePtEquiv ι α X (ι.map (rAct ι α g) ≫ φ) = X.ρ g (basePtEquiv ι α X φ) := by
  rw [basePtEquiv_precomp_map, ptEquiv_rAct, basePtEquiv_apply]
  exact hom_apply_ρ φ g (basePt ι α)

private lemma ptEquiv_rAct_comp {V : T} (g : G) (h : u₀ ⟶ V) :
    ptEquiv ι α V (rAct ι α g ≫ h) = (ι.obj V).ρ g (ptEquiv ι α V h) := by
  rw [ptEquiv_apply, ι.map_comp]
  exact basePtEquiv_rAct_comp ι α g (ι.map h)

/-- Under `ptEquiv`, the action of `g` on the points of `ι V` is precomposition with the right
translation `rAct g`. -/
private lemma ptEquiv_symm_ρ {V : T} (g : G) (y : (ι.obj V).V) :
    (ptEquiv ι α V).symm ((ι.obj V).ρ g y) = rAct ι α g ≫ (ptEquiv ι α V).symm y := by
  apply (ptEquiv ι α V).injective
  rw [Equiv.apply_symm_apply, ptEquiv_rAct_comp, Equiv.apply_symm_apply]

private lemma rAct_one : rAct ι α (1 : G) = 𝟙 u₀ := by
  apply (ptEquiv ι α u₀).injective
  rw [ptEquiv_rAct, ptEquiv_apply, ι.map_id, Action.id_hom, map_one, End.one_def]

private lemma rAct_mul (g h : G) : rAct ι α (g * h) = rAct ι α g ≫ rAct ι α h := by
  apply (ptEquiv ι α u₀).injective
  rw [ptEquiv_rAct, ptEquiv_rAct_comp, ptEquiv_rAct, map_mul, End.mul_def, types_comp_apply]

omit [ι.Full] [ι.Faithful] in
private lemma ρ_hom_basePt (y : (ι.obj u₀).V) : (ι.obj u₀).ρ (α.hom.hom y) (basePt ι α) = y :=
  (leftRegular_hom_apply α.inv (α.hom.hom y)).symm.trans (inv_hom_apply ι α y)

/-- **Every endomorphism of `u₀` is a right translation.** This is the case `U = {}_G G` of the
source's argument. -/
private lemma exists_rAct (m : u₀ ⟶ u₀) : ∃ g : G, m = rAct ι α g :=
  ⟨α.hom.hom (ptEquiv ι α u₀ m),
    (ptEquiv ι α u₀).injective
      ((ρ_hom_basePt ι α (ptEquiv ι α u₀ m)).symm.trans (ptEquiv_rAct ι α _).symm)⟩

/-! ### The covering sieves -/

include α in
/-- **A sieve is covering exactly when it contains every arrow out of `u₀`.** -/
private lemma mem_iff_forall_hom (J : GrothendieckTopology T)
    (hJ :
      ∀ (U : T) (S : Sieve U),
        S ∈ J U ↔
          ∀ a : Action.leftRegular G ⟶ ι.obj U,
            ∃ (V : T) (f : V ⟶ U) (b : Action.leftRegular G ⟶ ι.obj V),
              S.arrows f ∧ b ≫ ι.map f = a)
    (V : T) (R : Sieve V) : R ∈ J V ↔ ∀ h : u₀ ⟶ V, R.arrows h := by
  rw [hJ]
  refine ⟨fun hR h => ?_, fun hR a => ?_⟩
  · obtain ⟨W, f, b, hf, hb⟩ := hR (α.inv ≫ ι.map h)
    have hc : ι.preimage (α.hom ≫ b) ≫ f = h := by
      apply ι.map_injective
      rw [Functor.map_comp, ι.map_preimage, Category.assoc, hb, ← Category.assoc, α.hom_inv_id,
        Category.id_comp]
    rw [← hc]
    exact R.downward_closed hf _
  · refine ⟨u₀, ι.preimage (α.hom ≫ a), α.inv, hR _, ?_⟩
    rw [ι.map_preimage, ← Category.assoc, α.inv_hom_id, Category.id_comp]

/-! ### The `G`-set attached to a presheaf -/

/-- The `G`-set attached to a presheaf `P` on `T`: its value at `u₀`, with `g` acting as
`P(rAct g)`. -/
@[implicit_reducible]
private noncomputable def presheafAction (P : Tᵒᵖ ⥤ Type u) : Action (Type u) G where
  V := P.obj (op u₀)
  ρ :=
    { toFun := fun g => End.of (P.map (rAct ι α g).op)
      map_one' := End.ext (by simp [rAct_one ι α, op_id, P.map_id])
      map_mul' := fun g h => End.ext (by simp [rAct_mul ι α, End.mul_asHom, op_comp, P.map_comp,
        types_comp_apply]) }

/-- `presheafAction` is functorial in the presheaf: a morphism of presheaves is a `G`-map on the
attached `G`-sets, its equivariance being naturality at the right translations. -/
private noncomputable def presheafActionMap {P Q : Tᵒᵖ ⥤ Type u} (η : P ⟶ Q) :
    presheafAction ι α P ⟶ presheafAction ι α Q
    where
  hom := η.app (op u₀)
  comm := fun g => η.naturality ((rAct ι α g).op)

/-- Two successive restrictions of a section of a presheaf compose. -/
private lemma map_op_comp (P : Tᵒᵖ ⥤ Type u) {V W Z : T} (f : V ⟶ W) (g : W ⟶ Z)
    (s : P.obj (op Z)) : P.map f.op (P.map g.op s) = P.map (f ≫ g).op s := by
  rw [op_comp, P.map_comp, types_comp_apply]

/-- A family of sections over `u₀` indexed by the arrows `u₀ ⟶ V` is *equivariant* when reindexing
by a right translation is restriction along it. Such a family is the same thing as a `G`-map `ι V ⟶
P(u₀)`, by `Stacks.Sites.GSetSheaves.ofFamily` and
`Stacks.Sites.GSetSheaves.ofFamily_apply_ptEquiv`. -/
private abbrev IsEquivariantFamily (P : Tᵒᵖ ⥤ Type u) (V : T) (x : (u₀ ⟶ V) → P.obj (op u₀)) :
    Prop :=
  ∀ (g : G) (h : u₀ ⟶ V), x (rAct ι α g ≫ h) = P.map (rAct ι α g).op (x h)

/-- The `G`-map `ι V ⟶ P(u₀)` attached to an equivariant family of sections over `u₀` indexed by
the arrows `u₀ ⟶ V`. -/
private noncomputable def ofFamily (P : Tᵒᵖ ⥤ Type u) (V : T) (x : (u₀ ⟶ V) → P.obj (op u₀))
    (hx : IsEquivariantFamily ι α P V x) : ι.obj V ⟶ presheafAction ι α P
    where
  hom := ↾fun y => x ((ptEquiv ι α V).symm y)
  comm := fun g =>
    ConcreteCategory.hom_ext _ _ fun y => by
      simp [presheafAction, ptEquiv_symm_ρ, hx]

private lemma ofFamily_apply_ptEquiv (P : Tᵒᵖ ⥤ Type u) (V : T) (x : (u₀ ⟶ V) → P.obj (op u₀))
    (hx : IsEquivariantFamily ι α P V x) (h : u₀ ⟶ V) :
    (ofFamily ι α P V x hx).hom (ptEquiv ι α V h) = x h := by
  simp [ofFamily]

/-- The canonical map `P(V) → Mor_G(ι V, P(u₀))`, sending a section `s` to the map taking the point
`ι(h)(e)` of `ι V` to `h^* s`: the family of restrictions of `s` is equivariant because restriction
along a composite is the composite of restrictions. -/
private noncomputable def can (P : Tᵒᵖ ⥤ Type u) (V : T) (s : P.obj (op V)) :
    ι.obj V ⟶ presheafAction ι α P :=
  ofFamily ι α P V (fun h => P.map h.op s) fun g h => (map_op_comp P (rAct ι α g) h s).symm

private lemma can_apply_ptEquiv (P : Tᵒᵖ ⥤ Type u) {V : T} (s : P.obj (op V)) (h : u₀ ⟶ V) :
    (can ι α P V s).hom (ptEquiv ι α V h) = P.map h.op s :=
  ofFamily_apply_ptEquiv ι α P V (fun k => P.map k.op s) _ h

/-- `can` is a morphism of presheaves. This is the source's "trivial but confusing"
verification. -/
private lemma can_naturality (P : Tᵒᵖ ⥤ Type u) {V W : T} (f : W ⟶ V) (s : P.obj (op V)) :
    can ι α P W (P.map f.op s) = ι.map f ≫ can ι α P V s := by
  refine hom_ext_pt ι α (fun k => ?_)
  rw [can_apply_ptEquiv, Action.comp_hom, types_comp_apply, ← ptEquiv_comp, can_apply_ptEquiv]
  exact map_op_comp P k f s

/-- **Injectivity of `can` is separatedness for the arrows out of `u₀`**: a section is determined
by its restrictions along the arrows `u₀ ⟶ V`, which is what `can` records. -/
private lemma injective_can_iff (P : Tᵒᵖ ⥤ Type u) (V : T) :
    Function.Injective (can ι α P V) ↔
      ∀ s t : P.obj (op V), (∀ k : u₀ ⟶ V, P.map k.op s = P.map k.op t) → s = t := by
  refine
    ⟨fun hinj s t h => hinj (hom_ext_pt ι α fun k => ?_), fun hsep s t hst => hsep s t fun k => ?_⟩
  · rw [can_apply_ptEquiv, can_apply_ptEquiv, h]
  · rw [← can_apply_ptEquiv ι α P s k, ← can_apply_ptEquiv ι α P t k, hst]

/-! ### The sheaf condition, in terms of the arrows out of `u₀` -/

/-- For a sheaf, an `Arrows.Compatible` family indexed by the arrows out of `u₀` has a unique
amalgamation. -/
private lemma existsUnique_of_arrows_compatible (P : Tᵒᵖ ⥤ Type u) (J : GrothendieckTopology T)
    (hcov : ∀ (V : T) (R : Sieve V), R ∈ J V ↔ ∀ h : u₀ ⟶ V, R.arrows h)
    (hP : Presieve.IsSheaf J P) (V : T) (x : (u₀ ⟶ V) → P.obj (op u₀))
    (hx : Presieve.Arrows.Compatible P (fun h : u₀ ⟶ V => h) x) :
    ∃! t : P.obj (op V), ∀ h : u₀ ⟶ V, P.map h.op t = x h := by
  refine
    (Presieve.isSheafFor_arrows_iff (P := P) (X := fun _ : (u₀ ⟶ V) => u₀) (π := fun h : u₀ ⟶ V =>
          h)).mp
      (hP.isSheafFor _ ?_) x hx
  exact (hcov V _).mpr fun h => ⟨u₀, 𝟙 u₀, h, Presieve.ofArrows.mk h, by simp⟩

/-- **Separatedness.** Two sections of a sheaf agreeing on all arrows out of `u₀` are equal. -/
private lemma eq_of_map_eq (P : Tᵒᵖ ⥤ Type u) (J : GrothendieckTopology T)
    (hcov : ∀ (V : T) (R : Sieve V), R ∈ J V ↔ ∀ h : u₀ ⟶ V, R.arrows h)
    (hP : Presieve.IsSheaf J P) (V : T) {s t : P.obj (op V)}
    (h : ∀ k : u₀ ⟶ V, P.map k.op s = P.map k.op t) : s = t :=
  (existsUnique_of_arrows_compatible P J hcov hP V (fun k => P.map k.op s)
        (Presieve.Arrows.toCompatible P (fun k : u₀ ⟶ V => k) s).property).unique
    (fun _ => rfl) fun k => (h k).symm

/-- Restriction along an endomorphism of `u₀` translates the index of a family of the form
`h ↦ χ(ι(h)(e))`: the endomorphism is a right translation, and `χ` is equivariant. -/
private lemma map_endo_apply (P : Tᵒᵖ ⥤ Type u) {V : T} (χ : ι.obj V ⟶ presheafAction ι α P)
    (m : u₀ ⟶ u₀) (h : u₀ ⟶ V) :
    P.map m.op (χ.hom (ptEquiv ι α V h)) = χ.hom (ptEquiv ι α V (m ≫ h)) := by
  obtain ⟨g, rfl⟩ := exists_rAct ι α m
  rw [ptEquiv_rAct_comp]
  exact (hom_apply_ρ χ g (ptEquiv ι α V h)).symm

/-- Restricting `h ↦ χ(ι(h)(e))` along `g : Z ⟶ u₀` and then along `m : u₀ ⟶ Z` translates the
index by the endomorphism `m ≫ g`. -/
private lemma map_op_comp_apply_ptEquiv (P : Tᵒᵖ ⥤ Type u) {V Z : T}
    (χ : ι.obj V ⟶ presheafAction ι α P) (m : u₀ ⟶ Z) (g : Z ⟶ u₀) (k : u₀ ⟶ V) :
    P.map m.op (P.map g.op (χ.hom (ptEquiv ι α V k))) = χ.hom (ptEquiv ι α V (m ≫ g ≫ k)) := by
  rw [map_op_comp P m g (χ.hom (ptEquiv ι α V k)), map_endo_apply ι α P χ (m ≫ g) k,
    Category.assoc]

/-- **Compatibility is automatic.** For a sheaf `P` and a `G`-map `χ : ι V ⟶ P(u₀)`, the family of
sections `h ↦ χ(ι(h)(e))` indexed by the arrows `u₀ ⟶ V` is compatible in the sense of
`Presieve.Arrows.Compatible`, which quantifies over arbitrary test objects `Z`: the two
restrictions to `Z` agree because they agree after further restriction along every arrow `u₀ ⟶ Z`,
by separatedness at `Z`, and there each is the value of `χ` at a translated index. -/
private lemma arrows_compatible_hom_ptEquiv (P : Tᵒᵖ ⥤ Type u) (J : GrothendieckTopology T)
    (hcov : ∀ (V : T) (R : Sieve V), R ∈ J V ↔ ∀ h : u₀ ⟶ V, R.arrows h)
    (hP : Presieve.IsSheaf J P) {V : T} (χ : ι.obj V ⟶ presheafAction ι α P) :
    Presieve.Arrows.Compatible P (fun h : u₀ ⟶ V => h) fun h => χ.hom (ptEquiv ι α V h) := by
  intro k₁ k₂ Z g₁ g₂ hg
  refine eq_of_map_eq P J hcov hP Z (fun m => ?_)
  rw [map_op_comp_apply_ptEquiv ι α P χ m g₁ k₁, map_op_comp_apply_ptEquiv ι α P χ m g₂ k₂, hg]

/-- **For a sheaf, `can` is bijective.** -/
private lemma bijective_can (P : Tᵒᵖ ⥤ Type u) (J : GrothendieckTopology T)
    (hcov : ∀ (V : T) (R : Sieve V), R ∈ J V ↔ ∀ h : u₀ ⟶ V, R.arrows h)
    (hP : Presieve.IsSheaf J P) (V : T) : Function.Bijective (can ι α P V) := by
  refine ⟨(injective_can_iff ι α P V).mpr fun _ _ => eq_of_map_eq P J hcov hP V, fun χ => ?_⟩
  obtain ⟨t, ht, -⟩ :=
    existsUnique_of_arrows_compatible P J hcov hP V _
      (arrows_compatible_hom_ptEquiv ι α P J hcov hP χ)
  exact ⟨t, hom_ext_pt ι α fun k => (can_apply_ptEquiv ι α P t k).trans (ht k)⟩

/-- **Amalgamation.** If `can` is surjective at `V`, an equivariant family of sections over `u₀`
indexed by the arrows `u₀ ⟶ V` is the family of restrictions of a section over `V`. -/
private lemma exists_map_op_eq_of_surjective_can (P : Tᵒᵖ ⥤ Type u) (V : T)
    (hb : Function.Surjective (can ι α P V)) (x : (u₀ ⟶ V) → P.obj (op u₀))
    (hx : IsEquivariantFamily ι α P V x) :
    ∃ s : P.obj (op V), ∀ h : u₀ ⟶ V, P.map h.op s = x h := by
  obtain ⟨s, hs⟩ := hb (ofFamily ι α P V x hx)
  refine ⟨s, fun h => ?_⟩
  rw [← can_apply_ptEquiv ι α P s h, hs, ofFamily_apply_ptEquiv ι α P V x hx h]

/-- **A presheaf for which `can` is bijective is a sheaf.** -/
private lemma isSheaf_of_bijective_can (P : Tᵒᵖ ⥤ Type u) (J : GrothendieckTopology T)
    (hcov : ∀ (V : T) (R : Sieve V), R ∈ J V ↔ ∀ h : u₀ ⟶ V, R.arrows h)
    (hb : ∀ V : T, Function.Bijective (can ι α P V)) : Presieve.IsSheaf J P := by
  intro V R hR x hx
  have hall : ∀ h : u₀ ⟶ V, R.arrows h := (hcov V R).mp hR
  have hsc := (Presieve.compatible_iff_sieveCompatible x).mp hx
  obtain ⟨s, hs⟩ :=
    exists_map_op_eq_of_surjective_can ι α P V (hb V).2 (fun h => x h (hall h)) fun g h =>
      hsc h (rAct ι α g) (hall h)
  refine ⟨s, fun W f hf => ?_, fun t ht => ?_⟩
  · refine (injective_can_iff ι α P W).mp (hb W).1 _ _ fun k => ?_
    rw [map_op_comp P k f, hs (k ≫ f)]
    exact hsc f k hf
  · exact (injective_can_iff ι α P V).mp (hb V).1 _ _ fun h => by rw [ht h (hall h), hs h]

/-! ### Restricted Yoneda -/

/-- Restricted Yoneda: the presheaf `U ↦ Mor_G(ι U, S)`, functorially in the `G`-set `S`. -/
@[implicit_reducible]
private def presheafYoneda : Action (Type u) G ⥤ Tᵒᵖ ⥤ Type u :=
  yoneda ⋙ (Functor.whiskeringLeft Tᵒᵖ (Action (Type u) G)ᵒᵖ (Type u)).obj ι.op

/-- **`F_S({}_G G) ≅ S`.** Evaluation at the base point identifies the `G`-set attached to the
presheaf `U ↦ Mor_G(ι U, S)` with `S` itself. -/
private noncomputable def presheafActionYonedaIso (S : Action (Type u) G) :
    presheafAction ι α ((presheafYoneda ι).obj S) ≅ S :=
  Action.mkIso (basePtEquiv ι α S).toIso fun g =>
    ConcreteCategory.hom_ext _ _ fun (φ : ι.obj u₀ ⟶ S) => by
      simpa [presheafAction, presheafYoneda] using basePtEquiv_rAct_comp ι α g φ

/-- On the presheaf `U ↦ Mor_G(ι U, S)` the canonical map is, up to `F_S({}_G G) ≅ S`, the
identity. -/
private lemma can_yoneda_comp (S : Action (Type u) G) (V : T) (s : ι.obj V ⟶ S) :
    can ι α ((presheafYoneda ι).obj S) V s ≫ (presheafActionYonedaIso ι α S).hom = s := by
  refine hom_ext_pt ι α fun k => ?_
  dsimp
  rw [can_apply_ptEquiv ι α ((presheafYoneda ι).obj S) s k]
  exact basePtEquiv_precomp_map ι α k s

private lemma bijective_can_yoneda (S : Action (Type u) G) (V : T) :
    Function.Bijective (can ι α ((presheafYoneda ι).obj S) V) := by
  refine
    Function.bijective_iff_has_inverse.mpr
      ⟨(· ≫ (presheafActionYonedaIso ι α S).hom), can_yoneda_comp ι α S V, fun χ => ?_⟩
  rw [← Iso.cancel_iso_hom_right _ _ (presheafActionYonedaIso ι α S), can_yoneda_comp]

include α in
private lemma isSheaf_presheafYoneda (J : GrothendieckTopology T)
    (hcov : ∀ (V : T) (R : Sieve V), R ∈ J V ↔ ∀ h : u₀ ⟶ V, R.arrows h) (S : Action (Type u) G) :
    Presieve.IsSheaf J ((presheafYoneda ι).obj S) :=
  isSheaf_of_bijective_can ι α _ J hcov (bijective_can_yoneda ι α S)

/-- Restricted Yoneda as a functor to sheaves. -/
private noncomputable def sheafYoneda (J : GrothendieckTopology T)
    (hcov : ∀ (V : T) (R : Sieve V), R ∈ J V ↔ ∀ h : u₀ ⟶ V, R.arrows h) :
    Action (Type u) G ⥤ Sheaf J (Type u) :=
  ObjectProperty.lift _ (presheafYoneda ι) fun S =>
    (isSheaf_iff_isSheaf_of_type J _).mpr (isSheaf_presheafYoneda ι α J hcov S)

/-! ### Restricted Yoneda is an equivalence -/

omit [ι.Full] [ι.Faithful] in
/-- Naturality of a morphism of restricted-Yoneda presheaves, read at the component at `u₀`. -/
private lemma app_precomp {S S' : Action (Type u) G}
    (η : (presheafYoneda ι).obj S ⟶ (presheafYoneda ι).obj S') {V : T} (k : u₀ ⟶ V)
    (φ : ι.obj V ⟶ S) : η.app (op u₀) (ι.map k ≫ φ) = ι.map k ≫ η.app (op V) φ :=
  ConcreteCategory.congr_hom (η.naturality k.op) φ

/-- The `G`-map underlying a morphism of restricted-Yoneda presheaves: its component at `u₀`, read
through `F_S({}_G G) ≅ S` at both ends. -/
private noncomputable def ofNatTrans {S S' : Action (Type u) G}
    (η : (presheafYoneda ι).obj S ⟶ (presheafYoneda ι).obj S') : S ⟶ S' :=
  (presheafActionYonedaIso ι α S).inv ≫
    presheafActionMap ι α η ≫ (presheafActionYonedaIso ι α S').hom

private lemma ofNatTrans_apply {S S' : Action (Type u) G}
    (η : (presheafYoneda ι).obj S ⟶ (presheafYoneda ι).obj S') (φ : ι.obj u₀ ⟶ S) :
    (ofNatTrans ι α η).hom (basePtEquiv ι α S φ) = basePtEquiv ι α S' (η.app (op u₀) φ) := by
  simp [ofNatTrans, presheafActionYonedaIso, presheafActionMap]

/-- `ofNatTrans` is a retraction of restricted Yoneda on morphisms: this is faithfulness. -/
private lemma ofNatTrans_presheafYoneda_map {S S' : Action (Type u) G} (f : S ⟶ S') :
    ofNatTrans ι α ((presheafYoneda ι).map f) = f :=
  Action.hom_ext _ _
    (ConcreteCategory.hom_ext _ _ fun (y : S.V) => by
      simp [ofNatTrans, presheafActionYonedaIso, presheafActionMap, presheafYoneda,
        basePtEquiv_comp ι α ((basePtEquiv ι α S).symm y) f])

/-- `ofNatTrans` is a section of restricted Yoneda on morphisms: this is fullness. -/
private lemma presheafYoneda_map_ofNatTrans {S S' : Action (Type u) G}
    (η : (presheafYoneda ι).obj S ⟶ (presheafYoneda ι).obj S') :
    (presheafYoneda ι).map (ofNatTrans ι α η) = η := by
  refine NatTrans.ext (funext fun V => ?_)
  obtain ⟨V⟩ := V
  refine ConcreteCategory.hom_ext _ _ fun (φ : ι.obj V ⟶ S) => ?_
  dsimp [presheafYoneda]
  refine hom_ext_pt ι α fun k => ?_
  rw [Action.comp_hom, types_comp_apply, ← basePtEquiv_precomp_map ι α k φ,
    ofNatTrans_apply ι α η (ι.map k ≫ φ), app_precomp ι η k φ,
    basePtEquiv_precomp_map ι α k (η.app (op V) φ)]

/-- **Restricted Yoneda is fully faithful**: on morphisms it is a bijection, with inverse
`ofNatTrans`. -/
private noncomputable def fullyFaithfulPresheafYoneda : (presheafYoneda ι).FullyFaithful where
  preimage η := ofNatTrans ι α η
  map_preimage η := presheafYoneda_map_ofNatTrans ι α η
  preimage_map f := ofNatTrans_presheafYoneda_map ι α f

private lemma faithful_sheafYoneda (J : GrothendieckTopology T)
    (hcov : ∀ (V : T) (R : Sieve V), R ∈ J V ↔ ∀ h : u₀ ⟶ V, R.arrows h) :
    (sheafYoneda ι α J hcov).Faithful :=
  by
  haveI : (presheafYoneda ι).Faithful := (fullyFaithfulPresheafYoneda ι α).faithful
  exact Functor.Faithful.of_comp_eq (F := sheafYoneda ι α J hcov)
    (G := sheafToPresheaf J (Type u)) (H := presheafYoneda ι) rfl

private lemma full_sheafYoneda (J : GrothendieckTopology T)
    (hcov : ∀ (V : T) (R : Sieve V), R ∈ J V ↔ ∀ h : u₀ ⟶ V, R.arrows h) :
    (sheafYoneda ι α J hcov).Full :=
  by
  haveI : (presheafYoneda ι).Full := (fullyFaithfulPresheafYoneda ι α).full
  haveI : (sheafToPresheaf J (Type u)).Faithful := (fullyFaithfulSheafToPresheaf J (Type u)).faithful
  exact Functor.Full.of_comp_faithful_iso (F := sheafYoneda ι α J hcov)
    (G := sheafToPresheaf J (Type u)) (H := presheafYoneda ι) (Iso.refl _)

private lemma essSurj_sheafYoneda (J : GrothendieckTopology T)
    (hcov : ∀ (V : T) (R : Sieve V), R ∈ J V ↔ ∀ h : u₀ ⟶ V, R.arrows h) :
    (sheafYoneda ι α J hcov).EssSurj
    where
  mem_essImage H := by
    have hH : Presieve.IsSheaf J H.obj := (isSheaf_iff_isSheaf_of_type J _).mp H.property
    refine
      ⟨presheafAction ι α H.obj,
        ⟨(fullyFaithfulSheafToPresheaf J (Type u)).preimageIso
            (NatIso.ofComponents
                (fun V => (Equiv.ofBijective _ (bijective_can ι α H.obj J hcov hH V.unop)).toIso)
                ?_).symm⟩⟩
    intro V W f
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    change can ι α H.obj W.unop (H.obj.map f s) = ι.map f.unop ≫ can ι α H.obj V.unop s
    exact can_naturality ι α H.obj f.unop s

end Site

end Stacks.Sites.GSetSheaves

@[expose] public section

open Stacks.Sites.GSetSheaves in
/-- **Stacks 00W0**. Sheaves on `𝒯_G` are `G`-sets: let `G` be a monoid and let `J` be a
Grothendieck topology on a full subcategory `ι : T ⥤ Action (Type u) G` of the category of `G`-sets
whose essential image contains the left regular `G`-set `{}_G G` and whose covering sieves are
exactly the jointly surjective ones. Then `G`-sets are equivalent to the sheaves of sets on
`(T, J)` by an equivalence whose forward functor sends a `G`-set `S` to the sheaf
`U ↦ Hom_G(ι U, S)`; the quasi-inverse is `F ↦ F({}_G G)`. The source states this for a group. -/
@[stacks 00W0, sga "4 IV 2.3" "special case", sga "4 IV 9.1.12" "Clause e)"]
public theorem Action.exists_equivalence_sheaf {T : Type w} [Category.{v} T] {G : Type u}
    [Monoid G] (ι : T ⥤ Action (Type u) G) [ι.Full] [ι.Faithful]
    (hreg : ι.essImage (Action.leftRegular G)) (J : GrothendieckTopology T)
    (hJ :
      ∀ (U : T) (S : Sieve U),
        S ∈ J U ↔
          ∀ a : Action.leftRegular G ⟶ ι.obj U,
            ∃ (V : T) (f : V ⟶ U) (b : Action.leftRegular G ⟶ ι.obj V),
              S.arrows f ∧ b ≫ ι.map f = a) :
    ∃ e : Action (Type u) G ≌ Sheaf J (Type u),
      e.functor ⋙ sheafToPresheaf J (Type u) =
        yoneda ⋙ (Functor.whiskeringLeft Tᵒᵖ (Action (Type u) G)ᵒᵖ (Type u)).obj ι.op := by
  obtain ⟨u₀, ⟨α⟩⟩ := hreg
  have hcov := mem_iff_forall_hom ι α J hJ
  have : (sheafYoneda ι α J hcov).IsEquivalence :=
    { faithful := faithful_sheafYoneda ι α J hcov
      full := full_sheafYoneda ι α J hcov
      essSurj := essSurj_sheafYoneda ι α J hcov }
  exact ⟨(sheafYoneda ι α J hcov).asEquivalence, rfl⟩

end

end

end CategoryTheory.Sites.Sheaf
