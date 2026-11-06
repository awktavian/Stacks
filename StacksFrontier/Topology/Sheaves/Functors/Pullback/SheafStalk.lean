module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.LocalSite
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
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Functors
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stalk of the pullback sheaf

For a continuous map `f : X ⟶ Y` and a sheaf of sets `G` on `Y`, the stalk of
the pullback sheaf `f⁻¹ G` at a point `x : X` is canonically isomorphic to the
stalk of `G` at `f x`.

## Main definitions

* `stalkPullbackSheafIso`: the isomorphism `(f⁻¹ G)_x ≅ G_{f x}`.

## Main results

* `stalkPullbackSheafIso_inv_germ`: the inverse of `stalkPullbackSheafIso` sends the germ of a
  section `s` of `G` to the germ of the pullback of `s`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace TopCat TopCat.Presheaf

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/--
For a continuous map `f : X ⟶ Y` of topological spaces, a point `x : X`, and a sheaf of sets `G`
on `Y`, the canonical isomorphism between the stalk of the pullback sheaf `f⁻¹ G` at `x` and the
stalk of `G` at `f x`.
-/
@[stacks 008H, sga "4 IV 7.1" "partial"]
noncomputable def stalkPullbackSheafIso (G : Y.Sheaf (Type u)) (x : X) :
    ((TopCat.Sheaf.pullback (Type u) f).obj G).presheaf.stalk x ≅
      G.presheaf.stalk (f x) := by
  refine (Presheaf.stalkFunctor (Type u) x).mapIso
    ((TopCat.Sheaf.forget (Type u) X).mapIso ((TopCat.Sheaf.pullbackIso (Type u) f).app G)) ≪≫ ?_
  have hIso :
      IsIso ((Presheaf.stalkFunctor (Type u) x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          ((Presheaf.pullback (Type u) f).obj
            ((TopCat.Sheaf.forget (Type u) Y).obj G)))) :=
    Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (Type u) _
  exact (@asIso _ _ _ _ _ hIso).symm ≪≫ (Presheaf.stalkPullbackIso (Type u) f
    ((TopCat.Sheaf.forget (Type u) Y).obj G) x).symm

open Opposite

/-- Comparing the two models of the sheaf pullback carries the unit of one adjunction to the unit
of the other. -/
lemma pullbackIso_unit {Y Z : TopCat.{u}} (g : Z ⟶ Y)
    (F : Y.Sheaf (Type u)) (V : Opens Y) (s : F.obj.obj (op V)) :
    ((TopCat.Sheaf.pullbackIso (Type u) g).app F).hom.hom.app
      (op ((Opens.map g).obj V))
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app F).hom.app
        (op V) s) =
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map g) (Type u) (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology Z)).unit.app F).hom.app (op V)) s := by
  let adj₁ := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g
  let adj₂ := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map g) (Type u) (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology Z)
  exact congrArg (fun m : F ⟶ (TopCat.Sheaf.pushforward (Type u) g).obj
      ((presheafToSheaf (Opens.grothendieckTopology Z) (Type u)).obj
        ((TopCat.Presheaf.pullback (Type u) g).obj F.presheaf)) ↦
      m.hom.app (op V) s) (adj₁.unit_leftAdjointUniq_hom_app adj₂ F)

/-- The unit of the constructed sheaf pullback adjunction is the sheafification of the unit of the
presheaf pullback adjunction. -/
lemma pullbackConstruction_unit {Y Z : TopCat.{u}} (g : Z ⟶ Y)
    (F : Y.Sheaf (Type u)) (V : Opens Y) (s : F.obj.obj (op V)) :
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map g) (Type u) (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology Z)).unit.app F).hom.app (op V)) s =
      (toSheafify (Opens.grothendieckTopology Z)
        ((TopCat.Presheaf.pullback (Type u) g).obj F.presheaf)).app
        (op ((Opens.map g).obj V))
          (((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) g).unit.app
            F.presheaf).app (op V) s) :=
  rfl

/-- The identification of the stalks of a pullback sheaf sends the germ of a section of the
pullback coming from `s` to the germ of `s`. -/
lemma stalkPullbackSheafIso_inv_germ {Y Z : TopCat.{u}} (g : Z ⟶ Y)
    (F : Y.Sheaf (Type u)) (z : Z) (V : Opens Y) (hz : g z ∈ V)
    (s : F.obj.obj (op V)) :
    (stalkPullbackSheafIso g F z).inv (F.presheaf.germ V (g z) hz s) =
      ((TopCat.Sheaf.pullback (Type u) g).obj F).presheaf.germ
        ((Opens.map g).obj V) z hz
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app F).hom.app
          (op V) s) := by
  let W := (Opens.map g).obj V
  let P := (TopCat.Presheaf.pullback (Type u) g).obj F.presheaf
  let Q := (presheafToSheaf (Opens.grothendieckTopology Z) (Type u)).obj P
  let H := (TopCat.Sheaf.pullback (Type u) g).obj F
  let η := toSheafify (Opens.grothendieckTopology Z) P
  let e : H.presheaf ≅ Q.obj :=
    (TopCat.Sheaf.forget (Type u) Z).mapIso ((TopCat.Sheaf.pullbackIso (Type u) g).app F)
  have hzW : z ∈ W := hz
  let t := ((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) g).unit.app
    F.presheaf).app (op V) s
  let t' := ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app F).hom.app
    (op V) s
  have hu : e.hom.app (op W) t' = η.app (op W) t :=
    (pullbackIso_unit g F V s).trans (pullbackConstruction_unit g F V s)
  have hu' : e.inv.app (op W) (η.app (op W) t) = t' := by
    rw [← hu]
    exact congrArg (fun f : H.presheaf ⟶ H.presheaf ↦ f.app (op W) t') e.hom_inv_id
  have h₁ : (TopCat.Presheaf.stalkPullbackIso (Type u) g F.presheaf z).hom
      (F.presheaf.germ V (g z) hz s) = P.germ W z hzW t :=
    ConcreteCategory.congr_hom
      (TopCat.Presheaf.germ_stalkPullbackHom (Type u) g F.presheaf z V hz) s
  have h₂ := TopCat.Presheaf.stalkFunctor_map_germ_apply W z hzW η t
  have h₃ := TopCat.Presheaf.stalkFunctor_map_germ_apply W z hzW e.inv
    (η.app (op W) t)
  show ((TopCat.Presheaf.stalkFunctor (Type u) z).map e.inv)
      (((TopCat.Presheaf.stalkFunctor (Type u) z).map η)
        ((TopCat.Presheaf.stalkPullbackIso (Type u) g F.presheaf z).hom
          (F.presheaf.germ V (g z) hz s))) = H.presheaf.germ W z hzW t'
  rw [h₁, h₂, h₃, hu']
