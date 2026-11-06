module

public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
public import Mathlib.LinearAlgebra.TensorAlgebra.Grading
public import Mathlib.LinearAlgebra.TensorProduct.Submodule

/-!
# The external tensor powers are the homogeneous pieces of the tensor algebra

The degree-`n` part of `TensorAlgebra R M` has two descriptions. Externally it is the `n`-fold
tensor power `⨂[R]^n M`, mapped in by `TensorPower.toTensorAlgebra`, and the direct sum of these
powers is the whole algebra (`TensorAlgebra.equivDirectSum`). Internally it is the submodule
`LinearMap.range (TensorAlgebra.ι R) ^ n`, the grading of `TensorAlgebra.gradedAlgebra`. This file
shows that `TensorPower.toTensorAlgebra` is injective with range exactly that submodule, and
draws the consequence the graded algebra of a sheaf of modules needs: multiplication
`(range ι ^ i) ⊗ (range ι ^ j) → range ι ^ (i + j)` is an isomorphism.

The comparison is what lets a statement about the tensor powers of a module be read as a
statement about the homogeneous pieces of its tensor algebra, and conversely. The second
reading is the one Stacks Section 17.21 uses: the tensor algebra of a sheaf of modules has its
degree-`n` piece identified with the `n`-fold tensor power, and sectionwise that identification
*is* `TensorAlgebra.powRangeMulEquiv` iterated, because the comparison is multiplication.

## Main definitions

* `TensorPower.toTensorAlgebraEquiv`: the linear equivalence
  `⨂[R]^n M ≃ₗ[R] ↥(LinearMap.range (ι R) ^ n)` induced by `TensorPower.toTensorAlgebra`.
* `TensorAlgebra.powRangeMulEquiv`: multiplication as an isomorphism
  `↥(range ι ^ i) ⊗[R] ↥(range ι ^ j) ≃ₗ[R] ↥(range ι ^ (i + j))`.
* `TensorAlgebra.powRangeMulEquivOfEq`: the same with the target degree `k` supplied by an
  equation `i + j = k`.

## Main results

* `TensorAlgebra.toDirectSum_toTensorAlgebra`: `TensorAlgebra.toDirectSum` takes the image of a
  single tensor power back to that summand, which is what makes the comparison injective.
* `TensorPower.toTensorAlgebra_injective`: `TensorPower.toTensorAlgebra` is injective.
* `TensorPower.range_toTensorAlgebra`: the range of `TensorPower.toTensorAlgebra` on `⨂[R]^n M`
  is `LinearMap.range (TensorAlgebra.ι R) ^ n`.
* `TensorAlgebra.mulMap_pow_range_ι_injective`: multiplication on the homogeneous pieces is
  injective. Surjectivity onto `range ι ^ (i + j)` is Mathlib's
  `Submodule.mulMap'_surjective` together with `pow_add`.

## Implementation notes

Both halves of the comparison are proved from the external side, without the span description
of a homogeneous piece (`TensorAlgebra.pow_range_ι_eq_span_prod_ι`), and nothing needs `R` to be
a ring or `M` to be a group: the file works at Mathlib's generality for `TensorPower`,
`CommSemiring R` and `AddCommMonoid M`.

The induction in `TensorPower.range_toTensorAlgebra` peels a degree-one factor off the right
(`pow_succ`), for a reason that recurs in every consumer: `TensorPower.mulEquiv` lands in degree
`n + m`, so degree `n + 1` is definitionally the successor, while `1 + n` is only
propositionally equal to it, and every step would then carry a degree transport.
`powRangeMulEquivOfEq` exists so that a consumer forced into the left-handed shape pays that
transport once, as an equation between naturals, instead of inside a term.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open scoped DirectSum TensorProduct

noncomputable section

universe uR uM

variable {R : Type uR} {M : Type uM} [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace TensorAlgebra

/-- Assembling a single tensor power into the direct sum and then into the tensor algebra is the
canonical map out of that tensor power.  The `tprod` case of this is
`TensorAlgebra.ofDirectSum_of_tprod`. -/
theorem ofDirectSum_of {n : ℕ} (x : ⨂[R]^n M) :
    ofDirectSum (DirectSum.of (fun i => ⨂[R]^i M) n x) = TensorPower.toTensorAlgebra x := by
  refine PiTensorProduct.induction_on' x ?_ ?_
  · intro r f
    rw [PiTensorProduct.tprodCoeff_eq_smul_tprod, DirectSum.of_smul, map_smul,
      ofDirectSum_of_tprod, map_smul, TensorPower.toTensorAlgebra_tprod]
  · intro y z hy hz
    rw [map_add, map_add, hy, hz, map_add]

/-- Decomposing the image of a tensor power returns that tensor power, in its own degree. -/
theorem toDirectSum_toTensorAlgebra {n : ℕ} (x : ⨂[R]^n M) :
    toDirectSum (TensorPower.toTensorAlgebra x) = DirectSum.of (fun i => ⨂[R]^i M) n x := by
  rw [← ofDirectSum_of, toDirectSum_ofDirectSum]

end TensorAlgebra

namespace TensorPower

/-- **Each tensor power embeds into the tensor algebra.** -/
theorem toTensorAlgebra_injective (n : ℕ) :
    Function.Injective (toTensorAlgebra (R := R) (M := M) (n := n)) := by
  intro x y h
  refine DirectSum.of_injective (β := fun i => ⨂[R]^i M) n ?_
  rw [← TensorAlgebra.toDirectSum_toTensorAlgebra, ← TensorAlgebra.toDirectSum_toTensorAlgebra, h]

/-- The canonical maps out of the tensor powers turn the graded multiplication
`TensorPower.mulEquiv` into multiplication in the tensor algebra. -/
theorem toTensorAlgebra_mulEquiv {i j : ℕ} (a : ⨂[R]^i M) (b : ⨂[R]^j M) :
    toTensorAlgebra (mulEquiv (a ⊗ₜ[R] b)) = toTensorAlgebra a * toTensorAlgebra b := by
  rw [← gMul_def, toTensorAlgebra_gMul]

/-- A submodule containing the images of all pure tensors contains the image of the tensor power. -/
private theorem toTensorAlgebra_mem_of_tprod {n : ℕ} (N : Submodule R (TensorAlgebra R M))
    (h : ∀ f : Fin n → M, TensorAlgebra.tprod R M n f ∈ N) (x : ⨂[R]^n M) :
    toTensorAlgebra x ∈ N := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f => rw [map_smul, toTensorAlgebra_tprod]; exact N.smul_mem r (h f)
  | add x y hx hy => rw [map_add]; exact N.add_mem hx hy

/-- The first tensor power maps onto the degree-one generators. -/
theorem toTensorAlgebra_mem_range_ι (b : ⨂[R]^1 M) :
    toTensorAlgebra b ∈ LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) := by
  refine toTensorAlgebra_mem_of_tprod _ (fun f => ?_) b
  rw [TensorAlgebra.tprod_apply]
  simp

/-- **The image of the `n`-th tensor power is the degree-`n` homogeneous piece.**  The right-hand
side is the grading of `TensorAlgebra.gradedAlgebra`. -/
theorem range_toTensorAlgebra (n : ℕ) :
    LinearMap.range (toTensorAlgebra (R := R) (M := M) (n := n)) =
      LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ n := by
  induction n with
  | zero =>
      refine le_antisymm ?_ (Submodule.one_le.mpr ⟨_, toTensorAlgebra_gOne⟩)
      rintro _ ⟨x, rfl⟩
      refine toTensorAlgebra_mem_of_tprod _ (fun f => ?_) x
      rw [TensorAlgebra.tprod_apply]
      simp only [List.ofFn_zero, List.prod_nil, pow_zero]
      exact Submodule.one_le.mp le_rfl
  | succ n ih =>
      refine le_antisymm ?_ ?_
      · rintro _ ⟨z, rfl⟩
        obtain ⟨w, rfl⟩ := (mulEquiv (R := R) (M := M) (n := n) (m := 1)).surjective z
        induction w using TensorProduct.inductionOn with
        | tmul a b =>
            rw [toTensorAlgebra_mulEquiv, pow_succ]
            exact Submodule.mul_mem_mul (ih ▸ LinearMap.mem_range_self _ a)
              (by simpa only [pow_one] using toTensorAlgebra_mem_range_ι b)
        | add x y hx hy =>
            rw [map_add, map_add]
            exact Submodule.add_mem _ hx hy
      · rw [pow_succ]
        refine Submodule.mul_le.mpr fun x hx y hy => ?_
        obtain ⟨a, rfl⟩ : ∃ a, toTensorAlgebra a = x := by rwa [← ih] at hx
        obtain ⟨m, rfl⟩ := hy
        exact ⟨mulEquiv (a ⊗ₜ[R] PiTensorProduct.tprod R fun _ : Fin 1 => m), by
          rw [toTensorAlgebra_mulEquiv, toTensorAlgebra_tprod, TensorAlgebra.tprod_apply]
          simp⟩

/-- The canonical map identifies the `n`-th tensor power of `M` with the degree-`n` homogeneous
piece of `TensorAlgebra R M`, the `n`-th power of the range of `TensorAlgebra.ι`. -/
def toTensorAlgebraEquiv (n : ℕ) :
    ⨂[R]^n M ≃ₗ[R]
      ↥(LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ n) :=
  (LinearEquiv.ofInjective _ (toTensorAlgebra_injective n)).trans
    (LinearEquiv.ofEq _ _ (range_toTensorAlgebra n))

/-- The image of `x` under `TensorPower.toTensorAlgebraEquiv n` is
`TensorPower.toTensorAlgebra x`. -/
@[simp]
theorem coe_toTensorAlgebraEquiv (n : ℕ) (x : ⨂[R]^n M) :
    (toTensorAlgebraEquiv n x : TensorAlgebra R M) = toTensorAlgebra x := rfl

end TensorPower

namespace TensorAlgebra

/-- Under `TensorPower.toTensorAlgebraEquiv`, multiplication of homogeneous pieces is the graded
multiplication of tensor powers. This is the naturality that makes `powRangeMulEquiv` an
isomorphism. -/
theorem mulMap_congr_toTensorAlgebraEquiv (i j : ℕ) (w : (⨂[R]^i M) ⊗[R] (⨂[R]^j M)) :
    Submodule.mulMap (LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ i)
        (LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ j)
        (TensorProduct.congr (TensorPower.toTensorAlgebraEquiv i)
          (TensorPower.toTensorAlgebraEquiv j) w) =
      TensorPower.toTensorAlgebra (TensorPower.mulEquiv w) := by
  induction w using TensorProduct.inductionOn with
  | tmul a b =>
      rw [TensorProduct.congr_tmul, Submodule.mulMap_tmul,
        TensorPower.coe_toTensorAlgebraEquiv, TensorPower.coe_toTensorAlgebraEquiv,
        TensorPower.toTensorAlgebra_mulEquiv]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

/-- Multiplication of homogeneous pieces of the tensor algebra is injective on their tensor
product: there are no relations beyond the ones already present in the tensor product. -/
theorem mulMap_pow_range_ι_injective (i j : ℕ) :
    Function.Injective
      (Submodule.mulMap (LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ i)
        (LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ j)) := by
  intro x y h
  set e := TensorProduct.congr (TensorPower.toTensorAlgebraEquiv (R := R) (M := M) i)
    (TensorPower.toTensorAlgebraEquiv (R := R) (M := M) j) with he
  obtain ⟨x', rfl⟩ := e.surjective x
  obtain ⟨y', rfl⟩ := e.surjective y
  rw [he, mulMap_congr_toTensorAlgebraEquiv, mulMap_congr_toTensorAlgebraEquiv] at h
  exact congrArg _ (TensorPower.mulEquiv.injective
    (TensorPower.toTensorAlgebra_injective _ h))

/-- The corestriction of `Submodule.mulMap` to the product submodule is injective as well. -/
theorem mulMap'_pow_range_ι_injective (i j : ℕ) :
    Function.Injective
      (Submodule.mulMap' (LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ i)
        (LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ j)) := fun _ _ h =>
  mulMap_pow_range_ι_injective i j (congrArg Subtype.val h)

/-- **Multiplication identifies the tensor product of two homogeneous pieces of the tensor
algebra with the piece in the sum of the degrees.** -/
def powRangeMulEquiv (i j : ℕ) :
    ↥(LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ i) ⊗[R]
        ↥(LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ j) ≃ₗ[R]
      ↥(LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ (i + j)) :=
  (LinearEquiv.ofBijective _
      ⟨mulMap'_pow_range_ι_injective i j, Submodule.mulMap'_surjective _ _⟩).trans
    (LinearEquiv.ofEq _ _ (pow_add _ i j).symm)

/-- `TensorAlgebra.powRangeMulEquiv i j` sends `a ⊗ₜ b` to the product `a * b`. -/
@[simp]
theorem coe_powRangeMulEquiv_tmul (i j : ℕ)
    (a : ↥(LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ i))
    (b : ↥(LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ j)) :
    (powRangeMulEquiv i j (a ⊗ₜ[R] b) : TensorAlgebra R M) = (a : TensorAlgebra R M) * b := rfl

/-- `TensorAlgebra.powRangeMulEquiv` with the target degree `k` supplied by an equation
`i + j = k`, so that a consumer whose degrees are presented as `1 + (n + 1)` rather than `n + 2`
pays the transport once and outside the term. -/
def powRangeMulEquivOfEq {i j k : ℕ} (h : i + j = k) :
    ↥(LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ i) ⊗[R]
        ↥(LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ j) ≃ₗ[R]
      ↥(LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ k) :=
  (powRangeMulEquiv i j).trans (LinearEquiv.ofEq _ _ (by rw [h]))

/-- `TensorAlgebra.powRangeMulEquivOfEq h` sends `a ⊗ₜ b` to the product `a * b`. -/
@[simp]
theorem coe_powRangeMulEquivOfEq_tmul {i j k : ℕ} (h : i + j = k)
    (a : ↥(LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ i))
    (b : ↥(LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ j)) :
    (powRangeMulEquivOfEq h (a ⊗ₜ[R] b) : TensorAlgebra R M) = (a : TensorAlgebra R M) * b := rfl

end TensorAlgebra

end

end
