module

public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.CategoryTheory.Abelian.Refinements
import StacksCore.Tactic.StacksAttribute

/-! ## Snake Lemma -/

add_to_stacks 07JW CategoryTheory.ShortComplex.SnakeInput.snake_lemma
add_to_stacks 010H CategoryTheory.ShortComplex.SnakeInput.snake_lemma
add_to_stacks 08N7 CategoryTheory.ShortComplex.SnakeInput.naturality_δ

@[expose] public section

open CategoryTheory Limits Opposite

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C]

section KernelShortComplex

variable (S : ShortComplex C) {Y₁ Y₂ Y₃ : C} {k : Y₁ ⟶ Y₂} {l : Y₂ ⟶ Y₃}
  {α : S.X₁ ⟶ Y₁} {β : S.X₂ ⟶ Y₂} {γ : S.X₃ ⟶ Y₃}
  (comm₁ : α ≫ k = S.f ≫ β) (comm₂ : β ≫ l = S.g ≫ γ)

/-- Given a commutative ladder

```
S.X₁ ⟶ S.X₂ ⟶ S.X₃
 |      |      |
 α      β      γ
 v      v      v
 Y₁  ⟶  Y₂  ⟶  Y₃
```

in an abelian category, the induced short complex `kernel α ⟶ kernel β ⟶ kernel γ` on the
kernels of the vertical maps. The second row is not assumed to be a complex. -/
noncomputable abbrev kernelShortComplex : ShortComplex C :=
  ShortComplex.mk (kernel.map α β S.f k comm₁) (kernel.map β γ S.g l comm₂)
    (by rw [← cancel_mono (kernel.ι γ)]; simp)

variable {S}

/-- If the first row of a commutative ladder in an abelian category is exact and the first map
of the second row is a monomorphism, then the induced short complex
`kernel α ⟶ kernel β ⟶ kernel γ` is exact. -/
@[stacks 08N6 "(1)"]
lemma Exact.exact_kernelShortComplex (hS : S.Exact) [Mono k] :
    (S.kernelShortComplex comm₁ comm₂).Exact :=
    exact_iff_exact_up_to_refinements _|>.2 fun A x₂ hx₂ ↦ by
  obtain ⟨A', π, hπ, x₁, hx₁⟩ := hS.exact_up_to_refinements (x₂ ≫ kernel.ι β)
    (by simpa using hx₂ =≫ kernel.ι γ)
  refine ⟨A', π, hπ, kernel.lift α x₁ ?_, ?_⟩
  · rw [← cancel_mono k, Category.assoc, comm₁, ← Category.assoc, ← hx₁]
    simp
  · simpa [← cancel_mono (kernel.ι β)]

end KernelShortComplex

section CokernelShortComplex

variable (T : ShortComplex C) {Y₁ Y₂ Y₃ : C} {f : Y₁ ⟶ Y₂} {g : Y₂ ⟶ Y₃}
  {α : Y₁ ⟶ T.X₁} {β : Y₂ ⟶ T.X₂} {γ : Y₃ ⟶ T.X₃}
  (comm₁ : α ≫ T.f = f ≫ β) (comm₂ : β ≫ T.g = g ≫ γ)

/-- Given a commutative ladder

```
 Y₁  ⟶  Y₂  ⟶  Y₃
 |      |      |
 α      β      γ
 v      v      v
T.X₁ ⟶ T.X₂ ⟶ T.X₃
```

in an abelian category, the induced short complex `cokernel α ⟶ cokernel β ⟶ cokernel γ` on
the cokernels of the vertical maps. The first row is not assumed to be a complex. -/
noncomputable abbrev cokernelShortComplex : ShortComplex C :=
  ShortComplex.mk (cokernel.map α β f T.f comm₁) (cokernel.map β γ g T.g comm₂)
    (by simp [← cancel_epi (cokernel.π α)])

/-- The short complex of kernels induced by the opposite of a commutative ladder identifies
with the opposite of the short complex of cokernels induced by the ladder, via `kernelOpOp` on
each component. -/
noncomputable def kernelShortComplexOpIso
    (w₁ : γ.op ≫ g.op = T.op.f ≫ β.op) (w₂ : β.op ≫ f.op = T.op.g ≫ α.op) :
    T.op.kernelShortComplex w₁ w₂ ≅ (T.cokernelShortComplex comm₁ comm₂).op :=
  have sq₁ :  kernel.map γ.op β.op T.op.f g.op w₁ ≫ (kernelOpOp β).hom =
      (kernelOpOp γ).hom ≫ (cokernel.map β γ g T.g comm₂).op  := by
    simp only [← cancel_mono (cokernel.π β).op, op_f, kernelOpOp, op_unop, kernelOpUnop,
      Iso.symm_hom, Iso.op_inv, Category.assoc, ← op_comp, cokernel.π_desc, Quiver.Hom.op_unop,
      kernel.lift_ι, cokernel.π_desc_assoc]
    simp
  have sq₂ : kernel.map β.op α.op T.op.g f.op w₂ ≫ (kernelOpOp α).hom =
      (kernelOpOp β).hom ≫ (cokernel.map α β f T.f comm₁).op := by
    simp only [← cancel_mono (cokernel.π α).op, op_g, kernelOpOp, op_unop, kernelOpUnop,
      Iso.symm_hom, Iso.op_inv, Category.assoc, ← op_comp, cokernel.π_desc, Quiver.Hom.op_unop,
      kernel.lift_ι, cokernel.π_desc_assoc]
    simp
  isoMk (kernelOpOp γ) (kernelOpOp β) (kernelOpOp α) sq₁.symm sq₂.symm

variable {T}

/-- If the second row of a commutative ladder in an abelian category is exact and the second
map of the first row is an epimorphism, then the induced short complex
`cokernel α ⟶ cokernel β ⟶ cokernel γ` is exact. -/
@[stacks 08N6 "(2)"]
lemma Exact.exact_cokernelShortComplex (hT : T.Exact) [Epi g] :
    (T.cokernelShortComplex comm₁ comm₂).Exact := exact_op_iff _|>.1 <|
  exact_of_iso (kernelShortComplexOpIso T comm₁ comm₂
      (show γ.op ≫ g.op = T.g.op ≫ β.op by rw [← op_comp, ← op_comp, comm₂])
      (show β.op ≫ f.op = T.f.op ≫ α.op by rw [← op_comp, ← op_comp, comm₁]))
    (hT.op.exact_kernelShortComplex _ _)

end CokernelShortComplex

end CategoryTheory.ShortComplex
