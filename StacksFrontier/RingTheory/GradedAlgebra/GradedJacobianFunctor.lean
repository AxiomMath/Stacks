module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import StacksFrontier.RingTheory.GradedAlgebra.GradedJacobian

/-!
# The cokernel of the graded Jacobian as a functor of the test module

The proof of the tangent-space half of Stacks 0DVZ (`examples-defos.tex:683`) maps the set of
first-order deformations of a graded `k`-algebra `P` into the `k`-vector space

`W = Coker(P_{d_1} ⊕ … ⊕ P_{d_n} → P_{e_1} ⊕ … ⊕ P_{e_m})`

of its graded Jacobian. The criterion that turns such a map into finite-dimensionality of the
tangent space, `Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection`, needs
not a single vector space but an **additive `k`-linear functor** on finitely generated
`k`-modules, because the vector-space structure of Stacks 06IH is defined through the whole
functor `V ↦ 𝓕(k[V])` and not through its value at `k`. This file supplies that functor.

The functor is `V ↦ W ⊗[k] V`. That is Stacks' functor: over a field `- ⊗ V` is exact, so
`W ⊗ V` is the cokernel of the Jacobian base-changed to `V`, which is what a deformation over
`k[V]` records. Taking the tensor product of the *already formed* cokernel rather than the
cokernel of the base-changed Jacobian is what makes additivity and `k`-linearity immediate: no
functoriality of a cokernel is needed.

## Main results

* `FGModuleCat.tensorLeftToModuleCat`: tensoring a fixed module with a finitely generated
  module, as a functor `FGModuleCat k ⥤ ModuleCat k`, together with its `Functor.Additive`
  and `Functor.Linear k` instances.
* `GradedAlgebra.gradedJacobianCokernelFunctor`: the functor `V ↦ W ⊗[k] V` for `W` the
  cokernel of the graded Jacobian of a weighted graded presentation.
* `GradedAlgebra.finiteDimensional_gradedJacobianCokernelFunctor_obj`: its value at the
  rank-one module is finite-dimensional.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

namespace FGModuleCat

universe w u₂

variable {k : Type w} [Field k] (W : Type u₂) [AddCommGroup W] [Module k W]

/-- **Tensoring with a fixed module, as a functor on finitely generated modules.** The target
is `ModuleCat k` rather than `FGModuleCat k` because `W` is not assumed finitely generated;
in the application it is, but the criterion of
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection` asks for a
`ModuleCat`-valued functor anyway. -/
def tensorLeftToModuleCat : FGModuleCat.{w} k ⥤ ModuleCat.{max w u₂} k where
  obj V := ModuleCat.of k (W ⊗[k] (V : Type w))
  map f := ModuleCat.ofHom (LinearMap.lTensor W f.hom.hom)
  map_id V := by ext ξ; simp
  map_comp f g := by ext ξ; simp

/-- The functor `tensorLeftToModuleCat W` is additive. -/
instance : (tensorLeftToModuleCat (k := k) W).Additive where
  map_add := by
    intro V V' f g
    refine ModuleCat.hom_ext ?_
    rw [ModuleCat.hom_add]
    change LinearMap.lTensor W (ModuleCat.Hom.hom (f + g).hom) =
      ModuleCat.Hom.hom (ModuleCat.ofHom (LinearMap.lTensor W (ModuleCat.Hom.hom f.hom))) +
        ModuleCat.Hom.hom (ModuleCat.ofHom (LinearMap.lTensor W (ModuleCat.Hom.hom g.hom)))
    rw [ModuleCat.hom_ofHom, ModuleCat.hom_ofHom,
      show (f + g).hom = f.hom + g.hom from ModuleCat.hom_ext rfl, ModuleCat.hom_add,
      LinearMap.lTensor_add]

/-- The functor `tensorLeftToModuleCat W` is `k`-linear. -/
instance : (tensorLeftToModuleCat (k := k) W).Linear k where
  map_smul := by
    intro V V' f r
    refine ModuleCat.hom_ext ?_
    rw [ModuleCat.hom_smul]
    change LinearMap.lTensor W (ModuleCat.Hom.hom (r • f).hom) =
      r • ModuleCat.Hom.hom (ModuleCat.ofHom (LinearMap.lTensor W (ModuleCat.Hom.hom f.hom)))
    rw [ModuleCat.hom_ofHom, show (r • f).hom = r • f.hom from ModuleCat.hom_ext rfl,
      ModuleCat.hom_smul, LinearMap.lTensor_smul]

/-- The value of `tensorLeftToModuleCat` at the rank-one module is `W ⊗[k] k`, which is
finite-dimensional whenever `W` is. -/
theorem finiteDimensional_tensorLeftToModuleCat_obj [FiniteDimensional k W] :
    FiniteDimensional k ((tensorLeftToModuleCat (k := k) W).obj (FGModuleCat.of k k)) := by
  change FiniteDimensional k (W ⊗[k] k)
  infer_instance

end FGModuleCat

namespace GradedAlgebra

open MvPolynomial

universe u v

variable {k : Type u} {P : Type v} [Field k] [CommRing P] [Algebra k P]

/-- **The functor `G` of the proof of Stacks 0DVZ.** For a weighted graded presentation of `P`
with relations `F j` of weighted degree `e j`, this is `V ↦ W ⊗[k] V` where `W` is the cokernel
of the graded Jacobian — the space the source calls

`W = Coker(P_{d_1} ⊕ … ⊕ P_{d_n} → P_{e_1} ⊕ … ⊕ P_{e_m})`.

An abbreviation rather than a definition so that the `Functor.Additive` and `Functor.Linear k`
instances of `FGModuleCat.tensorLeftToModuleCat` apply to it without restating them, which is
what lets it be handed directly to
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection`. -/
abbrev gradedJacobianCokernelFunctor (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j)) :
    FGModuleCat.{u} k ⥤ ModuleCat.{max u v} k :=
  FGModuleCat.tensorLeftToModuleCat
    (((j : Fin r) → grading (e j)) ⧸ LinearMap.range (gradedJacobian grading hx F hF))

/-- The value of `gradedJacobianCokernelFunctor` at the rank-one module is
finite-dimensional, by `finiteDimensional_gradedJacobian_cokernel`. This is the hypothesis
`FiniteDimensional k (G.obj (FGModuleCat.of k k))` of
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection`. -/
theorem finiteDimensional_gradedJacobianCokernelFunctor_obj (grading : ℕ → Submodule k P)
    [GradedAlgebra grading] [∀ i, Module.Finite k (grading i)]
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j)) :
    FiniteDimensional k
      ((gradedJacobianCokernelFunctor grading hx F hF).obj (FGModuleCat.of k k)) := by
  have := finiteDimensional_gradedJacobian_cokernel grading hx F hF
  exact FGModuleCat.finiteDimensional_tensorLeftToModuleCat_obj _

end GradedAlgebra

end
