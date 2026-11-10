module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import StacksFrontier.Deformation.Artin.Basic
public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebrasRimSchlessinger
public import StacksFrontier.Deformation.TangentSpace.FiniteDimensional
public import StacksFrontier.RingTheory.GradedAlgebra.GradedJacobianFunctor

/-!
# The tangent space of the deformations of a graded algebra, reduced to four obligations

Let `P` be a graded `k`-algebra, finite-dimensional in each degree. Its deformations form a
deformation category (Stacks 0DVY), so its functor of fibrewise isomorphism classes carries the
canonical `k`-vector-space structure of Stacks 06IH on its value at the dual numbers: the
tangent space. Stacks 0DVZ asserts that this tangent space is finite-dimensional when `P` is of
finite type over `k`.

This file does not prove that. What it does is name the remaining obligation exactly: it
specialises the criterion `Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection`
to this deformation category, so that the tangent-space half of Stacks 0DVZ becomes the
construction of four things and nothing else —

* an additive `k`-linear functor `G` on finitely generated `k`-modules with
  `G (k)` finite-dimensional;
* a family of maps `t V` from the set of isomorphism classes of lifts of `P` over `k[V]` into
  `G V`;
* naturality of that family in `V`;
* injectivity of `t` at `V = k`.

In Stacks' proof (`examples-defos.tex:683`) the functor is
`V ↦ (∏_j (P_{e_j} ⊗_k V)) ⧸ range (gradedJacobian ⊗ V)` for a weighted graded presentation of
`P` with relations `F_j` of weighted degree `e_j`, the map `t` records the vector `(g_1, …, g_m)`
of the lifted relations, naturality is naturality of that record, and injectivity at `V = k` is
the converse construction of the lift from the vector.

The **first** of those four is discharged below: `GradedAlgebra.gradedJacobianCokernelFunctor`
is that functor — over a field it is `V ↦ W ⊗_k V` for `W` the cokernel of the Jacobian
itself — and it is additive, `k`-linear and finite-dimensional at `V = k`. So the second
theorem of this file is the same reduction with the functor supplied, leaving exactly `t`, its
naturality, and its injectivity at `V = k`. None of those three is proved here.

## Main results

* `Deformation.Examples.ProjectiveGradedAlgebra.deformationBasedCategory`: the deformation
  category of a graded algebra as a based category over `𝒞_Λ`.
* `Deformation.Examples.ProjectiveGradedAlgebra.tangentSetFunctor`: the set-valued functor
  `V ↦ 𝓕(k[V])` whose linear lift carries the tangent space, for that deformation category.
* `ProjectiveGradedAlgebra.finiteDimensional_tangentSpace_of_natural_injection`: the reduction
  above.
* `…ProjectiveGradedAlgebra.finiteDimensional_tangentSpace_of_gradedJacobian_natural_injection`
  : the same reduction with Stacks' own functor supplied, so three obligations remain.

## Implementation notes

The conclusion is spelled exactly as the sibling
`Deformation.Examples.FiniteProjectiveModule.finiteDimensional_tangentSpace` of Stacks 0DVQ
spells it, and exactly as `Stmt_0DVZ__graded_tangent_finite` spells it up to the renames
`artinianTangentSpaceOver → artinianTangentSpace` and
`associatedTangentSpace{AddCommGroup,Module} → …Unlifted`.

Three instance hypotheses the statement of the tag carries are **absent** here, because the
reduction does not use them: `[IsNoetherianRing Λ]`, `[Module.Finite Λ k]` — the Chapter-93
conventions — and `[Algebra.FiniteType k P]`. They are needed, if at all, inside the
construction of `t`, not in order to pass from `t` to finite-dimensionality. The statement is
therefore strictly stronger than the corresponding half of the tag, which is why it is safe; it
carries no `@[stacks]` tag because it does not prove 0DVZ's third theorem.

`tangentSetFunctor` is an abbreviation rather than a definition so that the existing API of
`Deformation.associatedTangentSpaceSetFunctor` applies to it unchanged; its value at
`FGModuleCat.of k k` is definitionally the tangent space itself, which is what makes the
injectivity hypothesis and the conclusion speak about the same type with no comparison map.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Deformation.Examples.ProjectiveGradedAlgebra

universe u w m u₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  (P : Type (max w m)) [CommRing P] [Algebra k P]
  (grading : ℕ → Submodule k P) [GradedAlgebra grading]
  [∀ d, Module.Finite k (grading d)]

/-- The deformation category of a graded `k`-algebra, finite-dimensional in each degree, as a
based category over `𝒞_Λ`. This is the `𝓕` of Stacks 0DVZ. -/
abbrev deformationBasedCategory : BasedCategory (ArtinianLocalAlgCat.{u, w, w} Λ k) :=
  BasedCategory.ofFunctor (objectsOverFunctor
    (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
    (specialFiber (Λ := Λ) P grading))

/-- The set-valued functor `V ↦ 𝓕(k[V])` of the deformation category of a graded algebra, in
the form Stacks 06IA and 06IH use it. Its value at the rank-one module is the tangent space. -/
abbrev tangentSetFunctor : FGModuleCat.{w} k ⥤ Type _ :=
  associatedTangentSpaceSetFunctor (deformationBasedCategory (Λ := Λ) P grading)
    (isDeformationCategory_deformationCategory (Λ := Λ) P grading).predeformation.cofibered

/-- **The tangent-space half of Stacks 0DVZ, reduced to four obligations.** The tangent space of
the deformation category of a graded `k`-algebra which is finite-dimensional in each degree is
finite-dimensional as soon as the set functor `V ↦ 𝓕(k[V])` admits a family of maps into an
additive `k`-linear module-valued functor `G`, natural in `V`, injective at the rank-one module
and with finite-dimensional value there.

Nothing beyond those four data is owed: this is a bare application of
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection`, which already
discharges every transport along the carrier equality of Stacks 06IH, composed with the
Rim–Schlessinger condition of Stacks 0DVY and the (S2) implication of Stacks 07WV for this
deformation category.

Deliberately untagged: it proves no theorem of 0DVZ, it reduces one. -/
theorem finiteDimensional_tangentSpace_of_natural_injection
    (G : FGModuleCat.{w} k ⥤ ModuleCat.{u₂} k) [G.Additive] [G.Linear k]
    [FiniteDimensional k (G.obj (FGModuleCat.of k k))]
    (t : ∀ V : FGModuleCat.{w} k, (tangentSetFunctor (Λ := Λ) P grading).obj V → G.obj V)
    (ht : ∀ {V V' : FGModuleCat.{w} k} (f : V ⟶ V')
        (x : (tangentSetFunctor (Λ := Λ) P grading).obj V),
      t V' ((tangentSetFunctor (Λ := Λ) P grading).map f x) = (G.map f) (t V x))
    (hinj : Function.Injective (t (FGModuleCat.of k k))) :
    letI p := objectsOverFunctor
      (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
      (specialFiber (Λ := Λ) P grading)
    letI 𝓕 := BasedCategory.ofFunctor p
    letI hD := isDeformationCategory_deformationCategory (Λ := Λ) P grading
    letI hS2 := Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
    letI T := artinianTangentSpace Λ k (isomorphismClasses 𝓕 hD.predeformation.cofibered)
    letI : AddCommGroup T := associatedTangentSpaceAddCommGroupUnlifted 𝓕
    letI : Module k T := associatedTangentSpaceModuleUnlifted 𝓕
    FiniteDimensional k T :=
  finiteDimensional_artinianTangentSpace_of_natural_injection _
    (isDeformationCategory_deformationCategory (Λ := Λ) P grading).predeformation
    (Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory _
      (isDeformationCategory_deformationCategory (Λ := Λ) P grading))
    G t ht hinj

/-- **The tangent-space half of Stacks 0DVZ, reduced to three obligations.** Specialising
`finiteDimensional_tangentSpace_of_natural_injection` to the functor the source actually uses —
`V ↦ W ⊗_k V` for `W` the cokernel of the graded Jacobian of a weighted graded presentation of
`P`, which is `GradedAlgebra.gradedJacobianCokernelFunctor` — discharges the first of its four
obligations. What remains is exactly the map `t`, its naturality, and its injectivity at the
rank-one module.

The functor and its finite-dimensionality at `V = k` are supplied here; `Functor.Additive` and
`Functor.Linear k` come from the instances on `FGModuleCat.tensorLeftToModuleCat`. The
presentation is taken as data rather than produced from `Algebra.FiniteType k P`, so that this
statement does not depend on which presentation is chosen.

Deliberately untagged: like its predecessor it reduces a theorem of 0DVZ rather than proving
one. -/
theorem finiteDimensional_tangentSpace_of_gradedJacobian_natural_injection
    {n r : ℕ} {x : Fin n → P} {wt : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (wt i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, MvPolynomial.IsWeightedHomogeneous wt (F j) (e j))
    (t : ∀ V : FGModuleCat.{w} k, (tangentSetFunctor (Λ := Λ) P grading).obj V →
      (GradedAlgebra.gradedJacobianCokernelFunctor grading hx F hF).obj V)
    (ht : ∀ {V V' : FGModuleCat.{w} k} (f : V ⟶ V')
        (x : (tangentSetFunctor (Λ := Λ) P grading).obj V),
      t V' ((tangentSetFunctor (Λ := Λ) P grading).map f x) =
        ((GradedAlgebra.gradedJacobianCokernelFunctor grading hx F hF).map f) (t V x))
    (hinj : Function.Injective (t (FGModuleCat.of k k))) :
    letI p := objectsOverFunctor
      (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
      (specialFiber (Λ := Λ) P grading)
    letI 𝓕 := BasedCategory.ofFunctor p
    letI hD := isDeformationCategory_deformationCategory (Λ := Λ) P grading
    letI hS2 := Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
    letI T := artinianTangentSpace Λ k (isomorphismClasses 𝓕 hD.predeformation.cofibered)
    letI : AddCommGroup T := associatedTangentSpaceAddCommGroupUnlifted 𝓕
    letI : Module k T := associatedTangentSpaceModuleUnlifted 𝓕
    FiniteDimensional k T :=
  have : FiniteDimensional k
      ((GradedAlgebra.gradedJacobianCokernelFunctor grading hx F hF).obj
        (FGModuleCat.of k k)) :=
    GradedAlgebra.finiteDimensional_gradedJacobianCokernelFunctor_obj grading hx F hF
  finiteDimensional_tangentSpace_of_natural_injection P grading _ t ht hinj

end Deformation.Examples.ProjectiveGradedAlgebra

end
