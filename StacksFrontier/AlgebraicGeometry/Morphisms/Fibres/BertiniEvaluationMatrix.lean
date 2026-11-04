module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniEvaluationFibreBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniImmersionCondition

/-!
# The matrix of the evaluation of a linear system at a closed point

Work in the standing situation of the Bertini theorems ([Stacks, Tag 0G47]) with `X` smooth over
an algebraically closed field `k`, under hypotheses (2) and (3) of [Stacks, Tag 0FD6], and let
`x` be a closed point of `X` at which `X` has dimension `n`. The evaluation
`ev_x : V → ℒ_x/𝔪_x²ℒ_x` is then surjective onto a space of dimension `n + 1`
(`Stacks.Bertini.FamilyDivisors.surjective_evalQuotient_of_isClosed`,
`Stacks.Bertini.FamilyDivisors.finrank_ker_evalCoord_of_smooth`), so after a choice of basis of
its target it becomes a surjection `k^r → k^{n+1}` with the same kernel.

That surjection is what the dimension count of the proof of Tag 0FD6 consumes: its matrix
supplies the `n + 1` linear forms cutting out the fibre bound of
`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniEvaluationSubspace`. This module produces
the matrix and discharges the two inputs that module's bound takes — surjectivity, and that the
number of forms is `n + 1` — leaving the Jacobian criterion as the only remaining input of the
chain.

## Main results

* `Stacks.Bertini.FamilyDivisors.exists_evalMatrix_of_basis`: **the matrix of `ev_x`**, indexed by
  the basis index of the family, with its associated map `k^r → k^{n+1}` surjective and with the
  same kernel as `ev_x`, **from hypothesis (3) at an arbitrary basis of the linear system** — the
  basis at which the immersion hypothesis is taken and the basis the matrix is read against are
  separate parameters. `Stacks.Bertini.FamilyDivisors.exists_evalMatrix` is the case of the two
  being the same basis.
* `Stacks.Bertini.FamilyDivisors.topologicalKrullDim_fiber_nonSmoothToX_le_of_jacobian`: the
  fibre bound `r - (n + 1)` over a closed point of `X`, from the Jacobian criterion.
* `Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_subset_smoothLocus_of_jacobian`:
  **`hsing`** from the Jacobian criterion, with no linear algebra left in the hypotheses.
* `Stacks.Bertini.FamilyDivisors.smooth_specializedDivisor_forGeneral_of_jacobian`: the
  conclusion of [Stacks, Tag 0FD6] from the same input.
* `…topologicalKrullDim_fiber_nonSmoothToX_le_of_jacobian_of_basis`,
  `…exists_nonempty_opens_subset_smoothLocus_of_jacobian_of_basis` and
  `…smooth_specializedDivisor_forGeneral_of_jacobian_of_basis`: those three **with hypothesis (3)
  taken at a basis of the linear system unrelated to the one the Jacobian criterion is stated
  against**, and at an unrelated index type. The hypothesis does not depend on the basis
  (`Stacks.Bertini.FamilyDivisors.isImmersive_basis_of_isImmersive`), so each is the unprimed
  statement with the hypothesis transported; see the implementation notes.

## What is still an input

The hypothesis `hjac` of the last three results: at a closed point `w` of `H_univ` lying over a
closed point `x` of `X`, if one coordinate of `ev_x` is nonzero at the coordinate vector of `w`,
then `q : H_univ → 𝔸^r_k` is smooth at `w`. This is the Jacobian criterion of
`StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.ZeroSchemeStalkRegular` read in the Bertini
situation; joining the two needs **flatness of `q`**, which this library has only over an open of
the parameter space and only conditionally on a fibrewise effective-Cartier hypothesis
(`Stacks.Bertini.FamilyDivisors.flat_universalDivisor_restrict`), and the identification of the
fibre of `q` through `w` with the divisor of the corresponding vector.

Accordingly **no `@[stacks]` attribute is attached**: Tag 0FD6 keeps its registration on
`Stacks.Bertini.FamilyDivisors.smooth_specializedDivisor_forGeneral`.

## Implementation notes

The target of `ev_x` carries no basis, so the surjection onto `k^{n+1}` is built from the
quotient `k^r / ker ev_x`: it is finite dimensional of dimension `n + 1` by rank-nullity, and
`Module.finBasisOfFinrankEq` gives it a basis indexed by `Fin (n + 1)`. The composite of the
quotient map with the coordinates of that basis has the kernel of `ev_x`, which is all the
dimension count uses.

The family's basis index is `ULift (Fin r)` while the evaluation is indexed by the `Fin (n + 1)`
of a basis of `V`, these being the two index sets the two halves of the proof are pinned to;
`Stacks.Bertini.FamilyDivisors.basisIndexEquiv` is the comparison, and `LinearMap.funLeft`
transports the surjection along it. The result is stated existentially so that no definition has
to carry the proofs that choose the basis.

The basis of `V` enters the three `…_of_jacobian` results in two roles, and the `…_of_basis`
siblings keep them apart. The Jacobian criterion `hjac` can only be stated against the basis
whose coefficients the coordinates of the parameter space are, so it stays at one basis `b`;
hypothesis (3) is a condition on the linear system alone, and `…_of_basis` takes it at any basis
`b'`, moving it onto `b` by `Stacks.Bertini.FamilyDivisors.isImmersive_basis_of_isImmersive`.
That transport also supplies hypothesis (2) at `b`, which is why `b` carries no generation
hypothesis of its own. Nothing is proved twice: each `…_of_basis` statement is its unprimed
sibling applied to the transported hypothesis.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.ImmersionEvaluationSurjective

universe u

namespace Stacks.LinearSubspace

/-- **Every linear map `κ^ι → κ^τ` is the coefficient map of its matrix.** -/
theorem coeffMap_matrix {κ : Type*} [Field κ] {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → κ) →ₗ[κ] (τ → κ)) :
    coeffMap (fun i j => F (Pi.single i 1) j) = F := by
  refine LinearMap.ext fun c => funext fun j => ?_
  have hc : c = ∑ i, c i • (Pi.single i 1 : ι → κ) := by
    funext i'
    simp [Finset.sum_apply, Pi.single_apply]
  have key : F c j = ∑ i, c i * F (Pi.single i 1) j := by
    conv_lhs => rw [hc]
    rw [map_sum]
    simp
  rw [coeffMap_apply, key]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end Stacks.LinearSubspace

namespace Stacks.Bertini.FamilyDivisors

open Stacks.LinearSubspace

variable (D : FamilyDivisors.{u, u})

/-- A basis of the linear system indexed by `Fin (m + 1)` forces `dim V = m + 1`. -/
theorem finrank_eq_of_basis {m : ℕ} (b : Module.Basis (Fin (m + 1)) D.k D.V) :
    Module.finrank D.k D.V = m + 1 := by
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

/-- **The comparison of the two index sets of the proof of [Stacks, Tag 0FD6]**: the index
`Fin (m + 1)` of a basis of the linear system and the index `ULift (Fin (dim V))` of the
coordinates of the parameter space. -/
def basisIndexEquiv {m : ℕ} (b : Module.Basis (Fin (m + 1)) D.k D.V) :
    Fin (m + 1) ≃ D.basisIndex :=
  (finCongr (D.finrank_eq_of_basis b).symm).trans Equiv.ulift.symm

/-- **The matrix of the evaluation `ev_x` at a closed point, from hypothesis (3) at an arbitrary
basis of the linear system.** At a closed point `x` of a smooth `X` of dimension `n` there, the
evaluation `ev_x` is a surjection of `k^r` onto a space of dimension `n + 1`; so there is a
matrix of `n + 1` coefficient vectors, indexed by the coordinates of the parameter space, whose
associated map `k^r → k^{n+1}` is surjective and has the kernel of `ev_x`.

The basis `b'` at which hypothesis (3) is taken and the basis `b` whose coordinates the matrix is
read against are unrelated, and `b` is not required to generate `L`: both numerical inputs of the
construction, the dimension of `ker ev_x` and the inequality `n + 1 ≤ dim V`, depend only on the
basis-free evaluation `Stacks.Bertini.FamilyDivisors.evalVector`
(`Stacks.Bertini.FamilyDivisors.finrank_ker_evalCoord_of_smooth_of_basis`,
`Stacks.Bertini.FamilyDivisors.succ_le_of_smooth_of_basis`). Decoupling the two is what carries
the generality of hypothesis (3) through the dimension count: the kernel condition on `M` has to
stay stated against the standing basis, because the coordinates of the parameter space are
coefficients against that basis, while hypothesis (3) is a condition on the linear system alone.

The kernel identity is what makes the matrix a faithful record of `ev_x`: a point of the fibre
lies on all the hyperplanes of the matrix exactly when its coordinate vector is killed by the
evaluation. -/
theorem exists_evalMatrix_of_basis [IsAlgClosed D.k] [Smooth D.toBase] {m n p : ℕ}
    {b' : Module.Basis (Fin (p + 1)) D.k D.V} {hb' : D.GeneratesBy b'}
    (himm : D.IsImmersive b' hb') (b : Module.Basis (Fin (m + 1)) D.k D.V) {x : D.X}
    (hx : IsClosed ({x} : Set D.X))
    (hdim : topologicalKrullDimAt D.X x = (n : WithBot ℕ∞)) :
    ∃ M : D.basisIndex → Fin (n + 1) → D.k, Function.Surjective (coeffMap M) ∧
      ∀ c : D.basisIndex → D.k, coeffMap M c = 0 ↔
        evalCoord (fun i => D.sectionOf (b i)) D.toBase x
          (fun l => c (D.basisIndexEquiv b l)) = 0 := by
  classical
  set ev := evalCoord (fun i => D.sectionOf (b i)) D.toBase x with hev
  have hkerdim : Module.finrank D.k (LinearMap.ker ev) = (m + 1) - (n + 1) :=
    D.finrank_ker_evalCoord_of_smooth_of_basis himm b hx hdim
  have hle : n + 1 ≤ m + 1 := D.succ_le_of_smooth_of_basis himm b hx hdim
  have hQ : Module.finrank D.k ((Fin (m + 1) → D.k) ⧸ LinearMap.ker ev) = n + 1 := by
    have h := Submodule.finrank_quotient_add_finrank (LinearMap.ker ev)
    rw [hkerdim, Module.finrank_fin_fun] at h
    omega
  set bQ := Module.finBasisOfFinrankEq D.k ((Fin (m + 1) → D.k) ⧸ LinearMap.ker ev) hQ with hbQ
  set ψ : (Fin (m + 1) → D.k) →ₗ[D.k] (Fin (n + 1) → D.k) :=
    bQ.equivFun.toLinearMap ∘ₗ (LinearMap.ker ev).mkQ with hψ
  have hψsurj : Function.Surjective ψ :=
    bQ.equivFun.surjective.comp (Submodule.mkQ_surjective (LinearMap.ker ev))
  have hψker : ∀ c, ψ c = 0 ↔ ev c = 0 := by
    intro c
    have hcomp : ψ c = bQ.equivFun ((LinearMap.ker ev).mkQ c) := rfl
    rw [hcomp, map_eq_zero_iff _ bQ.equivFun.injective, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker]
  set F : (D.basisIndex → D.k) →ₗ[D.k] (Fin (n + 1) → D.k) :=
    ψ ∘ₗ LinearMap.funLeft D.k D.k (D.basisIndexEquiv b) with hF
  refine ⟨fun i j => F (Pi.single i 1) j, ?_, ?_⟩
  · rw [coeffMap_matrix]
    exact hψsurj.comp (LinearMap.funLeft_surjective_of_injective D.k D.k _
      (D.basisIndexEquiv b).injective)
  · intro c
    rw [coeffMap_matrix]
    exact hψker _

/-- **The matrix of the evaluation `ev_x` at a closed point.** Under hypotheses (2) and (3) of
[Stacks, Tag 0FD6], at a closed point `x` of a smooth `X` of dimension `n` there, the evaluation
`ev_x` is a surjection of `k^r` onto a space of dimension `n + 1`; so there is a matrix of
`n + 1` coefficient vectors, indexed by the coordinates of the parameter space, whose associated
map `k^r → k^{n+1}` is surjective and has the kernel of `ev_x`.

The kernel identity is what makes the matrix a faithful record of `ev_x`: a point of the fibre
lies on all the hyperplanes of the matrix exactly when its coordinate vector is killed by the
evaluation.

This is `Stacks.Bertini.FamilyDivisors.exists_evalMatrix_of_basis` with hypothesis (3) taken at
the same basis the matrix is read against. -/
theorem exists_evalMatrix [IsAlgClosed D.k] [Smooth D.toBase] {m n : ℕ}
    {b : Module.Basis (Fin (m + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) {x : D.X} (hx : IsClosed ({x} : Set D.X))
    (hdim : topologicalKrullDimAt D.X x = (n : WithBot ℕ∞)) :
    ∃ M : D.basisIndex → Fin (n + 1) → D.k, Function.Surjective (coeffMap M) ∧
      ∀ c : D.basisIndex → D.k, coeffMap M c = 0 ↔
        evalCoord (fun i => D.sectionOf (b i)) D.toBase x
          (fun l => c (D.basisIndexEquiv b l)) = 0 :=
  D.exists_evalMatrix_of_basis himm b hx hdim

/-- **The fibre bound `r - (n + 1)` over a closed point of `X`, from the Jacobian criterion.**
Under hypotheses (2) and (3) of [Stacks, Tag 0FD6], at a closed point `x` of `X` where `X` has
dimension `n`, if the Jacobian criterion holds at the closed points of `H_univ` over `x`, then
the fibre of the projection `Σ → X` over `x` has dimension at most `r - (n + 1)`. -/
theorem topologicalKrullDim_fiber_nonSmoothToX_le_of_jacobian [IsAlgClosed D.k] [Smooth D.toBase]
    {m n : ℕ} {b : Module.Basis (Fin (m + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) {x : D.X} (hx : IsClosed ({x} : Set D.X))
    (hdim : topologicalKrullDimAt D.X x = (n : WithBot ℕ∞))
    (hjac : ∀ M : D.basisIndex → Fin (n + 1) → D.k,
      (∀ c : D.basisIndex → D.k, coeffMap M c = 0 ↔
        evalCoord (fun i => D.sectionOf (b i)) D.toBase x
          (fun l => c (D.basisIndexEquiv b l)) = 0) →
      ∀ w : D.universalDivisorScheme, IsClosed ({w} : Set D.universalDivisorScheme) →
      D.parameterProjection.base (D.universalDivisor.subschemeι.base w) = x →
      (∃ j, D.universalDivisor.subschemeι.base w ∈
        D.parameterSpace.basicOpen (D.evalCoordForm M j)) →
      w ∈ D.universalFamilyMap.smoothLocus) :
    topologicalKrullDim (D.nonSmoothToX.fiber x) ≤
      ((Nat.card D.basisIndex - (n + 1) : ℕ) : WithBot ℕ∞) := by
  obtain ⟨M, hMsurj, hMker⟩ := D.exists_evalMatrix himm hx hdim
  have h := D.topologicalKrullDim_fiber_nonSmoothToX_le_of_evalSubspace hx M hMsurj
    (hjac M hMker)
  rwa [Fintype.card_fin] at h

/-- **The fibre bound `r - (n + 1)` over a closed point of `X`, from the Jacobian criterion and
hypothesis (3) at an arbitrary basis of the linear system.** This is
`Stacks.Bertini.FamilyDivisors.topologicalKrullDim_fiber_nonSmoothToX_le_of_jacobian` with the
basis `b'` at which hypothesis (3) is taken and the basis `b` the Jacobian criterion is stated
against separate parameters, at unrelated index types.

The hypothesis is simply transported: it does not depend on the basis it is stated at
(`Stacks.Bertini.FamilyDivisors.isImmersive_congr_basis'`), and hypothesis (2) is basis free
(`Stacks.Bertini.FamilyDivisors.generatesBy_basis_of_generatesBy`), so no generation hypothesis
at `b` has to be supplied either. The criterion itself stays at `b`, as it must: the coordinates
of the parameter space are coefficients against the standing basis. -/
theorem topologicalKrullDim_fiber_nonSmoothToX_le_of_jacobian_of_basis [IsAlgClosed D.k]
    [Smooth D.toBase] {m n p : ℕ} {b' : Module.Basis (Fin (p + 1)) D.k D.V}
    {hb' : D.GeneratesBy b'} (himm : D.IsImmersive b' hb')
    (b : Module.Basis (Fin (m + 1)) D.k D.V) {x : D.X} (hx : IsClosed ({x} : Set D.X))
    (hdim : topologicalKrullDimAt D.X x = (n : WithBot ℕ∞))
    (hjac : ∀ M : D.basisIndex → Fin (n + 1) → D.k,
      (∀ c : D.basisIndex → D.k, coeffMap M c = 0 ↔
        evalCoord (fun i => D.sectionOf (b i)) D.toBase x
          (fun l => c (D.basisIndexEquiv b l)) = 0) →
      ∀ w : D.universalDivisorScheme, IsClosed ({w} : Set D.universalDivisorScheme) →
      D.parameterProjection.base (D.universalDivisor.subschemeι.base w) = x →
      (∃ j, D.universalDivisor.subschemeι.base w ∈
        D.parameterSpace.basicOpen (D.evalCoordForm M j)) →
      w ∈ D.universalFamilyMap.smoothLocus) :
    topologicalKrullDim (D.nonSmoothToX.fiber x) ≤
      ((Nat.card D.basisIndex - (n + 1) : ℕ) : WithBot ℕ∞) :=
  D.topologicalKrullDim_fiber_nonSmoothToX_le_of_jacobian
    (D.isImmersive_basis_of_isImmersive himm b) hx hdim hjac

/-- **`hsing` of [Stacks, Tag 0FD6] from the Jacobian criterion.** Under hypotheses (2) and (3)
of the tag, with `X` of dimension `n` at each of its closed points and of dimension at most `n`,
and with the Jacobian criterion available at the closed points of `H_univ`, there is a nonempty
open `U ⊂ 𝔸^r_k` whose preimage under `q` lies in the smooth locus of `q`. -/
theorem exists_nonempty_opens_subset_smoothLocus_of_jacobian [IsAlgClosed D.k] [Smooth D.toBase]
    [NoetherianSpace D.universalDivisorScheme] {m n : ℕ}
    {b : Module.Basis (Fin (m + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hdim : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      topologicalKrullDimAt D.X x = (n : WithBot ℕ∞))
    (hjac : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      ∀ M : D.basisIndex → Fin (n + 1) → D.k,
      (∀ c : D.basisIndex → D.k, coeffMap M c = 0 ↔
        evalCoord (fun i => D.sectionOf (b i)) D.toBase x
          (fun l => c (D.basisIndexEquiv b l)) = 0) →
      ∀ w : D.universalDivisorScheme, IsClosed ({w} : Set D.universalDivisorScheme) →
      D.parameterProjection.base (D.universalDivisor.subschemeι.base w) = x →
      (∃ j, D.universalDivisor.subschemeι.base w ∈
        D.parameterSpace.basicOpen (D.evalCoordForm M j)) →
      w ∈ D.universalFamilyMap.smoothLocus) :
    ∃ U : D.parameterBase.Opens, (U : Set D.parameterBase).Nonempty ∧
      ((D.universalFamilyMap ⁻¹ᵁ U : D.universalDivisorScheme.Opens) :
          Set D.universalDivisorScheme) ⊆
        (D.universalFamilyMap.smoothLocus : Set D.universalDivisorScheme) :=
  have : LocallyOfFiniteType D.toBase := inferInstance
  D.exists_nonempty_opens_subset_smoothLocus_of_closed_fiber_le hnr hX fun x hx =>
    D.topologicalKrullDim_fiber_nonSmoothToX_le_of_jacobian himm hx (hdim x hx) (hjac x hx)

/-- **`hsing` of [Stacks, Tag 0FD6] from the Jacobian criterion and hypothesis (3) at an
arbitrary basis of the linear system.** This is
`Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_subset_smoothLocus_of_jacobian` with the
basis `b'` at which hypothesis (3) is taken and the basis `b` the Jacobian criterion is stated
against separate parameters, at unrelated index types; the hypothesis is transported onto `b` by
`Stacks.Bertini.FamilyDivisors.isImmersive_basis_of_isImmersive`. -/
theorem exists_nonempty_opens_subset_smoothLocus_of_jacobian_of_basis [IsAlgClosed D.k]
    [Smooth D.toBase] [NoetherianSpace D.universalDivisorScheme] {m n p : ℕ}
    {b' : Module.Basis (Fin (p + 1)) D.k D.V} {hb' : D.GeneratesBy b'}
    (himm : D.IsImmersive b' hb') (b : Module.Basis (Fin (m + 1)) D.k D.V)
    (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hdim : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      topologicalKrullDimAt D.X x = (n : WithBot ℕ∞))
    (hjac : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      ∀ M : D.basisIndex → Fin (n + 1) → D.k,
      (∀ c : D.basisIndex → D.k, coeffMap M c = 0 ↔
        evalCoord (fun i => D.sectionOf (b i)) D.toBase x
          (fun l => c (D.basisIndexEquiv b l)) = 0) →
      ∀ w : D.universalDivisorScheme, IsClosed ({w} : Set D.universalDivisorScheme) →
      D.parameterProjection.base (D.universalDivisor.subschemeι.base w) = x →
      (∃ j, D.universalDivisor.subschemeι.base w ∈
        D.parameterSpace.basicOpen (D.evalCoordForm M j)) →
      w ∈ D.universalFamilyMap.smoothLocus) :
    ∃ U : D.parameterBase.Opens, (U : Set D.parameterBase).Nonempty ∧
      ((D.universalFamilyMap ⁻¹ᵁ U : D.universalDivisorScheme.Opens) :
          Set D.universalDivisorScheme) ⊆
        (D.universalFamilyMap.smoothLocus : Set D.universalDivisorScheme) :=
  D.exists_nonempty_opens_subset_smoothLocus_of_jacobian
    (D.isImmersive_basis_of_isImmersive himm b) hnr hX hdim hjac

/-- **[Stacks, Tag 0FD6] from the Jacobian criterion at the closed points of `H_univ`.** In the
standing situation of [Stacks, Tag 0G47] with `X` smooth over an algebraically closed field `k`,
under hypotheses (2) and (3) of the tag, with `X` of dimension `n` at each closed point and of
dimension at most `n`, and with the Jacobian criterion available at the closed points of
`H_univ`, the divisor `H_v` is smooth over `k'` for general `v ∈ V ⊗_k k'`.

Everything in the source's dimension count is proved here: the surjectivity of the evaluation at
a closed point and the resulting kernel dimension `r - (n + 1)`, the linear subspace of the
fibre that the kernel cuts out together with its dimension bound, the reduction of the fibre
bound to the closed points of `X` and then of `H_univ`, and the passage from `dim Σ < r` to a
nonempty open of `𝔸^r_k`. What remains is the Jacobian criterion in the Bertini situation; see
this module's header. -/
theorem smooth_specializedDivisor_forGeneral_of_jacobian [IsAlgClosed D.k] [Smooth D.toBase]
    [NoetherianSpace D.universalDivisorScheme] {m n : ℕ}
    {b : Module.Basis (Fin (m + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hdim : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      topologicalKrullDimAt D.X x = (n : WithBot ℕ∞))
    (hjac : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      ∀ M : D.basisIndex → Fin (n + 1) → D.k,
      (∀ c : D.basisIndex → D.k, coeffMap M c = 0 ↔
        evalCoord (fun i => D.sectionOf (b i)) D.toBase x
          (fun l => c (D.basisIndexEquiv b l)) = 0) →
      ∀ w : D.universalDivisorScheme, IsClosed ({w} : Set D.universalDivisorScheme) →
      D.parameterProjection.base (D.universalDivisor.subschemeι.base w) = x →
      (∃ j, D.universalDivisor.subschemeι.base w ∈
        D.parameterSpace.basicOpen (D.evalCoordForm M j)) →
      w ∈ D.universalFamilyMap.smoothLocus) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) := by
  obtain ⟨U, hU, hsing⟩ :=
    D.exists_nonempty_opens_subset_smoothLocus_of_jacobian himm hnr hX hdim hjac
  exact D.smooth_specializedDivisor_forGeneral U hU hsing

/-- **[Stacks, Tag 0FD6] from the Jacobian criterion at the closed points of `H_univ`, with
hypothesis (3) at an arbitrary basis of the linear system.** This is
`Stacks.Bertini.FamilyDivisors.smooth_specializedDivisor_forGeneral_of_jacobian` with the basis
`b'` at which hypothesis (3) is taken and the basis `b` the Jacobian criterion is stated against
separate parameters, at unrelated index types.

**No `@[stacks]` attribute is attached**, as for the unprimed version: the Jacobian criterion
`hjac` is still an assumed input, so this is not an assertion of the tag. -/
theorem smooth_specializedDivisor_forGeneral_of_jacobian_of_basis [IsAlgClosed D.k]
    [Smooth D.toBase] [NoetherianSpace D.universalDivisorScheme] {m n p : ℕ}
    {b' : Module.Basis (Fin (p + 1)) D.k D.V} {hb' : D.GeneratesBy b'}
    (himm : D.IsImmersive b' hb') (b : Module.Basis (Fin (m + 1)) D.k D.V)
    (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hdim : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      topologicalKrullDimAt D.X x = (n : WithBot ℕ∞))
    (hjac : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      ∀ M : D.basisIndex → Fin (n + 1) → D.k,
      (∀ c : D.basisIndex → D.k, coeffMap M c = 0 ↔
        evalCoord (fun i => D.sectionOf (b i)) D.toBase x
          (fun l => c (D.basisIndexEquiv b l)) = 0) →
      ∀ w : D.universalDivisorScheme, IsClosed ({w} : Set D.universalDivisorScheme) →
      D.parameterProjection.base (D.universalDivisor.subschemeι.base w) = x →
      (∃ j, D.universalDivisor.subschemeι.base w ∈
        D.parameterSpace.basicOpen (D.evalCoordForm M j)) →
      w ∈ D.universalFamilyMap.smoothLocus) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) :=
  D.smooth_specializedDivisor_forGeneral_of_jacobian
    (D.isImmersive_basis_of_isImmersive himm b) hnr hX hdim hjac

end Stacks.Bertini.FamilyDivisors

end
