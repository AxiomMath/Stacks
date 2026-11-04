module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.Examples.Geometric.RingsTangentSpaceEquivTangent
public import StacksFrontier.Deformation.SquareZero.AlgebraExtensionMaps

/-!
# The square-zero extension of a first-order deformation, and naturality of restriction

Two pieces of bookkeeping about the classification of first-order deformations of a
`k`-algebra `P` by square-zero extensions.

The first names the extension itself. `Deformation.Examples.fiberExtClass` sends a point of a
fibre of the deformation category over a base presented as `k ⊕ V` to its class in
`Ext¹_P(NL_{P/k}, P ⊗[k] V)`, and it does so by forming a square-zero extension of `P` by
`P ⊗[k] V` and taking the class of **Stacks 0GPT**; but the extension is built inline, so only
the class is available to a caller. `Deformation.Examples.fiberFirstOrderExtension` is that
extension, and `Deformation.Examples.fiberExtClass_eq_extClass` says the class is its class.
A statement about a *representative* of the class — the criterion of **Stacks 0GPV**, which
compares two extensions through a map of their middle rings — can only be applied once the
representative has a name.

The second is the naturality of the restriction map of **Stacks 0GPV** in the coefficients.
`Stacks.Deformation.naiveCotangentExtOneTowerMap` restricts along `S → T` and
`Stacks.Deformation.naiveCotangentExtOneMap` pushes forward along a coefficient map, and
`Stacks.Deformation.naiveCotangentExtOneTowerMap_map` says the two commute when the
coefficient map is `T`-linear. Both maps are conjugates of maps on conormal cokernels by
`Stacks.Deformation.extCokernelIso`, and on cokernels the two operations are postcomposition
and precomposition with fixed maps, so they commute on representatives; that is
`Stacks.Deformation.conormalCokernelPullback_push`.

## Main definitions

* `Deformation.Examples.fiberFirstOrderExtension`: the square-zero extension of `P` by
  `P ⊗[k] V` determined by a point of a fibre of the deformation category of `P` over a base
  presented as `k ⊕ V`.

## Main results

* `Deformation.Examples.fiberExtClass_eq_extClass`: the class of such a point is the class of
  that extension.
* `Stacks.Deformation.naiveCotangentExtOneTowerMap_map`: restriction along `S → T` commutes
  with a `T`-linear coefficient map.
* `Stacks.Deformation.bijective_naiveCotangentExtOneMap_of_inverse`: a coefficient map with a
  two-sided inverse induces a bijection on first Ext groups.

## Implementation notes

`Deformation.Examples.fiberFirstOrderExtension` repeats the instance preamble of
`Deformation.Examples.fiberExtClass` — the algebra structures transported from the base along
the presentation, the pushout square of the point, and the flatness it gives over `k ⊕ V` —
because those structures are what `Deformation.Examples.firstOrderExtension` is stated over and
they are local to the body of `fiberExtClass`. Reproducing them is what makes
`Deformation.Examples.fiberExtClass_eq_extClass` hold by `rfl`.

`Stacks.Deformation.bijective_naiveCotangentExtOneMap_of_inverse` takes the inverse as a map
with two equations rather than a `LinearEquiv`, so that a map which is an equivalence only after
restricting scalars can be fed to it directly.

## References

* [Stacks Project, Tag 0GPT](https://stacks.math.columbia.edu/tag/0GPT)
* [Stacks Project, Tag 0GPV](https://stacks.math.columbia.edu/tag/0GPV)
-/

@[expose] public section

open CategoryTheory Stacks.Deformation
open scoped TensorProduct

universe u w

namespace Deformation.Examples

section FiberExtension

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {P : Type w} [CommRing P] [Algebra k P]
  {V : Type w} [AddCommGroup V] [Module k V]
  {A : ArtinianLocalAlgCat.{u, w, w} Λ k}

/-- The `kᵐᵒᵖ`-module structure on `V` obtained from its `k`-module structure via
`MulOpposite.unop`. -/
local instance : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

/-- The actions of `k` and `kᵐᵒᵖ` on `V` agree. -/
local instance : IsCentralScalar k V := Module.isCentralScalar_oppositeOfCommSemiring k V

/-- **The square-zero extension of `P` by `P ⊗[k] V` determined by a first-order deformation.**
A point `x` of a fibre of the deformation category of `P` whose base is presented as `k ⊕ V` by
a ring isomorphism `e` compatible with the augmentations is a flat `k ⊕ V`-algebra whose
reduction is `P`; `Deformation.Examples.firstOrderExtension` reads that as a square-zero
extension of the `k`-algebra `P` by the `P`-module `P ⊗[k] V`, with middle ring the flat algebra
of `x` itself and reduction the structural map of the base-change square. This is that
extension. -/
public noncomputable def fiberFirstOrderExtension
    (x : (ringDeformationProjection Λ k P).Fiber A)
    (e : (x.1.left.base : Type w) ≃+* TrivSqZeroExt k V)
    (hρ : ∀ r, fiberAug x r = (e r).fst) :
    (algebraExtensionProblem k P (P ⊗[k] V)).CompatibleExtension.{w} :=
  letI := fiberAugAlgebra x
  letI := fiberRedAlgebra x
  letI := fiberBaseAlgebra x
  letI := fiber_isScalarTower_aug x
  letI := fiber_isScalarTower_red x
  letI := fiber_isPushout x
  letI := algebraOfBaseEquiv x.1.left.fiber e
  letI := baseAlgebraOfBaseEquiv x.1.left.fiber e
  letI := isScalarTower_baseAlgebraOfBaseEquiv x.1.left.fiber e
  letI := flat_algebraOfBaseEquiv x.1.left.fiber e
    (algebraMap_algebraOfBaseEquiv x.1.left.fiber e)
  firstOrderExtension (V := V)
    (reductionOfBaseEquiv (P := P) x.1.left.fiber e
      (algebraMap_algebraOfBaseEquiv x.1.left.fiber e) hρ)
    (surjective_algebraMap_of_isPushout x.1.left.fiber (fiberAug_surjective x))
    (isFirstOrderReduction_reductionOfBaseEquiv x.1.left.fiber e
      (algebraMap_algebraOfBaseEquiv x.1.left.fiber e) hρ)
    (mem_kerIdeal_smul_of_algebraMap_eq_zero x.1.left.fiber e
      (algebraMap_algebraOfBaseEquiv x.1.left.fiber e) hρ (fiberAug_surjective x))

/-- **The class of a point of a fibre is the class of the extension it determines.** The class
of `Deformation.Examples.fiberExtClass` is the class of **Stacks 0GPT** of
`Deformation.Examples.fiberFirstOrderExtension`. -/
public theorem fiberExtClass_eq_extClass
    (x : (ringDeformationProjection Λ k P).Fiber A)
    (e : (x.1.left.base : Type w) ≃+* TrivSqZeroExt k V)
    (hρ : ∀ r, fiberAug x r = (e r).fst) :
    fiberExtClass x e hρ = extClass (fiberFirstOrderExtension x e hρ) := rfl

/-- **The class of a point of the fibre over `k ⊕ V` is the class of the extension it
determines**, for the canonical presentation of its base. -/
public theorem squareZeroFiberExtClass_eq_extClass (W : FGModuleCat.{w} k)
    (x : (ringDeformationProjection Λ k P).Fiber ((squareZeroExtensionArtinian Λ k).obj W)) :
    squareZeroFiberExtClass W x
      = extClass (fiberFirstOrderExtension x (fiberSquareZeroEquiv W x)
          (fiberAug_fiberSquareZeroEquiv W x)) := rfl

/-- The middle ring of the extension determined by a point of a fibre is the flat algebra of
that point. -/
public theorem fiberFirstOrderExtension_B'
    (x : (ringDeformationProjection Λ k P).Fiber A)
    (e : (x.1.left.base : Type w) ≃+* TrivSqZeroExt k V)
    (hρ : ∀ r, fiberAug x r = (e r).fst) :
    (fiberFirstOrderExtension x e hρ).B' = x.1.left.fiber := rfl

end FiberExtension

end Deformation.Examples

namespace Stacks.Deformation

section Naturality

variable (R S T : Type w) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {M : Type w} [AddCommGroup M] [Module S M] [Module T M] [IsScalarTower S T M]
  {N : Type w} [AddCommGroup N] [Module S N] [Module T N] [IsScalarTower S T N]

/-- **Pulling a conormal functional back along `S → T` commutes with pushing it forward along
a `T`-linear coefficient map.** On representatives the two operations are precomposition with
the canonical map `NL_{S/R} → NL_{T/R}` and postcomposition with the coefficient map, which
commute. -/
public lemma conormalCokernelPullback_push (c : M →ₗ[T] N) (y : extOneCokernel R T M) :
    conormalCokernelPullback R S T (conormalCokernelPush R T c y)
      = conormalCokernelPush R S (c.restrictScalars S) (conormalCokernelPullback R S T y) := by
  induction y using Quotient.inductionOn' with
  | h δ => rfl

/-- **The restriction map of Stacks 0GPV is natural in the coefficients.** Restriction along
`S → T` on first Ext groups commutes with the map induced by a `T`-linear coefficient map,
read over `S` on the restricted side. -/
public lemma naiveCotangentExtOneTowerMap_map (c : M →ₗ[T] N)
    (ξ : naiveCotangentExtOne R T M) :
    naiveCotangentExtOneTowerMap R S T (naiveCotangentExtOneMap R T c ξ)
      = naiveCotangentExtOneMap R S (c.restrictScalars S)
          (naiveCotangentExtOneTowerMap R S T ξ) := by
  change (extCokernelIso R S N).symm (conormalCokernelPullback R S T
      (extCokernelIso R T N ((extCokernelIso R T N).symm
        (conormalCokernelPush R T c (extCokernelIso R T M ξ))))) = _
  rw [(extCokernelIso R T N).apply_symm_apply]
  change _ = (extCokernelIso R S N).symm (conormalCokernelPush R S (c.restrictScalars S)
    (extCokernelIso R S M ((extCokernelIso R S M).symm
      (conormalCokernelPullback R S T (extCokernelIso R T M ξ)))))
  rw [(extCokernelIso R S M).apply_symm_apply, conormalCokernelPullback_push]

end Naturality

section Inverse

variable (R S : Type w) [CommRing R] [CommRing S] [Algebra R S]
  {M N : Type w} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]

/-- **A coefficient map with a two-sided inverse induces a bijection on first Ext groups.** -/
public lemma bijective_naiveCotangentExtOneMap_of_inverse (c : M →ₗ[S] N) (d : N →ₗ[S] M)
    (hdc : ∀ m, d (c m) = m) (hcd : ∀ n, c (d n) = n) :
    Function.Bijective (naiveCotangentExtOneMap R S c) := by
  have hid : d.comp c = LinearMap.id := LinearMap.ext hdc
  have hid' : c.comp d = LinearMap.id := LinearMap.ext hcd
  refine ⟨fun ξ ζ h => ?_, fun ζ => ⟨naiveCotangentExtOneMap R S d ζ, ?_⟩⟩
  · have h' := congrArg (naiveCotangentExtOneMap R S d) h
    rw [← naiveCotangentExtOneMap_comp, ← naiveCotangentExtOneMap_comp, hid,
      naiveCotangentExtOneMap_id, naiveCotangentExtOneMap_id] at h'
    exact h'
  · rw [← naiveCotangentExtOneMap_comp, hid', naiveCotangentExtOneMap_id]

end Inverse

end Stacks.Deformation

end
