module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.Topology.Sheaves.Cohomology.RecoveryB.InverseLimitAsDerivedLimit
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Affine vanishing for the limit of an adic inverse system

Let `X` be a scheme, `I` a quasi-coherent ideal sheaf on `X` and `(F_n)` an adic inverse system
of quasi-coherent modules. The positive-degree cohomology of the inverse limit `F = lim F_n`
vanishes on every affine open.

The inverse limit of a tower of modules with surjective transitions is acyclic on a basis of
opens over which the terms are acyclic and the first derived inverse limit of the sections
vanishes. Both hypotheses hold on the affine opens of a scheme: the terms are quasi-coherent, so
Serre vanishing applies, and the transitions are surjective on affine sections, so the
Mittag-Leffler condition holds there.

## Main results

* `Stacks.Cohomology.SpaceInverseLimits.epi_inverseLimitDifference_of_surjective` — Mittag-Leffler
  for a countable inverse system of abelian groups with surjective transitions.
* `Stacks.Algebraization.AdicInverseSystem.surjective_transition_app` — the transitions of an
  adic inverse system are surjective on the sections over an affine open.
* `Stacks.Algebraization.AdicInverseSystem.isZero_cohomology_limitModule_of_affineOpen` — the
  positive-degree cohomology of the limit vanishes on affine opens.

## Implementation notes

Cohomology is the derived-functor model `Stacks.Cohomology.Hgroup`, the right derived functor of
the sections over an open, and `R¹ lim` of a countable tower of abelian groups is the cokernel of
`Stacks.Cohomology.SpaceInverseLimits.inverseLimitDifference`, so its vanishing is that morphism
being an epimorphism. The Mittag-Leffler argument is a recursion: given a target `b`, the
component `a (n + 1)` is chosen as a preimage of `a n - b n` under the `n`-th transition, which
is where surjectivity is used.

## References

* [Stacks Project, Tag 0EI8](https://stacks.math.columbia.edu/tag/0EI8)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

namespace Stacks.Cohomology.SpaceInverseLimits

/-- Mittag-Leffler: the difference endomorphism of the product of a countable inverse system
of abelian groups with surjective transition maps is an epimorphism; equivalently `R¹ lim`
vanishes for a tower of surjections. -/
public theorem epi_inverseLimitDifference_of_surjective (G : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (hG : ∀ n : ℕ, Function.Surjective (G.map (homOfLE (Nat.le_succ n)).op)) :
    Epi (inverseLimitDifference G) := by
  classical
  rw [AddCommGrpCat.epi_iff_surjective]
  choose t ht using fun n => hG n
  intro b
  set β : ∀ n : ℕ, G.obj ⟨n⟩ := fun n => Pi.π (fun n : ℕ => G.obj ⟨n⟩) n b with hβ
  set α : ∀ n : ℕ, G.obj ⟨n⟩ :=
    fun n => Nat.rec (0 : G.obj ⟨0⟩) (fun k ak => t k (ak - β k)) n with hα
  have hstep : ∀ n : ℕ, G.map (homOfLE (Nat.le_succ n)).op (α (n + 1)) = α n - β n :=
    fun n => ht n (α n - β n)
  have hd : ∀ n : ℕ, inverseLimitDifference G ≫ Pi.π (fun n : ℕ => G.obj ⟨n⟩) n =
      Pi.π (fun n : ℕ => G.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => G.obj ⟨n⟩) (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op :=
    fun n => Pi.lift_π _ n
  refine ⟨(Concrete.productEquiv (fun n : ℕ => G.obj ⟨n⟩)).symm α, ?_⟩
  refine (Concrete.productEquiv (fun n : ℕ => G.obj ⟨n⟩)).injective (funext fun n => ?_)
  rw [Concrete.productEquiv_apply_apply, Concrete.productEquiv_apply_apply]
  have h := ConcreteCategory.congr_hom (hd n)
    ((Concrete.productEquiv (fun n : ℕ => G.obj ⟨n⟩)).symm α)
  rw [ConcreteCategory.comp_apply] at h
  rw [h]
  simp [hstep n]
  rfl

end Stacks.Cohomology.SpaceInverseLimits

namespace Stacks.Algebraization

namespace AdicInverseSystem

variable (S : AdicInverseSystem.{u})

/-- The transition maps of an adic inverse system are surjective on the sections over an affine
open: there they present the sections of `F_n` as a quotient of the sections of `F_{n+1}`. -/
public theorem surjective_transition_app (U : S.X.affineOpens) (n : ℕ) :
    Function.Surjective
      (((S.system.map (homOfLE (Nat.le_succ n)).op).app U.1).hom) := by
  obtain ⟨e, he⟩ := S.sectionsQuotientEquiv U n
  intro y
  obtain ⟨q, hq⟩ := e.surjective y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨x, (he x).symm.trans hq⟩

/-- The positive-degree cohomology of the inverse limit of an adic inverse system vanishes on
every affine open. -/
@[stacks 0EI8 "affine_vanishing"]
public theorem isZero_cohomology_limitModule_of_affineOpen (U : S.X.affineOpens) (p : ℕ)
    (hp : 0 < p) :
    IsZero (Hgroup S.X.ringCatSheaf U.1 p S.limitModule) :=
  Stacks.Cohomology.SpaceInverseLimits.isZero_cohomology_limit_of_isBasis
    S.X.toRingedSpace S.system S.X.affineOpens S.X.isBasis_affineOpens
    (fun V hV n q hq => by
      have : (S.system.obj ⟨n⟩).IsQuasicoherent := S.isQuasicoherent ⟨n⟩
      exact Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen S.X
        (S.system.obj ⟨n⟩) V hV q hq)
    (fun V hV =>
      Stacks.Cohomology.SpaceInverseLimits.epi_inverseLimitDifference_of_surjective _
        (fun n => S.surjective_transition_app ⟨V, hV⟩ n))
    U.1 U.2 p hp

end AdicInverseSystem

end Stacks.Algebraization

end

end
