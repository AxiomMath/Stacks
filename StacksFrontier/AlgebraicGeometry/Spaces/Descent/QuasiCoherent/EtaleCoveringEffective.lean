module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FullnessViaSigmaSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberPerMemberIsoDirect

/-!
# Effectivity of descent data for an étale covering of an algebraic space

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be a family of
algebraic spaces over `X`. We give two criteria for a descent datum of quasi-coherent modules
relative to such a family to be effective.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEffective_of_forall_iso`: a descent datum is
  effective as soon as its components are the inverse images of one quasi-coherent module,
  compatibly with the pairwise isomorphisms, for any family.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEffective_of_isEtaleCovering`: every descent
  datum relative to an étale covering of an algebraic space is effective.

## References

* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X)

/-- **A descent datum is effective as soon as its component modules are the inverse images of one
quasi-coherent module, compatibly with the pairwise isomorphisms.** -/
theorem isEffective_of_forall_iso (D : DescentDatum B S hS Yi f)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (θ : ∀ i, D.F i ≅ (canonicalDescentDatum B S hS Yi f M hM).F i)
    (hθ : ∀ i j, (modulePullback B S hS (pairFst B S hS Yi f i j)).map (θ i).hom ≫
        ((canonicalDescentDatum B S hS Yi f M hM).transition i j).hom =
      (D.transition i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS Yi f i j)).map (θ j).hom) :
    IsEffective B S hS Yi f D :=
  ⟨M, hM, ⟨DescentDatum.isoMk B S hS Yi f θ hθ⟩⟩

/-- **Every descent datum for quasi-coherent modules relative to an étale covering of an
algebraic space is effective**: it is isomorphic to the canonical descent datum of a
quasi-coherent `𝒪_X`-module. -/
theorem isEffective_of_isEtaleCovering (hf : ∀ i, IsEtale B S hS (f i).hom)
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (f i).hom))
    (D : DescentDatum B S hS Yi f) : IsEffective B S hS Yi f D := by
  have := isCoverDense_memberFunctor B S hS Yi f hf hcov
  obtain ⟨M, hM, τ, hT⟩ := exists_memberReading B S hS Yi f hf D
  exact isEtaleEffective_of_memberReading B S hS Yi f hf D M hM τ hT

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
