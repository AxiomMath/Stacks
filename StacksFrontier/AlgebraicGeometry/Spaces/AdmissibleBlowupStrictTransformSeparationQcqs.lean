module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupStrictTransformSeparation

/-!
# Separating strict transforms and closures by an admissible blowup: Stacks 0F46

Let `S` be a scheme, let `X` be a quasi-compact and quasi-separated algebraic space over `S` and
let `U ⊆ X` be a quasi-compact open subspace.  Stacks 0F46 asserts:

1. if `Z₁, Z₂ ⊆ X` are closed subspaces of finite presentation with `Z₁ ∩ Z₂ ∩ U = ∅`, then
   there is a `U`-admissible blowup `X' ⟶ X` in which the strict transforms of `Z₁` and `Z₂`
   are disjoint;
2. if `T₁, T₂ ⊆ |U|` are disjoint constructible closed subsets, then there is a `U`-admissible
   blowup `X' ⟶ X` in which the closures of `T₁` and `T₂` are disjoint.

## Main results

* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_separating_strictTransforms_and_closures`:
  both assertions above, as one conjunction.

## Notation

"The strict transforms are disjoint" is disjointness of their sets of points in `|X'|`, the strict
transform being taken with respect to the blowup in a given centre (Stacks 0862). The hypothesis
`Z₁ ∩ Z₂ ∩ U = ∅` is stated on points. Each `Tᵢ` is read in `|X'|` as the set of points mapping
into its image in `|X|`.

## References

* [Stacks Project, Tag 0F46](https://stacks.math.columbia.edu/tag/0F46)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 0855](https://stacks.math.columbia.edu/tag/0855)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0F46.**  Let `S` be a scheme, let `X` be a quasi-compact and quasi-separated
algebraic space over `S` and let `U ⊆ X` be a quasi-compact open subspace.

1. If `Z₁, Z₂ ⊆ X` are closed subspaces of finite presentation with `Z₁ ∩ Z₂ ∩ U = ∅`, then
   there is a `U`-admissible blowup `b : X' ⟶ X` such that the strict transforms of `Z₁` and
   `Z₂` are disjoint.  The blowup is recorded with its centre `Y`, a finitely presented closed
   subspace of `X` disjoint from `U` in which `b` is the blowup, and the strict transforms are
   taken relative to the exceptional divisor `b⁻¹Y`.
2. If `T₁, T₂ ⊆ |U|` are disjoint constructible closed subsets, then there is a `U`-admissible
   blowup `b : X' ⟶ X` such that the closures of `T₁` and `T₂` in `|X'|` are disjoint, `Tᵢ`
   being read in `|X'|` through `b`, which is an isomorphism over `U`. -/
@[stacks 0F46]
theorem exists_isAdmissibleBlowup_separating_strictTransforms_and_closures
    (hZ : B.Contains (⊤_ Scheme.{u})) {X : AlgebraicSpaces B S hS}
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (U : OpenSubspaces B S hS X.1) (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor) :
    (∀ Z₁ Z₂ : ClosedSubspaces B S hS X.1,
      IsFinitePresentation B S hS Z₁.1.ι → IsFinitePresentation B S hS Z₂.1.ι →
        Disjoint (subspacePointSet B S hS X.1 U.1 ∩ subspacePointSet B S hS X.1 Z₁.1)
          (subspacePointSet B S hS X.1 Z₂.1) →
        ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X) (Y : ClosedSubspaces B S hS X.1),
          IsAdmissibleBlowup B S hS U b ∧ IsFinitePresentation B S hS Y.1.ι ∧
            Disjoint (subspacePointSet B S hS X.1 U.1) (subspacePointSet B S hS X.1 Y.1) ∧
              IsBlowupAlong B S hS Y b ∧
                Disjoint (strictTransformPointSet (closedSubspaceSpaceι X Z₁) b
                    (preimageClosedSubspace b Y).1)
                  (strictTransformPointSet (closedSubspaceSpaceι X Z₂) b
                    (preimageClosedSubspace b Y).1)) ∧
      ∀ T₁ T₂ : Set (points B S hS U.1.toFunctor), IsClosed T₁ → IsClosed T₂ →
        Topology.IsConstructible T₁ → Topology.IsConstructible T₂ → Disjoint T₁ T₂ →
        ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X), IsAdmissibleBlowup B S hS U b ∧
          Disjoint (closure (pointsMap B S hS _ b.hom ⁻¹' (pointsMap B S hS _ U.1.ι '' T₁)))
            (closure (pointsMap B S hS _ b.hom ⁻¹' (pointsMap B S hS _ U.1.ι '' T₂))) :=
  ⟨fun Z₁ Z₂ h₁ h₂ hdisj =>
      exists_isAdmissibleBlowup_disjoint_strictTransformPointSet U Z₁ Z₂ h₁ h₂ hdisj,
    fun T₁ T₂ hT₁ hT₂ hc₁ hc₂ hdisj =>
      exists_isAdmissibleBlowup_disjoint_closure hZ hXqc hXqs U hUqc T₁ T₂ hT₁ hT₂ hc₁ hc₂
        hdisj⟩

end AlgebraicGeometry.Space

end
