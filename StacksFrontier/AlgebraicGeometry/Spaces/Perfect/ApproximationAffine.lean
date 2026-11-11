module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationIso
import StacksCore.Tactic.StacksAttribute

/-!
# Approximation on an algebraic space representable by an affine scheme

Let `S` be a scheme and let `X` be an algebraic space over `S` which is representable by an
affine scheme.  Stacks 08HM says that approximation (Stacks 08HI) holds for every triple
`(T, E, m)` for which there exists an integer `r ≥ 0` with

1. `E` is `m`-pseudo-coherent,
2. `Hⁱ(E)` is supported on `T` for `i ≥ m - r + 1`,
3. `X ∖ T` is the union of `r` affine opens,

and that in particular approximation by perfect complexes (Stacks 08HJ) holds for `X`.

The source's proof writes `E = ε^*E₀` along the comparison `ε : X_étale ⟶ X₀,Zar` of Stacks 08H7
(Stacks 071Q), descends hypotheses (1) and (2) to `X₀` (Stacks 08HE and the stalk computation of
Stacks 08H8), applies Derived Categories of Schemes, Stacks 08EQ on `X₀`, and pulls the
approximation back (Stacks 08HG).  That argument is carried out, for the algebraic space
represented by an object with affine underlying scheme, in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ApproximationAffineRepresented.lean`, and is
transported to an arbitrary algebraic space representable by an affine scheme in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ApproximationIso.lean`.

## Main results

* `AlgebraicGeometry.Space.approximationHolds_of_affineCover`: **Stacks 08HM**, first
  assertion, with the integer `r` and the affine opens covering `X ∖ T` quantified
  existentially, as in the source.
* `AlgebraicGeometry.Space.approximationByPerfectComplexes_of_affine`: **Stacks 08HM**, second
  assertion.

## Implementation notes

`T` is an arbitrary subset of `|X|` rather than a closed one, which is the convention of
`AlgebraicGeometry.Space.ApproximationHolds`; it is closed anyway, its complement being the
union of the images of the open subspaces `V₁, …, V_r`.

## References

* [Stacks Project, Tag 08HM](https://stacks.math.columbia.edu/tag/08HM)
* [Stacks Project, Tag 08HI](https://stacks.math.columbia.edu/tag/08HI)
* [Stacks Project, Tag 08HJ](https://stacks.math.columbia.edu/tag/08HJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- **Stacks 08HM.**  Let `S` be a scheme and let `X` be an algebraic space over `S` which is
representable by an affine scheme.  Then approximation holds (Stacks 08HI) for every triple
`(T, E, m)` for which there exists an integer `r ≥ 0` such that

1. `E` is `m`-pseudo-coherent,
2. `Hⁱ(E)` is supported on `T` for `i ≥ m - r + 1`,
3. `X ∖ T` is the union of `r` affine opens `V₁, …, V_r` of `X`.

This is `AlgebraicGeometry.Space.approximationHolds_of_isAffineSpace`, applied to the integer and
the affine opens provided. -/
@[stacks 08HM "first assertion: for X an algebraic space representable by an affine scheme,
approximation holds for every triple (T, E, m) such that there exists an integer r ≥ 0 with E
m-pseudo-coherent, H^i(E) supported on T for i ≥ m - r + 1 and X \\ T a union of r affine
opens"]
theorem approximationHolds_of_affineCover (hXa : IsAffineSpace B S hS X)
    (T : Set (points B S hS X)) (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) (m : ℤ)
    (h : ∃ r : ℕ,
      (smallEtaleRingedSite B S hS X hX).IsPseudoCoherentFrom E.obj m ∧
      (∀ i : ℤ, m - (r : ℤ) + 1 ≤ i →
        supportOfSheaf B S hS X
          ((SheafOfModules.toSheaf
              ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))).obj
            ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).obj E.obj)) ⊆ T) ∧
      ∃ V : Fin r → {G : Subfunctor X // IsOpenSubspace B S hS G},
        (∀ k, IsAffineSpace B S hS (V k).1.toFunctor) ∧
        ⋃ k, Set.range (pointsMap B S hS (V k).1.toFunctor (V k).1.ι) = Tᶜ) :
    ApproximationHolds B S hS X hX T E m := by
  obtain ⟨r, hpc, hsupp, V, hV, hcover⟩ := h
  exact approximationHolds_of_isAffineSpace B S hS X hX hXa T E m r hpc hsupp V hV hcover

/-- **The "in particular" of Stacks 08HM**: approximation by perfect complexes (Stacks 08HJ)
holds on an algebraic space representable by an affine scheme.

This is `AlgebraicGeometry.Space.approximationByPerfectComplexes_of_isAffineSpace`. -/
@[stacks 08HM "second assertion: approximation by perfect complexes holds on an algebraic space
representable by an affine scheme"]
theorem approximationByPerfectComplexes_of_affine (hXa : IsAffineSpace B S hS X) :
    ApproximationByPerfectComplexes.{u, u} B S hS X hX :=
  approximationByPerfectComplexes_of_isAffineSpace B S hS X hX hXa

end AlgebraicGeometry.Space

end
