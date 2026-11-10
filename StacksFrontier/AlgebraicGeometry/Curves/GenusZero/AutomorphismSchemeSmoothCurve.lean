module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.AutomorphismSchemeDimension
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZero.AutomorphismSchemeDimension
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.ProjectiveLineEquivalences
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineProjModel
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointFinrank

/-!
# The automorphism group scheme of a smooth curve of genus zero

Let `k` be an algebraically closed field and `X` a smooth proper curve over `k` of genus zero.
A closed point `x` of `X` has residue field `k` and a normal local ring, so the invertible
module `𝒪_X(x)` has degree one; together with `H⁰(X, 𝒪_X) = k` and genus zero this gives
`X ≅ ℙ¹_k` ([Stacks, Tag 0C6U]). Since `Aut(ℙ¹_k) = PGL_{2,k}` as functors, the automorphism
functor of `X` is represented by `PGL_{2,k}`, and every scheme representing it has dimension
three. This is the genus zero clause of [Stacks, Tag 0DSV]; the genus one clause is
`AlgebraicGeometry.GenusOne.autScheme_topologicalKrullDim_eq_one_of_genus_eq_one`.

## Main results

* `AlgebraicGeometry.GenusZero.nonempty_iso_projectiveLineOver_of_genus_eq_zero`: a smooth proper
  curve of genus zero over an algebraically closed field is isomorphic to `ℙ¹_k` over `k`.
* `AlgebraicGeometry.GenusZero.autScheme_topologicalKrullDim_eq_three_of_genus_eq_zero`:
  **[Stacks, Tag 0DSV], genus zero**: for a smooth proper curve of genus zero over an
  algebraically closed field the automorphism functor is represented by `PGL_{2,k}`, and every
  representing scheme has dimension three.

## Implementation notes

The hypotheses are those of the genus one clause: a smooth curve (`AlgebraicGeometry.IsCurve`
with `Smooth`), proper as every object of the stack of curves over `k` is, of genus zero in the
sense of `AlgebraicGeometry.genus`, over an algebraically closed field. The projective line is
the glued model `AlgebraicGeometry.projectiveLine`, identified with `Proj k[T₀, T₁]` by
`AlgebraicGeometry.projectiveLineIsoProj`; the latter is the model of `ℙ¹_k` in
`AlgebraicGeometry.projectiveLine_tfae`.

## References

* [Stacks Project, Tag 0DSV](https://stacks.math.columbia.edu/tag/0DSV)
* [Stacks Project, Tag 0C6U](https://stacks.math.columbia.edu/tag/0C6U)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GenusZero

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsProper f] [Smooth f] [IsCurve k f]

/-- **A smooth proper curve of genus zero over an algebraically closed field is the projective
line.** A closed point has residue field `k` and a normal local ring, which gives an invertible
module of degree one, and `H⁰(X, 𝒪_X) = k`; hence `X ≅ ℙ¹_k` by [Stacks, Tag 0C6U]. -/
theorem nonempty_iso_projectiveLineOver_of_genus_eq_zero (hg : genus f = 0) :
    Nonempty (Over.mk f ≅ projectiveLineOver k) := by
  have hdim : topologicalKrullDim X = 1 := IsCurve.topologicalKrullDim_eq_one (f := f)
  have : IsNormal (Spec (.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  have : IsNormal X := isNormal_of_smooth f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hx⟩ : (closedPoints X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    have := closure_closedPoints (X := X)
    rw [h, closure_empty] at this
    exact Set.empty_ne_univ this
  replace hx : IsClosed ({x} : Set X) := hx
  obtain ⟨L, hL, hdeg⟩ := exists_invertibleCurveDegree_eq_one_of_gcd f hdim.le (n := 1)
    (fun _ ↦ x) (fun _ ↦ hx) (fun _ ↦ IsNormal.stalk_normal x)
    (by simpa using finrank_residueField_of_isClosed f x hx)
  obtain ⟨e, he⟩ := ((projectiveLine_tfae f).out 6 1).mp
    (by exact ⟨GenusOne.isIso_globalSections_of_isAlgClosed f, hg, L, hL, hdeg⟩)
  refine ⟨Over.isoMk (e ≪≫ (projectiveLineIsoProj k).symm) ?_⟩
  change (e.hom ≫ (projectiveLineIsoProj k).inv) ≫ (projectiveLine k ↘ Spec (.of k)) = f
  rw [← projectiveLineIsoProj_hom_comp_projToSpecCoeff, Category.assoc, Iso.inv_hom_id_assoc, he]

/-- **Stacks Project, Tag 0DSV**, genus zero. **The automorphism group scheme of a smooth proper
curve of genus zero over an algebraically closed field is `PGL_{2,k}` and has dimension three.**
The automorphism functor `T ↦ Aut_T(X ×_k T)` of `X` over `k` is represented by `PGL_{2,k}`, and
every scheme representing it has dimension three. -/
@[stacks 0DSV "genus zero: the automorphism functor of a smooth proper genus zero curve over an \
algebraically closed field is represented by PGL_{2,k}, and every representing scheme has \
dimension three"]
theorem autScheme_topologicalKrullDim_eq_three_of_genus_eq_zero (hg : genus f = 0) :
    Nonempty ((Scheme.autFunctor (Over.mk f)).RepresentableBy
        (projectiveGeneralLinearTwoScheme k)) ∧
      ∀ G : Over (Spec (.of k)), (Scheme.autFunctor (Over.mk f)).RepresentableBy G →
        topologicalKrullDim G.left = 3 := by
  obtain ⟨e⟩ := nonempty_iso_projectiveLineOver_of_genus_eq_zero f hg
  exact ⟨⟨(projectiveLineAutFunctorRepresentableBy k).ofIso (Scheme.autFunctorIsoOfIso e).symm⟩,
    (autScheme_topologicalKrullDim_eq_three_of_iso_projectiveLine k f e).2⟩

end AlgebraicGeometry.GenusZero
