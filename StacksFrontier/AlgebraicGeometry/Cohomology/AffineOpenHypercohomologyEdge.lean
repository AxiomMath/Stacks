module

public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.TruncationTower
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.AcyclicObject
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The hypercohomology edge isomorphism over an affine open of a scheme

Let `X` be a scheme and let `E` be an object of `D(𝒪_X)` all of whose cohomology sheaves are
quasi-coherent.  Over an **affine open** `U` of `X` the edge morphism of the hypercohomology
spectral sequence
$$ H^q(R\Gamma(U, E)) \longrightarrow \Gamma(U, H^q(E)) $$
is an isomorphism, in every degree `q` and with **no boundedness hypothesis on `E`**.

This is [Stacks, Tag 0BKZ] at the basis of affine opens, whose two hypotheses are discharged
here and nowhere else in the library:

* the basis has enough objects, `TopologicalSpace.Opens.hasEnoughObjects_of_isBasis` applied to
  `AlgebraicGeometry.Scheme.isBasis_affineOpens`;
* the cohomology sheaves are acyclic over every affine open, which is Serre vanishing
  ([Stacks, Tag 01XB]) in the `rightDerived (evaluation)` spelling,
  `AlgebraicGeometry.isZero_rightDerived_evaluation_homologyFunctor_of_isAffineOpen`.

## Why this statement and not the one beside it

`AlgebraicGeometry.isIso_derivedGlobalSectionsHomologyComparison_app_of_isGE` records the same
comparison for the `A`-linear global sections of an affine scheme over a ring, and only for a
cohomologically **bounded below** `E`: it is read off
`Stacks.BoundedBelowEdge.isIso_derivedHomologyComparison_app_of_isGE`, which is about the
comparison `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedHomologyComparison`
built from the universal property of a right derived functor.  The statement here is about the
*other* edge morphism of this development,
`Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge`, which is built from the
sheafification unit; the two have the same type and are not identified anywhere in the library,
and only the second has the unbounded theorem 0BKZ attached to it.

## Main results

* `AlgebraicGeometry.isIso_hypercohomologyEdge_app_of_isAffineOpen`: **the edge morphism over an
  affine open is invertible at an object with quasi-coherent cohomology.**
* `AlgebraicGeometry.affineOpenHypercohomologyIso`: the same as an isomorphism
  `H^q(RΓ(U, E)) ≅ Γ(U, H^q(E))` of `Γ(X, U)`-modules.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.HypercohomologyEdge.evaluation_additive

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (E : DerivedCategory X.Modules)

/-- **The hypercohomology edge morphism over an affine open of a scheme is invertible**, at an
object of `D(𝒪_X)` whose cohomology sheaves are all quasi-coherent, in every degree and with no
boundedness hypothesis.

This is [Stacks, Tag 0BKZ] at the basis of affine opens of `X`: the basis has enough objects,
and the cohomology sheaves are acyclic over every member of it by Serre vanishing. -/
@[stacks 0BKZ "at the affine opens of a scheme, for an object with quasi-coherent cohomology",
  ega "III 1.3.1" "more general"]
theorem isIso_hypercohomologyEdge_app_of_isAffineOpen
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj E).IsQuasicoherent)
    (U : X.Opens) (hU : U ∈ X.affineOpens) (q : ℤ) :
    IsIso ((Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge
      X.ringCatSheaf U q).app E) :=
  Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover
    X.ringCatSheaf U E (· ∈ X.affineOpens)
    (TopologicalSpace.Opens.hasEnoughObjects_of_isBasis X.isBasis_affineOpens)
    (fun V hV p hp m => isZero_rightDerived_evaluation_homologyFunctor_of_isAffineOpen
      X E hE V hV p hp m) hU q

/-- **`H^q(RΓ(U, E)) ≅ Γ(U, H^q(E))` over an affine open**, as an isomorphism of modules over the
ring of sections, for an object with quasi-coherent cohomology.  This is
`AlgebraicGeometry.isIso_hypercohomologyEdge_app_of_isAffineOpen` read as an isomorphism. -/
def affineOpenHypercohomologyIso
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj E).IsQuasicoherent)
    (U : X.Opens) (hU : U ∈ X.affineOpens) (q : ℤ) :
    (Stacks.Cohomology.HypercohomologyEdge.derivedSections X.ringCatSheaf U ⋙
        DerivedCategory.homologyFunctor
          (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U))) q).obj E ≅
      (DerivedCategory.homologyFunctor X.Modules q ⋙
        SheafOfModules.evaluation X.ringCatSheaf (op U)).obj E :=
  @asIso _ _ _ _ _ (isIso_hypercohomologyEdge_app_of_isAffineOpen X E hE U hU q)

end AlgebraicGeometry

end
