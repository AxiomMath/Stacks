module

public import StacksFrontier.AlgebraicGeometry.Duality.CohomologyHypercohomology
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.ModelComparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CoefficientScalars
public import StacksFrontier.Homology.DerivedCategory.LocallySmall

/-!
# The twists of `ℙⁿ_R` as objects of `D_QCoh`, and their hypercohomology

Let `R` be a commutative ring and `n ≥ 0`, and write `X = ℙⁿ_R = Proj R[T₀, …, Tₙ]`. Serre's
computation of the cohomology of the twisting sheaves, [Stacks, Tag 01XT], is carried out in this
library through the Čech complex of the standard coordinate cover and produces the `R`-module
`Stacks.ProjectiveSpace.Cohomology.twistCohomology R n d q`, the `q`-th classical right derived
functor of global sections at `𝒪_X(d)`.

The duality machinery of `StacksFrontier/AlgebraicGeometry/Duality/`, on the other hand, works in
the quasi-coherent derived category `D_QCoh(𝒪_X)` of
`Stacks.Duality.quasiCoherentDerivedCategory`. This file connects the two:

* it produces `𝒪_X(d)` as an *object* of `D_QCoh(𝒪_X)`, placed in cohomological degree zero; and
* it identifies `twistCohomology R n d q` with the degree-`q` cohomology of unbounded derived
  global sections `RΓ(X, -) : D(𝒪_X) ⥤ D(R)` evaluated at that object.

Both halves are what the Stacks project's computation of the twisted inverse image on projective
space, [Stacks, Tag 0A9W], consumes: there the asserted isomorphism `f^*ℒ(-n-1)[n] ≅ a(𝒪_Y)` is
tested against the generators `𝒪_X, 𝒪_X(-1), …, 𝒪_X(-n)` of `D_QCoh(𝒪_X)` of
[Stacks, Tag 0A9V], and the groups the test produces are the cohomology modules of twists that
Serre's computation evaluates.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.twistQcoh` — **`𝒪_X(d)` in degree zero, as an object of
  `D_QCoh(𝒪_X)`.**
* `Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoDerivedGlobalSections` — **the comparison
  `H^q(ℙⁿ_R, 𝒪(d)) ≅ H^q(RΓ(X, 𝒪_X(d)))`**, from Serre's Čech computation to the hypercohomology
  of the `D_QCoh` object.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.globalSectionsOver_projToSpecCoeff` — `R`-linear global
  sections along the structure morphism `ℙⁿ_R ⟶ Spec R` are sections over `⊤` with scalars
  restricted along `Stacks.ProjectiveSpace.Cohomology.coeffScalar`.
* `Stacks.ProjectiveSpace.Cohomology.twistQcoh_obj` — the underlying object of `twistQcoh` is the
  twisting sheaf placed in degree zero.

## Implementation notes

*The derived-category model.* `Stacks.Duality.quasiCoherentDerivedCategory` is a full subcategory
of `DerivedCategory X.Modules`, and the model taken here is the locally small one of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, whose instances
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and `ModuleCat.hasDerivedCategory` are
global and apply with no hypothesis. That is the model in which `D_QCoh(𝒪_X)`, its direct sums,
Brown representability and the right adjoint of [Stacks, Tag 0A9E] live, so it is the model the
comparison has to be stated at. `CategoryTheory.HasDerivedCategory.standard` is used by
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/SerreComputation.lean` and
`StacksFrontier/AlgebraicGeometry/ProjectiveCohomology/ModelComparison.lean`, but only as a *local*
instance, so nothing of it reaches this module: `Stacks.ProjectiveSpace.Cohomology.twistCohomology`
is a classical right derived functor, computed from injective resolutions in the abelian category
`X.Modules`, and mentions no derived category at all. So no isomorphism is transported between
the two models here, and the obstruction recorded in
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/DerivedModelCrossing.lean` is not met.

*Quasi-coherence.* The twisting sheaves are invertible, a polynomial ring being generated in
degree one, hence quasi-coherent — `Stacks.ProjectiveCohomology.isQuasicoherent_twistingSheaf`.
That a quasi-coherent module placed in degree zero lies in `D_QCoh` is the general
`Stacks.Duality.DerivedPushforward.derivedCategoryB_singleFunctor_obj`; nothing about `Proj` is
used for it.

*The two steps of the comparison.* `AlgebraicGeometry.globalSectionsOver` of the structure
morphism is evaluation on `⊤` followed by restriction of scalars along the structure map, and the
structure map *is* `Stacks.ProjectiveSpace.Cohomology.coeffScalar` — that is
`Stacks.ProjectiveSpace.Cohomology.ΓSpecIso_inv_comp_appTop_hom_eq_coeffScalar`, which holds by
`rfl`. So the comparison is

1. restriction of scalars pulled out of the right derived functor, which is legitimate because
   restriction of scalars is exact — `Stacks.Duality.rightDerivedCompRestrictScalarsIso`; and
2. the identification of the degree-`q` cohomology of a total right derived functor at an object
   in degree zero with the `q`-th classical right derived functor —
   `Stacks.Duality.rightDerivedGlobalSectionsIsoDerivedCohomology`.

No `@[stacks]` attribute is attached. Nothing here is a new reading of a source result: the
cohomology computation it quotes is the already-registered covering set of [Stacks, Tag 01XT],
and the comparison itself is a change of spelling, not a lemma of the Stacks project.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0A9V](https://stacks.math.columbia.edu/tag/0A9V)
* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)
open Stacks.ProjectiveCohomology (polyGrading isQuasicoherent_twistingSheaf)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveSpace.Cohomology

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

/-! ### `𝒪_X(d)` as an object of `D_QCoh(𝒪_X)` -/

/-- **The twisting sheaf `𝒪_X(d)` of `X = ℙⁿ_R`, in cohomological degree zero, as an object of
`D_QCoh(𝒪_X)`.** The twisting sheaf is quasi-coherent, and a quasi-coherent module placed in
degree zero has quasi-coherent cohomology sheaves in every degree. These are the objects against
which the twisted inverse image on projective space is tested in [Stacks, Tag 0A9W]. -/
def twistQcoh : Stacks.Duality.quasiCoherentDerivedCategory
    (AlgebraicGeometry.Proj (polyGrading R n)) :=
  ⟨(DerivedCategory.singleFunctor
      (AlgebraicGeometry.Proj (polyGrading R n)).Modules 0).obj
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d),
   Stacks.Duality.DerivedPushforward.derivedCategoryB_singleFunctor_obj _
     (isQuasicoherent_twistingSheaf R n d)⟩

/-- The underlying object of `Stacks.ProjectiveSpace.Cohomology.twistQcoh` is the twisting sheaf
placed in cohomological degree zero. -/
theorem twistQcoh_obj :
    (twistQcoh R n d).obj =
      (DerivedCategory.singleFunctor
        (AlgebraicGeometry.Proj (polyGrading R n)).Modules 0).obj
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) :=
  rfl

/-! ### Serre's computation against derived global sections -/

/-- **`R`-linear global sections along `ℙⁿ_R ⟶ Spec R` are sections over `⊤` with scalars
restricted along `Stacks.ProjectiveSpace.Cohomology.coeffScalar`.** The two differ only in how
the structure map `R → Γ(ℙⁿ_R, 𝒪)` is spelled, and
`Stacks.ProjectiveSpace.Cohomology.ΓSpecIso_inv_comp_appTop_hom_eq_coeffScalar` says those
spellings are the same homomorphism. -/
theorem globalSectionsOver_projToSpecCoeff :
    AlgebraicGeometry.globalSectionsOver (projToSpecCoeff R n) =
      Stacks.Cohomology.sectionsFunctor
          (AlgebraicGeometry.Proj (polyGrading R n)) ⊤ ⋙
        ModuleCat.restrictScalars.{u} (coeffScalar R n) :=
  rfl

/-- **Serre's cohomology of a twist is the hypercohomology of the `D_QCoh` object `𝒪_X(d)`.**
The `q`-th classical right derived functor of global sections at `𝒪_X(d)`, read as an `R`-module
as in [Stacks, Tag 01XT], is the degree-`q` cohomology of unbounded derived global sections
`RΓ(X, -) : D(𝒪_X) ⥤ D(R)` at `Stacks.ProjectiveSpace.Cohomology.twistQcoh`. -/
def twistCohomologyIsoDerivedGlobalSections (q : ℕ) :
    twistCohomology R n d q ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (q : ℤ)).obj
        ((AlgebraicGeometry.derivedGlobalSectionsOver (projToSpecCoeff R n)).obj
          (twistQcoh R n d).obj) :=
  (Stacks.Duality.rightDerivedCompRestrictScalarsIso (coeffScalar R n)
      (Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading R n)) ⊤)
      (hE := Stacks.Cohomology.sectionsFunctor_additive _ _)
      (AlgebraicGeometry.globalSectionsOver (projToSpecCoeff R n))
      (hH := AlgebraicGeometry.globalSectionsOver_additive _)
      (eqToIso (globalSectionsOver_projToSpecCoeff R n).symm) q).app _ ≪≫
    (Stacks.Duality.rightDerivedGlobalSectionsIsoDerivedCohomology
      (projToSpecCoeff R n) q).app _

end Stacks.ProjectiveSpace.Cohomology

end
