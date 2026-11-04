module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedTotalRing
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraToAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistTotalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.RelativeSpecCriterion

/-!
# `π_* 𝒪_L` is the ungraded realization of the nonnegative twist algebra, as a sheaf of rings

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A`, and let `π : L ⟶ P` be the cone attached
to the truncation algebra. `Stacks.AlgebraicGeometry.ProjConeTwist.coneStructureCoproductIso`
identifies `π_* 𝒪_L` with the coproduct of the homogeneous pieces of
`Stacks.AlgebraicGeometry.ProjConeTwist.nonnegTwistAlgebra` as sheaves of `𝒪_P`-modules. **This
file upgrades that identification to one of sheaves of rings**: the degreewise inclusions on the
sections over an open assemble into a morphism of presheaves of *rings* out of the ungraded
realization of [Stacks, Tag 01CF], and that morphism is bijective on the sections over a standard
open of a positive-degree homogeneous element, hence exhibits `π_* 𝒪_L` as the sheafification —
which is the ungraded realization `SheafOfModules.GradedAlgebra.ungradedSheaf`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjConeTwist.conePushforwardRingSheaf`: the direct image `π_* 𝒪_L`,
  read as a sheaf of rings — the sheaf of rings of the algebra sheaf
  `Stacks.AffineAlgebraEquivalence.pushforwardAlgebra` of the cone projection.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTotalPresheafHom`: **the degreewise inclusions as a
  morphism of presheaves of rings** from the ungraded realization of the nonnegative twist algebra
  to `π_* 𝒪_L`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneUngradedSheafIso`: **`π_* 𝒪_L` is the ungraded
  realization of the algebra of nonnegative twists, as sheaves of rings.**

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.bijective_coneTotalPresheafHom_app`: the morphism of
  presheaves of rings is bijective on the sections over a standard open of a positive-degree
  homogeneous element.
* `Stacks.AlgebraicGeometry.ProjConeTwist.isLocallyInjective_coneTotalPresheafHom` and
  `isLocallySurjective_coneTotalPresheafHom`: hence it is locally bijective.
* `Stacks.AlgebraicGeometry.ProjConeTwist.toSheafify_coneUngradedSheafIso_hom`: the
  identification restricts along the sheafification unit to the degreewise inclusions.

## Implementation notes

Only naturality is new content here: on the sections over a fixed open the morphism *is* the ring
homomorphism `Stacks.AlgebraicGeometry.ProjConeTwist.coneTotalRingHom`, and naturality is the
naturality of `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistDirectSumHom`, which is already a
morphism of presheaves of modules. Everything else is the shape of the target: the sections of
`π_* 𝒪_L` as a sheaf of commutative rings, forgotten into `RingCat`, are the functions
`Stacks.AlgebraicGeometry.ProjConeTwist.coneSections` on the part of the cone lying over the open,
which is the ring `coneTotalRingHom` maps into.

Local bijectivity is read off the basis of positive-degree standard opens exactly as
`Stacks.AlgebraicGeometry.ProjConeTwist.coneStructureSheafifyIso` does it for the underlying
sheaves of modules, by `Stacks.AlgebraicGeometry.MeromorphicConstantModule`'s two criteria, which
are stated for an arbitrary concrete target category and so apply to `RingCat` unchanged. The
passage from local bijectivity to the isomorphism of sheaves of rings is
`Stacks.sheafifyRingIsoOfLocallyBijective`.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory
open CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation
open Stacks.AlgebraicGeometry.ProjTwistComparison

namespace Stacks.AlgebraicGeometry.ProjConeTwist

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The direct image `π_* 𝒪_L` of the structure sheaf of the cone, read as a sheaf of rings: the
sheaf of rings underlying the algebra sheaf of the cone projection. -/
abbrev conePushforwardRingSheaf :
    Sheaf (Opens.grothendieckTopology ↥(AlgebraicGeometry.Proj 𝒜)) RingCat.{u} :=
  Stacks.RelativeSpec.AlgebraSheaf.ringSheaf (pushforwardAlgebra (pi 𝒜))

/-- **The degreewise inclusions as a morphism of presheaves of rings** from the ungraded
realization of the algebra of nonnegative twists into `π_* 𝒪_L`. Over an open of `P` it is the
ring homomorphism `Stacks.AlgebraicGeometry.ProjConeTwist.coneTotalRingHom`; naturality is the
naturality of `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistDirectSumHom`. -/
@[stacks 0EKG "the degreewise inclusions as a morphism of presheaves of rings from the ungraded \
realization of the nonnegative twist algebra to pi_* O_L, for the truncation cone"]
def coneTotalPresheafHom :
    (nonnegTwistPresheafAlgebra 𝒜).totalPresheaf ⟶ (conePushforwardRingSheaf 𝒜).obj where
  app U := RingCat.ofHom (coneTotalRingHom 𝒜 U.unop)
  naturality _ _ f :=
    RingCat.hom_ext (RingHom.ext fun z =>
      PresheafOfModules.naturality_apply (coneTwistDirectSumHom 𝒜) f z)

/-- **Over a standard open of a positive-degree homogeneous element the morphism of presheaves of
rings is bijective**, which is `bijective_coneTwistDirectSumHom_app` read in `RingCat`. -/
theorem bijective_coneTotalPresheafHom_app (p : PositiveElem 𝒜) :
    Function.Bijective (ConcreteCategory.hom
      ((coneTotalPresheafHom 𝒜).app (op (positiveBasicOpen 𝒜 p)))) :=
  bijective_coneTwistDirectSumHom_app 𝒜 p

/-- The morphism of presheaves of rings is locally injective. -/
theorem isLocallyInjective_coneTotalPresheafHom :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥(AlgebraicGeometry.Proj 𝒜))
      (coneTotalPresheafHom 𝒜) :=
  Stacks.AlgebraicGeometry.MeromorphicConstantModule.isLocallyInjective_of_injective_basis
    (B := positiveBasicOpen 𝒜) _ (isBasis_positiveBasicOpen 𝒜)
    fun p => (bijective_coneTotalPresheafHom_app 𝒜 p).1

/-- The morphism of presheaves of rings is locally surjective. -/
theorem isLocallySurjective_coneTotalPresheafHom :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥(AlgebraicGeometry.Proj 𝒜))
      (coneTotalPresheafHom 𝒜) :=
  Stacks.AlgebraicGeometry.MeromorphicConstantModule.isLocallySurjective_of_surjective_basis
    (B := positiveBasicOpen 𝒜) _ (isBasis_positiveBasicOpen 𝒜)
    fun p => (bijective_coneTotalPresheafHom_app 𝒜 p).2

/-- **`π_* 𝒪_L` is the ungraded realization of the algebra of nonnegative twists**, as sheaves of
rings. This is the identification of [Stacks, Tag 0EKG] at the level of sheaves of rings, as
opposed to the identification `coneStructureCoproductIso` of the underlying sheaves of
`𝒪_P`-modules. -/
@[stacks 0EKG "the identification pi_* O_L = the ungraded realization of the nonnegative twist \
algebra, as sheaves of rings, for the cone of the truncation algebra"]
def coneUngradedSheafIso :
    (nonnegTwistAlgebra 𝒜).ungradedSheaf ≅ conePushforwardRingSheaf 𝒜 :=
  Stacks.sheafifyRingIsoOfLocallyBijective (coneTotalPresheafHom 𝒜)
    (isLocallyInjective_coneTotalPresheafHom 𝒜) (isLocallySurjective_coneTotalPresheafHom 𝒜)

/-- The identification restricts along the sheafification unit to the degreewise inclusions. -/
theorem toSheafify_coneUngradedSheafIso_hom :
    (nonnegTwistPresheafAlgebra 𝒜).toTotalSheaf
          (Opens.grothendieckTopology ↥(AlgebraicGeometry.Proj 𝒜)) ≫
        (coneUngradedSheafIso 𝒜).hom.hom =
      coneTotalPresheafHom 𝒜 :=
  Stacks.toSheafify_sheafifyRingHom (coneTotalPresheafHom 𝒜)

end Stacks.AlgebraicGeometry.ProjConeTwist

end
