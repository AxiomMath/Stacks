module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedTotalRing
public import StacksFrontier.AlgebraicGeometry.AlgebraSheafModuleFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.CommRingSheafLiftIso
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPuncturedTotalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.RelativeSpecTransport

/-!
# The punctured cone is the relative spectrum of the algebra of all integral twists

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A`, and let `π : L ⟶ P` be the cone attached
to the truncation algebra, with `U ⊆ L` the punctured cone. The degreewise inclusions assemble
into a ring homomorphism `Γ(V, ⨁_{m ∈ ℤ} 𝒪_P(m)) →+* Γ(U, (π|_U)⁻¹V)` over every open `V` of `P`,
which is `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTotalRingHom`. **This file assembles
those into a morphism of presheaves of rings, identifies `(π|_U)_* 𝒪_U` with the ungraded
realization of `Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra`, and carries the
identification through to the relative spectrum**, arriving at the presentation on the left of
the diagram of [Stacks, Tag 0EKG]:

  `U = Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m))`,

an isomorphism of schemes over `P` naming the twist algebra itself rather than the direct image
`(π|_U)_* 𝒪_U` it was computed from.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConePushforwardRingSheaf`: the direct image
  `(π|_U)_* 𝒪_U`, read as a sheaf of rings.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTotalPresheafHom`: the degreewise inclusions
  as a morphism of presheaves of rings.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeUngradedSheafIso`: **`(π|_U)_* 𝒪_U` is the
  ungraded realization of the algebra of all integral twists**, as sheaves of rings.
* `Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebraSheaf`: **the algebra of all
  integral twists as a sheaf of commutative `𝒪_P`-algebras.**
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeAlgebraSheafIso`: **`(π|_U)_* 𝒪_U` is that
  algebra sheaf.**
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeRelativeSpecTwistAlgebraIso`: **`U` is,
  over `P`, the relative spectrum of the algebra of all integral twists.**

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.bijective_puncturedTotalPresheafHom_app`,
  `isLocallyInjective_puncturedTotalPresheafHom` and
  `isLocallySurjective_puncturedTotalPresheafHom`: the morphism of presheaves of rings is
  bijective on the sections over a standard open of a positive-degree homogeneous element, hence
  locally bijective.
* `Stacks.AlgebraicGeometry.ProjConeTwist.heq_twistMul_comm`: the multiplication of the algebra of
  all integral twists is commutative on homogeneous local sections.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTotalMap_structureMap`: the degreewise
  inclusions carry the structure map `r ↦ r · 1` of the ungraded realization to the pullback of
  functions along `π|_U`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.isQuasicoherent_integerTwistAlgebraSheaf`: the algebra
  sheaf is quasi-coherent.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeRelativeSpecTwistAlgebraIso_hom_left_comp`:
  the presentation lies over `P`.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
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

attribute [local instance] ProjectiveSpectrum.isPrime ProjAndSpec.isAffineHom_pi_restrict
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-! ### The direct image as a sheaf of rings -/

/-- The direct image `(π|_U)_* 𝒪_U` of the structure sheaf of the punctured cone, read as a sheaf
of rings: the sheaf of rings underlying the algebra sheaf of the restricted cone projection. -/
abbrev puncturedConePushforwardRingSheaf :
    Sheaf (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜)) RingCat.{u} :=
  Stacks.RelativeSpec.AlgebraSheaf.ringSheaf (pushforwardAlgebra ((openUInL 𝒜).ι ≫ pi 𝒜))

/-- **The degreewise inclusions as a morphism of presheaves of rings** from the ungraded
realization of the algebra of all integral twists into `(π|_U)_* 𝒪_U`. -/
@[stacks 0EKG "the degreewise inclusions as a morphism of presheaves of rings from the ungraded \
realization of the integral twist algebra to (pi|_U)_* O_U, for the truncation cone"]
def puncturedTotalPresheafHom :
    (integerTwistPresheafAlgebra 𝒜).totalPresheaf ⟶ (puncturedConePushforwardRingSheaf 𝒜).obj where
  app V := RingCat.ofHom (puncturedTotalRingHom 𝒜 V.unop)
  naturality _ _ g :=
    RingCat.hom_ext (RingHom.ext fun z =>
      PresheafOfModules.naturality_apply (puncturedTwistDirectSumHom 𝒜) g z)

/-- **Over a standard open of a positive-degree homogeneous element the morphism of presheaves of
rings is bijective.** -/
theorem bijective_puncturedTotalPresheafHom_app (p : PositiveElem 𝒜) :
    Function.Bijective (ConcreteCategory.hom
      ((puncturedTotalPresheafHom 𝒜).app (op (positiveBasicOpen 𝒜 p)))) :=
  bijective_puncturedTwistDirectSumHom_app 𝒜 p

/-- The morphism of presheaves of rings is locally injective. -/
theorem isLocallyInjective_puncturedTotalPresheafHom :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜))
      (puncturedTotalPresheafHom 𝒜) :=
  Stacks.AlgebraicGeometry.MeromorphicConstantModule.isLocallyInjective_of_injective_basis
    (B := positiveBasicOpen 𝒜) _ (isBasis_positiveBasicOpen 𝒜)
    fun p => (bijective_puncturedTotalPresheafHom_app 𝒜 p).1

/-- The morphism of presheaves of rings is locally surjective. -/
theorem isLocallySurjective_puncturedTotalPresheafHom :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜))
      (puncturedTotalPresheafHom 𝒜) :=
  Stacks.AlgebraicGeometry.MeromorphicConstantModule.isLocallySurjective_of_surjective_basis
    (B := positiveBasicOpen 𝒜) _ (isBasis_positiveBasicOpen 𝒜)
    fun p => (bijective_puncturedTotalPresheafHom_app 𝒜 p).2

/-- **`(π|_U)_* 𝒪_U` is the ungraded realization of the algebra of all integral twists**, as
sheaves of rings. -/
@[stacks 0EKG "the identification (pi|_U)_* O_U = the ungraded realization of the integral twist \
algebra, as sheaves of rings, for the punctured cone of the truncation algebra"]
def puncturedConeUngradedSheafIso :
    (integerTwistAlgebra 𝒜).ungradedSheaf ≅ puncturedConePushforwardRingSheaf 𝒜 :=
  Stacks.sheafifyRingIsoOfLocallyBijective (puncturedTotalPresheafHom 𝒜)
    (isLocallyInjective_puncturedTotalPresheafHom 𝒜)
    (isLocallySurjective_puncturedTotalPresheafHom 𝒜)

/-- The identification restricts along the sheafification unit to the degreewise inclusions. -/
theorem toSheafify_puncturedConeUngradedSheafIso_hom :
    (integerTwistPresheafAlgebra 𝒜).toTotalSheaf
          (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜)) ≫
        (puncturedConeUngradedSheafIso 𝒜).hom.hom =
      puncturedTotalPresheafHom 𝒜 :=
  Stacks.toSheafify_sheafifyRingHom (puncturedTotalPresheafHom 𝒜)

/-! ### Commutativity of the graded multiplication -/

/-- **The multiplication of the algebra of all integral twists is commutative** on homogeneous
local sections: it is the pointwise product of the values in the module fibres. -/
@[stacks 0EKG "the multiplication of the integral twist algebra is commutative on homogeneous \
local sections"]
theorem heq_twistMul_comm (i j : ℤ) (V : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a : (twistingSheaf 𝒜 i).val.obj V) (b : (twistingSheaf 𝒜 j).val.obj V) :
    HEq ((twistMul 𝒜 i j).app V a b) ((twistMul 𝒜 j i).app V b a) := by
  refine twist_heq 𝒜 (add_comm i j) fun s => ?_
  show a.1 s * b.1 s = b.1 s * a.1 s
  exact mul_comm _ _

/-! ### The algebra of all integral twists as a sheaf of algebras over the structure sheaf -/

/-- **The algebra of all integral twists `⨁_{m ∈ ℤ} 𝒪_P(m)` as a sheaf of commutative
`𝒪_P`-algebras.** -/
@[stacks 0EKG "the integral twist algebra as a sheaf of commutative algebras over the structure \
sheaf of P"]
def integerTwistAlgebraSheaf : Stacks.RelativeSpec.AlgebraSheaf (AlgebraicGeometry.Proj 𝒜) :=
  Stacks.RelativeSpec.gradedAlgebraSheaf (AlgebraicGeometry.Proj 𝒜) (integerTwistAlgebra 𝒜)
    (heq_twistMul_comm 𝒜)

/-! ### The structure morphism -/

/-- **The degreewise inclusions carry the structure map `r ↦ r · 1` of the ungraded realization to
the pullback of functions along `π|_U`.** -/
@[stacks 0EKG "the degreewise inclusions carry the structure map of the ungraded realization of \
the integral twist algebra to the pullback of functions along the punctured cone projection"]
theorem puncturedTotalMap_structureMap (V : Opens (ProjectiveSpectrum.top 𝒜))
    (r : ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj ⋙
      forget₂ CommRingCat.{u} RingCat.{u}).obj (op V)) :
    puncturedTotalMap 𝒜 V ((integerTwistPresheafAlgebra 𝒜).structureMap (op V) r) =
      (((openUInL 𝒜).ι ≫ pi 𝒜).c.app (op V)).hom r := by
  have key : puncturedTotalMap 𝒜 V ((integerTwistPresheafAlgebra 𝒜).structureMap (op V) r) =
      ((openUInL 𝒜).ι ≫ pi 𝒜).app V r * puncturedTotalMap 𝒜 V 1 :=
    map_smul (ConcreteCategory.hom ((puncturedTwistDirectSumHom 𝒜).app (op V))) r
      (1 : (integerTwistPresheafAlgebra 𝒜).Total (op V))
  rw [key, puncturedTotalMap_one, mul_one]

/-- The identification of `(π|_U)_* 𝒪_U` with the ungraded realization, read on a section coming
from the presheaf: it is the degreewise inclusion. -/
theorem puncturedConeUngradedSheafIso_totalUnit (V : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (z : (integerTwistPresheafAlgebra 𝒜).Total V) :
    ((puncturedConeUngradedSheafIso 𝒜).hom.hom.app V).hom
        ((integerTwistPresheafAlgebra 𝒜).totalUnit
          (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜)) V z) =
      puncturedTotalMap 𝒜 V.unop z :=
  congrArg
    (fun φ : (integerTwistPresheafAlgebra 𝒜).totalPresheaf ⟶
        (puncturedConePushforwardRingSheaf 𝒜).obj => (φ.app V).hom z)
    (toSheafify_puncturedConeUngradedSheafIso_hom 𝒜)

/-! ### The identification of algebra sheaves, and the relative spectrum -/

/-- **`(π|_U)_* 𝒪_U` is the algebra of all integral twists**, as sheaves of commutative
`𝒪_P`-algebras. -/
@[stacks 0EKG "the identification (pi|_U)_* O_U = the integral twist algebra, as sheaves of \
commutative algebras over the structure sheaf of P, for the punctured cone of the truncation \
algebra"]
def puncturedConeAlgebraSheafIso :
    integerTwistAlgebraSheaf 𝒜 ≅ pushforwardAlgebra ((openUInL 𝒜).ι ≫ pi 𝒜) :=
  Under.isoMk
    (Stacks.CommRingSheaf.isoMk (pushforwardAlgebra ((openUInL 𝒜).ι ≫ pi 𝒜)).right
      ((integerTwistAlgebra 𝒜).mul_comm_ungradedSheaf (heq_twistMul_comm 𝒜))
      (puncturedConeUngradedSheafIso 𝒜))
    (by
      refine CategoryTheory.Sheaf.hom_ext (NatTrans.ext (funext fun V => CommRingCat.hom_ext
        (RingHom.ext fun r => ?_)))
      exact (puncturedConeUngradedSheafIso_totalUnit 𝒜 V
        ((integerTwistPresheafAlgebra 𝒜).structureMap V r)).trans
        (puncturedTotalMap_structureMap 𝒜 V.unop r))

/-- The algebra of all integral twists is a quasi-coherent sheaf of `𝒪_P`-algebras: it is the
direct image of the structure sheaf of the punctured cone along the affine morphism `π|_U`. -/
@[stacks 0EKG "the integral twist algebra is a quasi-coherent sheaf of algebras over the \
structure sheaf of P"]
instance isQuasicoherent_integerTwistAlgebraSheaf :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (integerTwistAlgebraSheaf 𝒜) :=
  Stacks.RelativeSpec.AlgebraSheaf.isQuasicoherent_of_iso (puncturedConeAlgebraSheafIso 𝒜).symm
    (isQuasicoherent_pushforwardAlgebra ((openUInL 𝒜).ι ≫ pi 𝒜))

/-- **`U = Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m))`**: the punctured cone is, over `P = Proj A`, the relative
spectrum of the algebra of all integral twists. -/
@[stacks 0EKG "U is, over P, the relative spectrum of the integral twist algebra, for the \
punctured cone of the truncation algebra"]
def puncturedConeRelativeSpecTwistAlgebraIso :
    Over.mk ((openUInL 𝒜).ι ≫ pi 𝒜) ≅
      Over.mk (relativeSpecToBase (integerTwistAlgebraSheaf 𝒜)) :=
  relativeSpecIsoOfAlgebraIso ((openUInL 𝒜).ι ≫ pi 𝒜) (integerTwistAlgebraSheaf 𝒜)
    (puncturedConeAlgebraSheafIso 𝒜).symm

/-- The presentation of the punctured cone as a relative spectrum is one over `P`. -/
theorem puncturedConeRelativeSpecTwistAlgebraIso_hom_left_comp :
    (puncturedConeRelativeSpecTwistAlgebraIso 𝒜).hom.left ≫
        relativeSpecToBase (integerTwistAlgebraSheaf 𝒜) =
      (openUInL 𝒜).ι ≫ pi 𝒜 :=
  Over.w (puncturedConeRelativeSpecTwistAlgebraIso 𝒜).hom

/-- **The map `U ⟶ Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m))` of the diagram is exhibited**: it is the morphism
glued, over the standard opens of `P`, out of the identification
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeAlgebraSheafIso` of `(π|_U)_* 𝒪_U` with the
integral twist algebra. -/
theorem puncturedConeRelativeSpecTwistAlgebraIso_hom :
    (puncturedConeRelativeSpecTwistAlgebraIso 𝒜).hom =
      toRelativeSpecOfAlgebraIso ((openUInL 𝒜).ι ≫ pi 𝒜) (integerTwistAlgebraSheaf 𝒜)
        (puncturedConeAlgebraSheafIso 𝒜).symm :=
  rfl

/-- **The map `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ U` of the diagram is exhibited** in the same way. -/
theorem puncturedConeRelativeSpecTwistAlgebraIso_inv :
    (puncturedConeRelativeSpecTwistAlgebraIso 𝒜).inv =
      fromRelativeSpecOfAlgebraIso ((openUInL 𝒜).ι ≫ pi 𝒜) (integerTwistAlgebraSheaf 𝒜)
        (puncturedConeAlgebraSheafIso 𝒜).symm :=
  rfl

end Stacks.AlgebraicGeometry.ProjConeTwist

end
