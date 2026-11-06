module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.PhComparisonTorsionAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.PhComparisonFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhSpacesEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhSpaceSiteOfFppfSite
public import StacksFrontier.Homology.AdjunctionSquareDescent
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardGlobalSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.LerayDerivedUnitComparison
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringCohomologicalDescent
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow

/-!
# Cohomological descent along a proper hypercovering of algebraic spaces

Let `S` be a scheme, `X` an algebraic space over `S` and `a : U → X` a proper hypercovering of `X`
by a simplicial algebraic space (Section 0DHI), with the morphism of topoi
`a : Sh(U_étale) → Sh(X_étale)` of Section 0DE7. This file proves Stacks 0DHL and Stacks 0DHM for
torsion coefficients: for `K ∈ D⁺(X_étale)` with torsion cohomology sheaves,

`K = Ra_*(a⁻¹K)` and `RΓ(X_étale, K) = RΓ(U_étale, a⁻¹K)`.

The source states both for every `K ∈ D⁺(X_étale)`. As written they are false, and their proofs
use the torsion hypothesis through Stacks 0DGU; see
`AlgebraicGeometry.Space.isIso_etaleAugmentation_derivedPlusUnit_of_isProperHypercovering` for a
counterexample with rational coefficients.

## The proof

Choose a big ph site `(Spaces/S)_ph` on the algebraic spaces over `S`
(`AlgebraicGeometry.BigFppfSite.bigPHSpaceSite`) and consider the commutative diagram of topoi of
Tag 0DHJ
```
Sh((Spaces/U)_{ph, total}) --h--> Sh(U_étale)
        | a_ph                       | a
Sh((Spaces/X)_ph)        --h₋₁--> Sh(X_étale)
```
For an abelian sheaf `F` on `X_étale`:

* the units of `h`, `a_ph` and `h₋₁` are invertible (Stacks 0DGT, part (1), degreewise, the proof
  of Tag 0DHK, Stacks 0DA8), so the unit `F → a_* a⁻¹ F` is invertible;
* if `F` is torsion, `h₋₁⁻¹ F` is acyclic for `h₋₁,*` (Stacks 0DGT, part (2)), `a_ph⁻¹ h₋₁⁻¹ F` is
  acyclic for `a_ph,*` (Stacks 0D8N, `U` being a ph hypercovering by Stacks 0DFI) and for `h_*`
  (Stacks 0DGT, part (2), degreewise), so `a⁻¹ F` is acyclic for `a_*`.

This is the computation `Ra_*a⁻¹ = Ra_* Rh_* h⁻¹ a⁻¹ = Rh₋₁,* Ra_{ph,*} a_ph⁻¹ h₋₁⁻¹ = id` of the
source on a single torsion sheaf, carried out by
`CategoryTheory.Adjunction.isIso_unit_app_of_comp_iso` and
`CategoryTheory.Adjunction.isZero_rightDerived_of_comp_iso`. A complex with torsion cohomology
sheaves is a complex of torsion sheaves (Stacks 0DD7), and Leray's acyclicity lemma gives the
statement on `D⁺`
(`Stacks.ComparingTopologies.isIso_derivedPlusAdjunction_unit_app_mapDerivedCategoryPlus`).
Stacks 0DHM follows by Cohomology on Sites, Remark 08J6.

## Main results

* `AlgebraicGeometry.Space.isIso_etaleAugmentation_derivedPlusUnit_of_isProperHypercovering`:
  **Stacks 0DHL**, for torsion coefficients.
* `AlgebraicGeometry.Space.derivedGlobalSectionsIsoOfIsProperHypercovering`: **Stacks 0DHM**, for
  torsion coefficients.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.isIso_rightDerivedFunctorPlus_unit_app_iff`:
  the unit of `a⁻¹ ⊣ Ra_*` is the same whether `a⁻¹` is read degreewise or as its right derived
  functor.

## Implementation notes

The derived categories are in the model `HasDerivedCategory.standard`, the model in which
Stacks 0DD7 and Stacks 0DGU are available.

## References

* [Stacks Project, Tag 0DHL](https://stacks.math.columbia.edu/tag/0DHL)
* [Stacks Project, Tag 0DHM](https://stacks.math.columbia.edu/tag/0DHM)
* [Stacks Project, Tag 0DHJ](https://stacks.math.columbia.edu/tag/0DHJ)
* [Stacks Project, Tag 0DHK](https://stacks.math.columbia.edu/tag/0DHK)
* [Stacks Project, Tag 0DGT](https://stacks.math.columbia.edu/tag/0DGT)
* [Stacks Project, Tag 0DGU](https://stacks.math.columbia.edu/tag/0DGU)
* [Stacks Project, Tag 0D8N](https://stacks.math.columbia.edu/tag/0D8N)
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

/-- The spaces-étale site has global sections of abelian sheaves, through its final object
(instance search through limits of shape `(SpacesEtale B S hS X)ᵒᵖ` times out). -/
local instance (priority := high)
    AlgebraicGeometry.Space.hasGlobalSectionsFunctor_spacesEtale_ProperHypercoveringDerivedDescent
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X : AlgebraicSpaces B S hS) :
    HasGlobalSectionsFunctor (AlgebraicGeometry.Space.SpacesEtale.topology B S hS X)
      AddCommGrpCat.{u + 1} :=
  ⟨_, ⟨constantSheafAdj _ _
    (terminalIsTerminal (C := AlgebraicGeometry.Space.SpacesEtale B S hS X))⟩⟩

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS))

/-- The abelian inverse image along the augmentation of `U_étale` is additive. -/
instance etaleAugmentation_abelianInverseImage_additive :
    (CategoryTheory.Sites.abelianInverseImage (etaleAugmentationMorphism A)).Additive :=
  Functor.additive_of_preserves_binary_products _

open Stacks.Topos.AbelianPushforward in
/-- The direct image along the augmentation of `U_étale` preserves injective abelian sheaves, its
left adjoint being exact. -/
instance etaleAugmentation_abelianPushforward_preservesInjectiveObjects :
    (abelianPushforward (etaleSimplicialSite A).totalTopology
      (etaleAugmentationMorphism A)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (abelianInverseImageAdjPushforward _ (etaleAugmentationMorphism A))

end AlgebraicGeometry.Space

namespace Stacks.Topos.AbelianPushforward

/-- The unit of the abelian adjunction of a morphism of topoi is invertible where the unit of the
geometric adjunction is. -/
theorem isIso_abelianInverseImageAdjPushforward_unit_app {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
    (f : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u)))
    (G : Sheaf K AddCommGrpCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [HasSheafify K AddCommGrpCat.{u}]
    (h : IsIso (f.adj.unit.app ((sheafCompose K (forget AddCommGrpCat.{u})).obj G))) :
    IsIso ((abelianInverseImageAdjPushforward J f).unit.app G) := by
  have : IsIso ((sheafCompose K (forget AddCommGrpCat.{u})).map
      ((abelianInverseImageAdjPushforward J f).unit.app G)) := by
    rw [abelianInverseImageAdjPushforward_unit_forget]; exact h
  exact isIso_of_reflects_iso _ (sheafCompose K (forget AddCommGrpCat.{u}))

end Stacks.Topos.AbelianPushforward

namespace AlgebraicGeometry.BigPHSpaceSite
open Stacks.Topos.AbelianPushforward Space Stacks.CategoryTheory.Hypercovering
variable {S : Scheme.{u}} (P : BigPHSpaceSite S) (A : SimplicialObject.Augmented P.Spaces)

/-- The square of Tag 0DHJ on abelian direct images. -/
def phEtaleComparisonSquareAbelianPushforwardIso :
    abelianPushforward (SimplicialOver.totalTopology P.topology A.left)
        (SimplicialOver.augmentationMorphismOfTopoi P.topology A.left A.hom) ⋙
      abelianPushforward (P.topology.over A.right)
        (spacesEtaleComparisonMorphism P.topology A.right) ≅
    abelianPushforward (SimplicialOver.totalTopology P.topology A.left)
        (phComparisonMorphism A P.topology) ⋙
      abelianPushforward (etaleSimplicialSite A).totalTopology (etaleAugmentationMorphism A) :=
  conjugateIsoEquiv
    ((abelianInverseImageAdjPushforward _ (spacesEtaleComparisonMorphism P.topology A.right)).comp
      (abelianInverseImageAdjPushforward _
        (SimplicialOver.augmentationMorphismOfTopoi P.topology A.left A.hom)))
    ((abelianInverseImageAdjPushforward _ (etaleAugmentationMorphism A)).comp
      (abelianInverseImageAdjPushforward _ (phComparisonMorphism A P.topology)))
    (StacksTag03LR.abelianInverseImageSquareIso _ _ _ _
      (phEtaleComparisonSquareInverseImageIso P A))

/-- **`h⁻¹` is fully faithful** (the proof of Tag 0DHK): the unit of `h⁻¹ ⊣ h_*` for the comparison
`h : Sh((Spaces/U)_{ph, total}) → Sh(U_étale)` of Tag 0DHJ is an isomorphism. -/
instance isIso_phComparisonMorphism_adj_unit :
    IsIso (phComparisonMorphism A P.topology).adj.unit :=
  have hff := fullyFaithfulPhComparisonInverseImage (A := A) P.topology
    (isIso_spacesEtaleComparison_unit P)
  haveI := hff.full
  haveI := hff.faithful
  (phComparisonMorphism A P.topology).adj.unit_isIso_of_L_fully_faithful

variable {P A} (hA : IsProperHypercovering P.fppfSite S P.fppf_mem A)
include hA

/-- The units of `a_ph` and `h` are invertible at the pullbacks of `F`, for a proper
hypercovering. -/
private theorem isIso_augmentation_units_app
    (F : Sheaf (SpacesEtale.topology P.fppfSite S P.fppf_mem A.right) AddCommGrpCat.{u + 1}) :
    IsIso ((abelianInverseImageAdjPushforward _
      (SimplicialOver.augmentationMorphismOfTopoi P.topology A.left A.hom)).unit.app
        ((CategoryTheory.Sites.abelianInverseImage
          (spacesEtaleComparisonMorphism P.topology A.right)).obj F)) ∧
    IsIso ((abelianInverseImageAdjPushforward _ (phComparisonMorphism A P.topology)).unit.app
      ((CategoryTheory.Sites.abelianInverseImage (etaleAugmentationMorphism A)).obj F)) :=
  ⟨SimplicialOver.isIso_augmentationAbelianUnit_app_of_eq P.topology.toPretopology
    (toGrothendieck_toPretopology P) (IsProperHypercovering.isHypercoveringAugmentation hA) _,
    isIso_abelianInverseImageAdjPushforward_unit_app _ (phComparisonMorphism A P.topology) _
      (NatIso.isIso_app_of_isIso _ _)⟩

/-- **The unit `F → a_* a⁻¹ F` is invertible** on abelian sheaves, for a proper hypercovering: the
units of `h`, `a_ph` and `h₋₁` around the square of Tag 0DHJ are invertible. -/
theorem isIso_etaleAugmentation_abelianUnit_app
    (F : Sheaf (SpacesEtale.topology P.fppfSite S P.fppf_mem A.right) AddCommGrpCat.{u + 1}) :
    IsIso ((abelianInverseImageAdjPushforward (etaleSimplicialSite A).totalTopology
      (etaleAugmentationMorphism A)).unit.app F) := by
  have := isIso_spacesEtaleComparison_abelianUnit P A.right F
  obtain ⟨_, _⟩ := isIso_augmentation_units_app hA F
  exact Adjunction.isIso_unit_app_of_comp_iso
    (abelianInverseImageAdjPushforward _ (etaleAugmentationMorphism A))
    (abelianInverseImageAdjPushforward _ (phComparisonMorphism A P.topology))
    (abelianInverseImageAdjPushforward _
      (SimplicialOver.augmentationMorphismOfTopoi P.topology A.left A.hom))
    (abelianInverseImageAdjPushforward _ (spacesEtaleComparisonMorphism P.topology A.right))
    (phEtaleComparisonSquareAbelianPushforwardIso P A) F


/-- **`a⁻¹ F` is acyclic for `a_*`** for a torsion abelian sheaf `F` on `X_étale` and a proper
hypercovering: `Rᵠ a_* (a⁻¹ F) = 0` for `q > 0`. -/
theorem isZero_rightDerived_etaleAugmentation_of_torsion
    (F : Sheaf (SpacesEtale.topology P.fppfSite S P.fppf_mem A.right) AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty _ F) (q : ℕ) (hq : 0 < q) :
    IsZero (((abelianPushforward (etaleSimplicialSite A).totalTopology
      (etaleAugmentationMorphism A)).rightDerived q).obj
        ((CategoryTheory.Sites.abelianInverseImage (etaleAugmentationMorphism A)).obj F)) := by
  let adj_h := abelianInverseImageAdjPushforward _ (phComparisonMorphism A P.topology)
  let adj_b := abelianInverseImageAdjPushforward _
    (SimplicialOver.augmentationMorphismOfTopoi P.topology A.left A.hom)
  have : (abelianPushforward (SimplicialOver.totalTopology P.topology A.left)
      (phComparisonMorphism A P.topology)).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj_h
  have : (abelianPushforward (SimplicialOver.totalTopology P.topology A.left)
      (SimplicialOver.augmentationMorphismOfTopoi P.topology A.left
        A.hom)).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj_b
  obtain ⟨_, _⟩ := isIso_augmentation_units_app hA F
  exact Adjunction.isZero_rightDerived_of_comp_iso
    (abelianInverseImageAdjPushforward _ (etaleAugmentationMorphism A)) adj_h adj_b
    (abelianInverseImageAdjPushforward _ (spacesEtaleComparisonMorphism P.topology A.right))
    (phEtaleComparisonSquareAbelianPushforwardIso P A) F
    (isZero_rightDerived_phComparison_of_torsion P A F hF)
    (SimplicialOver.isZero_rightDerived_augmentationAbelianPushforward_of_eq
      P.topology.toPretopology (toGrothendieck_toPretopology P)
      (IsProperHypercovering.isHypercoveringAugmentation hA) _)
    (isZero_rightDerived_spacesEtaleComparison_of_torsion P A.right F hF) q hq


section Derived

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0DHL for a big ph site `P`**: for a proper hypercovering of algebraic spaces of `P`,
the unit `K → Ra_*(a⁻¹K)` is invertible for `K ∈ D⁺(X_étale)` with torsion cohomology sheaves. -/
theorem isIso_etaleAugmentation_derivedPlusUnit_of_torsion
    (K : DerivedCategory.Plus
      (Sheaf (SpacesEtale.topology P.fppfSite S P.fppf_mem A.right) AddCommGrpCat.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty _
      ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Plus.ι.obj K))) :
    IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction
      (abelianInverseImageAdjPushforward (etaleSimplicialSite A).totalTopology
        (etaleAugmentationMorphism A))).unit.app K) := by
  have : (CategoryTheory.Sites.abelianInverseImage (etaleAugmentationMorphism A)).Additive :=
    (abelianInverseImageAdjPushforward (etaleSimplicialSite A).totalTopology
      (etaleAugmentationMorphism A)).left_adjoint_additive
  obtain ⟨K', ⟨eK⟩⟩ := Stacks.Torsion.exists_mapDerivedCategoryPlus_iso_of_torsionCohomology _ K hK
  refine (NatTrans.isIso_app_iff_of_iso _ eK).1 ?_
  exact Stacks.ComparingTopologies.isIso_derivedPlusAdjunction_unit_app_mapDerivedCategoryPlus
    (Stacks.Torsion.torsionSheafProperty _).ι _
    (fun F ↦ isIso_etaleAugmentation_abelianUnit_app hA F.obj)
    (fun F ↦ (CategoryTheory.rightAcyclic_iff_isZero_rightDerived _ _).2
      (isZero_rightDerived_etaleAugmentation_of_torsion hA F.obj F.property)) K'

/-- **Stacks 0DHM for a big ph site `P`**: the pullback `RΓ(X_étale, K) → RΓ(U_étale, a⁻¹K)` on
derived global sections is invertible for `K` with torsion cohomology sheaves. -/
theorem isIso_lerayPullback_etaleAugmentation_app_of_torsion
    (K : DerivedCategory.Plus
      (Sheaf (SpacesEtale.topology P.fppfSite S P.fppf_mem A.right) AddCommGrpCat.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty _
      ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Plus.ι.obj K))) :
    IsIso ((Stacks.LerayPullbackComparison.lerayPullback
      (abelianInverseImageAdjPushforward (etaleSimplicialSite A).totalTopology
        (etaleAugmentationMorphism A))
      (Sheaf.Γ (SpacesEtale.topology P.fppfSite S P.fppf_mem A.right) AddCommGrpCat.{u + 1})
      (Sheaf.Γ (etaleSimplicialSite A).totalTopology AddCommGrpCat.{u + 1})
      (abelianPushforwardΓIso _ (etaleAugmentationMorphism A))).app K) := by
  have : IsIso ((Stacks.LerayPullbackComparison.derivedUnit
      (abelianInverseImageAdjPushforward (etaleSimplicialSite A).totalTopology
        (etaleAugmentationMorphism A))).app K) := by
    rw [Stacks.LerayPullbackComparison.derivedUnit_eq_derivedPlusAdjunction_unit]
    exact isIso_etaleAugmentation_derivedPlusUnit_of_torsion hA K hK
  exact Stacks.LerayPullbackComparison.isIso_lerayPullback_app _ _ _ _ K

end Derived

end AlgebraicGeometry.BigPHSpaceSite

namespace AlgebraicGeometry.Space

open Stacks.Topos.AbelianPushforward

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

section Derived

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks Project, Tag 0DHL**, for torsion coefficients. Let `S` be a scheme, `X` an algebraic
space over `S`, `U` a simplicial algebraic space over `S` and `a : U → X` an augmentation. If
`a : U → X` is a proper hypercovering of `X`, then for `K ∈ D⁺(X_étale)` with torsion cohomology
sheaves the canonical map

`K → Ra_*(a⁻¹K)`

is an isomorphism, where `a : Sh(U_étale) → Sh(X_étale)` is the morphism of topoi of
Section 0DE7.

Here `X = A.right`, `U = A.left` and `a = A.hom`; `X_étale` is the spaces-étale site of `X`, the
proper hypercovering condition is Section 0DHI (`AlgebraicGeometry.Space.IsProperHypercovering`),
and `D⁺` is the bounded below derived category of abelian sheaves. The map is the unit at `K` of
the adjunction `a⁻¹ ⊣ Ra_*` on `D⁺`, `a⁻¹` being exact and applied degreewise.

The statement of the source is for every `K ∈ D⁺(X_étale)`, and as written it is false: its proof
cites Stacks 0DGU, which holds only for complexes with torsion cohomology sheaves. For a
counterexample with rational coefficients let `X` be a normal surface over an algebraically closed
field with a cusp singularity `x`, let `π : X̃ → X` be a resolution whose exceptional curve `E`
over `x` is a cycle of rational curves, and let `U` be the Čech nerve of the proper surjective
morphism `X̃ ⊔ {x} → X`, a proper hypercovering. Descent `ℚ = Ra_*a⁻¹ℚ` would give, through the
spectral sequence of the hypercovering, `H²(X_étale, ℚ) ≠ 0`, coming from `H¹(E, ℚ) = ℚ`; but
`Hⁱ(X_étale, ℚ) = 0` for `i > 0` because `X` is normal. The torsion hypothesis on `K` is
therefore part of the statement, and this is the corrected form.

The proof is that of the source: a big ph site `(Spaces/S)_ph` on the algebraic spaces over `S`
exists (`AlgebraicGeometry.BigFppfSite.bigPHSpaceSite`), and in it the square of Tag 0DHJ, the
comparison of ph and étale cohomology of torsion sheaves (Stacks 0DGT, Stacks 0DGU), and descent
along the ph hypercovering `U` of `X` (Stacks 0DA8, Stacks 0D8N) give
`Ra_*a⁻¹K = Rh₋₁,* Ra_{ph,*} a_ph⁻¹ h₋₁⁻¹ K = K`; see
`AlgebraicGeometry.BigPHSpaceSite.isIso_etaleAugmentation_derivedPlusUnit_of_torsion`. -/
@[stacks 0DHL]
theorem isIso_etaleAugmentation_derivedPlusUnit_of_isProperHypercovering
    (hA : IsProperHypercovering B S hS A)
    (K : DerivedCategory.Plus (Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty _
      ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Plus.ι.obj K))) :
    IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction
      (abelianInverseImageAdjPushforward (etaleSimplicialSite A).totalTopology
        (etaleAugmentationMorphism A))).unit.app K) :=
  BigPHSpaceSite.isIso_etaleAugmentation_derivedPlusUnit_of_torsion
    (P := B.bigPHSpaceSite S hS) hA K hK

/-- **Stacks Project, Tag 0DHM**, for torsion coefficients. Let `S` be a scheme, `X` an algebraic
space over `S`, `U` a simplicial algebraic space over `S` and `a : U → X` an augmentation. If
`a : U → X` is a proper hypercovering of `X`, then

`RΓ(X_étale, K) = RΓ(U_étale, a⁻¹K)`

for `K ∈ D⁺(X_étale)` with torsion cohomology sheaves, where `a : Sh(U_étale) → Sh(X_étale)` is the
morphism of topoi of Section 0DE7.

The isomorphism is the canonical one: `RΓ(X_étale, -)` of the unit `K → Ra_*a⁻¹K` followed by the
factorisation `RΓ(U_étale, -) = RΓ(X_étale, -) ∘ Ra_*` of Cohomology on Sites, Remark 08J6
(`Stacks.LerayPullbackComparison.lerayPullback`), invertible by
`isIso_etaleAugmentation_derivedPlusUnit_of_isProperHypercovering` (Stacks 0DHL).

As for Stacks 0DHL, the source states this for every `K ∈ D⁺(X_étale)`, and as written it is false:
for the proper hypercovering of a normal surface with a cusp by the Čech nerve of
`X̃ ⊔ {x} → X` described at `isIso_etaleAugmentation_derivedPlusUnit_of_isProperHypercovering`, the
spectral sequence of the hypercovering computes `H²(U_étale, ℚ) ≠ 0` from `H¹(E, ℚ) = ℚ` for the
exceptional curve `E`, while `H²(X_étale, ℚ) = 0` since `X` is normal. The torsion hypothesis on
`K` is the correction. -/
@[stacks 0DHM]
def derivedGlobalSectionsIsoOfIsProperHypercovering (hA : IsProperHypercovering B S hS A)
    (K : DerivedCategory.Plus (Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty _
      ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Plus.ι.obj K))) :
    (Sheaf.Γ (SpacesEtale.topology B S hS A.right)
        AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj
        K ≅
      (Sheaf.Γ (etaleSimplicialSite A).totalTopology
        AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj
        ((CategoryTheory.Sites.abelianInverseImage
          (etaleAugmentationMorphism A)).mapDerivedCategoryPlus.obj
          K) :=
  haveI := BigPHSpaceSite.isIso_lerayPullback_etaleAugmentation_app_of_torsion
    (P := B.bigPHSpaceSite S hS) hA K hK
  asIso ((Stacks.LerayPullbackComparison.lerayPullback
    (abelianInverseImageAdjPushforward (etaleSimplicialSite A).totalTopology
      (etaleAugmentationMorphism A))
    (Sheaf.Γ (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1})
    (Sheaf.Γ (etaleSimplicialSite A).totalTopology AddCommGrpCat.{u + 1})
    (abelianPushforwardΓIso _ (etaleAugmentationMorphism A))).app K)

/-- The isomorphism of Stacks 0DHM is the pullback on derived global sections along `a`. -/
theorem derivedGlobalSectionsIsoOfIsProperHypercovering_hom (hA : IsProperHypercovering B S hS A)
    (K : DerivedCategory.Plus (Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty _
      ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Plus.ι.obj K))) :
    (derivedGlobalSectionsIsoOfIsProperHypercovering hA K hK).hom =
      (Stacks.LerayPullbackComparison.lerayPullback
        (abelianInverseImageAdjPushforward (etaleSimplicialSite A).totalTopology
          (etaleAugmentationMorphism A))
        (Sheaf.Γ (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1})
        (Sheaf.Γ (etaleSimplicialSite A).totalTopology AddCommGrpCat.{u + 1})
        (abelianPushforwardΓIso _ (etaleAugmentationMorphism A))).app K :=
  rfl

end Derived

end AlgebraicGeometry.Space

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- The unit of `a⁻¹ ⊣ Ra_*` on `D⁺`, with `a⁻¹` read as its right derived functor, is invertible
exactly where it is with `a⁻¹` applied degreewise: the two left adjoints are isomorphic. -/
theorem isIso_rightDerivedFunctorPlus_unit_app_iff
    (X : DerivedCategory.Plus (Sheaf K AddCommGrpCat.{u})) :
    haveI : (totalInverseImageAb S D K a).PreservesHomology := Functor.preservesHomologyOfExact _
    IsIso ((abelianTotalAdjunction S D K a).rightDerivedFunctorPlus.unit.app X) ↔
      IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction
        (abelianTotalAdjunction S D K a)).unit.app X) := by
  have : (totalInverseImageAb S D K a).PreservesHomology := Functor.preservesHomologyOfExact _
  exact Adjunction.isIso_unit_app_iff_of_iso _ _ (Iso.refl _) X

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
