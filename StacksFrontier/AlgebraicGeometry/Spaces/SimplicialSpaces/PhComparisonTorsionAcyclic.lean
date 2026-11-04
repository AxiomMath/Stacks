module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.PhComparisonSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.ProperHypercovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhToSmallEtaleDerivedTorsion
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhToSmallEtaleInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleSpaceSiteOfFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianInverseImageSquare
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObjectOverAbelianDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionSheavesAndAdjunctions
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftDerived

/-!
# The ph comparison of a simplicial algebraic space on torsion sheaves

Let `a : U → X` be an augmented simplicial algebraic space over a scheme `S`, and consider the
diagram of topoi of Tag 0DHJ
```
Sh((Spaces/U)_{ph, total}) --h--> Sh(U_étale)
        | a_ph                       | a
Sh((Spaces/X)_ph)        --h₋₁--> Sh(X_étale)
```
This file proves the acyclicity statements about the horizontal arrows on which the proof of
Stacks 0DHL rests, for an abelian sheaf `F` on `X_étale` with torsion sections:

* `F → h₋₁,* h₋₁⁻¹ F` is an isomorphism and `h₋₁⁻¹ F` is acyclic for `h₋₁,*` (Stacks 0DGT and
  Stacks 0DGU for `X`), the lower arrow being the comparison morphism `a_X` of Stacks 0DGW;
* `a_ph⁻¹ h₋₁⁻¹ F` is acyclic for `h_*`. In simplicial degree `n` the direct image of `h` is the
  direct image along the comparison of degree `n`, which is that of `U_n` followed by the
  equivalence of the topos of the degree-`n` component of `U_étale` with the spaces-étale topos of
  `U_n`; restriction to a degree is exact on `U_étale` and exact and injective-preserving on
  `(Spaces/U)_{ph, total}` (Stacks 09WH), and the restriction of `a_ph⁻¹ h₋₁⁻¹ F` to degree `n`
  is `h_{U_n}⁻¹ a_n⁻¹ F` by the second diagram of Stacks 0DGW. Its higher direct images along the
  comparison of `U_n` vanish by Stacks 0DGT, part (2), `a_n⁻¹ F` being torsion.

## Main results

* `AlgebraicGeometry.BigPHSpaceSite.isIso_spacesEtaleComparison_abelianUnit` and
  `AlgebraicGeometry.BigPHSpaceSite.isZero_rightDerived_spacesEtaleComparison_of_torsion`: the
  lower arrow `h₋₁`.
* `AlgebraicGeometry.BigPHSpaceSite.spacesEtaleComparisonAbelianInverseImageSquareIso`: the
  second diagram of Stacks 0DGW for `h₋₁`, on abelian sheaves.
* `AlgebraicGeometry.BigPHSpaceSite.isZero_rightDerived_phComparison_of_torsion`: the upper
  arrow `h`.

## Implementation notes

The comparison morphisms `a_X` of Stacks 0DGU are stated for a big ph site `P` and a big étale
site over the same big fppf site of schemes. They are used here with the big étale site
`P.fppfSite.bigEtaleSpaceSite`, whose algebraic spaces are those of `P` on the nose and which is
reducible, so that the direct image of `a_X` is that of the lower arrow `h₋₁` of Tag 0DHJ
definitionally and the comparison is checked quickly.

## References

* [Stacks Project, Tag 0DHJ](https://stacks.math.columbia.edu/tag/0DHJ)
* [Stacks Project, Tag 0DHL](https://stacks.math.columbia.edu/tag/0DHL)
* [Stacks Project, Tag 0DGT](https://stacks.math.columbia.edu/tag/0DGT)
* [Stacks Project, Tag 0DGU](https://stacks.math.columbia.edu/tag/0DGU)
* [Stacks Project, Tag 0DGW](https://stacks.math.columbia.edu/tag/0DGW)
* [Stacks Project, Tag 09WH](https://stacks.math.columbia.edu/tag/09WH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.BigPHSpaceSite
open Stacks.Topos.AbelianPushforward
variable {S : Scheme.{u}} (P : BigPHSpaceSite S) (X : P.Spaces)

/-- The abelian direct image of `h₋₁` is restriction of abelian sheaves along `W ↦ W/X`. -/
def spacesEtaleComparisonAbelianPushforwardIso :
    abelianPushforward (P.topology.over X) (Space.spacesEtaleComparisonMorphism P.topology X) ≅
      (Space.SpacesEtale.inclusion _ S _ X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Space.SpacesEtale.topology _ S _ X) (P.topology.over X) :=
  haveI : ((Space.SpacesEtale.inclusion _ S _ X).sheafPushforwardContinuous (Type (u + 1))
      (Space.SpacesEtale.topology _ S _ X) (P.topology.over X)).IsRightAdjoint :=
    ⟨_, ⟨(Space.spacesEtaleComparisonMorphism P.topology X).adj⟩⟩
  abelianPushforwardIsoSheafPushforwardContinuous (Space.SpacesEtale.inclusion _ S _ X) _ _
    (Space.spacesEtaleComparisonMorphism P.topology X) (Iso.refl _)

/-- The direct image `a_{X,*}` of Stacks 0DGU, for the big étale site over the fppf site of `P`,
is restriction of abelian sheaves along `W ↦ W/X`. -/
def phToSmallEtaleAbelianPushforwardIso :
    phToSmallEtaleAbelianPushforward P (P.fppfSite.bigEtaleSpaceSite S P.fppf_mem) rfl X ≅
      (Space.SpacesEtale.inclusion _ S _ X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Space.SpacesEtale.topology _ S _ X) (P.topology.over X) :=
  Iso.refl _

/-- **Stacks 0DGT, part (1), for `h₋₁`**: the unit `F → h₋₁,* h₋₁⁻¹ F` is an isomorphism for
every abelian sheaf `F` on `X_étale`. -/
theorem isIso_spacesEtaleComparison_abelianUnit
    (F : Sheaf (Space.SpacesEtale.topology P.fppfSite S P.fppf_mem X) AddCommGrpCat.{u + 1}) :
    IsIso ((abelianInverseImageAdjPushforward (P.topology.over X)
      (Space.spacesEtaleComparisonMorphism P.topology X)).unit.app F) := by
  have hu := isIso_phToSmallEtaleAbelianAdjunction_unit P
    (P.fppfSite.bigEtaleSpaceSite S P.fppf_mem) rfl X
  exact (Adjunction.isIso_unit_app_iff_of_iso _
    (phToSmallEtaleAbelianAdjunction P (P.fppfSite.bigEtaleSpaceSite S P.fppf_mem) rfl X)
    (spacesEtaleComparisonAbelianPushforwardIso P X ≪≫
      (phToSmallEtaleAbelianPushforwardIso P X).symm) F).2
    (@NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hu F)

/-- **Stacks 0DGT, part (2), for `h₋₁`**: `Rᵠ h₋₁,* (h₋₁⁻¹ F) = 0` for `q > 0` and a torsion
abelian sheaf `F` on `X_étale`. -/
theorem isZero_rightDerived_spacesEtaleComparison_of_torsion
    (F : Sheaf (Space.SpacesEtale.topology P.fppfSite S P.fppf_mem X) AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty _ F) (q : ℕ) (hq : 0 < q) :
    IsZero (((abelianPushforward (P.topology.over X)
      (Space.spacesEtaleComparisonMorphism P.topology X)).rightDerived q).obj
        ((CategoryTheory.Sites.abelianInverseImage
          (Space.spacesEtaleComparisonMorphism P.topology X)).obj F)) := by
  let := HasDerivedCategory.standard
  let G : Sheaf (P.topology.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Space.SpacesEtale.topology P.fppfSite S P.fppf_mem X) AddCommGrpCat.{u + 1} :=
    (Space.SpacesEtale.inclusion _ S _ X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Space.SpacesEtale.topology _ S _ X) (P.topology.over X)
  let e : abelianPushforward (P.topology.over X)
      (Space.spacesEtaleComparisonMorphism P.topology X) ≅ G :=
    spacesEtaleComparisonAbelianPushforwardIso P X
  have h := (CategoryTheory.rightAcyclic_iff_isZero_rightDerived _ _).1
    (rightAcyclic_phToSmallEtaleAbelianPushforward_of_torsion P
      (P.fppfSite.bigEtaleSpaceSite S P.fppf_mem) rfl X F hF) q hq
  have h' : IsZero ((G.rightDerived q).obj ((CategoryTheory.Sites.abelianInverseImage
      (phToSmallEtaleMorphism P (P.fppfSite.bigEtaleSpaceSite S P.fppf_mem) rfl X)).obj F)) := h
  let i1 := (Functor.rightDerivedIsoOfNatIso e q).app ((CategoryTheory.Sites.abelianInverseImage
    (Space.spacesEtaleComparisonMorphism P.topology X)).obj F)
  let adj' := (phToSmallEtaleAbelianAdjunction P
    (P.fppfSite.bigEtaleSpaceSite S P.fppf_mem) rfl X).ofNatIsoRight
      (phToSmallEtaleAbelianPushforwardIso P X)
  let i2 : (CategoryTheory.Sites.abelianInverseImage
      (Space.spacesEtaleComparisonMorphism P.topology X)).obj F ≅
      (CategoryTheory.Sites.abelianInverseImage
        (phToSmallEtaleMorphism P (P.fppfSite.bigEtaleSpaceSite S P.fppf_mem) rfl X)).obj F :=
    (Adjunction.leftAdjointIsoOfIso (abelianInverseImageAdjPushforward (P.topology.over X)
        (Space.spacesEtaleComparisonMorphism P.topology X)) adj' e).app F
  exact h'.of_iso (i1 ≪≫ (G.rightDerived q).mapIso i2)

end AlgebraicGeometry.BigPHSpaceSite

namespace AlgebraicGeometry.BigPHSpaceSite
open Stacks.Topos.AbelianPushforward Space EtaleComponent
variable {S : Scheme.{u}} (P : BigPHSpaceSite S) (A : SimplicialObject.Augmented P.Spaces)

/-- The direct image of abelian sheaves along the comparison of degree `b`, from `Spaces/U_b` to
the degree-`b` component of `U_étale`: restriction along `V/U_b ↦ V/U_b`. -/
abbrev phComparisonDegreeAb (b : SimplexCategoryᵒᵖ) :
    Sheaf (P.topology.over (A.left.obj b)) AddCommGrpCat.{u + 1} ⥤
      Sheaf (EtaleComponent.precoverage (A := A) b.unop).toGrothendieck AddCommGrpCat.{u + 1} :=
  (EtaleComponent.realizeFunctor (A := A) b.unop ⋙
      SpacesEtale.inclusion _ S _ (A.left.obj b)).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (EtaleComponent.precoverage (A := A) b.unop).toGrothendieck
    (P.topology.over (A.left.obj b))

/-- The higher direct images along the comparison of degree `b` vanish at `h_{U_b}⁻¹ G` for a
torsion abelian sheaf `G` on `U_b`: the comparison of degree `b` is that of `U_b` followed by the
equivalence of topoi of Section 0DE7. -/
theorem isZero_rightDerived_phComparisonDegreeAb (b : SimplexCategoryᵒᵖ)
    (G : Sheaf (SpacesEtale.topology P.fppfSite S P.fppf_mem (A.left.obj b)) AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty _ G) (q : ℕ) (hq : 0 < q) :
    IsZero (((phComparisonDegreeAb P A b).rightDerived q).obj
      ((CategoryTheory.Sites.abelianInverseImage
        (spacesEtaleComparisonMorphism P.topology (A.left.obj b))).obj G)) := by
  let Rincl := (SpacesEtale.inclusion _ S _ (A.left.obj b)).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (SpacesEtale.topology _ S _ (A.left.obj b))
    (P.topology.over (A.left.obj b))
  let Rreal := (EtaleComponent.sheafEquiv (A := A) b.unop AddCommGrpCat.{u + 1}).inverse
  have : Rreal.Additive := Functor.additive_of_preserves_binary_products _
  have : Rreal.PreservesHomology := Functor.preservesHomologyOfExact _
  have : (phComparisonDegreeAb P A b).Additive := Functor.additive_of_preserves_binary_products _
  have e : (phComparisonDegreeAb P A b).rightDerived q ≅ Rincl.rightDerived q ⋙ Rreal :=
    Functor.rightDerivedCompIso Rincl Rreal q
  refine (Rreal.map_isZero ?_).of_iso (e.app _)
  exact (isZero_rightDerived_spacesEtaleComparison_of_torsion P (A.left.obj b) G hG q hq).of_iso
    ((Functor.rightDerivedIsoOfNatIso
      (spacesEtaleComparisonAbelianPushforwardIso P _) q).app _).symm

end AlgebraicGeometry.BigPHSpaceSite

namespace AlgebraicGeometry.BigPHSpaceSite
open Stacks.Topos.AbelianPushforward Space
variable {S : Scheme.{u}} (P : BigPHSpaceSite S)

/-- **The second diagram of Stacks 0DGW for `h₋₁`, on direct images**: for `f : Y ⟶ X`,
`f_{small,*} ∘ h_{Y,*} ≅ h_{X,*} ∘ f_{big,ph,*}`. -/
def spacesEtaleComparisonPushforwardSquareIso {X Y : P.Spaces} (f : Y ⟶ X) :
    (Space.spacesEtaleComparisonMorphism P.topology Y).pushforward ⋙
        (Space.spacesBaseChange_isMorphismOfSites P.fppfSite S P.fppf_mem
          f).morphismOfTopoi.pushforward ≅
      (bigPHMorphism P f).pushforward ⋙
        (Space.spacesEtaleComparisonMorphism P.topology X).pushforward :=
  (eqToIso (by rfl : (Space.spacesEtaleComparisonMorphism P.topology Y).pushforward ⋙
        (Space.spacesBaseChange_isMorphismOfSites P.fppfSite S P.fppf_mem
          f).morphismOfTopoi.pushforward =
      (((P.fppfSite.bigEtaleSpaceSite S P.fppf_mem).smallEtaleMorphism
        (etaleMap P (P.fppfSite.bigEtaleSpaceSite S P.fppf_mem) rfl f)).comp
          (phToSmallEtaleMorphism P (P.fppfSite.bigEtaleSpaceSite S P.fppf_mem) rfl
            Y)).pushforward)).trans
    ((bigPHSmallEtale_pushforwardCommIso P (P.fppfSite.bigEtaleSpaceSite S P.fppf_mem) rfl f).trans
      (eqToIso (by rfl)))

/-- **The second diagram of Stacks 0DGW for `h₋₁`, on inverse images**: the conjugate of
`spacesEtaleComparisonPushforwardSquareIso`. -/
def spacesEtaleComparisonInverseImageSquareIso {X Y : P.Spaces} (f : Y ⟶ X) :
    (spacesEtaleComparisonMorphism P.topology X).inverseImage ⋙ (bigPHMorphism P f).inverseImage ≅
      (spacesBaseChange_isMorphismOfSites P.fppfSite S P.fppf_mem f).morphismOfTopoi.inverseImage ⋙
        (spacesEtaleComparisonMorphism P.topology Y).inverseImage :=
  (conjugateIsoEquiv
    ((spacesBaseChange_isMorphismOfSites P.fppfSite S P.fppf_mem f).morphismOfTopoi.adj.comp
      (spacesEtaleComparisonMorphism P.topology Y).adj)
    ((spacesEtaleComparisonMorphism P.topology X).adj.comp (bigPHMorphism P f).adj)).symm
      (spacesEtaleComparisonPushforwardSquareIso P f)

/-- **The second diagram of Stacks 0DGW for `h₋₁`, on abelian sheaves**: restricting `h_{X}⁻¹ F`
to `Spaces/Y` along `f : Y ⟶ X` is `h_{Y}⁻¹ f_{small}⁻¹ F`. -/
def spacesEtaleComparisonAbelianInverseImageSquareIso {X Y : P.Spaces} (f : Y ⟶ X) :
    CategoryTheory.Sites.abelianInverseImage (spacesEtaleComparisonMorphism P.topology X) ⋙
        (Over.map f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (P.topology.over Y) (P.topology.over X) ≅
      CategoryTheory.Sites.abelianInverseImage
          (spacesBaseChange_isMorphismOfSites P.fppfSite S P.fppf_mem f).morphismOfTopoi ⋙
        CategoryTheory.Sites.abelianInverseImage (spacesEtaleComparisonMorphism P.topology Y) :=
  haveI : ((Over.map f).sheafPushforwardContinuous (Type (u + 1))
      (P.topology.over Y) (P.topology.over X)).IsRightAdjoint :=
    ⟨_, ⟨bigPHMorphismLowerShriekAdjunction P f⟩⟩
  Functor.isoWhiskerLeft _ (CategoryTheory.Sites.abelianInverseImageIsoSheafPushforwardContinuous
      (Over.map f) _ _ (bigPHMorphism P f) (Iso.refl _)).symm ≪≫
    StacksTag03LR.abelianInverseImageSquareIso _ _ _ _
      (spacesEtaleComparisonInverseImageSquareIso P f)

end AlgebraicGeometry.BigPHSpaceSite

namespace AlgebraicGeometry.BigPHSpaceSite
open Stacks.Topos.AbelianPushforward Space
variable {S : Scheme.{u}} (P : BigPHSpaceSite S) (A : SimplicialObject.Augmented P.Spaces)

/-- The inclusion of the simplicial degree `b` into the total category of `U_étale` is
continuous (Stacks 09WG). -/
instance etaleComponentInclusion_isContinuous (b : SimplexCategoryᵒᵖ) :
    (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor b).IsContinuous
      (EtaleComponent.precoverage (A := A) b.unop).toGrothendieck
        (etaleSimplicialSite A).totalTopology :=
  SimplicialSiteSituation.componentFunctor_isContinuous (etaleSituation A) b.unop

/-- The inclusion of the simplicial degree `b` into the total category of `U_étale` is
cocontinuous (Stacks 09WG). -/
instance etaleComponentInclusion_isCocontinuous (b : SimplexCategoryᵒᵖ) :
    (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor b).IsCocontinuous
      (EtaleComponent.precoverage (A := A) b.unop).toGrothendieck
        (etaleSimplicialSite A).totalTopology :=
  SimplicialSiteSituation.componentFunctor_isCocontinuous (etaleSituation A) b.unop

/-- `h_*` on abelian sheaves is restriction along the comparison functor. -/
def phComparisonAbelianPushforwardIso :
    haveI := phComparisonFunctor_isContinuous (A := A) P.topology
    abelianPushforward (SimplicialOver.totalTopology P.topology A.left)
        (phComparisonMorphism A P.topology) ≅
      (phComparisonFunctor A).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (etaleSimplicialSite A).totalTopology (SimplicialOver.totalTopology P.topology A.left) :=
  haveI := phComparisonFunctor_isContinuous (A := A) P.topology
  haveI : ((phComparisonFunctor A).sheafPushforwardContinuous (Type (u + 1))
      (etaleSimplicialSite A).totalTopology
        (SimplicialOver.totalTopology P.topology A.left)).IsRightAdjoint :=
    ⟨_, ⟨(phComparisonMorphism A P.topology).adj⟩⟩
  abelianPushforwardIsoSheafPushforwardContinuous (phComparisonFunctor A) _ _
    (phComparisonMorphism A P.topology) (Iso.refl _)

/-- Restriction of abelian sheaves on `U_étale` to the simplicial degree `b`. -/
abbrev etaleComponentRestrictionAb (b : SimplexCategoryᵒᵖ) :
    Sheaf (etaleSimplicialSite A).totalTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (EtaleComponent.precoverage (A := A) b.unop).toGrothendieck AddCommGrpCat.{u + 1} :=
  (Pseudofunctor.CoGrothendieck.ι
      (etaleSimplicialSite A).totalPseudofunctor b).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (EtaleComponent.precoverage (A := A) b.unop).toGrothendieck
    (etaleSimplicialSite A).totalTopology

/-- Restriction to a simplicial degree of `U_étale` is left exact. -/
instance etaleComponentRestrictionAb_preservesFiniteLimits (b : SimplexCategoryᵒᵖ) :
    PreservesFiniteLimits (etaleComponentRestrictionAb P A b) :=
  Functor.preservesFiniteLimits_sheafPushforwardContinuous _ _ _ AddCommGrpCat.{u + 1}

/-- Restriction to a simplicial degree of `U_étale` is right exact, being a left adjoint. -/
instance etaleComponentRestrictionAb_preservesFiniteColimits (b : SimplexCategoryᵒᵖ) :
    PreservesFiniteColimits (etaleComponentRestrictionAb P A b) :=
  haveI : PreservesColimitsOfSize.{0, 0} (etaleComponentRestrictionAb P A b) :=
    ((Pseudofunctor.CoGrothendieck.ι
      (etaleSimplicialSite A).totalPseudofunctor b).sheafAdjunctionCocontinuous
      AddCommGrpCat.{u + 1} (EtaleComponent.precoverage (A := A) b.unop).toGrothendieck
      (etaleSimplicialSite A).totalTopology).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Restriction to a simplicial degree of `U_étale` is additive. -/
instance etaleComponentRestrictionAb_additive (b : SimplexCategoryᵒᵖ) :
    (etaleComponentRestrictionAb P A b).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Restriction to a simplicial degree of `U_étale` is exact. -/
instance etaleComponentRestrictionAb_preservesHomology (b : SimplexCategoryᵒᵖ) :
    (etaleComponentRestrictionAb P A b).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- The comparison functor in degree `b`, followed by the inclusion of that degree into
`(Spaces/U)_{ph, total}`, is continuous. -/
instance phComparisonFib_isContinuous (b : SimplexCategoryᵒᵖ) :
    (phComparisonFib (A := A) b).IsContinuous
      (EtaleComponent.precoverage (A := A) b.unop).toGrothendieck
      (SimplicialOver.totalTopology P.topology A.left) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ (EtaleComponent.realizeFunctor (A := A) b.unop ⋙
    SpacesEtale.inclusion _ S _ (A.left.obj b)) (Grothendieck.ι (SimplicialOver.slices A.left) b)
    (EtaleComponent.precoverage (A := A) b.unop).toGrothendieck (P.topology.over (A.left.obj b))
    (SimplicialOver.totalTopology P.topology A.left)
    (phComparisonFib_realize_isContinuous (A := A) P.topology b)
    (SimplicialOver.ι_isContinuous A.left P.topology b)

/-- Restricting `h_*` to the simplicial degree `b` is restricting to the degree `b` and then taking
the direct image along the comparison of degree `b`. -/
def phComparisonRestrictionSquareIso (b : SimplexCategoryᵒᵖ) :
    haveI := phComparisonFunctor_isContinuous (A := A) P.topology
    (phComparisonFunctor A).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (etaleSimplicialSite A).totalTopology (SimplicialOver.totalTopology P.topology A.left) ⋙
      etaleComponentRestrictionAb P A b ≅
    SimplicialOver.componentRestrictionAb A.left P.topology b ⋙ phComparisonDegreeAb P A b :=
  haveI := phComparisonFunctor_isContinuous (A := A) P.topology
  Functor.sheafPushforwardContinuousComp' (G := phComparisonFunctor A)
      (Pseudofunctor.CoGrothendieck.ιCompFunctorFrom phComparisonFib (fun f => phComparisonHom f)
        phComparisonHom_id (fun f g => phComparisonHom_comp f g) b :
        Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor b ⋙
          phComparisonFunctor A ≅ phComparisonFib b) AddCommGrpCat.{u + 1}
      (EtaleComponent.precoverage (A := A) b.unop).toGrothendieck
      (etaleSimplicialSite A).totalTopology (SimplicialOver.totalTopology P.topology A.left) ≪≫
    Iso.refl _

/-- In each simplicial degree, `R^q h_*` of `a_ph⁻¹ h₋₁⁻¹ F` vanishes for a torsion `F`. -/
theorem isZero_etaleComponentRestrictionAb_rightDerived_phComparison (b : SimplexCategoryᵒᵖ)
    (F : Sheaf (SpacesEtale.topology P.fppfSite S P.fppf_mem A.right) AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty _ F) (q : ℕ) (hq : 0 < q) :
    haveI := phComparisonFunctor_isContinuous (A := A) P.topology
    IsZero ((etaleComponentRestrictionAb P A b).obj
      ((((phComparisonFunctor A).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (etaleSimplicialSite A).totalTopology
        (SimplicialOver.totalTopology P.topology A.left)).rightDerived q).obj
        ((CategoryTheory.Sites.abelianInverseImage
          (SimplicialOver.augmentationMorphismOfTopoi P.topology A.left A.hom)).obj
            ((CategoryTheory.Sites.abelianInverseImage
              (spacesEtaleComparisonMorphism P.topology A.right)).obj F)))) := by
  have := phComparisonFunctor_isContinuous (A := A) P.topology
  let f : A.left.obj b ⟶ A.right := SimplicialOver.augmentationApp A.left A.hom b
  have hG := Stacks.Torsion.torsionSheafProperty_obj_of_adjunction
    (abelianInverseImageAdjPushforward _
      (spacesBaseChange_isMorphismOfSites P.fppfSite S P.fppf_mem f).morphismOfTopoi) hF
  refine (isZero_rightDerived_phComparisonDegreeAb P A b _ hG q hq).of_iso ?_
  exact ((Functor.rightDerivedIsoOfSquare
      (SimplicialOver.componentRestrictionAb A.left P.topology b)
      _ (phComparisonDegreeAb P A b) (etaleComponentRestrictionAb P A b)
      (phComparisonRestrictionSquareIso P A b) q).app _) ≪≫
    ((phComparisonDegreeAb P A b).rightDerived q).mapIso
      ((SimplicialOver.augmentationAbelianInverseImageCompRestrictionIso A.left A.hom
          P.topology b).app _ ≪≫
        (spacesEtaleComparisonAbelianInverseImageSquareIso P f).app F)

/-- **`a_ph⁻¹ h₋₁⁻¹ F` is acyclic for `h_*`** when `F` is torsion. -/
theorem isZero_rightDerived_phComparison_of_torsion
    (F : Sheaf (SpacesEtale.topology P.fppfSite S P.fppf_mem A.right) AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty _ F) (q : ℕ) (hq : 0 < q) :
    IsZero (((abelianPushforward (SimplicialOver.totalTopology P.topology A.left)
      (phComparisonMorphism A P.topology)).rightDerived q).obj
        ((CategoryTheory.Sites.abelianInverseImage
          (SimplicialOver.augmentationMorphismOfTopoi P.topology A.left A.hom)).obj
            ((CategoryTheory.Sites.abelianInverseImage
              (spacesEtaleComparisonMorphism P.topology A.right)).obj F))) := by
  have := phComparisonFunctor_isContinuous (A := A) P.topology
  refine IsZero.of_iso ?_ ((Functor.rightDerivedIsoOfNatIso
    (phComparisonAbelianPushforwardIso P A) q).app _)
  refine IsZero.of_full_of_faithful_of_isZero
    (sheafToPresheaf (etaleSimplicialSite A).totalTopology AddCommGrpCat.{u + 1}) _
    (Functor.isZero _ fun x => ?_)
  exact (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op x.unop.fiber)).map_isZero
    (isZero_etaleComponentRestrictionAb_rightDerived_phComparison P A x.unop.base F hF q hq)

end AlgebraicGeometry.BigPHSpaceSite

end
