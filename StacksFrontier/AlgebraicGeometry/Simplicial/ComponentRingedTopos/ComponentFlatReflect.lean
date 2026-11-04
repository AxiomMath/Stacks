module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackFlatInverseImage
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackJointEpiReflect
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentConservative
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSheafify
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransition

/-!
# Flatness of a sheaf of modules on a total simplicial site is componentwise

Let `S` be a simplicial-site situation, `O` a sheaf of commutative rings on its total site and
`M` a sheaf of `O`-modules. If the inverse image of `M` along the component morphism of topoi
`g_n` is flat over `g_n^{-1}O` for every simplicial degree `n`, then `M` is flat over `O`.

This is the converse of Stacks 05VD at the component morphisms, and the content of the converse
half of Stacks 0DH3.

## The argument

Flatness is the local equational criterion of Stacks 08FC part (2): every relation among `n`
sections of `M` locally factors through a finite free module. Read as a morphism of sheaves of
sets out of the coproduct over the ranks
(`Stacks.Sheaves.RelationSheaf.epi_sigmaDesc_factorizationToRelation_of_isLocallySurjective`),
the criterion is epimorphy, and epimorphy transfers in both directions:

* downwards, along `Stacks.Sheaves.ToposPullback.epi_map_sigmaDesc_factorizationToRelation`,
  because the relation sheaf and each rank's factorization sheaf are finite limits and `g_n^{-1}`
  is exact;
* and from the family of components back to the total site, because the component restrictions
  jointly reflect epimorphisms
  (`CategoryTheory.SimplicialSiteSituation.epi_iff_forall_epi_restrict`) — the component
  inclusion is continuous, hence cover-preserving, so a covering of a component is a covering of
  the total site.

## Main results

* `CategoryTheory.SimplicialSiteSituation.isFlat_of_forall_isFlat_componentPullbackModule`:
  **a sheaf of modules on the total site whose inverse image on every component is flat is
  flat.**

## Implementation notes

The two sheafification facts on each site — sheafifiability of abelian presheaves and the
identification of the sheafification equivalences with the local bijections — are needed to state
flatness at all, and are supplied here as local instances, as they are in
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleLowerShriek.lean`; the total
category and each component are small at the site universe, so both hold.

The transport of epimorphy between the inverse image along the component morphism of topoi and
restriction to the component is the comparison of Stacks 00XR (1), as in
`CategoryTheory.SimplicialSiteSituation.mono_iff_forall_mono_componentMorphism_inverseImage`.

## References

* [Stacks Project, Tag 0DH3](https://stacks.math.columbia.edu/tag/0DH3)
* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.RelationSheaf Stacks.Sheaves.ToposPullback

universe u

namespace CategoryTheory.SimplicialSiteSituation

/-- Abelian presheaves on the total site are sheafifiable at the site universe. -/
local instance hasWeakSheafifyTotalSite (S : SimplicialSiteSituation.{u}) :
    HasWeakSheafify S.totalTopology AddCommGrpCat.{u} :=
  (GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} S.totalTopology).1

/-- Abelian presheaves on a component are sheafifiable at the site universe. -/
local instance hasWeakSheafifyComponentSite (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) : HasWeakSheafify (S.componentTopology n) AddCommGrpCat.{u} :=
  (GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} (S.componentTopology n)).1

/-- On the total site the maps inverted by sheafification of abelian presheaves are the locally
bijective ones. -/
local instance wEqualsLocallyBijectiveTotalSite (S : SimplicialSiteSituation.{u}) :
    S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u, u, u}
    S.totalTopology

/-- On a component the maps inverted by sheafification of abelian presheaves are the locally
bijective ones. -/
local instance wEqualsLocallyBijectiveComponentSite (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) :
    (S.componentTopology n).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u, u, u}
    (S.componentTopology n)

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The sheaf of rings underlying a sheaf of commutative rings on the total site. -/
noncomputable abbrev totalRingSheafOf : Sheaf S.totalTopology RingCat.{u} :=
  _root_.Stacks.commRingSheafToRingSheaf.{u, u, u} O

/-- The inverse image of the structure sheaf along the component morphism of topoi of
Stacks 09WG. -/
noncomputable def componentPullbackCommRing (n : SimplexCategory) :
    Sheaf (S.componentTopology n) CommRingCat.{u} :=
  pullbackCommRingSheaf.{u, u, u, u, u, u} (S.componentTopology n)
    ((componentMorphism S n).inverseImage) O

/-- The inverse image of a sheaf of `O`-modules along the component morphism of topoi, over the
inverse image of the structure sheaf. -/
noncomputable def componentPullbackModule (n : SimplexCategory)
    (M : SheafOfModules.{u} (totalRingSheafOf S O)) :
    SheafOfModules.{u} (_root_.Stacks.commRingSheafToRingSheaf.{u, u, u}
      (componentPullbackCommRing S O n)) :=
  pullbackModuleObj.{u, u, u, u, u, u} (S.componentTopology n)
    ((componentMorphism S n).inverseImage)
    (totalRingSheafOf S O) M

/-- The inverse image of a sheaf of `O`-modules along the component morphism of topoi, over the
inverse image of the structure sheaf. -/
noncomputable def componentPullbackModule' (n : SimplexCategory)
    (M : SheafOfModules.{u} (totalRingSheaf S O)) :
    SheafOfModules.{u} (_root_.Stacks.commRingSheafToRingSheaf.{u, u, u}
      (componentPullbackCommRing S O n)) :=
  pullbackModuleObj.{u, u, u, u, u, u} (S.componentTopology n)
    ((componentMorphism S n).inverseImage)
    (totalRingSheaf S O) M

/-- **A sheaf of modules on the total site whose inverse image on every simplicial component is
flat is flat.** The converse of Stacks 05VD at the component morphisms of topoi, and the module
form of the converse half of Stacks 0DH3. -/
theorem isFlat_of_forall_isFlat_componentPullbackModule
    (M : SheafOfModules.{u} (totalRingSheafOf S O))
    (h : ∀ n : SimplexCategory, Stacks.SheafOfModules.IsFlat.{u, u, u, u}
      (O := componentPullbackCommRing S O n) (componentPullbackModule S O n M)) :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := O) M := by
  have htotal := hasColimitsOfShape_discreteNat.{u, u} (J := S.totalTopology)
  refine (Stacks.SheafOfModules.isFlat_iff_isLocallySurjective_relationOfFactorization.{u, u, u}
    O M).2 fun k => ?_
  refine isLocallySurjective_relationOfFactorization_of_epi.{u, u} O M k ?_
  rw [epi_iff_forall_epi_restrict]
  intro n
  have hcomp := hasColimitsOfShape_discreteNat.{u, u} (J := S.componentTopology n)
  have hadj : ((componentMorphism S n).inverseImage).IsLeftAdjoint :=
    ⟨_, ⟨(componentMorphism S n).adj⟩⟩
  have hepi : ((componentMorphism S n).inverseImage).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_isLeftAdjoint _
  have hlim : PreservesFiniteLimits ((componentMorphism S n).inverseImage) :=
    (componentMorphism S n).preservesFiniteLimits
  have hdown : Presheaf.IsLocallySurjective (S.componentTopology n)
      (Stacks.SheafOfModules.relationOfFactorization (componentPullbackCommRing S O n)
        (componentPullbackModule S O n M) k) :=
    (Stacks.SheafOfModules.isFlat_iff_isLocallySurjective_relationOfFactorization.{u, u, u}
      _ _).1 (h n) k
  have hepipull := epi_sigmaDesc_factorizationToRelation_of_isLocallySurjective.{u, u}
    (componentPullbackCommRing S O n) (componentPullbackModule S O n M) k hdown
  have hmap := epi_map_sigmaDesc_factorizationToRelation.{u, u, u, u, u, u}
    (S.componentTopology n)
    ((componentMorphism S n).inverseImage) (totalRingSheafOf S O) M k
    (Stacks.Sheaves.ToposPullback.commRingSheaf_mul_comm O) hepipull
  have e := componentMorphismInverseImageIsoRestrict S n
  have key : (S.restrict.{u, u} n).map (Sigma.desc (fun l : ℕ =>
        factorizationToRelation (totalRingSheafOf S O) M k l
          (Stacks.Sheaves.ToposPullback.commRingSheaf_mul_comm O))) =
      e.inv.app _ ≫ ((componentMorphism S n).inverseImage).map (Sigma.desc (fun l : ℕ =>
        factorizationToRelation (totalRingSheafOf S O) M k l
          (Stacks.Sheaves.ToposPullback.commRingSheaf_mul_comm O))) ≫ e.hom.app _ := by
    rw [e.hom.naturality, ← Category.assoc, e.inv_hom_id_app, Category.id_comp]
  rw [key]
  have := hmap
  infer_instance

/-- **A sheaf of modules on the total site whose inverse image on every simplicial component is
flat is flat.** The converse of Stacks 05VD at the component morphisms of topoi, and the module
form of the converse half of Stacks 0DH3. -/
theorem isFlat_of_forall_isFlat_componentPullbackModule'
    (M : SheafOfModules.{u} (totalRingSheaf S O))
    (h : ∀ n : SimplexCategory, Stacks.SheafOfModules.IsFlat.{u, u, u, u}
      (O := componentPullbackCommRing S O n) (componentPullbackModule' S O n M)) :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := O) M :=
  isFlat_of_forall_isFlat_componentPullbackModule S O M h

end CategoryTheory.SimplicialSiteSituation

end
