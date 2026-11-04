module

public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackDerivedModuleLowerShriekCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFreeModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFppfWeakSerreAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeWeakSerreEtaleModules
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakSerreClassOfAbelian

/-!
# Stacks 07B3 over an affine scheme, for the faithful `LQCoh^fbc`

For an affine scheme `U` and a module `H` with a global presentation on the flat-fppf
(resp. lisse-étale) site of `(Sch/U)_{fppf}`, every cohomology sheaf `H^p(Lg_! H)` lies in
`LQCoh^fbc(𝒪)`, the flat base change property of Stacks 0762 being read with the pullback of
sheaves of Stacks 06WC. This is the affine step of Stacks 07B3 for the class of the source: it is
`AlgebraicGeometry.Stack.FlatFppf.prop_homology_derivedModuleLowerShriek_schemeStack` (resp. its
lisse-étale twin) at that class, which is a weak Serre subcategory (Stacks 0771 (2)) containing
the free modules (Stacks 0771 (5) applied to the structure sheaf).

## Main results

In the namespace `AlgebraicGeometry.Stack`:

* `isLocallyQuasicoherentWithSheafFlatBaseChange_of_isFree`: a free module on the étale site of a
  category fibred in groupoids lies in `LQCoh^fbc(𝒪)`.
* `FlatFppf.locallyQuasicoherentSheafFlatBaseChange_homology_schemeStack`: Stacks 07B3 (2) over an
  affine scheme, for a globally presented module.
* `LisseEtale.locallyQuasicoherentSheafFlatBaseChange_homology_schemeStack`: Stacks 07B3 (1) over
  an affine scheme, for a globally presented module.

## References

* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Stack

section Free

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) {𝒳 : Type v} [Category.{w} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- A property of sheaves of modules containing `𝒪` and closed under coproducts holds for free
modules. -/
private theorem prop_of_isFree {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (P : ObjectProperty (SheafOfModules.{u} R))
    (hP : ∀ I : Type u, P.IsClosedUnderColimitsOfShape (Discrete I))
    (hunit : P (SheafOfModules.unit R)) {F : SheafOfModules.{u} R} (hF : F.IsFree) : P F := by
  obtain ⟨I, ι, ⟨hc⟩⟩ := hF
  exact ObjectProperty.prop_of_isColimit P hc fun _ => hunit

/-- **A free module on the étale site lies in `LQCoh^fbc(𝒪)`**: it is a coproduct of copies of
the structure sheaf, which lies in it, and `LQCoh^fbc(𝒪)` is closed under coproducts
(Stacks 0771 (5)). -/
theorem isLocallyQuasicoherentWithSheafFlatBaseChange_of_isFree
    {F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))} (hF : F.IsFree) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, u} B E h S hS p hp F.val :=
  prop_of_isFree (fun F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp
    (etaleTopology B) (etaleTopology_le_topology B)) =>
      IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, u} B E h S hS p hp F.val)
    (fun I => isClosedUnderColimitsOfShape_locallyQuasicoherentSheafFlatBaseChange B E h S hS p hp
      (Discrete I))
    (isLocallyQuasicoherentWithSheafFlatBaseChange_unit B E h S hS p hp) hF

/-- **A free module on the fppf site lies in `LQCoh^fbc(𝒪)`.** -/
theorem locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules_of_isFree
    [HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
    [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F : fppfSiteModules B S hS p hp} (hF : F.IsFree) :
    locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules B E h S hS p hp F :=
  prop_of_isFree _
    (fun I => isClosedUnderColimitsOfShape_locallyQuasicoherentSheafFlatBaseChangeFppf B E h S hS p
      hp (Discrete I))
    (locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules_unit B E h S hS p hp) hF

end Free

namespace FlatFppf

open Stacks.Cohomology.DerivedLowerShriek

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- **Stacks 07B3 (2) over an affine scheme, for a globally presented module.** For `U` affine
and `H` a module with a global presentation on the flat-fppf site of `(Sch/U)_{fppf}`, every
`H^p(Lg_! H)` lies in `LQCoh^fbc(𝒪)`, read with the pullback of sheaves of Stacks 06WC. -/
theorem locallyQuasicoherentSheafFlatBaseChange_homology_schemeStack
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (H : flatFppfModules B S hS (schemeStack.{u, w} B S hS U))
    (hH : H.IsPresentedByGlobalSections) (p : ℤ) :
    letI := AlgebraicGeometry.Stack.abelianFppfModules B S hS (schemeStack.{u, w} B S hS U)
    letI := abelianFlatFppfModulesSpelling B S hS (schemeStack.{u, w} B S hS U)
    letI := HasDerivedCategory.standard (flatFppfModules B S hS (schemeStack.{u, w} B S hS U))
    letI := HasDerivedCategory.standard (fppfModules B S hS (schemeStack.{u, w} B S hS U))
    lqcohSheafFbcFppfModules.{u, _, u} B E h S hS (schemeStack.{u, w} B S hS U)
      ((DerivedCategory.homologyFunctor _ p).obj
        ((derivedModuleLowerShriek B S hS (schemeStack.{u, w} B S hS U)).obj
          ((DerivedCategory.singleFunctor _ 0).obj H))) := by
  let := hasSheafify_associatedTopology_algebraicStack B S hS (schemeStack.{u, w} B S hS U)
    .fppf
  let := wEqualsLocallyBijective_associatedTopology_algebraicStack B S hS
    (schemeStack.{u, w} B S hS U) .fppf
  have := ObjectProperty.isWeakSerreClass_of_abelian _
    (AlgebraicGeometry.Stack.abelianFppfModules B S hS (schemeStack.{u, w} B S hS U)) _
    (isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppfModules B E h S hS
      (schemeStack.{u, w} B S hS U))
  exact prop_homology_derivedModuleLowerShriek_schemeStack B S hS U hU _
    (fun F hF => locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules_of_isFree B E h S hS
      _ _ hF) H hH p

end FlatFppf

namespace LisseEtale

open Stacks.Cohomology.DerivedLowerShriek

attribute [local instance] isContinuous_inclusion_schemeStack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- **Stacks 07B3 (1) over an affine scheme, for a globally presented module.** For `U` affine
and `H` a module with a global presentation on the lisse-étale site of `(Sch/U)_{fppf}`, every
`H^p(Lg_! H)` lies in `LQCoh^fbc(𝒪) ⊆ Mod((Sch/U)_étale, 𝒪)`, read with the pullback of sheaves
of Stacks 06WC. -/
theorem locallyQuasicoherentSheafFlatBaseChange_homology_schemeStack
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (H : SheafOfModules.{u} (inverseImageRing (subsiteTopology B S hS
      (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B)
      (smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U)))
      (associatedTopology B S hS (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U)).ι
      (SmallModel.targetRing (associatedTopology B S hS
        (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS (schemeStack.{u, w} B S hS U).val.val.p
          (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)))
    (hH : H.IsPresentedByGlobalSections) (p : ℤ) :
    letI := abelianEtaleModules B S hS (schemeStack.{u, w} B S hS U)
    letI := abelianLisseEtaleModules B S hS (schemeStack.{u, w} B S hS U)
    letI := HasDerivedCategory.standard (SheafOfModules.{u}
      (inverseImageRing (subsiteTopology B S hS
      (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B)
      (smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U)))
      (associatedTopology B S hS (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U)).ι
      (SmallModel.targetRing (associatedTopology B S hS
        (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS (schemeStack.{u, w} B S hS U).val.val.p
          (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)))
    letI := HasDerivedCategory.standard (SheafOfModules.{u}
      (SmallModel.targetRing (associatedTopology B S hS
        (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS (schemeStack.{u, w} B S hS U).val.val.p
          (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O))
    IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u} B E h S hS
      (schemeStack.{u, w} B S hS U).val.val.p (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids
      ((DerivedCategory.homologyFunctor _ p).obj
        ((derivedModuleLowerShriek B S hS (schemeStack.{u, w} B S hS U)).obj
          ((DerivedCategory.singleFunctor _ 0).obj H))).val := by
  let := hasSheafify_etaleAssociatedTopology B S hS (schemeStack.{u, w} B S hS U).val.val.p
    (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids
  let := wEqualsLocallyBijective_etaleAssociatedTopology B S hS
    (schemeStack.{u, w} B S hS U).val.val.p (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids
  exact @prop_homology_derivedModuleLowerShriek_schemeStack B S hS U hU _
    (ObjectProperty.isWeakSerreClass_of_abelian _
      (abelianEtaleModules B S hS (schemeStack.{u, w} B S hS U)) _
      (isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChange B E h S hS
        (schemeStack.{u, w} B S hS U).val.val.p
        (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids))
    (fun F hF => isLocallyQuasicoherentWithSheafFlatBaseChange_of_isFree B E h S hS _ _ hF) H hH p

end LisseEtale

end AlgebraicGeometry.Stack
