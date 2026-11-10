module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoidSquare
public import StacksFrontier.CategoryTheory.Sites.Descent.CoreDescentData
public import StacksFrontier.CategoryTheory.Sites.Descent.CoGrothendieckIsStack
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackCriterion

/-!
# The groupoid pseudofunctor of Stacks Tag 0EXE as the fibrewise core of the vector bundles

The category fibred in groupoids of Stacks Tag 0EXE is the Grothendieck construction of
`AlgebraicGeometry.frobeniusVectorBundleGroupoidPseudofunctor`, the fibrewise maximal subgroupoid
of `AlgebraicGeometry.frobeniusVectorBundlePseudofunctor`.  Descent statements are naturally
proved for the second (categories of finite locally free modules, where the comparison functors
of Stacks Tags 0EXB and 0EXE live) and consumed for the first.  This file supplies the crossing.

## Main definitions

* `AlgebraicGeometry.frobeniusVectorBundleGroupoidInclusionTrans`: **the fibrewise inclusion of
  the groupoid pseudofunctor into the pseudofunctor of finite locally free modules**, as a strong
  transformation; its components are `AlgebraicGeometry.frobeniusVectorBundleGroupoidInclusion`.

## Main results

* `AlgebraicGeometry.isStackFor_frobeniusVectorBundleGroupoidPseudofunctor_of_isStackFor`: a
  presieve along which the pseudofunctor of finite locally free modules is a stack is one along
  which the groupoid pseudofunctor is.
* `isAffineFlatProperFinitePresentationDescent_frobeniusVectorBundleGroupoidFibration_of`:
  **condition (2) of Stacks 0EX9 for the structure functor of Stacks Tag 0EXE, from effective
  descent of finite locally free Frobenius-colimit modules along the morphisms it ranges over.**

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pseudofunctor Opposite
open Stacks.Frobenius

namespace AlgebraicGeometry

universe u

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

include hpS

/-- The inclusion of a fibre of the groupoid pseudofunctor of Stacks Tag 0EXE into the
corresponding fibre of the pseudofunctor of finite locally free modules: the identity on objects,
an isomorphism of the maximal subgroupoid going to its underlying morphism. -/
def frobeniusVectorBundleGroupoidFiberInclusion (a : LocallyDiscrete (BigHOver B S hS)ᵒᵖ) :
    (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).obj a ⥤
      (frobeniusVectorBundlePseudofunctor B S hS p hpS).obj a where
  obj M := ⟨M.obj.of, M.property⟩
  map g := ObjectProperty.homMk g.hom.iso.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inclusion of a fibre of the groupoid pseudofunctor presents it as the maximal subgroupoid
of the fibre of the pseudofunctor of finite locally free modules. -/
theorem isCoreInclusion_frobeniusVectorBundleGroupoidFiberInclusion
    (a : LocallyDiscrete (BigHOver B S hS)ᵒᵖ) :
    (frobeniusVectorBundleGroupoidFiberInclusion B S hS p hpS a).IsCoreInclusion where
  faithful := ⟨fun h => ObjectProperty.hom_ext _ (Core.hom_ext (congrArg (·.hom) h))⟩
  isIso_map g :=
    ⟨ObjectProperty.homMk g.hom.iso.inv,
      ObjectProperty.hom_ext _ g.hom.iso.hom_inv_id,
      ObjectProperty.hom_ext _ g.hom.iso.inv_hom_id⟩
  exists_map_eq e :=
    ⟨ObjectProperty.homMk (Core.isoMk ((CategoryTheory.ObjectProperty.ι _).mapIso e)).hom, rfl⟩
  essSurj := ⟨fun N => ⟨⟨⟨N.obj⟩, N.property⟩, ⟨Iso.refl _⟩⟩⟩

/-- **The fibrewise inclusion of the groupoid pseudofunctor of Stacks Tag 0EXE into the
pseudofunctor of finite locally free Frobenius-colimit modules**, as a strong transformation.
Its components are the inclusions of the maximal subgroupoids, and its naturality isomorphisms
are identities, the transition functors of the groupoid pseudofunctor being the cores of those of
the modules. -/
def frobeniusVectorBundleGroupoidInclusionTrans :
    (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).StrongTrans
      (frobeniusVectorBundlePseudofunctor B S hS p hpS) :=
  catStrongTransOfIsLocallyDiscrete _ _
    (frobeniusVectorBundleGroupoidFiberInclusion B S hS p hpS)
    (fun {_ _} _ => NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))
    (fun _ _ => ObjectProperty.hom_ext _ (Category.id_comp _))
    (fun {a _ _} f g X => by
      have h1 : (((frobeniusVectorBundlePseudofunctor B S hS p hpS).mapComp f g).hom.toNatTrans.app
          ((frobeniusVectorBundleGroupoidFiberInclusion B S hS p hpS a).obj X)).hom =
          ((frobeniusColimitModulePseudofunctor B S hS p hpS).mapComp f g).hom.toNatTrans.app
            X.obj.of := by
        simp only [frobeniusVectorBundlePseudofunctor,
          Pseudofunctor.ObjectProperty.fullsubcategory_mapComp, Cat.Hom.isoMk_hom]
        rfl
      have h2 : (((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).mapComp f
          g).hom.toNatTrans.app X).hom.iso.hom =
          ((frobeniusColimitModulePseudofunctor B S hS p hpS).mapComp f g).hom.toNatTrans.app
            X.obj.of := by
        rw [← Pseudofunctor.mapComp'_eq_mapComp,
          frobeniusVectorBundleGroupoidPseudofunctor_mapComp'_hom_app_hom,
          frobeniusColimitModuleCorePseudofunctor_mapComp'_hom_app_iso_hom,
          Pseudofunctor.mapComp'_eq_mapComp]
      have h3 := ((frobeniusVectorBundlePseudofunctor B S hS p hpS).map g).toFunctor.map_id
        (((frobeniusVectorBundlePseudofunctor B S hS p hpS).map f).toFunctor.obj
          ((frobeniusVectorBundleGroupoidFiberInclusion B S hS p hpS a).obj X))
      refine (Category.id_comp _).trans ?_
      refine Eq.trans ?_ (congrArg (fun t => _ ≫ _ ≫ t) h3).symm
      refine Eq.trans ?_ (congrArg (fun t => _ ≫ t) (Category.id_comp _)).symm
      refine Eq.trans ?_ (Category.comp_id _).symm
      exact ObjectProperty.hom_ext _ (h1.trans h2.symm))

/-- Each component of `AlgebraicGeometry.frobeniusVectorBundleGroupoidInclusionTrans` presents
the fibre of the groupoid pseudofunctor as the maximal subgroupoid of the category of finite
locally free modules. -/
lemma isCoreInclusion_frobeniusVectorBundleGroupoidInclusionTrans_app
    (a : LocallyDiscrete (BigHOver B S hS)ᵒᵖ) :
    ((frobeniusVectorBundleGroupoidInclusionTrans B S hS p hpS).app a).toFunctor.IsCoreInclusion :=
  isCoreInclusion_frobeniusVectorBundleGroupoidFiberInclusion B S hS p hpS a

/-- **The groupoid pseudofunctor of Stacks Tag 0EXE is a stack along every presieve along which
the pseudofunctor of finite locally free Frobenius-colimit modules is one.** -/
theorem isStackFor_frobeniusVectorBundleGroupoidPseudofunctor_of_isStackFor
    {U : BigHOver B S hS} (R : Presieve U)
    (h : (frobeniusVectorBundlePseudofunctor B S hS p hpS).IsStackFor R) :
    (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).IsStackFor R :=
  (frobeniusVectorBundleGroupoidInclusionTrans B S hS p hpS).isStackFor_of_isCoreInclusion
    (isCoreInclusion_frobeniusVectorBundleGroupoidInclusionTrans_app B S hS p hpS) R h

/-- **Condition (2) of Stacks 0EX9 for the structure functor of Stacks Tag 0EXE**, from effective
descent of finite locally free Frobenius-colimit modules along every surjective flat proper
morphism of finite presentation onto an affine object of `(Sch/S)_h`. -/
theorem isAffineFlatProperFinitePresentationDescent_frobeniusVectorBundleGroupoidFibration_of
    (h : ∀ {X Y : BigHOver B S hS} (f : X ⟶ Y),
      IsAffine ((BigHOver.toScheme B S hS).obj Y) →
      Flat ((BigHOver.toScheme B S hS).map f) →
      IsProper ((BigHOver.toScheme B S hS).map f) →
      Surjective ((BigHOver.toScheme B S hS).map f) →
      FinitePresentation ((BigHOver.toScheme B S hS).map f) →
      (frobeniusVectorBundlePseudofunctor B S hS p hpS).IsStackFor (Presieve.singleton f)) :
    BigHOver.IsAffineFlatProperFinitePresentationDescent B S hS
      (frobeniusVectorBundleGroupoidFibration B S hS p hpS) := by
  intro Y X f hY hfl hpr hsu hfp
  rw [← Pseudofunctor.isStackFor_ofArrows_iff, Presieve.ofArrows_pUnit]
  exact (CoGrothendieck.isStackFor_forget_iff.{u, u + 1, u, u + 1}
    (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS) (Presieve.singleton f)).2
    (isStackFor_frobeniusVectorBundleGroupoidPseudofunctor_of_isStackFor B S hS p hpS _
      (h f hY hfl hpr hsu hfp))

end AlgebraicGeometry

end
