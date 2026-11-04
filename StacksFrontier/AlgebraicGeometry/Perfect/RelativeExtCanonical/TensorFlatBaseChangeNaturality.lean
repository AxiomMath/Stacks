module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatOverBase.TensorFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackMonoidalFunctor

/-!
# Naturality of the base-change map of Stacks 0A1D in the first factor

The canonical map

`Lg^*Rf_*(E ⊗^L_{𝒪_X} 𝒢^•) ⟶ Rf'_*(L(g')^*E ⊗^L_{𝒪_{X'}} (g')^*𝒢^•)`

of `AlgebraicGeometry.tensorFlatBaseChangeMap` is natural in `E`. It is the derived base-change
map of [Stacks, Tag 08HY], a natural transformation, at `E ⊗^L 𝒢^•`, followed by `Rf'_*` of the
monoidality isomorphism of [Stacks, Tag 079U], natural in both factors, and of a map in the
second factor only.

## Main results

* `AlgebraicGeometry.tensorFlatBaseChangeMap_naturality`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open Stacks.Cohomology.DerivedBaseChangeComparison (baseChangeTensorComparison)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

namespace AlgebraicGeometry

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

/-- **The base-change map of Stacks 0A1D is natural in the first factor.** For `p : E₁ ⟶ E₂`
the square formed by the base-change maps at `E₁` and `E₂`, `Lg^*Rf_*(p ⊗ 𝒢^•)` and
`Rf'_*(L(g')^*p ⊗ (g')^*𝒢^•)` commutes. -/
theorem tensorFlatBaseChangeMap_naturality {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (f' : X' ⟶ S') (g' : X' ⟶ X)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom) :
    letI := HasDerivedCategory.standard X.Modules
    letI := HasDerivedCategory.standard X'.Modules
    letI := HasDerivedCategory.standard S.Modules
    letI := HasDerivedCategory.standard S'.Modules
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    letI := HasDerivedCategory.standard (Stacks.DerivedTensor.RingedSite.Modules X.sheaf)
    letI := HasDerivedCategory.standard (Stacks.DerivedTensor.RingedSite.Modules X'.sheaf)
    ∀ {E₁ E₂ : DerivedCategory X.Modules} (p : E₁ ⟶ E₂) (G : CochainComplex X.Modules ℤ),
    (derivedPullback g.toLRSHom.toShHom).map ((derivedPushforward f.toLRSHom.toShHom).map
        (((derivedTensorProductFunctor X.sheaf).map p).app (DerivedCategory.Q.obj G))) ≫
      tensorFlatBaseChangeMap f g f' g' sq E₂ G =
    tensorFlatBaseChangeMap f g f' g' sq E₁ G ≫
      (derivedPushforward f'.toLRSHom.toShHom).map
        (((derivedTensorProductFunctor X'.sheaf).map
          ((derivedPullback g'.toLRSHom.toShHom).map p)).app
            (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj G))) := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard X'.Modules
  let := HasDerivedCategory.standard S.Modules
  let := HasDerivedCategory.standard S'.Modules
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
  let := HasDerivedCategory.standard (Stacks.DerivedTensor.RingedSite.Modules X.sheaf)
  let := HasDerivedCategory.standard (Stacks.DerivedTensor.RingedSite.Modules X'.sheaf)
  intro E₁ E₂ p G
  unfold tensorFlatBaseChangeMap
  have hnat := Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_naturality
    g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq
    (((derivedTensorProductFunctor X.sheaf).map p).app (DerivedCategory.Q.obj G))
  have h := Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_hom_app_naturality_left
    g'.toLRSHom.toShHom p (DerivedCategory.Q.obj G)
  have hbtc : (derivedPullback g'.toLRSHom.toShHom).map
      (((derivedTensorProductFunctor X.sheaf).map p).app (DerivedCategory.Q.obj G)) ≫
      baseChangeTensorComparison g'.toLRSHom.toShHom E₂ (DerivedCategory.Q.obj G)
        (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj G))
        ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app G) =
      baseChangeTensorComparison g'.toLRSHom.toShHom E₁ (DerivedCategory.Q.obj G)
        (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj G))
        ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app G) ≫
      ((derivedTensorProductFunctor X'.sheaf).map
          ((derivedPullback g'.toLRSHom.toShHom).map p)).app
        (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj G)) := by
    unfold baseChangeTensorComparison
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) h.symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact congrArg (_ ≫ ·) (((derivedTensorProductFunctor X'.sheaf).map
      ((derivedPullback g'.toLRSHom.toShHom).map p)).naturality _).symm
  calc _ = ((derivedPullback g.toLRSHom.toShHom).map ((derivedPushforward f.toLRSHom.toShHom).map
        (((derivedTensorProductFunctor X.sheaf).map p).app (DerivedCategory.Q.obj G))) ≫
        derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
          g.toLRSHom.toShHom sq _) ≫ _ := (Category.assoc _ _ _).symm
    _ = _ := by
      refine (congrArg (· ≫ _) hnat).trans ?_
      simp only [Category.assoc]
      congr 1
      exact ((derivedPushforward f'.toLRSHom.toShHom).map_comp _ _).symm.trans
        ((congrArg (derivedPushforward f'.toLRSHom.toShHom).map hbtc).trans
          ((derivedPushforward f'.toLRSHom.toShHom).map_comp _ _))

end AlgebraicGeometry
