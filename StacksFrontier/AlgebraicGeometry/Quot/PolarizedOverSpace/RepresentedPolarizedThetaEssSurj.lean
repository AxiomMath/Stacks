module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.RepresentedPolarizedThetaFull
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.CategoryTheory.FiberedCategory.EquivalenceOfFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional

/-!
# Every polarized family is vertically isomorphic to one in the image of `Θ`

Let `(X ⟶ S, L)` be a polarized family of Stacks 0D1M. Read over `Spec(ℤ)`, its structure
morphism is an arrow of the big fppf site, and the associated module `L^a` of `L` on the small
étale site of `X` (Stacks 03DU (4)), read on the small étale site of the representable algebraic
space `yoneda X`, is a quasi-coherent module there (Stacks 03DV (2)) whose restriction to the
Zariski site is `L` again (the unit of the associated-module adjunction is an isomorphism at a
quasi-coherent module, Stacks 0GN7). An invertible module is quasi-coherent, invertibility and
relative ampleness only depend on the isomorphism class of a module, so this is an object of
`AlgebraicGeometry.PolarizedOverSpace.RepresentedPolarized` whose image under
`Θ = AlgebraicGeometry.PolarizedOverSpace.toPolarized` is isomorphic to `(X ⟶ S, L)` by an
isomorphism over the identity of `S`.

Together with full faithfulness of `Θ` this makes postcomposition with `Θ` an equivalence of the
categories of functors over the site from any category over the site.

## Main definitions

* `AlgebraicGeometry.PolarizedOverSpace.representedOfPolarized`: the object over a polarized
  family.
* `AlgebraicGeometry.PolarizedOverSpace.toPolarizedRepresentedOfPolarizedIso`: the isomorphism
  `Θ(x P) ≅ P`.

## Main results

* `AlgebraicGeometry.PolarizedOverSpace.isEquivalence_postcompFunctor_toPolarizedBased`:
  postcomposition with `Θ` is an equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.Functor.IsFiberedInGroupoids

/-- **In a category fibred in groupoids a morphism over an isomorphism is an isomorphism.** -/
theorem isIso_of_isIso_map {𝒮 𝒞 : Type*} [Category 𝒮] [Category 𝒞] {p : 𝒮 ⥤ 𝒞}
    (hp : p.IsFiberedInGroupoids) {y x : 𝒮} (φ : y ⟶ x) (hφ : IsIso (p.map φ)) : IsIso φ := by
  obtain ⟨χ, ⟨hχ, hχφ⟩, -⟩ := hp.unique_lift φ (𝟙 x) (CategoryTheory.inv (p.map φ)) (by simp)
  refine ⟨χ, ?_, hχφ⟩
  exact (hp.unique_lift φ φ (𝟙 _) (by simp)).unique (y₁ := φ ≫ χ) (y₂ := 𝟙 y)
    ⟨by simp [hχ], by simp [hχφ]⟩ ⟨by simp, by simp⟩

end CategoryTheory.Functor.IsFiberedInGroupoids

namespace AlgebraicGeometry.PolarizedOverSpace

attribute [local irreducible] Space.modulePullback Space.modulePullbackCompIso
        Scheme.Modules.pullback
  Space.representedSmallEtaleModuleEquivalence SmallEtale.restrictModule

variable {B : BigFppfSite.{u}} (P : PolarizedFamily B)

/-- The structure morphism of a polarized family, as an arrow of the site over `Spec(ℤ)`. -/
abbrev polarizedArrow : Arrow (Site B) := Arrow.mk P.structureMapOverIntegers

/-- The associated module of the polarization on the small étale site of the total space. -/
abbrev polarizedEtaleModule :
    SheafOfModules.{u} (Space.representedSchemeStructureSheaf B integerBase (hZ B)
      (polarizedArrow P).left) :=
  (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B integerBase (hZ B)).obj (polarizedArrow P).left)
    (polarizedArrow P).left.left.property).obj P.lineBundle

/-- The polarization is quasi-coherent, being invertible. -/
theorem isQuasicoherent_lineBundle :
    SheafOfModules.IsQuasicoherent (R := P.total.ringCatSheaf) P.lineBundle :=
  Stacks.Picard.isQuasicoherent_of_isInvertible P.lineBundle P.invertible

/-- The polarization read on the small étale site of the representable algebraic space. -/
abbrev polarizedSpaceModule :
    SheafOfModules.{u} (Space.representedStructureRingSheaf B integerBase (hZ B)
      (polarizedArrow P).left) :=
  (Space.representedSmallEtaleModuleEquivalence B integerBase (hZ B)
    (polarizedArrow P).left).functor.obj (polarizedEtaleModule P)

/-- The polarization read on the small étale site of the representable algebraic space is
quasi-coherent. -/
theorem isQuasicoherentOnSite_polarizedSpaceModule :
    SheafOfModules.IsQuasicoherentOnSite (polarizedSpaceModule P) := by
  rw [polarizedSpaceModule, Space.representedSmallEtaleModuleEquivalence_functor_obj]
  exact (Space.isQuasicoherentOnSite_representedSmallEtaleModule_iff B integerBase (hZ B)
    (polarizedArrow P).left (polarizedEtaleModule P)).mpr
    (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent
      (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B integerBase (hZ B)).obj (polarizedArrow P).left)
      (polarizedArrow P).left.left.property P.lineBundle (isQuasicoherent_lineBundle P))

/-- The unit of the associated-module adjunction is an isomorphism at the polarization. -/
instance isIso_unit_lineBundle :
    IsIso ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
        (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B integerBase (hZ B)).obj (polarizedArrow P).left)
        (polarizedArrow P).left.left.property).unit.app P.lineBundle) :=
  _root_.AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B integerBase (hZ B)).obj (polarizedArrow P).left)
    (polarizedArrow P).left.left.property ⟨P.lineBundle, isQuasicoherent_lineBundle P⟩

/-- **The Zariski restriction of the polarization read on the small étale site is the
polarization.** -/
def zariskiPolarizedSpaceModuleIso :
    (zariskiRestriction (polarizedArrow P)).obj
        ((etaleInverse (polarizedArrow P)).obj (polarizedSpaceModule P)) ≅ P.lineBundle :=
  (zariskiRestriction (polarizedArrow P)).mapIso
      ((Space.representedSmallEtaleModuleEquivalence B integerBase (hZ B)
        (polarizedArrow P).left).unitIso.app (polarizedEtaleModule P)).symm ≪≫
    (asIso ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
        (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B integerBase (hZ B)).obj (polarizedArrow P).left)
        (polarizedArrow P).left.left.property).unit.app P.lineBundle)).symm

/-- The Zariski restriction of the polarization read on the small étale site is invertible. -/
theorem isInvertible_zariskiPolarizedSpaceModule :
    SheafOfModules.IsInvertible P.total.presheaf P.total.ringCatSheaf.2
      ((zariskiRestriction (polarizedArrow P)).obj
        ((etaleInverse (polarizedArrow P)).obj (polarizedSpaceModule P))) :=
  Stacks.Picard.isInvertible_of_iso (zariskiPolarizedSpaceModuleIso P).symm P.invertible

/-- **The object of `RepresentedPolarized` over a polarized family.** -/
def representedOfPolarized : RepresentedPolarized B :=
  ⟨⟨⟨polarizedArrow P, polarizedSpaceModule P⟩,
    { proper := P.proper
      flat := P.flat
      finitePresentation := P.finitePresentation
      quasicoherent := isQuasicoherentOnSite_polarizedSpaceModule P
      invertible := isInvertible_zariskiPolarizedSpaceModule P
      relativelyAmple := by
        letI := P.invertible
        letI := isInvertible_zariskiPolarizedSpaceModule P
        exact (Stacks.RelativeVeryAmple.isRelativelyAmple_congr P.toBase _ _
          (zariskiPolarizedSpaceModuleIso P)).mpr P.relativelyAmple }⟩⟩

/-- The comparison `Θ(x P) ⟶ P`: identities, with the identification of polarizations. -/
def toPolarizedRepresentedOfPolarizedHom :
    (toPolarized B).obj (representedOfPolarized P) ⟶ P where
  baseMap := 𝟙 P.base
  totalMap := 𝟙 P.total
  cartesian := by
    change IsPullback (𝟙 P.total) P.toBase P.toBase (B.inclusion.map (𝟙 P.base))
    rw [B.inclusion.map_id P.base]
    exact IsPullback.id_horiz P.toBase
  lineBundleIso := (Scheme.Modules.pullbackId P.total).app P.lineBundle ≪≫
    (zariskiPolarizedSpaceModuleIso P).symm

/-- The comparison `Θ(x P) ⟶ P` maps to the identity of the base. -/
theorem polarizedProjection_map_toPolarizedRepresentedOfPolarizedHom :
    (polarizedProjection B ⋙ schemeOverIntegers B).map
      (toPolarizedRepresentedOfPolarizedHom P) = 𝟙 _ :=
  (schemeOverIntegers B).map_id P.base

/-- **The isomorphism `Θ(x P) ≅ P`.** -/
def toPolarizedRepresentedOfPolarizedIso :
    (toPolarized B).obj (representedOfPolarized P) ≅ P :=
  haveI : IsIso (toPolarizedRepresentedOfPolarizedHom P) :=
    (polarizedProjection_isFiberedInGroupoids_unconditional (B := B)).isIso_of_isIso_map _
      (by change IsIso (𝟙 P.base); infer_instance)
  asIso (toPolarizedRepresentedOfPolarizedHom P)

/-- The isomorphism `Θ(x P) ≅ P` lies over the identity of the base. -/
theorem isHomLift_toPolarizedRepresentedOfPolarizedIso :
    (polarizedProjection B ⋙ schemeOverIntegers B).IsHomLift
      (𝟙 ((polarizedProjection B ⋙ schemeOverIntegers B).obj P))
      (toPolarizedRepresentedOfPolarizedIso P).hom := by
  have h := Functor.IsHomLift.map (p := polarizedProjection B ⋙ schemeOverIntegers B)
    (toPolarizedRepresentedOfPolarizedIso P).hom
  change (polarizedProjection B ⋙ schemeOverIntegers B).IsHomLift
    ((polarizedProjection B ⋙ schemeOverIntegers B).map
      (toPolarizedRepresentedOfPolarizedHom P)) _ at h
  rwa [polarizedProjection_map_toPolarizedRepresentedOfPolarizedHom] at h

variable (B) in
/-- **Postcomposition with `Θ` is an equivalence** of the categories of functors over the site
from any category over the site. -/
theorem isEquivalence_postcompFunctor_toPolarizedBased
    (𝒵 : BasedCategory.{v, w} (Site B)) :
    (BasedFunctor.postcompFunctor 𝒵 (toPolarizedBased B)).IsEquivalence :=
  BasedCategory.Equivalence.isEquivalence_postcompFunctor_of_fullyFaithful (toPolarizedBased B)
    (Functor.FullyFaithful.ofFullyFaithful (toPolarized B)) representedOfPolarized
    toPolarizedRepresentedOfPolarizedIso isHomLift_toPolarizedRepresentedOfPolarizedIso 𝒵

end AlgebraicGeometry.PolarizedOverSpace

end
