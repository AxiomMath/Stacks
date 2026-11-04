module

public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpacePulledNaiveTransfer
public import StacksFrontier.Cotangent.SheavesOfRings.ThickeningLiftCorrespondence
public import StacksFrontier.Deformation.Examples.Geometric.OpenSubschemes
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationSolution
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionBase
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSequenceTerms

/-!
# The extension `f⁻¹𝒪_{Y'}` of `f⁻¹𝒪_Y` attached to a deformation of the target

Let `f : X → Y` be a morphism of schemes over `k`, `M` a finite-dimensional `k`-vector space and
`Y'` a deformation of `Y` over `k[M]`, with special-fibre immersion `j : Y → Y'`. On the opens of
`X`, the inverse image `f⁻¹𝒪_{Y'}` is an extension of `f⁻¹𝒪_Y` (the structure sheaf of
`X_A = (X, f⁻¹𝒪_Y)`) by the inverse image of the ideal of `Y` in `Y'`; mapping that ideal to
`𝒪_X ⊗_k M` makes it a square-zero extension of `f⁻¹𝒪_Y` by `𝒪_X ⊗_k M` of algebras over `k`.
Its class, transferred to `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)`, is the class `Push(Y')` whose
difference with the class of the deformation of the source is the obstruction of
[Stacks Project, Tag 0E3V].

## Main definitions

* `Deformation.Examples.schemeMorphismPushStructure`: the structure morphism `Y' ⟶ Spec k`.
* `Deformation.Examples.schemeMorphismPushBase`: the `k`-algebra structure of `f⁻¹𝒪_{Y'}`.
* `Deformation.Examples.schemeMorphismPushExtension`: the square-zero extension `f⁻¹𝒪_{Y'}` of
  `f⁻¹𝒪_Y`, for a given map of its ideal to `𝒪_X ⊗_k M`.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

/-- Transport along an equality of morphisms of ringed spaces turns one structure map into the
other. -/
theorem eqToHom_comp_ringedSpaceStructureMap {Z W : RingedSpace.{u, u}} {a b : Z ⟶ W} (h : a = b)
    (e : (TopCat.Sheaf.pullback CommRingCat.{u} a.hom.base).obj W.sheaf =
      (TopCat.Sheaf.pullback CommRingCat.{u} b.hom.base).obj W.sheaf) :
    eqToHom e ≫ Stacks.SheafOfModules.ringedSpaceStructureMap b =
      Stacks.SheafOfModules.ringedSpaceStructureMap a := by
  subst h
  simp

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  {M : FGModuleCat.{u} k}
  (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))

/-- The base of `X_A = (X, f⁻¹𝒪_Y)` over `Spec k`: the projection `X_A ⟶ Y` followed by `p_Y`. -/
abbrev schemeMorphismInverseImageBase :
    RingedSpace.inverseImage Y.toRingedSpace f.toLRSHom.toShHom.hom.base ⟶
      (baseSpec (residueFieldBase Λ k)).toRingedSpace :=
  RingedSpace.inverseImageProjection Y.toRingedSpace f.toLRSHom.toShHom.hom.base ≫
    pY.toLRSHom.toShHom

/-- The structure morphism `Y' ⟶ Spec k[M] ⟶ Spec k` of a deformation of `Y` over `k[M]`. -/
abbrev schemeMorphismPushStructure : yε.1.scheme ⟶ baseSpec (residueFieldBase Λ k) :=
  (yε.1.rebase yε.2).toBase ≫ squareZeroStructureSpecMap M

/-- The special fibre `Y ⟶ Y'` is a morphism over `k`. -/
theorem specialMap_comp_schemeMorphismPushStructure :
    yε.1.specialMap ≫ schemeMorphismPushStructure pY yε = pY := by
  have h := (yε.1.rebase yε.2).specialCartesian.w
  rw [SchemeDeformationCategory.rebase_specialMap] at h
  exact ((reassoc_of% h) (squareZeroStructureSpecMap M)).trans
    ((congrArg (pY ≫ ·) (residueSpecMap_comp_squareZeroStructureSpecMap M)).trans
      (Category.comp_id _))

/-- The composite `X ⟶ Y ⟶ Y' ⟶ Spec k` is `f ≫ p_Y`. -/
theorem schemeMorphismPush_comp_eq :
    (f ≫ yε.1.specialMap) ≫ schemeMorphismPushStructure pY yε = f ≫ pY := by
  rw [Category.assoc, specialMap_comp_schemeMorphismPushStructure]

/-- **The `k`-algebra structure of `f⁻¹𝒪_{Y'}`**, over the base of `X_A`: the comparison
`(f ≫ j ≫ p_{Y'})⁻¹ ≅ (f ≫ j)⁻¹ ∘ p_{Y'}⁻¹` followed by the inverse image of the structure map of
`p_{Y'} : Y' ⟶ Spec k`. -/
def schemeMorphismPushBase :
    AlgebraicGeometry.RingedSpaceThickening.inverseImageBaseRing
        (schemeMorphismInverseImageBase f pY) ⟶
      Scheme.liftSource yε.1.specialMap f :=
  eqToHom (congrArg (fun t : X.carrier ⟶ (baseSpec (residueFieldBase Λ k)).carrier =>
      (TopCat.Sheaf.pullback CommRingCat.{u} t).obj
        (baseSpec (residueFieldBase Λ k)).toRingedSpace.sheaf)
      (congrArg (fun t : X ⟶ baseSpec (residueFieldBase Λ k) => t.toLRSHom.toShHom.hom.base)
        (schemeMorphismPush_comp_eq f pY yε).symm)) ≫
    (Stacks.SheafOfModules.inverseImageCompIso (f ≫ yε.1.specialMap).toLRSHom.toShHom
      (schemeMorphismPushStructure pY yε).toLRSHom.toShHom).hom ≫
      (TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base).map
        (Stacks.SheafOfModules.ringedSpaceStructureMap
          (schemeMorphismPushStructure pY yε).toLRSHom.toShHom)

/-- The reduction `f⁻¹𝒪_{Y'} ⟶ f⁻¹𝒪_Y` is the structure map of `X_A ⟶ Y ⟶ Y'`. -/
theorem homOver_liftSourceReduction :
    RingedSpace.homOver (Z := RingedSpace.inverseImage Y.toRingedSpace f.toLRSHom.toShHom.hom.base)
        (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base
        (Scheme.liftSourceReduction yε.1.specialMap f) =
      RingedSpace.inverseImageProjection Y.toRingedSpace f.toLRSHom.toShHom.hom.base ≫
        yε.1.specialMap.toLRSHom.toShHom := by
  have h := Stacks.SheafOfModules.inverseImageCompIso_hom_comp
    (RingedSpace.inverseImageProjection Y.toRingedSpace f.toLRSHom.toShHom.hom.base)
      yε.1.specialMap.toLRSHom.toShHom
  rw [AlgebraicGeometry.RingedSpace.ringedSpaceStructureMap_inverseImageProjection] at h
  have h' : Scheme.liftSourceReduction yε.1.specialMap f =
      Stacks.SheafOfModules.ringedSpaceStructureMap
        (RingedSpace.inverseImageProjection Y.toRingedSpace f.toLRSHom.toShHom.hom.base ≫
          yε.1.specialMap.toLRSHom.toShHom) :=
    ((Category.comp_id _).symm.trans (Category.assoc _ _ _)).trans h
  rw [h']
  exact RingedSpace.homOver_base_ringedSpaceStructureMap
    (RingedSpace.inverseImageProjection Y.toRingedSpace f.toLRSHom.toShHom.hom.base ≫
      yε.1.specialMap.toLRSHom.toShHom)

/-- The `k`-algebra structure of `f⁻¹𝒪_{Y'}` lifts the one of `f⁻¹𝒪_Y`. -/
theorem schemeMorphismPushBase_comp_reduction :
    schemeMorphismPushBase f pY yε ≫ Scheme.liftSourceReduction yε.1.specialMap f =
      AlgebraicGeometry.RingedSpaceThickening.structureRingMap
        (schemeMorphismInverseImageBase f pY) := by
  have h := RingedSpace.ringedSpaceStructureMap_homOver_comp
    (Z := RingedSpace.inverseImage Y.toRingedSpace f.toLRSHom.toShHom.hom.base)
    (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base
    (Scheme.liftSourceReduction yε.1.specialMap f)
    (schemeMorphismPushStructure pY yε).toLRSHom.toShHom
  have hc : RingedSpace.homOver (Z := RingedSpace.inverseImage Y.toRingedSpace
        f.toLRSHom.toShHom.hom.base) (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base
        (Scheme.liftSourceReduction yε.1.specialMap f) ≫
          (schemeMorphismPushStructure pY yε).toLRSHom.toShHom =
      schemeMorphismInverseImageBase f pY := by
    rw [homOver_liftSourceReduction, Category.assoc]
    exact congrArg (RingedSpace.inverseImageProjection Y.toRingedSpace
      f.toLRSHom.toShHom.hom.base ≫ ·) (congrArg (fun t : Y ⟶ baseSpec (residueFieldBase Λ k) =>
        t.toLRSHom.toShHom) (specialMap_comp_schemeMorphismPushStructure pY yε))
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (eqToHom _ ≫ ·) ((Category.assoc _ _ _).trans h.symm)).trans ?_
  exact eqToHom_comp_ringedSpaceStructureMap hc.symm _

variable (M) in
/-- The coefficients `ι_*(𝒪_X ⊗_k M)` of the extension, as a module over `f⁻¹𝒪_Y`. -/
abbrev schemeMorphismPushCoefficients :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology X.carrier)
      (RingedSpace.inverseImage Y.toRingedSpace f.toLRSHom.toShHom.hom.base).sheaf) :=
  (RingedSpaceModuleAdjunction.modulePushforward
    (RingedSpace.inverseImageSourceInclusion f.toLRSHom.toShHom)).obj
      (schemeMorphismCoefficientSheaf f pY M)

/-- **The square-zero extension `f⁻¹𝒪_{Y'}` of `f⁻¹𝒪_Y`** of algebras over `k`, with a given map
`c` of its ideal `Ker(f⁻¹𝒪_{Y'} ⟶ f⁻¹𝒪_Y)` to the coefficients `𝒪_X ⊗_k M`. -/
def schemeMorphismPushExtension
    (c : Stacks.Sites.Conormal.IdealRestriction.{u, u, u, u}
      (Scheme.liftSourceReduction yε.1.specialMap f) (schemeMorphismPushCoefficients f pY M)) :
    AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension
      (schemeMorphismInverseImageBase f pY) (schemeMorphismPushCoefficients f pY M) :=
  haveI : IsClosedImmersion yε.1.specialMap := deformationSpecialMap_isClosedImmersion yε.1
  { sheaf := Scheme.liftSource yε.1.specialMap f
    base := schemeMorphismPushBase f pY yε
    reduction := Scheme.liftSourceReduction yε.1.specialMap f
    base_comp_reduction := schemeMorphismPushBase_comp_reduction f pY yε
    reduction_surjective := Scheme.isLocallySurjective_liftSourceReduction yε.1.specialMap f
    ideal := c }

end Deformation.Examples

end
