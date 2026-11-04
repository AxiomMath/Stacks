module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionKey
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionSourceIdeal
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionFibreInverseImage

/-!
# The obstruction of Stacks 0E3V vanishes exactly when `f` lifts

Let `X'`, `Y'` be first-order deformations of `X`, `Y` over `k[M]`. The class `Push(Y')` is the
class of the extension `f⁻¹𝒪_{Y'}` of `f⁻¹𝒪_Y`, with the canonical map `c` of its ideal to
`𝒪_X ⊗_k M`; the class `Pull(X')` is the class of the fibre extension `𝒪_{X'} ×_{𝒪_X} f⁻¹𝒪_Y`.
The two classes agree exactly when `f` lifts to a morphism `X' ⟶ Y'` over `Spec k[M]`.

This file proves that equivalence for any identification `c` of the ideal of `f⁻¹𝒪_{Y'}` that
sends the generators `ũ(m)` (the images of the functions `(0, m)`) to `1 ⊗ m` and is determined by
them, and any bijective identification of the ideal of `𝒪_{X'}` sending the functions `(0, m)` to
`1 ⊗ m`.

## Main results

* `Deformation.Examples.pushClass_eq_pullClass_iff`: the two classes agree exactly when `f` lifts
  to a morphism `X' ⟶ Y'` over `Spec k[M]`.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 0GQ2](https://stacks.math.columbia.edu/tag/0GQ2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Sites.Conormal (kernelIdeal IdealRestriction)
open AlgebraicGeometry.RingedSpaceThickening

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} {f : X ⟶ Y}
  {pX : X ⟶ baseSpec (residueFieldBase Λ k)} {pY : Y ⟶ baseSpec (residueFieldBase Λ k)}
  (hf : f ≫ pY = pX) {M : FGModuleCat.{u} k}
  (xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
  (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))

/-- The structure sheaf of a deformation of `X` over `k[M]`, as a square-zero extension of `𝒪_X`
by `𝒪_X ⊗_k M`, for a given identification `ι` of its ideal with `𝒪_X ⊗_k M`. -/
def thickenedExtensionOfIdeal
    (ι : IdealRestriction.{u, u, u, u}
      (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two (Λ := Λ) M)
        xε).thickenedSheafReduction (schemeMorphismCoefficientSheaf f pY M)) :
    AlgebraSquareZeroExtension
      ((Over.mk pX).hom.toLRSHom.toShHom ≫
        (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom)
      (schemeMorphismCoefficientSheaf f pY M) :=
  { (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two (Λ := Λ) M)
      xε).toAlgebraExtension with ideal := ι }

/-- The algebra structure of the thickened structure sheaf over the base of `X_A`, written as the
adjoint of the comorphism of `X' ⟶ Spec k` read on the opens of `X`, is the one of
`Scheme.liftTargetBaseMap` transported along `thickenedSheafIsoInverseImage`. -/
theorem eqToHom_comp_comorphismOnOpens_eq (hf : f ≫ pY = pX)
    (e : inverseImageBaseRing (schemeMorphismInverseImageBase f pY) =
      (TopCat.Sheaf.pullback CommRingCat.{u}
        ((fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two (Λ := Λ) M)
          xε).i.hom.base ≫
          (schemeMorphismPushStructure pX xε).toLRSHom.toShHom.hom.base)).obj
        (baseSpec (residueFieldBase Λ k)).toRingedSpace.sheaf) :
    eqToHom e ≫ ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        ((fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two (Λ := Λ) M)
          xε).i.hom.base ≫
          (schemeMorphismPushStructure pX xε).toLRSHom.toShHom.hom.base)).homEquiv _ _).symm
        ((fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two (Λ := Λ) M)
          xε).comorphismOnOpensSheafMap (schemeMorphismPushStructure pX xε).toLRSHom.toShHom) =
      eqToHom (congrArg (fun t : X ⟶ baseSpec (residueFieldBase Λ k) =>
        (TopCat.Sheaf.pullback CommRingCat.{u} t.toLRSHom.toShHom.hom.base).obj
          (baseSpec (residueFieldBase Λ k)).toRingedSpace.sheaf)
        ((specialMap_comp_schemeMorphismPushStructure pX xε).trans hf.symm).symm) ≫
      Scheme.liftTargetBaseMap xε.1.specialMap (schemeMorphismPushStructure pX xε) ≫
        (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two (Λ := Λ) M)
          xε).thickenedSheafIsoInverseImage.inv := by
  rw [show Scheme.liftTargetBaseMap xε.1.specialMap (schemeMorphismPushStructure pX xε) ≫
      (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two (Λ := Λ) M)
        xε).thickenedSheafIsoInverseImage.inv = _ from
    fiberSolution_liftTargetBaseMap_comp_inv (maximalIdeal_squareZeroExtensionArtinian_pow_two
      (Λ := Λ) M) xε (squareZeroStructureSpecMap M)]
  rfl

variable
  (c : IdealRestriction.{u, u, u, u} (Scheme.liftSourceReduction yε.1.specialMap f)
    (schemeMorphismPushCoefficients f pY M))
  (u : M → ↥((Scheme.liftSource yε.1.specialMap f).obj.obj (Opposite.op ⊤)))
  (hu_eq : ∀ m, u m = (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base).unit.app
        yε.1.scheme.toRingedSpace.sheaf).hom.app (Opposite.op ⊤)).hom
      ((yε.1.rebase yε.2).toBase.appTop (squareZeroSpecFunction (Λ := Λ) M m)))
  (hu : ∀ m, u m ∈ kernelIdeal (Scheme.liftSourceReduction yε.1.specialMap f).hom (Opposite.op ⊤))
  (hc : ∀ m, c.app (Opposite.op ⊤) ⟨u m, hu m⟩ = coefficientSheafSection (f ≫ pY) M m)
  (hgen : ∀ (V : Opens X.carrier) (z : ↥((Scheme.liftSource yε.1.specialMap f).obj.obj
      (Opposite.op V))),
    z ∈ kernelIdeal (Scheme.liftSourceReduction yε.1.specialMap f).hom (Opposite.op V) →
    ∃ (J : Type u) (W : J → Opens X.carrier) (hW : ∀ j, W j ≤ V), V ≤ iSup W ∧
      ∀ j, ((Scheme.liftSource yε.1.specialMap f).obj.map (homOfLE (hW j)).op).hom z ∈
        Ideal.span (Set.range fun m => ((Scheme.liftSource yε.1.specialMap f).obj.map
          (homOfLE (le_top (a := W j))).op).hom (u m)))
  (ι : IdealRestriction.{u, u, u, u}
    (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two (Λ := Λ) M)
      xε).thickenedSheafReduction
    (schemeMorphismCoefficientSheaf f pY M))
  (hι : ∀ U, Function.Bijective ((thickenedExtensionOfIdeal xε ι).ideal.app U))
  (hX : ∀ m : M, (thickenedExtensionOfIdeal xε ι).idealIncl hι (Opposite.op ⊤)
      (coefficientSheafSection (f ≫ pY) M m) =
    ((thickenedExtensionOfIdeal xε ι).adjointBase.hom.app (Opposite.op ⊤)).hom
      (squareZeroSpecFunction (Λ := Λ) M m))
  (v : inverseImageBaseRing (schemeMorphismInverseImageBase f pY) ⟶
    (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two (Λ := Λ) M) xε).thickenedSheaf)
  (hv : v ≫ (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two (Λ := Λ) M)
      xε).thickenedSheafReduction =
    structureRingMap (schemeMorphismInverseImageBase f pY) ≫
      Stacks.SheafOfModules.ringedSpaceStructureMap f.toLRSHom.toShHom)
  (hv_eq : v = eqToHom (congrArg (fun t : X ⟶ baseSpec (residueFieldBase Λ k) =>
      (TopCat.Sheaf.pullback CommRingCat.{u} t.toLRSHom.toShHom.hom.base).obj
        (baseSpec (residueFieldBase Λ k)).toRingedSpace.sheaf)
      ((specialMap_comp_schemeMorphismPushStructure pX xε).trans hf.symm).symm) ≫
    Scheme.liftTargetBaseMap xε.1.specialMap (schemeMorphismPushStructure pX xε) ≫
      (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two (Λ := Λ) M)
        xε).thickenedSheafIsoInverseImage.inv)

include hu_eq hc hgen hX in
/-- For a lift `b` of `f` over `Spec k`, its map `f⁻¹𝒪_{Y'} ⟶ 𝒪_{X'}` is compatible with the
identifications of the two ideals exactly when `b` pulls each function `(0, m)` of `Y'` back to
that of `X'`. -/
theorem sheafLift_ideal_compat_iff
    (b : { b : xε.1.scheme ⟶ yε.1.scheme //
        b ≫ schemeMorphismPushStructure pY yε = schemeMorphismPushStructure pX xε ∧
          xε.1.specialMap ≫ b = f ≫ yε.1.specialMap }) :
    (∀ (V : (Opens X.carrier)ᵒᵖ)
        (z : ↥(kernelIdeal (Scheme.liftSourceReduction yε.1.specialMap f).hom V)),
        (schemeMorphismSheafLiftEquiv xε yε hf b).1.hom.app V z =
          ((thickenedExtensionOfIdeal xε ι).fibreExtensionData f.toLRSHom.toShHom hι
            (schemeMorphismInverseImageBase f pY) v hv).ι.app V (c.app V z)) ↔
      ∀ m : M, b.1.appTop ((yε.1.rebase yε.2).toBase.appTop (squareZeroSpecFunction (Λ := Λ) M m)) =
        (xε.1.rebase xε.2).toBase.appTop (squareZeroSpecFunction (Λ := Λ) M m) := by
  refine (((thickenedExtensionOfIdeal xε ι).fibreExtensionData f.toLRSHom.toShHom hι
    (schemeMorphismInverseImageBase f pY) v hv).ideal_compat_iff_generators
    (schemeMorphismPushExtension f pY yε c) _ (schemeMorphismSheafLiftEquiv xε yε hf b).2.1 u hu
    hgen).trans (forall_congr' fun m => ?_)
  have hY : (schemeMorphismSheafLiftEquiv xε yε hf b).1.hom.app (Opposite.op ⊤) (u m) =
      b.1.appTop ((yε.1.rebase yε.2).toBase.appTop (squareZeroSpecFunction (Λ := Λ) M m)) := by
    rw [hu_eq]
    exact schemeMorphismSheafLiftEquiv_apply_unit xε yε hf b _
  have hXm : ((thickenedExtensionOfIdeal xε ι).fibreExtensionData f.toLRSHom.toShHom hι
      (schemeMorphismInverseImageBase f pY) v hv).ι.app (Opposite.op ⊤)
        ((schemeMorphismPushExtension f pY yε c).ideal.app (Opposite.op ⊤) ⟨u m, hu m⟩) =
      (xε.1.rebase xε.2).toBase.appTop (squareZeroSpecFunction (Λ := Λ) M m) := by
    change (thickenedExtensionOfIdeal xε ι).idealIncl hι (Opposite.op ⊤)
      (c.app (Opposite.op ⊤) ⟨u m, hu m⟩) = _
    have hab : (thickenedExtensionOfIdeal xε ι).adjointBase =
        (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two (Λ := Λ) M)
          xε).deformedBaseSheafMap :=
      (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two (Λ := Λ) M)
        xε).adjoint_thickenedSheafBase
    rw [hc, hX, hab]
    change ((fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two (Λ := Λ) M)
      xε).deformedBasePresheafMap.app (Opposite.op ⊤)).hom _ = _
    rw [DeformationSolution.deformedBasePresheafMap_app]
    exact presheaf_map_apply_self _ _ _
  exact Eq.congr hY hXm

include hu_eq hc hgen hX hv_eq in
/-- The class of the extension `f⁻¹𝒪_{Y'}` of `f⁻¹𝒪_Y` (ideal map `c`) and the class of the fibre
extension `𝒪_{X'} ×_{𝒪_X} f⁻¹𝒪_Y`, transferred to `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)`, are equal
exactly when there is a morphism `X' ⟶ Y'` over `Spec k[M]` restricting to `f`. -/
theorem pushClass_eq_pullClass_iff :
    haveI := (schemeMorphismPushExtension f pY yε c).presentation_isLocallySurjective
    haveI := ((thickenedExtensionOfIdeal xε ι).fibreExtensionData f.toLRSHom.toShHom hι
      (schemeMorphismInverseImageBase f pY) v hv).toExtension.presentation_isLocallySurjective
    pulledNaiveCotangentTransfer f.toLRSHom.toShHom pY.toLRSHom.toShHom
        (schemeMorphismCoefficientSheaf f pY M)
        (schemeMorphismPushExtension f pY yε c).toPresented.extClass =
      pulledNaiveCotangentTransfer f.toLRSHom.toShHom pY.toLRSHom.toShHom
        (schemeMorphismCoefficientSheaf f pY M)
        ((thickenedExtensionOfIdeal xε ι).fibreExtensionData f.toLRSHom.toShHom hι
          (schemeMorphismInverseImageBase f pY) v hv).toExtension.toPresented.extClass ↔
      Nonempty (globalLiftsOverBase f xε.1 yε.1 (eqToHom (yε.2.trans xε.2.symm))) := by
  refine (EmbeddingLike.apply_eq_iff_eq _).trans
    ((((thickenedExtensionOfIdeal xε ι).fibreExtensionData f.toLRSHom.toShHom hι
      (schemeMorphismInverseImageBase f pY) v hv).extClass_eq_extClass_toExtension_iff
        (schemeMorphismPushExtension f pY yε c)).trans ?_)
  subst hv_eq
  constructor
  · rintro ⟨φ, h1, h2, h3⟩
    let b := (schemeMorphismSheafLiftEquiv xε yε hf).symm ⟨φ, h1, h2⟩
    have hb : (schemeMorphismSheafLiftEquiv xε yε hf b).1 = φ :=
      congrArg Subtype.val ((schemeMorphismSheafLiftEquiv xε yε hf).apply_symm_apply _)
    exact ⟨(globalLiftsOverBaseEquivField f xε yε).symm ⟨b.1, b.2,
      (sheafLift_ideal_compat_iff hf xε yε c u hu_eq hu hc hgen ι hι hX _ hv b).1 (hb ▸ h3)⟩⟩
  · rintro ⟨ℓ⟩
    let e := globalLiftsOverBaseEquivField f xε yε ℓ
    let b : { b : xε.1.scheme ⟶ yε.1.scheme //
        b ≫ schemeMorphismPushStructure pY yε = schemeMorphismPushStructure pX xε ∧
          xε.1.specialMap ≫ b = f ≫ yε.1.specialMap } := ⟨e.1, e.2.1⟩
    exact ⟨_, (schemeMorphismSheafLiftEquiv xε yε hf b).2.1,
      (schemeMorphismSheafLiftEquiv xε yε hf b).2.2,
      (sheafLift_ideal_compat_iff hf xε yε c u hu_eq hu hc hgen ι hι hX _ hv b).2 e.2.2⟩

end Deformation.Examples

end
