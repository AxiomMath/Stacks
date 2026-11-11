module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TrivialRingSheafModules
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.DerivedPushforwardBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.CategoryTheory.Sites.VanishingOnCoveringContinuous
public import StacksFrontier.Cotangent.SmoothUnconditional
public import StacksFrontier.Cotangent.Spaces.ModelCotangentHomologyCoherent

/-!
# The cotangent complex of a smooth morphism to an affine scheme

Let `f : X ⟶ T` be a smooth morphism from an algebraic space to an object `T` of the big fppf
site with affine underlying scheme, and let `L_{X/T}` be its cotangent complex (Stacks 08SU),
formed on the model of the small étale site of `X`
(`AlgebraicGeometry.Space.modelRingedToposHom`). This file proves that `L_{X/T}` has cohomology
only in degree `0` (`AlgebraicGeometry.Space.isZero_homology_modelCotangentComplex_of_isSmooth`),
so that in the derived category it is its degree `0` cohomology sheaf placed in degree `0`
(`AlgebraicGeometry.Space.modelCotangentComplexDerivedIsoOfIsSmooth`).

The cohomology sheaf `H^i(L_{X/T})` is the sheafification of `W ↦ H^i(L_{𝒪(W)/Λ})`,
`Λ = Γ(T, 𝒪_T)` (`AlgebraicGeometry.Space.modelCotangentHomologyIso`), whose sections over the
affine étale charts are unchanged by sheafification. Over an affine étale chart `U`, the ring map
`Λ → 𝒪(U)` is the ring map of global sections of the smooth morphism of affine schemes `U ⟶ T`,
hence smooth, and `H^i(L_{𝒪(U)/Λ}) = 0` for `i ≠ 0` (Stacks 08R5). The affine étale charts are
a covering family of the small étale site (Stacks 04JS), carried to the model by the
comparison, so a sheaf vanishing over them vanishes.

## Main results

* `AlgebraicGeometry.Space.smooth_modelSectionsAlgebraMap`
* `AlgebraicGeometry.Space.isZero_homology_modelCotangentComplex_of_isSmooth`
* `AlgebraicGeometry.Space.modelCotangentComplexDerivedIsoOfIsSmooth`

## References

* [Stacks Project, Tag 08R5](https://stacks.math.columbia.edu/tag/08R5)
* [Stacks Project, Tag 08SU](https://stacks.math.columbia.edu/tag/08SU)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T : BigFppfOver B S hS}
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)

/-- **Over an object of the model lying over an affine étale chart, the sections of `𝒪_X` are a
smooth algebra over `Λ = Γ(T, 𝒪_T)`**, for `f` smooth and `T` affine: the ring map is that of
global sections of the smooth morphism of affine schemes `U ⟶ T` of the chart. -/
theorem smooth_modelSectionsAlgebraMap (hf : IsSmooth B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (W : (modelTopos X).C)
    (hW : IsAffine (chartScheme ((smallEtaleModelEquiv B S hS X).inverse.obj W))) :
    ((modelConstantBaseMap f ≫ (modelTowerMap f).hom).app (op W)).hom.Smooth := by
  rw [modelSectionsAlgebraMap_eq]
  let d := affineTargetChartDiagram f ((smallEtaleModelEquiv B S hS X).inverse.obj W)
  have hsm : Smooth ((BigFppfOver.toScheme B S hS).map d.g) :=
    hf d.U.1.left d.V.1.left d.U.1.hom d.V.1.hom d.g d.U.2 d.V.2 d.comm.symm
  have : IsAffine (unop ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).op.obj
      (op ((smallEtaleModelEquiv B S hS X).inverse.obj W)))) := hW
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj d.V.1.left) := hT
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  exact HasRingHomProperty.appTop (P := @Smooth) _ hsm

/-- **Over an affine étale chart, the sections of `H^i(L_{X/T})` vanish for `i ≠ 0`**, for `f`
smooth and `T` affine: they are `H^i(L_{𝒪(U)/Λ})` (sheafification not changing them), which
vanishes for the smooth ring map `Λ → 𝒪(U)` (Stacks 08R5). -/
theorem subsingleton_modelCotangentHomology_obj (hf : IsSmooth B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (i : ℤ) (hi : i ≠ 0)
    (U : AffineEtale B S hS X.1) :
    Subsingleton (((modelRingedToposHom f).cotangentComplex.homology i).val.obj
      (op ((modelAffineChartFunctor X).obj U))) := by
  let W := (modelAffineChartFunctor X).obj U
  have hW : IsAffine (chartScheme ((smallEtaleModelEquiv B S hS X).inverse.obj W)) :=
    (IsAffineChart B S hS X.1).prop_of_iso ((smallEtaleModelEquiv B S hS X).unitIso.app U.obj)
      U.property
  let : Algebra (baseRing B S hS T) ((modelTopos X).O.obj.obj (op W)) :=
    ((modelConstantBaseMap f ≫ (modelTowerMap f).hom).app (op W)).hom.toAlgebra
  have : Algebra.Smooth (baseRing B S hS T) ((modelTopos X).O.obj.obj (op W)) :=
    smooth_modelSectionsAlgebraMap f hf hT W hW
  have h0 : IsZero ((CommAlgCat.cotangentComplex.{u, u}
      ((modelConstantPresheaf (X := X) (T := T)).obj (op W))
        (CategoryTheory.Sheaf.sectionsAlgebra ⊥ (CategoryTheory.Sheaf.presheafBaseHom.{u, u, u}
          (modelTopos X).J (modelTowerMap f) (modelConstantBaseMap f)) (op W))).homology i) :=
    CommAlgCat.isZero_homology_cotangentComplex_of_smooth_unconditional (baseRing B S hS T)
      ((modelTopos X).O.obj.obj (op W)) i hi
  have h1 : Subsingleton (((𝟭 (PresheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf
      (modelTopos X).O).obj)).obj (modelPresheafBaseHomology f i)).obj (op W)) :=
    (ModuleCat.isZero_iff_subsingleton).1 (h0.of_iso
      (CategoryTheory.Sheaf.presheafBaseHomologyObjIso.{u, u, u}
        (modelTopos X).J (modelTowerMap f) (modelConstantBaseMap f) i (op W)).symm)
  have h2 : Subsingleton ((PresheafOfModules.evaluation _ (op W)).obj ((SheafOfModules.forget _).obj
      ((CategoryTheory.Sheaf.moduleSheafification.{u, u, u} (modelTopos X).J
        (B := (modelTopos X).O)).obj (modelPresheafBaseHomology f i)))) :=
    (bijective_modelPresheafBaseHomology_unit_app f i U).2.subsingleton
  exact ((PresheafOfModules.evaluation _ (op W)).mapIso
    ((SheafOfModules.forget _).mapIso
      (modelCotangentHomologyIso f hT i))).toLinearEquiv.toEquiv.subsingleton

/-- **The cotangent complex of a smooth morphism to an affine scheme has cohomology only in
degree `0`**: for `f : X ⟶ T` smooth with `T` affine, `H^i(L_{X/T}) = 0` for `i ≠ 0`, on the
model of the small étale site of `X`. Its sections vanish over the affine étale charts
(Stacks 08R5 chart by chart), which are a covering family (Stacks 04JS). -/
theorem isZero_homology_modelCotangentComplex_of_isSmooth
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (hf : IsSmooth B S hS f.hom)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((modelRingedToposHom f).cotangentComplex.homology i) := by
  let N := (modelRingedToposHom f).cotangentComplex.homology i
  let G : Sheaf (modelTopos X).J AddCommGrpCat.{u} := ⟨N.val.presheaf, N.isSheaf⟩
  have hG := CategoryTheory.Sheaf.isZero_sections_of_isCoveringFamily_of_isContinuous
    (smallEtaleModelEquiv B S hS X).functor G (isCoveringFamily_isAffineChart B S hS X)
    (fun Y hY => @AddCommGrpCat.isZero_of_subsingleton _
      (subsingleton_modelCotangentHomology_obj f hf hT i hi ⟨Y, hY⟩))
  exact Stacks.SheafOfModules.isZero_of_forall_subsingleton_sections N fun V =>
    AddCommGrpCat.subsingleton_of_isZero (hG V.unop)

variable [HasDerivedCategory.{t} (modelModules X)]

/-- **The cotangent complex of a smooth morphism to an affine scheme is its degree `0`
cohomology sheaf placed in degree `0`**: for `f : X ⟶ T` smooth with `T` affine,
`L_{X/T} ≅ H^0(L_{X/T})[0]` in the derived category of `𝒪_X`-modules on the model. The complex
vanishes in positive degrees and its cohomology vanishes in negative degrees
(`AlgebraicGeometry.Space.isZero_homology_modelCotangentComplex_of_isSmooth`). -/
def modelCotangentComplexDerivedIsoOfIsSmooth
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (hf : IsSmooth B S hS f.hom) :
    (modelRingedToposHom f).cotangentComplexDerived ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((modelRingedToposHom f).cotangentComplex.homology 0) := by
  let K := (modelRingedToposHom f).cotangentComplex
  have : K.IsStrictlyLE 0 := (K.isStrictlyLE_iff 0).2
    fun i hi => (modelRingedToposHom f).cotangentComplex_isZero_pos i hi
  have : (modelRingedToposHom f).cotangentComplexDerived.IsGE 0 := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact IsZero.of_iso (isZero_homology_modelCotangentComplex_of_isSmooth f hT hf i (by omega))
      ((DerivedCategory.homologyFunctorFactors _ i).app _)
  have : (modelRingedToposHom f).cotangentComplexDerived.IsLE 0 :=
    (DerivedCategory.isLE_Q_obj_iff _ 0).2 inferInstance
  let hex := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (modelRingedToposHom f).cotangentComplexDerived 0
  let e := hex.choose_spec.some
  refine e ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso ?_
  exact (((DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm) ≪≫
      (DerivedCategory.homologyFunctorFactors _ 0).app K

end AlgebraicGeometry.Space

end
