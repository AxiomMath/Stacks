module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceComplexIso
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothWedgeDegreeZeroMono
public import StacksCore.CategoryTheory.Subobject.Lattice
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite

/-!
# Section 0FMK in the degree of the cut

[Stacks, Section 0FMK] identifies the `k`-th graded piece of the filtration of `Ω^•_{X/S}` by the
forms pulled back from `Y` with

`gr^kΩ^•_{X/S}  ≅  f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`

for `f : X ⟶ Y` smooth over a base `S`.
`Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX` identifies the two sides degreewise in every
degree of the form `n = k + 1 + m` with `m : ℕ`. This file treats the remaining degree `n = k`,
the degree of the cut:

`(gr^kΩ^•_{X/S})^k  ≅  (f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y})^k`.

## Main definitions

* `Stacks.GradedPieceImage.mapSubobjectsObjIso`: the underlying object of a subobject transported
  along a functor preserving monomorphisms.
* `Stacks.GradedPieceImage.imageSubobjectIsoSource`: the image subobject of a monomorphism is its
  source.
* `Stacks.DeRhamSmooth.cutProdWedgeHom`: the wedge-product morphism
  `⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} ⋀^0Ω_{X/S} ⟶ Ω^k_{X/S}` cutting out the top step of the filtration.

## Main results

* `Stacks.DeRhamSmooth.filtrationXIsoCutWedgeSource`: for `f` smooth, in the degree of the cut the
  step of the filtration is the source of the wedge-product morphism.
* `Stacks.DeRhamSmooth.filtrationXIsoCutWedgeSource_inv_arrow`: read on that source, the inclusion
  of the step into `Ω^k_{X/S}` is the wedge-product morphism.
* `Stacks.DeRhamSmooth.cutWedgeSourceIsoPullbackTensor`: that source is
  `f^*Ω^k_{Y/S} ⊗_{𝒪_X} Ω^0_{X/Y}`.
* `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetXAtCut`: the degreewise comparison of
  Section 0FMK in the degree of the cut.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 08DE](https://stacks.math.columbia.edu/tag/08DE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.DeRhamDirectImage

attribute [local instance 2000] HasDerivedCategory.standard

/-! `Stacks.SheafOfModules.Tensor.ringSheaf` and `CategoryTheory.Sheaf.toRingCat` are the same
bundled sheaf of rings; making `ringSheaf` reducible for implicit-argument unification identifies
the two. -/
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

universe u

namespace Stacks.GradedPieceImage

/-- **Transporting a subobject along a functor preserving monomorphisms does not change its
underlying object**: `mapSubobjects U X` carries `P` to the subobject presented by `U.map P.arrow`
(`Stacks.GradedPieceImage.mapSubobjects_obj`), whose underlying object is `U.obj P`. -/
noncomputable def mapSubobjectsObjIso {C₁ : Type*} [Category* C₁] {D₁ : Type*} [Category* D₁]
    (U : C₁ ⥤ D₁) [U.PreservesMonomorphisms] {Z : C₁} (P : Subobject Z) :
    (((mapSubobjects U Z).obj P : D₁)) ≅ U.obj (P : C₁) :=
  Subobject.isoOfEq _ _ (mapSubobjects_obj U P) ≪≫
    @Subobject.underlyingIso _ _ _ _ (U.map P.arrow) (U.map_mono P.arrow)

/-- **`Stacks.GradedPieceImage.mapSubobjectsObjIso` is compatible with the inclusions**: the
inclusion of the transported subobject into `U.obj Z`, read on `U.obj P`, is `U.map P.arrow`. -/
@[reassoc]
theorem mapSubobjectsObjIso_inv_arrow {C₁ : Type*} [Category* C₁] {D₁ : Type*} [Category* D₁]
    (U : C₁ ⥤ D₁) [U.PreservesMonomorphisms] {Z : C₁} (P : Subobject Z) :
    (mapSubobjectsObjIso U P).inv ≫ ((mapSubobjects U Z).obj P).arrow = U.map P.arrow := by
  have := U.map_mono P.arrow
  simp [mapSubobjectsObjIso]

/-- **The image of a monomorphism is its source**, read on the image as a subobject:
`CategoryTheory.Limits.imageSubobjectIso` presents the subobject by the image and
`CategoryTheory.Limits.imageMonoIsoSource` identifies the image of a monomorphism with its
source. -/
noncomputable def imageSubobjectIsoSource {C₁ : Type*} [Category* C₁] {A B : C₁} (w : A ⟶ B)
    [HasImage w] (hw : Mono w) : ((imageSubobject w : C₁)) ≅ A :=
  have := hw
  imageSubobjectIso w ≪≫ imageMonoIsoSource w

/-- **`Stacks.GradedPieceImage.imageSubobjectIsoSource` is compatible with the inclusions**: the
inclusion of the image into `B`, read on the source, is the morphism itself. -/
@[reassoc]
theorem imageSubobjectIsoSource_inv_arrow {C₁ : Type*} [Category* C₁] {A B : C₁} (w : A ⟶ B)
    [HasImage w] (hw : Mono w) :
    (imageSubobjectIsoSource w hw).inv ≫ (imageSubobject w).arrow = w := by
  have := hw
  simp [imageSubobjectIsoSource]

/-- **A subobject known to be the image of a monomorphism `w`, read as its source and pushed
under a functor, has `w` for its inclusion**: the change of description of the subobject
(`CategoryTheory.Subobject.isoOfEq`) followed by
`Stacks.GradedPieceImage.imageSubobjectIsoSource`, carried along `U`, takes the inclusion of
`U(R)` to `U(w)`. -/
theorem map_imageSubobjectIsoSource_inv_arrow {C₁ : Type*} [Category* C₁] {D₁ : Type*}
    [Category* D₁] (U : C₁ ⥤ D₁) {Z A : C₁} (R : Subobject Z) (w : A ⟶ Z) {hi : HasImage w}
    (hw : Mono w) (h : R = imageSubobject w) :
    (U.mapIso (Subobject.isoOfEq R (imageSubobject w) h ≪≫
          imageSubobjectIsoSource w hw)).inv ≫ U.map R.arrow =
      U.map w :=
  Eq.trans (U.map_comp _ _).symm
    (congrArg U.map
      (Eq.trans (Category.assoc _ _ _)
        (Eq.trans (congrArg (fun u ↦ _ ≫ u) (Subobject.ofLE_arrow h.ge))
          (imageSubobjectIsoSource_inv_arrow w hw))))

end Stacks.GradedPieceImage

namespace Stacks.DeRhamSmooth

attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The wedge-product morphism cutting out the top step of the filtration of `Ω^k_{X/S}`**,

`⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} ⋀^0Ω_{X/S} ⟶ Ω^k_{X/S}`,

with its target transported along `k + 0 = k`. -/
abbrev cutProdWedgeHom (k : ℕ) :=
  _root_.SheafOfModules.prodWedgeHomOfEq
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
      (Scheme.Hom.relativeDifferentialsShortComplex f g).X₁)
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
      (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂)
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
      (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂)
    (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) k 0 k (by omega)

/-- **Restriction of scalars along `𝒪_X ⟶ (f ∘ g)^{-1}𝒪_S`**. -/
abbrev deRhamSmoothRestrictScalars :=
  _root_.SheafOfModules.restrictScalars.{u}
    (AlgebraicGeometry.SheafOfModules.underlyingRingHom
      (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g)))

/-- **The extension by zero of `Ω^•_{X/S}` in degree `k`**: the `ℤ`-indexed complex agrees with
the `ℕ`-indexed one in the degrees the latter has. -/
abbrev deRhamSmoothExtendXIso (k : ℕ) :=
  (AlgebraicGeometry.SheafOfModules.deRhamComplex
      (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential
        (Scheme.Hom.deRhamAlgebras (f ≫ g)))).extendXIso
    ComplexShape.embeddingUpNat (i := k) (i' := (k : ℤ)) rfl

/-- **In the degree of the cut the step of the filtration is the source of the wedge-product
morphism**: for `f : X ⟶ Y` smooth over a base `S`,

`(F^kΩ^•_{X/S})^k  ≅  (⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} ⋀^0Ω_{X/S})|_{(f∘g)^{-1}𝒪_S}`. -/
def filtrationXIsoCutWedgeSource [Smooth f] (k : ℕ) :
    ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).X (k : ℤ) ≅
      (deRhamSmoothRestrictScalars f g).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf)).obj
          ((_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
              (Scheme.Hom.relativeDifferentialsShortComplex f g).X₁).exteriorPower k,
            (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
              (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂).exteriorPower 0)) :=
  (Subobject.underlyingIso
      (((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f (k : ℤ))).symm ≪≫
    Subobject.isoOfEq _ _ (mk_ι_app_f_eq f g k k le_rfl) ≪≫
    Subobject.mapObjIso (deRhamSmoothExtendXIso f g k).inv _ ≪≫
    Stacks.GradedPieceImage.mapSubobjectsObjIso (deRhamSmoothRestrictScalars f g) _ ≪≫
    (deRhamSmoothRestrictScalars f g).mapIso (Subobject.isoOfEq _ _
      (_root_.SheafOfModules.exteriorImageFiltration_eq_imageSubobject _ _ _ k 0 k (by omega)) ≪≫
      Stacks.GradedPieceImage.imageSubobjectIsoSource (cutProdWedgeHom f g k)
        (AlgebraicGeometry.Scheme.Hom.mono_relativeDifferentialsProdWedgeHomOfEq_of_eq_zero
          f g k 0 k rfl (by omega)))

/-- **`Stacks.GradedPieceImage.mapSubobjectsObjIso_inv_arrow` for
`AlgebraicGeometry.SheafOfModules.exteriorPowerSubobjectRestriction`**: the inclusion of the
restriction of scalars of a subobject `P` of `Ω^k_{X/S}`, read on the restriction of scalars of
`P`, is the restriction of scalars of `P.arrow`. -/
@[reassoc]
theorem mapSubobjectsObjIso_inv_exteriorPowerRestriction_arrow (k : ℕ)
    (P : Subobject ((Scheme.Hom.deRhamAlgebras (f ≫ g)).exteriorPower k)) :
    (Stacks.GradedPieceImage.mapSubobjectsObjIso (deRhamSmoothRestrictScalars f g) P).inv ≫
        ((AlgebraicGeometry.SheafOfModules.exteriorPowerSubobjectRestriction
          (Scheme.Hom.deRhamAlgebras (f ≫ g)) k).obj P).arrow =
      (deRhamSmoothRestrictScalars f g).map P.arrow :=
  Stacks.GradedPieceImage.mapSubobjectsObjIso_inv_arrow _ _

/-- **`Stacks.DeRhamSmooth.filtrationXIsoCutWedgeSource` is compatible with the inclusions into
`Ω^k_{X/S}`**: read on the source of the wedge-product morphism, the inclusion of the degree-`k`
term of the `k`-th step of the filtration into the degree-`k` term of `Ω^•_{X/S}` **is** that
morphism, restricted to `(f∘g)^{-1}𝒪_S` and pushed into the extension by zero. -/
@[reassoc]
theorem filtrationXIsoCutWedgeSource_inv_arrow [Smooth f] (k : ℕ) :
    (filtrationXIsoCutWedgeSource f g k).inv ≫
        (((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f (k : ℤ)) =
      (deRhamSmoothRestrictScalars f g).map (cutProdWedgeHom f g k) ≫
        (deRhamSmoothExtendXIso f g k).inv := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun u ↦ _ ≫ u)
    (Subobject.underlyingIso_hom_comp_eq_mk
      (((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f (k : ℤ)))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun u ↦ _ ≫ u) (Subobject.ofLE_arrow _)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun u ↦ _ ≫ u)
    (Subobject.mapObjIso_inv_arrow (deRhamSmoothExtendXIso f g k).inv _)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun u ↦ _ ≫ u)
    (mapSubobjectsObjIso_inv_exteriorPowerRestriction_arrow_assoc f g k _
      (deRhamSmoothExtendXIso f g k).inv)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun u ↦ u ≫ (deRhamSmoothExtendXIso f g k).inv)
    (Stacks.GradedPieceImage.map_imageSubobjectIsoSource_inv_arrow
      (deRhamSmoothRestrictScalars f g) _ (cutProdWedgeHom f g k) _ _)

/-- **The source of the wedge-product morphism at the cut**:

`⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} ⋀^0Ω_{X/S}  ≅  f^*Ω^k_{Y/S} ⊗_{𝒪_X} Ω^0_{X/Y}`,

by [Stacks, Tag 01CI] (`AlgebraicGeometry.Scheme.Modules.exteriorPowerPullbackIso`) on the first
factor and the identification of both `⋀^0Ω_{X/S}` and `Ω^0_{X/Y}` with the structure sheaf on the
second. -/
def cutWedgeSourceIsoPullbackTensor (k : ℕ) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf)).obj
        ((_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
            (Scheme.Hom.relativeDifferentialsShortComplex f g).X₁).exteriorPower k,
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
            (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂).exteriorPower 0) ≅
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf)).obj
        ((Scheme.Modules.pullback f).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)),
          AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((0 : ℕ) : ℤ)) :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf)).mapIso
    (Iso.prod
      (Scheme.Modules.exteriorPowerPullbackIso f
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g) (k : ℤ)).symm
      ((_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂).exteriorPieceZeroIsoUnit ≪≫
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsZeroIso f).symm))

/-- **Stacks Project, Section 0FMK, in the degree of the cut.** For `f : X ⟶ Y` smooth over a
base `S` and a cut `k`, the degree-`k` term of the `k`-th graded piece of the filtration of
`Ω^•_{X/S}` by the forms pulled back from `Y` is the degree-`k` term of
`f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`:

`(gr^kΩ^•_{X/S})^k  ≅  (f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y})^k`. -/
def gradedPieceXIsoGradedTargetXAtCut [Smooth f] (k : ℕ) :
    (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).X (k : ℤ) ≅
      (gradedTargetComplex f g k).X (k : ℤ) :=
  gradedPieceXIsoFiltrationX f g (k : ℤ) (k : ℤ) le_rfl ≪≫
    filtrationXIsoCutWedgeSource f g k ≪≫
    (pushforward (toInverseImageBase (f ≫ g))).mapIso
      (cutWedgeSourceIsoPullbackTensor f g k) ≪≫
    (gradedSourceMixedTensorCoefficientIso f g k
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((0 : ℕ) : ℤ))).symm ≪≫
    (gradedTargetXIso f g k 0 k (by omega)).symm

end Stacks.DeRhamSmooth

end
