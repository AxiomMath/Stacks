module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedAbovePCellular
public import StacksFrontier.Deformation.ToposThickening.DerivedExtensionOfScalarsMinus
public import StacksFrontier.Deformation.ToposThickening.DerivedIdealTensorIdentification
public import StacksFrontier.Deformation.ToposThickening.DerivedReductionUnit
public import StacksFrontier.Deformation.ToposThickening.SquareZeroReductionSequence

/-!
# The reduction triangle of a square-zero thickening, computed by flat resolutions

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site, `I₀` a sheaf of
`O₀`-modules, and `0 ⟶ I₀|_O ⟶ O ⟶ O₀|_O ⟶ 0` a short exact sequence of sheaves of `O`-modules
whose second map is the structure map. For a complex `P` of `O`-modules with flat terms the
reduction sequence `0 ⟶ ((O₀ ⊗_O P) ⊗_{O₀} I₀)|_O ⟶ P ⟶ (O₀ ⊗_O P)|_O ⟶ 0` of
`StacksFrontier/Deformation/ToposThickening/SquareZeroReductionSequence.lean` is short exact, and
when `P` is moreover `P`-cellular for the flat modules (Stacks 0794), its three terms compute
`(K ⊗^L_O O₀ ⊗^L_{O₀} I₀)|_O`, `K` and `(K ⊗^L_O O₀)|_O` for `K = Q(P)`. Its distinguished
triangle, read through those identifications, is a triangle

`(K ⊗^L_O O₀ ⊗^L_{O₀} I₀)|_O ⟶ K ⟶ (K ⊗^L_O O₀)|_O ⟶ ((K ⊗^L_O O₀ ⊗^L_{O₀} I₀)|_O)⟦1⟧`

whose second morphism is the unit of the adjunction between derived base change and derived
restriction of scalars.

The triangle does not depend on the resolution: two `P`-cellular resolutions of `K` are joined
by a roof of quasi-isomorphisms between `P`-cellular complexes, the reduction sequence is natural
in the complex, and the identifications of its terms are natural too. So the triangle at any
`P`-cellular resolution is the one at a chosen resolution, which is what makes it a reduction
triangle in the sense of `Deformation.ComplexLift.DerivedReduction` that can be computed at
whichever resolution is at hand: `Deformation.ComplexLift.flatReduction_triangle_eq`.

## Main definitions

* `Deformation.ComplexLift.reductionTriangleAt`: the triangle attached to a `P`-cellular complex
  `P` and an isomorphism `Q(P) ≅ K`.
* `Deformation.ComplexLift.flatReduction`: **the reduction triangle of the square-zero
  sequence**, as a `Deformation.ComplexLift.DerivedReduction` for the derived base change of
  Stacks 0794 and the derived tensor product with `I₀`.

## Main results

* `Deformation.ComplexLift.unit_eq_reductionMapComplex`: the unit of the derived adjunction at
  `Q(P)` is the structure map `P ⟶ (O₀ ⊗_O P)|_O`, for `P`-cellular `P`.
* `Deformation.ComplexLift.reductionTriangleAt_eq`: the triangle does not depend on the
  resolution.
* `Deformation.ComplexLift.flatReduction_triangle_eq`: the reduction triangle of `K` is the
  triangle at any `P`-cellular resolution of `K`.

## References

* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StacksDraft.UnboundedLeftDerivedFunctor

universe d d₀ v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- A `P`-cellular complex of `O`-modules, `P` being the flat modules: the class of complexes on
which the derived base change of Stacks 0794 is computed degreewise. -/
abbrev IsFlatCellular
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) : Prop :=
  IsPCellular (flatObjects O) P

/-! ### The comparisons are invertible on cellular complexes -/

/-- The comparison `derivedExtensionOfScalarsCounit f` is an isomorphism at a `P`-cellular
complex. -/
theorem isIso_derivedExtensionOfScalarsCounit_app
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hP : IsFlatCellular P) :
    IsIso ((derivedExtensionOfScalarsCounit.{d, d₀} f).app P) := by
  have := isIso_derivedExtensionOfScalarsCounitHomotopy_app.{d, d₀} f _
    (cellular_quotient_obj O hP)
  dsimp only [derivedExtensionOfScalarsCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

/-- The comparison `derivedTensorRightCounit I₀` is an isomorphism at the base change
`O₀ ⊗_O P` of a `P`-cellular complex `P`. -/
theorem isIso_derivedTensorRightCounit_app_extensionOfScalars
    (I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hP : IsFlatCellular P) :
    IsIso ((derivedTensorRightCounit.{d₀} I₀).app
      ((extensionOfScalarsCochainComplex J f).obj P)) := by
  have := isIso_derivedTensorRightCounitHomotopy_app_extensionOfScalars.{d, d₀} f I₀ _
    (cellular_quotient_obj O hP)
  have : IsIso ((derivedTensorRightCounitHomotopy.{d₀} I₀).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((extensionOfScalarsCochainComplex J f).obj P))) := this
  dsimp only [derivedTensorRightCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

/-- A chain of four commuting squares, the last of which closes up to an isomorphism, collapses:
the abstract shape of the comparison of the unit of a derived adjunction with the degreewise unit,
stated with the objects abstract so that the different spellings of the same object of the
derived category meet only when it is applied. -/
theorem comp_chain_eq_comp_inv {D : Type*} [Category D] {X₀ X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ : D}
    (x : X₀ ⟶ X₁) (r₁ : X₁ ⟶ X₂) (r₂ : X₂ ⟶ X₃) (r₃ : X₃ ⟶ X₄) (i : X₀ ⟶ Y₁) (y : Y₁ ⟶ X₂)
    (v : Y₁ ⟶ Y₂) (b : Y₂ ⟶ X₃) (w : X₀ ⟶ Y₃) (i' : Y₃ ⟶ Y₂) (h : X₄ ≅ Y₃)
    (ha : x ≫ r₁ = i ≫ y) (hb : y ≫ r₂ = v ≫ b) (hc : i ≫ v = w ≫ i')
    (hd : i' ≫ b ≫ r₃ ≫ h.hom = 𝟙 Y₃) :
    x ≫ r₁ ≫ r₂ ≫ r₃ = w ≫ h.inv := by
  have hd' : i' ≫ b ≫ r₃ = h.inv := by
    rw [← Iso.comp_hom_eq_id h]
    simpa only [Category.assoc] using hd
  rw [reassoc_of% ha, reassoc_of% hb, reassoc_of% hc, hd']

/-! ### The unit of the derived adjunction on complexes -/

/-- **The unit of the derived adjunction, read on a complex.** At `Q(P)`, the unit of the
adjunction between derived base change and derived restriction of scalars, followed by the
comparison of derived base change with degreewise extension of scalars, is the degreewise unit
`P ⟶ (O₀ ⊗_O P)|_O` followed by the comparison of restriction of scalars on complexes and on
derived categories. -/
theorem derivedAdjunction_unit_app_comp_counit
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    (derivedAdjunction.{d, d₀} f).unit.app (DerivedCategory.Q.obj P) ≫
        (restrictionOnDerived.{d, d₀} f).map ((derivedExtensionOfScalarsCounit.{d, d₀} f).app P) =
      DerivedCategory.Q.map (reductionMapComplex (f := f) P) ≫
        ((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f)).mapDerivedCategoryFactors).inv.app
            ((extensionOfScalarsCochainComplex J f).obj P) := by
  have := isLeftDerivedFunctor_comp_derivedExtensionOfScalars.{d, d₀} f
    (restrictionOnDerived.{d, d₀} f)
  have hu : (derivedAdjunction.{d, d₀} f).unit =
      (extendRestrictAdjunctionHomotopy f).derivedη
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
          (ComplexShape.up ℤ))
        (derivedExtensionOfScalarsCounitHomotopy f) (restrictionOnDerivedComparison f) := rfl
  have hfac := Adjunction.derivedη_fac_app (extendRestrictAdjunctionHomotopy f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ))
    (derivedExtensionOfScalarsCounitHomotopy f) (restrictionOnDerivedComparison f)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)
  rw [← hu] at hfac
  have hc : (extendRestrictAdjunctionHomotopy f).unit.app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
          (ComplexShape.up ℤ)).obj P) =
      (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
          (ComplexShape.up ℤ)).map (reductionMapComplex (f := f) P) := rfl
  rw [hc] at hfac
  have hnatη : (derivedAdjunction.{d, d₀} f).unit.app (DerivedCategory.Q.obj P) ≫
      (restrictionOnDerived.{d, d₀} f).map ((derivedExtensionOfScalars.{d, d₀} f).map
        ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))).inv.app P)) =
      (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))).inv.app P ≫
        (derivedAdjunction.{d, d₀} f).unit.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) :=
    ((derivedAdjunction.{d, d₀} f).unit.naturality
      ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))).inv.app P)).symm
  have hnatQ : (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))).inv.app P ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (ComplexShape.up ℤ)).map
            (reductionMapComplex (f := f) P)) =
      DerivedCategory.Q.map (reductionMapComplex (f := f) P) ≫
        (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))).inv.app
          (((extensionOfScalars f ⋙ SheafOfModules.restrictScalars
            (ringSheafMapOf J f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    (DerivedCategory.quotientCompQhIso_inv_naturality _).symm
  have hbook := restrictionOnDerivedComparison_bookkeeping.{d, d₀} f P
  dsimp only [derivedExtensionOfScalarsCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  rw [Functor.map_comp, Functor.map_comp]
  exact comp_chain_eq_comp_inv _ _ _ _ _ _ _ _ _ _
    (((SheafOfModules.restrictScalars.{u}
      (ringSheafMapOf J f)).mapDerivedCategoryFactors).app
        ((extensionOfScalarsCochainComplex J f).obj P)) hnatη hfac hnatQ hbook

/-! ### The vertex identifications -/

section Vertices

variable (I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))

/-- The third vertex: `(Q(P) ⊗^L_O O₀)|_O ⟶ Q((O₀ ⊗_O P)|_O)`, natural in the complex `P`. Its
component at a `P`-cellular complex is invertible. -/
def vertexThree :
    DerivedCategory.Q ⋙ derivedExtensionOfScalars.{d, d₀} f ⋙ restrictionOnDerived.{d, d₀} f ⟶
      (reductionPart f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (derivedExtensionOfScalarsCounit.{d, d₀} f)
      (restrictionOnDerived.{d, d₀} f) ≫
    Functor.whiskerLeft (extensionOfScalarsCochainComplex J f)
      ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapDerivedCategoryFactors).hom

/-- The first vertex: `(Q(P) ⊗^L_O O₀ ⊗^L_{O₀} I₀)|_O ⟶ Q(((O₀ ⊗_O P) ⊗_{O₀} I₀)|_O)`, natural in
the complex `P`. Its component at a `P`-cellular complex is invertible. -/
def vertexOne :
    DerivedCategory.Q ⋙ derivedExtensionOfScalars.{d, d₀} f ⋙ derivedTensorRight.{d₀} I₀ ⋙
        restrictionOnDerived.{d, d₀} f ⟶
      (idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (derivedExtensionOfScalarsCounit.{d, d₀} f)
      (derivedTensorRight.{d₀} I₀ ⋙ restrictionOnDerived.{d, d₀} f) ≫
    Functor.whiskerLeft (extensionOfScalarsCochainComplex J f)
      (Functor.whiskerRight (derivedTensorRightCounit.{d₀} I₀) (restrictionOnDerived.{d, d₀} f)) ≫
    Functor.whiskerLeft (extensionOfScalarsCochainComplex J f ⋙
        (tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ))
      ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapDerivedCategoryFactors).hom

/-- The component of `vertexThree f` at `P` is the restriction of the base-change comparison at
`P` followed by the comparison of restriction of scalars with its derived functor. -/
theorem vertexThree_app
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    (vertexThree.{d, d₀} f).app P =
      (restrictionOnDerived.{d, d₀} f).map ((derivedExtensionOfScalarsCounit.{d, d₀} f).app P) ≫
        ((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f)).mapDerivedCategoryFactors).hom.app
            ((extensionOfScalarsCochainComplex J f).obj P) := rfl

/-- The component of `vertexThree f` at a `P`-cellular complex is an isomorphism. -/
theorem isIso_vertexThree_app
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hP : IsFlatCellular P) : IsIso ((vertexThree.{d, d₀} f).app P) := by
  have := isIso_derivedExtensionOfScalarsCounit_app.{d, d₀} f P hP
  rw [vertexThree_app]
  exact IsIso.comp_isIso' inferInstance (Iso.isIso_hom (((SheafOfModules.restrictScalars.{u}
    (ringSheafMapOf J f)).mapDerivedCategoryFactors).app
      ((extensionOfScalarsCochainComplex J f).obj P)))

/-- The component of `vertexOne f I₀` at a `P`-cellular complex is an isomorphism. -/
theorem isIso_vertexOne_app
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hP : IsFlatCellular P) : IsIso ((vertexOne.{d, d₀} f I₀).app P) := by
  have := isIso_derivedExtensionOfScalarsCounit_app.{d, d₀} f P hP
  have := isIso_derivedTensorRightCounit_app_extensionOfScalars.{d, d₀} f I₀ P hP
  dsimp only [vertexOne, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map]
  have h₂ : IsIso ((restrictionOnDerived.{d, d₀} f).map ((derivedTensorRightCounit.{d₀} I₀).app
      ((extensionOfScalarsCochainComplex J f).obj P))) := inferInstance
  refine IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h₂ ?_)
  exact Iso.isIso_hom (((SheafOfModules.restrictScalars.{u}
    (ringSheafMapOf J f)).mapDerivedCategoryFactors).app
      (((tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((extensionOfScalarsCochainComplex J f).obj P)))

/-- The unit of the derived adjunction at `Q(P)` is the structure map of the reduction
sequence, read through the third vertex identification. -/
theorem unit_comp_vertexThree_app
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    (derivedAdjunction.{d, d₀} f).unit.app (DerivedCategory.Q.obj P) ≫
        (vertexThree.{d, d₀} f).app P =
      DerivedCategory.Q.map (reductionMapComplex (f := f) P) := by
  rw [vertexThree_app]
  exact ((reassoc_of% (derivedAdjunction_unit_app_comp_counit.{d, d₀} f P))
    (((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapDerivedCategoryFactors).hom.app
      ((extensionOfScalarsCochainComplex J f).obj P))).trans
    ((Category.assoc _ _ _).trans <| (congrArg
      (fun k ↦ DerivedCategory.Q.map (reductionMapComplex (f := f) P) ≫ k)
      (((SheafOfModules.restrictScalars.{u}
        (ringSheafMapOf J f)).mapDerivedCategoryFactors).inv_hom_id_app
          ((extensionOfScalarsCochainComplex J f).obj P))).trans (Category.comp_id _))

end Vertices

/-! ### Cellular complexes have flat terms -/

omit [HasDerivedCategory (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf O))] in
/-- **The terms of a `P`-cellular complex are flat**: each is the colimit along `ℕ` of flat
terms, colimits of complexes being computed degreewise, and a colimit along `ℕ` of flat sheaves
of modules is flat (Stacks 03EU). -/
theorem flatObjects_X_of_isFlatCellular
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P) (n : ℤ) : flatObjects O (P.X n) := by
  obtain ⟨Q, g, c, hc, e, -, hQ, -⟩ := hP
  have := hasExactColimitsOfShape_nat (Stacks.SheafOfModules.Tensor.ringSheaf O)
  let D : ℕ ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
    Functor.ofSequence g ⋙ HomologicalComplex.eval _ _ n
  have hD : IsColimit ((HomologicalComplex.eval _ _ n).mapCocone c) := isColimitOfPreserves _ hc
  have hcol : flatObjects O (colimit D) :=
    Stacks.SheafOfModules.FlatCoproduct.isFlat_colimit_ofSize.{v', u', u} O D (fun k ↦ hQ k n)
  exact flatObjects_of_iso ((colimit.isColimit D).coconePointUniqueUpToIso hD ≪≫
    (HomologicalComplex.eval _ _ n).mapIso e) hcol

/-! ### The triangle at a cellular resolution -/

section Triangle

variable {I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
  (ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
  (hι : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f) = 0)
  (hS : (idealSequenceOf f I₀ ι hι).ShortExact)

/-- The first vertex identification at a cellular complex `P` and an isomorphism `Q(P) ≅ K`. -/
def vertexOneIso
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P)
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (w : DerivedCategory.Q.obj P ≅ K) :
    DerivedCategory.Q.obj (((idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      (restrictionOnDerived.{d, d₀} f).obj ((derivedTensorRight.{d₀} I₀).obj
        ((derivedExtensionOfScalars.{d, d₀} f).obj K)) :=
  haveI := isIso_vertexOne_app.{d, d₀} f I₀ P hP
  (asIso ((vertexOne.{d, d₀} f I₀).app P)).symm ≪≫
    (restrictionOnDerived.{d, d₀} f).mapIso ((derivedTensorRight.{d₀} I₀).mapIso
      ((derivedExtensionOfScalars.{d, d₀} f).mapIso w))

/-- The third vertex identification at a cellular complex `P` and an isomorphism `Q(P) ≅ K`. -/
def vertexThreeIso
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P)
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (w : DerivedCategory.Q.obj P ≅ K) :
    DerivedCategory.Q.obj (((reductionPart f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      (restrictionOnDerived.{d, d₀} f).obj ((derivedExtensionOfScalars.{d, d₀} f).obj K) :=
  haveI := isIso_vertexThree_app.{d, d₀} f P hP
  (asIso ((vertexThree.{d, d₀} f).app P)).symm ≪≫
    (restrictionOnDerived.{d, d₀} f).mapIso ((derivedExtensionOfScalars.{d, d₀} f).mapIso w)

/-- The inclusion of the ideal part `(K ⊗^L_O O₀ ⊗^L_{O₀} I₀)|_O ⟶ K`, computed at a cellular
complex `P` with `Q(P) ≅ K`. -/
def idealInclusionAt
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P)
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (w : DerivedCategory.Q.obj P ≅ K) :
    (restrictionOnDerived.{d, d₀} f).obj ((derivedTensorRight.{d₀} I₀).obj
        ((derivedExtensionOfScalars.{d, d₀} f).obj K)) ⟶ K :=
  (vertexOneIso.{d, d₀} f hP w).inv ≫ DerivedCategory.Q.map (idealPartInclComplex ι P) ≫ w.hom

/-- The connecting morphism `(K ⊗^L_O O₀)|_O ⟶ ((K ⊗^L_O O₀ ⊗^L_{O₀} I₀)|_O)⟦1⟧`, computed at a
cellular complex `P` with `Q(P) ≅ K`: the connecting morphism of the reduction sequence of `P`. -/
def connectingAt
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P)
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (w : DerivedCategory.Q.obj P ≅ K) :
    (restrictionOnDerived.{d, d₀} f).obj ((derivedExtensionOfScalars.{d, d₀} f).obj K) ⟶
      ((restrictionOnDerived.{d, d₀} f).obj ((derivedTensorRight.{d₀} I₀).obj
        ((derivedExtensionOfScalars.{d, d₀} f).obj K)))⟦(1 : ℤ)⟧ :=
  (vertexThreeIso.{d, d₀} f hP w).inv ≫
    DerivedCategory.triangleOfSESδ
      (shortExact_reductionSequence ι hι hS P (flatObjects_X_of_isFlatCellular hP)) ≫
    ((vertexOneIso.{d, d₀} f hP w).hom)⟦(1 : ℤ)⟧'

/-- The structure map of the reduction sequence of a cellular `P` is the unit of the derived
adjunction at `K ≅ Q(P)`, read through the third vertex identification. -/
theorem reductionMap_comp_vertexThreeIso
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P)
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (w : DerivedCategory.Q.obj P ≅ K) :
    DerivedCategory.Q.map (reductionMapComplex (f := f) P) ≫
        (vertexThreeIso.{d, d₀} f hP w).hom =
      w.hom ≫ (derivedAdjunction.{d, d₀} f).unit.app K := by
  have := isIso_vertexThree_app.{d, d₀} f P hP
  have hu := unit_comp_vertexThree_app.{d, d₀} f P
  have hnat := (derivedAdjunction.{d, d₀} f).unit.naturality w.hom
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hnat
  dsimp only [vertexThreeIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom]
  rw [← hu, Category.assoc, IsIso.hom_inv_id_assoc, hnat]

/-- **The reduction triangle at a cellular resolution is distinguished.** -/
theorem reductionTriangleAt_distinguished
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P)
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (w : DerivedCategory.Q.obj P ≅ K) :
    Triangle.mk (idealInclusionAt.{d, d₀} f ι hP w) ((derivedAdjunction.{d, d₀} f).unit.app K)
        (connectingAt.{d, d₀} f ι hι hS hP w) ∈ distTriang _ :=
  isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished
      (shortExact_reductionSequence ι hι hS P (flatObjects_X_of_isFlatCellular hP))) _
    (transportTriangleIso (DerivedCategory.triangleOfSES
        (shortExact_reductionSequence ι hι hS P (flatObjects_X_of_isFlatCellular hP)))
      (vertexOneIso.{d, d₀} f hP w) w (vertexThreeIso.{d, d₀} f hP w)
      ((derivedAdjunction.{d, d₀} f).unit.app K)
      (reductionMap_comp_vertexThreeIso.{d, d₀} f hP w))

/-! ### Independence of the resolution -/

/-- Naturality of a transformation `α : Q ⋙ L ⟶ T` at invertible components, written for the
inverse of the component followed by `L` applied to a morphism out of `Q.obj P'`. -/
private theorem inv_app_comp_map_comp {X D E : Type*} [Category X] [Category D] [Category E]
    (Q : X ⥤ D) (L : D ⥤ E) (T : X ⥤ E) (α : Q ⋙ L ⟶ T) {P P' : X} {K : D} (g : P ⟶ P')
    (w' : Q.obj P' ⟶ K) [IsIso (α.app P)] [IsIso (α.app P')] :
    inv (α.app P) ≫ L.map (Q.map g ≫ w') = T.map g ≫ inv (α.app P') ≫ L.map w' := by
  have h : inv (α.app P) ≫ L.map (Q.map g) = T.map g ≫ inv (α.app P') := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
    exact α.naturality g
  rw [Functor.map_comp, ← Category.assoc, h, Category.assoc]

section Independence

variable {P P' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
  (hP : IsFlatCellular P) (hP' : IsFlatCellular P') (g : P ⟶ P') [IsIso (DerivedCategory.Q.map g)]
  {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
  (w' : DerivedCategory.Q.obj P' ≅ K)

include hP' in
/-- The first vertex identification at `P`, along a quasi-isomorphism `g : P ⟶ P'` of cellular
complexes, is the image of `g` followed by the first vertex identification at `P'`. -/
theorem vertexOneIso_hom_of_hom :
    (vertexOneIso.{d, d₀} (I₀ := I₀) f hP (asIso (DerivedCategory.Q.map g) ≪≫ w')).hom =
      DerivedCategory.Q.map (((idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫
        (vertexOneIso.{d, d₀} f hP' w').hom := by
  have := isIso_vertexOne_app.{d, d₀} f I₀ P hP
  have := isIso_vertexOne_app.{d, d₀} f I₀ P' hP'
  exact inv_app_comp_map_comp DerivedCategory.Q (derivedExtensionOfScalars.{d, d₀} f ⋙
    derivedTensorRight.{d₀} I₀ ⋙ restrictionOnDerived.{d, d₀} f) _ (vertexOne.{d, d₀} f I₀) g w'.hom

include hP' in
/-- The third vertex identification at `P`, along a quasi-isomorphism `g : P ⟶ P'` of cellular
complexes, is the image of `g` followed by the third vertex identification at `P'`. -/
theorem vertexThreeIso_hom_of_hom :
    (vertexThreeIso.{d, d₀} f hP (asIso (DerivedCategory.Q.map g) ≪≫ w')).hom =
      DerivedCategory.Q.map (((reductionPart f).mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫
        (vertexThreeIso.{d, d₀} f hP' w').hom := by
  have := isIso_vertexThree_app.{d, d₀} f P hP
  have := isIso_vertexThree_app.{d, d₀} f P' hP'
  exact inv_app_comp_map_comp DerivedCategory.Q (derivedExtensionOfScalars.{d, d₀} f ⋙
    restrictionOnDerived.{d, d₀} f) _ (vertexThree.{d, d₀} f) g w'.hom

/-- The inclusion of the ideal part computed at `P` is the one computed at `P'`, along a
quasi-isomorphism `P ⟶ P'` of cellular complexes. -/
theorem idealInclusionAt_of_hom :
    idealInclusionAt.{d, d₀} f ι hP (asIso (DerivedCategory.Q.map g) ≪≫ w') =
      idealInclusionAt.{d, d₀} f ι hP' w' := by
  dsimp only [idealInclusionAt]
  rw [← cancel_epi (vertexOneIso.{d, d₀} f hP (asIso (DerivedCategory.Q.map g) ≪≫ w')).hom,
    Iso.hom_inv_id_assoc, vertexOneIso_hom_of_hom.{d, d₀} f hP hP' g w', Category.assoc,
    Iso.hom_inv_id_assoc, Iso.trans_hom, asIso_hom, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, idealPartInclComplex_naturality]

/-- The connecting morphism computed at `P` is the one computed at `P'`, along a
quasi-isomorphism `P ⟶ P'` of cellular complexes. -/
theorem connectingAt_of_hom :
    connectingAt.{d, d₀} f ι hι hS hP (asIso (DerivedCategory.Q.map g) ≪≫ w') =
      connectingAt.{d, d₀} f ι hι hS hP' w' := by
  dsimp only [connectingAt]
  rw [← cancel_epi (vertexThreeIso.{d, d₀} f hP (asIso (DerivedCategory.Q.map g) ≪≫ w')).hom,
    Iso.hom_inv_id_assoc, vertexThreeIso_hom_of_hom.{d, d₀} f hP hP' g w', Category.assoc,
    Iso.hom_inv_id_assoc, vertexOneIso_hom_of_hom.{d, d₀} f hP hP' g w', Functor.map_comp,
    ← Category.assoc, ← Category.assoc]
  congr 1
  exact DerivedCategory.triangleOfSESδ_naturality _ _ (reductionSequenceMap ι hι g)

end Independence

/-! ### Cellular resolutions -/

omit [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))] in
/-- Every complex of `O`-modules receives a quasi-isomorphism from a `P`-cellular complex
(Stacks 06XX). -/
theorem exists_isFlatCellular_quasiIso
    (X : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    ∃ (S : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
      (_ : IsFlatCellular S) (t : S ⟶ X), QuasiIso t := by
  obtain ⟨Y, hY, s, hs⟩ := exists_cellular_quasiIso O
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj X)
  obtain ⟨S, hS, ⟨eY⟩⟩ := hY
  obtain ⟨t, ht⟩ :=
    (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ)).map_surjective (eY.inv ≫ s)
  refine ⟨S, hS, t, ?_⟩
  rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff, ht]
  exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ eY.inv) hs

/-- Every object of `D(O)` has a `P`-cellular resolution. -/
theorem exists_isFlatCellular_iso
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))) :
    ∃ (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ),
      IsFlatCellular P ∧ Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  obtain ⟨S, hS, t, ht⟩ := exists_isFlatCellular_quasiIso (DerivedCategory.Q.objPreimage K)
  have : IsIso (DerivedCategory.Q.map t) := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := t)).2 ht
  exact ⟨S, hS, ⟨asIso (DerivedCategory.Q.map t) ≪≫ DerivedCategory.Q.objObjPreimageIso K⟩⟩

/-- A morphism `Q(P) ⟶ Q(P')` is represented by a morphism of cellular complexes after replacing
`P` by a cellular complex mapping to it by a quasi-isomorphism. -/
private theorem exists_isFlatCellular_roof_of_hom
    {P P' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (m : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj P') :
    ∃ (W : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
      (_hW : IsFlatCellular W) (a : W ⟶ P) (b : W ⟶ P') (_ : IsIso (DerivedCategory.Q.map a)),
      DerivedCategory.Q.map b = DerivedCategory.Q.map a ≫ m := by
  obtain ⟨X', s, hs, g, hfac⟩ := DerivedCategory.right_fac m
  obtain ⟨W, hW, t, ht⟩ := exists_isFlatCellular_quasiIso X'
  have : IsIso (DerivedCategory.Q.map t) := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := t)).2 ht
  refine ⟨W, hW, t ≫ s, t ≫ g, ?_, ?_⟩
  · rw [Functor.map_comp]; infer_instance
  · rw [hfac]; simp

section General

variable {P P' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
  (hP : IsFlatCellular P) (hP' : IsFlatCellular P')
  {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
  (w : DerivedCategory.Q.obj P ≅ K) (w' : DerivedCategory.Q.obj P' ≅ K)

include hP hP' in
/-- Two cellular resolutions of `K` are joined by a roof of quasi-isomorphisms from a cellular
complex, compatible with the two identifications with `K`. -/
theorem exists_isFlatCellular_roof :
    ∃ (W : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
      (_hW : IsFlatCellular W) (a : W ⟶ P) (b : W ⟶ P') (_ : IsIso (DerivedCategory.Q.map a))
      (_ : IsIso (DerivedCategory.Q.map b)),
      DerivedCategory.Q.map a ≫ w.hom = DerivedCategory.Q.map b ≫ w'.hom := by
  obtain ⟨W, hW, a, b, ha, hb⟩ := exists_isFlatCellular_roof_of_hom (w.hom ≫ w'.inv)
  have : IsIso (DerivedCategory.Q.map b) := by rw [hb]; infer_instance
  exact ⟨W, hW, a, b, ha, this, by simp [hb]⟩

/-- A construction on cellular resolutions of `K` that is invariant under quasi-isomorphisms of
cellular complexes does not depend on the resolution. -/
private theorem eq_of_forall_asIso_comp {T : Sort*}
    (F : ∀ {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ},
      IsFlatCellular P → (DerivedCategory.Q.obj P ≅ K) → T)
    (h : ∀ {P P' : CochainComplex (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ} (hP : IsFlatCellular P)
      (hP' : IsFlatCellular P') (g : P ⟶ P') [IsIso (DerivedCategory.Q.map g)]
      (w' : DerivedCategory.Q.obj P' ≅ K), F hP (asIso (DerivedCategory.Q.map g) ≪≫ w') = F hP' w')
    {P P' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P) (hP' : IsFlatCellular P')
    (w : DerivedCategory.Q.obj P ≅ K) (w' : DerivedCategory.Q.obj P' ≅ K) : F hP w = F hP' w' := by
  obtain ⟨W, hW, a, b, ha, hb, hab⟩ := exists_isFlatCellular_roof.{d} hP hP' w w'
  rw [← h hW hP a w, ← h hW hP' b w']
  exact congrArg (F hW) (Iso.ext hab)

/-- **The connecting morphism does not depend on the cellular resolution.** -/
theorem connectingAt_eq :
    connectingAt.{d, d₀} f ι hι hS hP w = connectingAt.{d, d₀} f ι hι hS hP' w' :=
  eq_of_forall_asIso_comp (fun hP w ↦ connectingAt.{d, d₀} f ι hι hS hP w) (fun hP hP' g _ w' ↦
    connectingAt_of_hom.{d, d₀} f ι hι hS hP hP' g w') hP hP' w w'

/-- **The inclusion of the ideal part does not depend on the cellular resolution.** -/
theorem idealInclusionAt_eq :
    idealInclusionAt.{d, d₀} f ι hP w = idealInclusionAt.{d, d₀} f ι hP' w' :=
  eq_of_forall_asIso_comp (fun hP w ↦ idealInclusionAt.{d, d₀} f ι hP w) (fun hP hP' g _ w' ↦
    idealInclusionAt_of_hom.{d, d₀} f ι hP hP' g w') hP hP' w w'

end General

/-! ### The reduction triangle -/

/-- The chosen cellular resolution of an object of `D(O)`. -/
def cellularModel
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ :=
  (exists_isFlatCellular_iso K).choose

/-- The chosen cellular resolution of `K` is `P`-cellular. -/
theorem isFlatCellular_cellularModel
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))) :
    IsFlatCellular (cellularModel K) :=
  (exists_isFlatCellular_iso K).choose_spec.1

/-- The chosen identification of the chosen cellular resolution with the object. -/
def cellularModelIso
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))) :
    DerivedCategory.Q.obj (cellularModel K) ≅ K :=
  (exists_isFlatCellular_iso K).choose_spec.2.some

/-- **The reduction triangle of a square-zero thickening**, computed by cellular resolutions:
for every `K ∈ D(O)` the triangle

`(K ⊗^L_O O₀ ⊗^L_{O₀} I₀)|_O ⟶ K ⟶ (K ⊗^L_O O₀)|_O ⟶ ((K ⊗^L_O O₀ ⊗^L_{O₀} I₀)|_O)⟦1⟧`

of the reduction sequence `0 ⟶ ((O₀ ⊗_O P) ⊗_{O₀} I₀)|_O ⟶ P ⟶ (O₀ ⊗_O P)|_O ⟶ 0` of a
`P`-cellular resolution `P` of `K`, whose second morphism is the unit of the adjunction between
derived base change and restriction of scalars. By
`Deformation.ComplexLift.flatReduction_connecting` and
`Deformation.ComplexLift.flatReduction_idealInclusion` it may be computed at any cellular
resolution of `K`. -/
def flatReduction :
    DerivedReduction (derivedExtensionOfScalarsData.{d, d₀} f) (derivedTensorRight.{d₀} I₀) where
  restriction := restrictionOnDerived.{d, d₀} f
  additive := inferInstance
  commShift := inferInstance
  adjunction := derivedAdjunction.{d, d₀} f
  idealInclusion K := idealInclusionAt.{d, d₀} f ι (isFlatCellular_cellularModel K)
    (cellularModelIso K)
  connecting K := connectingAt.{d, d₀} f ι hι hS (isFlatCellular_cellularModel K)
    (cellularModelIso K)
  distinguished K := reductionTriangleAt_distinguished.{d, d₀} f ι hι hS
    (isFlatCellular_cellularModel K) (cellularModelIso K)

/-- The restriction functor of `flatReduction` is restriction of scalars on derived categories. -/
theorem flatReduction_restriction :
    (flatReduction.{d, d₀} f ι hι hS).restriction = restrictionOnDerived.{d, d₀} f := rfl

/-- The adjunction of `flatReduction` is the derived adjunction between base change and
restriction of scalars. -/
theorem flatReduction_adjunction :
    (flatReduction.{d, d₀} f ι hι hS).adjunction = derivedAdjunction.{d, d₀} f := rfl

/-- The connecting morphism of the reduction triangle of `K`, computed at any cellular
resolution of `K`. -/
theorem flatReduction_connecting
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P)
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (w : DerivedCategory.Q.obj P ≅ K) :
    (flatReduction.{d, d₀} f ι hι hS).connecting K = connectingAt.{d, d₀} f ι hι hS hP w :=
  connectingAt_eq.{d, d₀} f ι hι hS _ hP _ w

/-- The inclusion of the ideal part of `K`, computed at any cellular resolution of `K`. -/
theorem flatReduction_idealInclusion
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P)
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (w : DerivedCategory.Q.obj P ≅ K) :
    (flatReduction.{d, d₀} f ι hι hS).idealInclusion K = idealInclusionAt.{d, d₀} f ι hP w :=
  idealInclusionAt_eq.{d, d₀} f ι _ hP _ w

/-! ### Naturality -/

section Naturality

variable {P P' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
  (hP : IsFlatCellular P) (hP' : IsFlatCellular P') (g : P ⟶ P')
  {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
  (w : DerivedCategory.Q.obj P ≅ K) (w' : DerivedCategory.Q.obj P' ≅ K') (φ : K ⟶ K')
  (hφ : DerivedCategory.Q.map g ≫ w'.hom = w.hom ≫ φ)

include hφ

/-- The first vertex identification is natural along a morphism `g : P ⟶ P'` of cellular
complexes lifting a morphism `φ : K ⟶ K'`. -/
theorem vertexOneIso_hom_naturality :
    (vertexOneIso.{d, d₀} (I₀ := I₀) f hP w).hom ≫
        (restrictionOnDerived.{d, d₀} f).map ((derivedTensorRight.{d₀} I₀).map
          ((derivedExtensionOfScalars.{d, d₀} f).map φ)) =
      DerivedCategory.Q.map (((idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫
        (vertexOneIso.{d, d₀} f hP' w').hom := by
  have := isIso_vertexOne_app.{d, d₀} f I₀ P hP
  have := isIso_vertexOne_app.{d, d₀} f I₀ P' hP'
  dsimp only [vertexOneIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← hφ]
  exact inv_app_comp_map_comp DerivedCategory.Q (derivedExtensionOfScalars.{d, d₀} f ⋙
    derivedTensorRight.{d₀} I₀ ⋙ restrictionOnDerived.{d, d₀} f) _ (vertexOne.{d, d₀} f I₀) g w'.hom

/-- The third vertex identification is natural along a morphism `g : P ⟶ P'` of cellular
complexes lifting a morphism `φ : K ⟶ K'`. -/
theorem vertexThreeIso_hom_naturality :
    (vertexThreeIso.{d, d₀} f hP w).hom ≫
        (restrictionOnDerived.{d, d₀} f).map ((derivedExtensionOfScalars.{d, d₀} f).map φ) =
      DerivedCategory.Q.map (((reductionPart f).mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫
        (vertexThreeIso.{d, d₀} f hP' w').hom := by
  have := isIso_vertexThree_app.{d, d₀} f P hP
  have := isIso_vertexThree_app.{d, d₀} f P' hP'
  dsimp only [vertexThreeIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ← hφ]
  exact inv_app_comp_map_comp DerivedCategory.Q (derivedExtensionOfScalars.{d, d₀} f ⋙
    restrictionOnDerived.{d, d₀} f) _ (vertexThree.{d, d₀} f) g w'.hom

/-- **The inclusion of the ideal part is natural** along a morphism of cellular complexes. -/
theorem idealInclusionAt_naturality :
    idealInclusionAt.{d, d₀} f ι hP w ≫ φ =
      (restrictionOnDerived.{d, d₀} f).map ((derivedTensorRight.{d₀} I₀).map
          ((derivedExtensionOfScalars.{d, d₀} f).map φ)) ≫
        idealInclusionAt.{d, d₀} f ι hP' w' := by
  dsimp only [idealInclusionAt]
  rw [← cancel_epi (vertexOneIso.{d, d₀} f hP w).hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% (vertexOneIso_hom_naturality.{d, d₀} f hP hP' g w w' φ hφ), Iso.hom_inv_id_assoc,
    ← hφ, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, idealPartInclComplex_naturality]

/-- **The connecting morphism is natural** along a morphism of cellular complexes. -/
theorem connectingAt_naturality :
    connectingAt.{d, d₀} f ι hι hS hP w ≫
        ((restrictionOnDerived.{d, d₀} f).map ((derivedTensorRight.{d₀} I₀).map
          ((derivedExtensionOfScalars.{d, d₀} f).map φ)))⟦(1 : ℤ)⟧' =
      (restrictionOnDerived.{d, d₀} f).map ((derivedExtensionOfScalars.{d, d₀} f).map φ) ≫
        connectingAt.{d, d₀} f ι hι hS hP' w' := by
  dsimp only [connectingAt]
  rw [← cancel_epi (vertexThreeIso.{d, d₀} f hP w).hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% (vertexThreeIso_hom_naturality.{d, d₀} f hP hP' g w w' φ hφ),
    Iso.hom_inv_id_assoc, ← Functor.map_comp,
    vertexOneIso_hom_naturality.{d, d₀} f hP hP' g w w' φ hφ, Functor.map_comp,
    ← Category.assoc, ← Category.assoc]
  congr 1
  exact DerivedCategory.triangleOfSESδ_naturality _ _ (reductionSequenceMap ι hι g)

end Naturality

/-- A morphism of `D(O)` between objects with cellular resolutions is represented, after
replacing the first resolution, by a morphism of cellular complexes. -/
theorem exists_isFlatCellular_hom
    {P P' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (w : DerivedCategory.Q.obj P ≅ K) (w' : DerivedCategory.Q.obj P' ≅ K') (φ : K ⟶ K') :
    ∃ (W : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
      (_hW : IsFlatCellular W) (a : W ⟶ P) (b : W ⟶ P') (_ : IsIso (DerivedCategory.Q.map a)),
      DerivedCategory.Q.map b ≫ w'.hom = (asIso (DerivedCategory.Q.map a) ≪≫ w).hom ≫ φ := by
  obtain ⟨W, hW, a, b, ha, hb⟩ := exists_isFlatCellular_roof_of_hom (w.hom ≫ φ ≫ w'.inv)
  exact ⟨W, hW, a, b, ha, by simp [hb]⟩

/-- **The reduction triangle is natural**: the inclusion of the ideal part. -/
theorem flatReduction_idealInclusion_naturality
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (φ : K ⟶ K') :
    (flatReduction.{d, d₀} f ι hι hS).idealInclusion K ≫ φ =
      (restrictionOnDerived.{d, d₀} f).map ((derivedTensorRight.{d₀} I₀).map
          ((derivedExtensionOfScalars.{d, d₀} f).map φ)) ≫
        (flatReduction.{d, d₀} f ι hι hS).idealInclusion K' := by
  obtain ⟨W, hW, a, b, ha, hab⟩ := exists_isFlatCellular_hom.{d} (cellularModelIso K)
    (cellularModelIso K') φ
  rw [flatReduction_idealInclusion.{d, d₀} f ι hι hS hW (asIso (DerivedCategory.Q.map a) ≪≫
      cellularModelIso K),
    flatReduction_idealInclusion.{d, d₀} f ι hι hS (isFlatCellular_cellularModel K')
      (cellularModelIso K')]
  exact idealInclusionAt_naturality.{d, d₀} f ι hW (isFlatCellular_cellularModel K') b _ _ φ hab

/-- **The reduction triangle is natural**: the connecting morphism. -/
theorem flatReduction_connecting_naturality
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (φ : K ⟶ K') :
    (flatReduction.{d, d₀} f ι hι hS).connecting K ≫
        ((restrictionOnDerived.{d, d₀} f).map ((derivedTensorRight.{d₀} I₀).map
          ((derivedExtensionOfScalars.{d, d₀} f).map φ)))⟦(1 : ℤ)⟧' =
      (restrictionOnDerived.{d, d₀} f).map ((derivedExtensionOfScalars.{d, d₀} f).map φ) ≫
        (flatReduction.{d, d₀} f ι hι hS).connecting K' := by
  obtain ⟨W, hW, a, b, ha, hab⟩ := exists_isFlatCellular_hom.{d} (cellularModelIso K)
    (cellularModelIso K') φ
  rw [flatReduction_connecting.{d, d₀} f ι hι hS hW (asIso (DerivedCategory.Q.map a) ≪≫
      cellularModelIso K),
    flatReduction_connecting.{d, d₀} f ι hι hS (isFlatCellular_cellularModel K')
      (cellularModelIso K')]
  exact connectingAt_naturality.{d, d₀} f ι hι hS hW (isFlatCellular_cellularModel K') b _ _ φ hab

end Triangle

end Deformation.ComplexLift

end
