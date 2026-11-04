module

public import StacksFrontier.Deformation.ToposThickening.DerivedLiftConnectingClass
public import StacksFrontier.Deformation.ToposThickening.SquareZeroReductionTriangle

/-!
# Cellular models of lifts, and their connecting classes

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site with a square-zero ideal
sequence `0 ⟶ I₀|_O ⟶ O ⟶ O₀|_O ⟶ 0`, and let `(K, α)` be a lift of `K₀ ∈ D⁻(O₀)` for the derived
base change of Stacks 0794. A *cellular model* of the lift is a cellular complex `P` of
`O`-modules with `Q(P) ≅ K`; the derived base change of `Q(P)` is then the degreewise extension of
scalars `P₀ = O₀ ⊗_O P`, so the model identifies `Q(P₀)` with `K₀`.

The connecting class of the lift, for the reduction triangle
`Deformation.ComplexLift.flatReduction`, is then the connecting morphism of the reduction
sequence `0 ⟶ (P₀ ⊗_{O₀} I₀)|_O ⟶ P ⟶ P₀|_O ⟶ 0` of `P`, transported along that identification:
`Deformation.ComplexLift.connectingClass_flatReduction_eq`. Two lifts are compared through models
joined by a morphism of complexes `P'₀ ⟶ P₀` over `K₀`; such models always exist, by the
factorization of Tag 0DIX: `Deformation.ComplexLift.exists_models_hom`.

## Main definitions

* `Deformation.ComplexLift.modelIso`: the identification `Q(P₀) ≅ K₀` attached to a model.
* `Deformation.ComplexLift.modelIdealIso`: the identification
  `Q(P₀ ⊗_{O₀} I₀) ≅ K₀ ⊗^L_{O₀} I₀` attached to a model.

## Main results

* `Deformation.ComplexLift.connectingClass_flatReduction_eq`: the connecting class computed at a
  model.
* `Deformation.ComplexLift.exists_models_hom`: two lifts have models joined by a morphism of
  their reductions over `K₀`.

## References

* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
* [Stacks Project, Tag 0DIX](https://stacks.math.columbia.edu/tag/0DIX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe d d₀ v' u u'

namespace Deformation.ComplexLift

attribute [-instance] CategoryTheory.catToReflQuiver

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
variable {I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
  {K₀ : DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))}

/-- The inverse of a composite with an isomorphism, with the objects abstract. -/
theorem inv_comp_iso_hom' {D : Type*} [Category D] {X Y Z : D} (a : X ⟶ Y) [IsIso a]
    (e : Y ≅ Z) : inv (a ≫ e.hom) = e.inv ≫ inv a := by simp

/-- The inverse of a threefold composite ending with an isomorphism, with the objects
abstract. -/
theorem inv_comp_comp_iso_hom' {D : Type*} [Category D] {X Y Y' Z : D} (a : X ⟶ Y) (b : Y ⟶ Y')
    [IsIso a] [IsIso b] (e : Y' ≅ Z) :
    inv (a ≫ b ≫ e.hom) = e.inv ≫ inv b ≫ inv a := by simp

/-- Associativity of a fourfold composite, with the objects abstract. -/
theorem comp_assoc₄' {D : Type*} [Category D] {X₁ X₂ X₃ X₄ X₅ : D} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃)
    (c : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) : (a ≫ b ≫ c) ≫ e = a ≫ b ≫ c ≫ e := by simp

/-- The comparison of restriction of scalars on complexes and on derived categories, stated for
`Deformation.ComplexLift.restrictionOnDerived`. -/
abbrev restrictionFactors :
    DerivedCategory.Q ⋙ restrictionOnDerived.{d, d₀} f ≅
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapDerivedCategoryFactors

/-- The component of `vertexThree` at a complex `P`, as the restriction of the derived base
change counit at `P` followed by the comparison `restrictionFactors`. -/
theorem vertexThree_app'
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    (vertexThree.{d, d₀} f).app P =
      (restrictionOnDerived.{d, d₀} f).map ((derivedExtensionOfScalarsCounit.{d, d₀} f).app P) ≫
        (restrictionFactors.{d, d₀} f).hom.app ((extensionOfScalarsCochainComplex J f).obj P) :=
  rfl

/-- The component of `vertexOne` at a complex `P`, as the restriction of the derived base change
counit tensored with `I₀`, then of the derived tensor counit, then the comparison
`restrictionFactors`. -/
theorem vertexOne_app' (I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    (vertexOne.{d, d₀} f I₀).app P =
      (restrictionOnDerived.{d, d₀} f).map ((derivedTensorRight.{d₀} I₀).map
          ((derivedExtensionOfScalarsCounit.{d, d₀} f).app P)) ≫
        (restrictionOnDerived.{d, d₀} f).map
          ((derivedTensorRightCounit.{d₀} I₀).app ((extensionOfScalarsCochainComplex J f).obj P)) ≫
        (restrictionFactors.{d, d₀} f).hom.app
          (((tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((extensionOfScalarsCochainComplex J f).obj P)) := rfl

/-- The identification `Q(P₀) ≅ K ⊗^L_O O₀` attached to a cellular resolution `w : Q(P) ≅ K`:
the comparison of derived base change with degreewise extension of scalars, then `w`. -/
def baseModelIso
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P)
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (w : DerivedCategory.Q.obj P ≅ K) :
    DerivedCategory.Q.obj ((extensionOfScalarsCochainComplex J f).obj P) ≅
      (derivedExtensionOfScalars.{d, d₀} f).obj K :=
  haveI := isIso_derivedExtensionOfScalarsCounit_app.{d, d₀} f P hP
  (asIso ((derivedExtensionOfScalarsCounit.{d, d₀} f).app P)).symm ≪≫
    (derivedExtensionOfScalars.{d, d₀} f).mapIso w

/-- The forward map of `baseModelIso` is the inverse of the derived base change counit at `P`
followed by the base change of `w`. -/
theorem baseModelIso_hom
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P)
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (w : DerivedCategory.Q.obj P ≅ K) :
    (baseModelIso.{d, d₀} f hP w).hom =
      @inv _ _ _ _ ((derivedExtensionOfScalarsCounit.{d, d₀} f).app P)
          (isIso_derivedExtensionOfScalarsCounit_app.{d, d₀} f P hP) ≫
        (derivedExtensionOfScalars.{d, d₀} f).map w.hom := rfl

/-- The derived base change counit at `P` followed by `baseModelIso` is the base change of `w`. -/
theorem counit_comp_baseModelIso_hom
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P)
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (w : DerivedCategory.Q.obj P ≅ K) :
    (derivedExtensionOfScalarsCounit.{d, d₀} f).app P ≫ (baseModelIso.{d, d₀} f hP w).hom =
      (derivedExtensionOfScalars.{d, d₀} f).map w.hom := by
  simp [baseModelIso]

/-- For a flat cellular complex `P`, the inverse of the component of `vertexThree` at `P`, as the
inverse comparison `restrictionFactors` followed by the restriction of the inverse counit. -/
theorem inv_vertexThree_app
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P) :
    haveI := isIso_vertexThree_app.{d, d₀} f P hP
    haveI := isIso_derivedExtensionOfScalarsCounit_app.{d, d₀} f P hP
    inv ((vertexThree.{d, d₀} f).app P) =
      (restrictionFactors.{d, d₀} f).inv.app ((extensionOfScalarsCochainComplex J f).obj P) ≫
        (restrictionOnDerived.{d, d₀} f).map
          (inv ((derivedExtensionOfScalarsCounit.{d, d₀} f).app P)) := by
  have := isIso_vertexThree_app.{d, d₀} f P hP
  have := isIso_derivedExtensionOfScalarsCounit_app.{d, d₀} f P hP
  simp only [vertexThree_app']
  rw [CategoryTheory.Functor.map_inv]
  exact inv_comp_iso_hom' _ ((restrictionFactors.{d, d₀} f).app _)

/-- The third vertex identification, through `baseModelIso`. -/
theorem vertexThreeIso_hom_eq
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P)
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (w : DerivedCategory.Q.obj P ≅ K) :
    (vertexThreeIso.{d, d₀} f hP w).hom =
      (restrictionFactors.{d, d₀} f).inv.app ((extensionOfScalarsCochainComplex J f).obj P) ≫
        (restrictionOnDerived.{d, d₀} f).map (baseModelIso.{d, d₀} f hP w).hom := by
  have := isIso_vertexThree_app.{d, d₀} f P hP
  have := isIso_derivedExtensionOfScalarsCounit_app.{d, d₀} f P hP
  simp only [vertexThreeIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom,
    inv_vertexThree_app.{d, d₀} f hP, baseModelIso_hom, Functor.map_comp]
  exact Category.assoc (obj := DerivedCategory
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))) _ _ _

/-- For a flat cellular complex `P`, the inverse of the component of `vertexOne` at `P`, as the
inverse comparison `restrictionFactors` followed by the restrictions of the inverse derived tensor
counit and of the inverse base change counit tensored with `I₀`. -/
theorem inv_vertexOne_app (I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P) :
    haveI := isIso_vertexOne_app.{d, d₀} f I₀ P hP
    haveI := isIso_derivedExtensionOfScalarsCounit_app.{d, d₀} f P hP
    haveI := isIso_derivedTensorRightCounit_app_extensionOfScalars.{d, d₀} f I₀ P hP
    inv ((vertexOne.{d, d₀} f I₀).app P) =
      (restrictionFactors.{d, d₀} f).inv.app
          (((tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((extensionOfScalarsCochainComplex J f).obj P)) ≫
        (restrictionOnDerived.{d, d₀} f).map
          (inv ((derivedTensorRightCounit.{d₀} I₀).app
            ((extensionOfScalarsCochainComplex J f).obj P))) ≫
        (restrictionOnDerived.{d, d₀} f).map ((derivedTensorRight.{d₀} I₀).map
          (inv ((derivedExtensionOfScalarsCounit.{d, d₀} f).app P))) := by
  have := isIso_vertexOne_app.{d, d₀} f I₀ P hP
  have := isIso_derivedExtensionOfScalarsCounit_app.{d, d₀} f P hP
  have := isIso_derivedTensorRightCounit_app_extensionOfScalars.{d, d₀} f I₀ P hP
  simp only [vertexOne_app']
  rw [CategoryTheory.Functor.map_inv, CategoryTheory.Functor.map_inv,
    CategoryTheory.Functor.map_inv]
  exact inv_comp_comp_iso_hom' _ _ ((restrictionFactors.{d, d₀} f).app _)

/-- The first vertex identification, through `baseModelIso`. -/
theorem vertexOneIso_hom_eq (I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P)
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (w : DerivedCategory.Q.obj P ≅ K) :
    haveI := isIso_derivedTensorRightCounit_app_extensionOfScalars.{d, d₀} f I₀ P hP
    (vertexOneIso.{d, d₀} (I₀ := I₀) f hP w).hom =
      (restrictionFactors.{d, d₀} f).inv.app
          (((tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((extensionOfScalarsCochainComplex J f).obj P)) ≫
        (restrictionOnDerived.{d, d₀} f).map
          (inv ((derivedTensorRightCounit.{d₀} I₀).app
            ((extensionOfScalarsCochainComplex J f).obj P))) ≫
        (restrictionOnDerived.{d, d₀} f).map
          ((derivedTensorRight.{d₀} I₀).map (baseModelIso.{d, d₀} f hP w).hom) := by
  have := isIso_vertexOne_app.{d, d₀} f I₀ P hP
  have := isIso_derivedExtensionOfScalarsCounit_app.{d, d₀} f P hP
  have := isIso_derivedTensorRightCounit_app_extensionOfScalars.{d, d₀} f I₀ P hP
  simp only [vertexOneIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom,
    inv_vertexOne_app.{d, d₀} f I₀ hP, baseModelIso_hom, Functor.map_comp, Functor.map_inv]
  exact comp_assoc₄' (D := DerivedCategory
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))) _ _ _ _

/-! ### Models of two lifts joined by a morphism of complexes -/

/-- The morphism of the derived category induced by a morphism of the homotopy category. -/
abbrev homotopyToDerived {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {X Y : CochainComplex A ℤ}
    (h : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj X ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y) :
    DerivedCategory.Q.obj X ⟶ DerivedCategory.Q.obj Y :=
  (DerivedCategory.quotientCompQhIso A).inv.app X ≫ DerivedCategory.Qh.map h ≫
    (DerivedCategory.quotientCompQhIso A).hom.app Y

/-- `homotopyToDerived` sends a composite to the composite. -/
theorem homotopyToDerived_comp {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {X Y Z : CochainComplex A ℤ}
    (h : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj X ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)
    (h' : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z) :
    homotopyToDerived (h ≫ h') = homotopyToDerived h ≫ homotopyToDerived h' := by
  simp [homotopyToDerived]

/-- `homotopyToDerived` of the class of a morphism of complexes `g` is `Q(g)`. -/
theorem homotopyToDerived_quotient_map {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {X Y : CochainComplex A ℤ} (g : X ⟶ Y) :
    homotopyToDerived ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g) =
      DerivedCategory.Q.map g := by
  have := (DerivedCategory.quotientCompQhIso A).hom.naturality g
  simp only [Functor.comp_map] at this
  rw [homotopyToDerived, this, Iso.inv_hom_id_app_assoc]

/-- The identification of a lift, with its source written through the derived base change of
Stacks 0794. -/
abbrev liftIdentification (L : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) K₀) :
    (derivedExtensionOfScalars.{d, d₀} f).obj L.K.obj ≅ K₀.obj :=
  L.identification

/-- The reduction of a cellular resolution of a lift, identified with `K₀`. -/
abbrev liftModelIso (L : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) K₀)
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P) (w : DerivedCategory.Q.obj P ≅ L.K.obj) :
    DerivedCategory.Q.obj ((extensionOfScalarsCochainComplex J f).obj P) ≅ K₀.obj :=
  baseModelIso.{d, d₀} f hP w ≪≫ liftIdentification.{d, d₀} f L

/-- For a morphism of flat cellular complexes `g : P' ⟶ P` with `Q(g)` invertible, the
identification `liftModelIso` for `P'` and the resolution `Q(g) ≫ w` is the base change of `g`
followed by `liftModelIso` for `P` and `w`. -/
theorem liftModelIso_hom_of_hom (L : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) K₀)
    {P P' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P) (hP' : IsFlatCellular P') (g : P' ⟶ P)
    [IsIso (DerivedCategory.Q.map g)] (w : DerivedCategory.Q.obj P ≅ L.K.obj) :
    (liftModelIso.{d, d₀} f L hP' (asIso (DerivedCategory.Q.map g) ≪≫ w)).hom =
      DerivedCategory.Q.map ((extensionOfScalarsCochainComplex J f).map g) ≫
        (liftModelIso.{d, d₀} f L hP w).hom := by
  have h₁ := isIso_derivedExtensionOfScalarsCounit_app.{d, d₀} f P hP
  have h₂ := isIso_derivedExtensionOfScalarsCounit_app.{d, d₀} f P' hP'
  have hn := (derivedExtensionOfScalarsCounit.{d, d₀} f).naturality g
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  dsimp only [liftModelIso, Iso.trans_hom]
  rw [baseModelIso_hom, baseModelIso_hom, Iso.trans_hom, asIso_hom,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [IsIso.inv_comp_eq, ← reassoc_of% hn, IsIso.hom_inv_id_assoc]

/-- **Two lifts have cellular models joined by a morphism of their reductions over `K₀`**: for
lifts `L` and `L'` of `K₀` there are cellular resolutions `P` of `L` and `P'` of `L'` and a
morphism of complexes `a₀ : P'₀ ⟶ P₀` whose image in `D(O₀)` matches the two identifications
with `K₀`. This is the factorization of Tag 0DIX, applied to a fraction representing the
comparison of the two identifications, followed by cellular resolution. -/
theorem exists_models_hom (L L' : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) K₀) :
    ∃ (P P' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
      (hP : IsFlatCellular P) (hP' : IsFlatCellular P') (w : DerivedCategory.Q.obj P ≅ L.K.obj)
      (w' : DerivedCategory.Q.obj P' ≅ L'.K.obj)
      (a₀ : (extensionOfScalarsCochainComplex J f).obj P' ⟶
        (extensionOfScalarsCochainComplex J f).obj P),
      DerivedCategory.Q.map a₀ ≫ (liftModelIso.{d, d₀} f L hP w).hom =
        (liftModelIso.{d, d₀} f L' hP' w').hom := by
  have hm := isFlatCellular_cellularModel L.K.obj
  have hm' := isFlatCellular_cellularModel L'.K.obj
  let P := cellularModel L.K.obj
  let P₁ := cellularModel L'.K.obj
  let w := cellularModelIso L.K.obj
  let w₁ := cellularModelIso L'.K.obj
  let ρ := (liftModelIso.{d, d₀} f L' hm' w₁).hom ≫ (liftModelIso.{d, d₀} f L hm w).inv
  obtain ⟨Z, s, hs, g, hρ⟩ := DerivedCategory.right_fac ρ
  have hsq : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := s)).1 hs
  obtain ⟨G, γ, hγ, h, hh⟩ :=
    exists_quasiIso_with_extensionOfScalars_factorization_of_hom J f P₁ Z s hsq
  obtain ⟨W, hW, t, ht⟩ := exists_isFlatCellular_quasiIso G
  have hQt : IsIso (DerivedCategory.Q.map (t ≫ γ)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    have := hγ; have := ht
    infer_instance
  obtain ⟨a₀, ha₀⟩ := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_surjective
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((extensionOfScalarsCochainComplex J f).map t) ≫ h ≫
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map g)
  refine ⟨P, W, hm, hW, w, asIso (DerivedCategory.Q.map (t ≫ γ)) ≪≫ w₁, a₀, ?_⟩
  rw [liftModelIso_hom_of_hom.{d, d₀} f L' hm' hW (t ≫ γ) w₁]
  have hQa : DerivedCategory.Q.map a₀ =
      DerivedCategory.Q.map ((extensionOfScalarsCochainComplex J f).map t) ≫
        homotopyToDerived h ≫ DerivedCategory.Q.map g := by
    rw [← homotopyToDerived_quotient_map, ha₀]
    simp [homotopyToDerived_comp, homotopyToDerived_quotient_map]
  have hQγ : DerivedCategory.Q.map ((extensionOfScalarsCochainComplex J f).map γ) =
      homotopyToDerived h ≫ DerivedCategory.Q.map s := by
    rw [← homotopyToDerived_quotient_map, hh]
    simp [homotopyToDerived_comp, homotopyToDerived_quotient_map]
  have hg : DerivedCategory.Q.map g = DerivedCategory.Q.map s ≫ ρ := by
    rw [hρ, IsIso.hom_inv_id_assoc]
  rw [hQa, hg, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hQγ]
  simp only [ρ, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-! ### The connecting class at a model -/

/-- The identification `Q(P₀ ⊗_{O₀} I₀) ≅ K₀ ⊗^L_{O₀} I₀` attached to a cellular model of a
lift. -/
def liftModelIdealIso (I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    (L : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) K₀)
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P) (w : DerivedCategory.Q.obj P ≅ L.K.obj) :
    DerivedCategory.Q.obj (((tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((extensionOfScalarsCochainComplex J f).obj P)) ≅
      (derivedTensorRight.{d₀} I₀).obj K₀.obj :=
  haveI := isIso_derivedTensorRightCounit_app_extensionOfScalars.{d, d₀} f I₀ P hP
  (asIso ((derivedTensorRightCounit.{d₀} I₀).app
      ((extensionOfScalarsCochainComplex J f).obj P))).symm ≪≫
    (derivedTensorRight.{d₀} I₀).mapIso (liftModelIso.{d, d₀} f L hP w)

/-- The forward map of `liftModelIdealIso` is the inverse of the derived tensor counit followed by
the derived tensor product with `I₀` of `liftModelIso`. -/
theorem liftModelIdealIso_hom (I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    (L : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) K₀)
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P) (w : DerivedCategory.Q.obj P ≅ L.K.obj) :
    haveI := isIso_derivedTensorRightCounit_app_extensionOfScalars.{d, d₀} f I₀ P hP
    (liftModelIdealIso.{d, d₀} f I₀ L hP w).hom =
      inv ((derivedTensorRightCounit.{d₀} I₀).app ((extensionOfScalarsCochainComplex J f).obj P)) ≫
        (derivedTensorRight.{d₀} I₀).map (liftModelIso.{d, d₀} f L hP w).hom :=
  rfl

/-- Rearranging a transported connecting morphism, with the objects abstract. -/
theorem transport_rearrange' {D₀ D : Type*} [Category D₀] [Category D] [HasShift D ℤ]
    (r : D₀ ⥤ D) (I : D₀ ⥤ D₀) {A B : D} {X Y K₀ T₁ : D₀}
    (α : T₁ ≅ K₀) (b : X ≅ T₁) (fh : r.obj X ≅ A) (fh' : r.obj Y ≅ B) (t : Y ⟶ I.obj X)
    (δ : A ⟶ B⟦(1 : ℤ)⟧) (v₃ : A ≅ r.obj T₁) (v₁ : B ≅ r.obj (I.obj T₁))
    (h₃ : v₃.hom = fh.inv ≫ r.map b.hom) (h₁ : v₁.hom = fh'.inv ≫ r.map t ≫ r.map (I.map b.hom)) :
    r.map α.inv ≫ (v₃.inv ≫ δ ≫ v₁.hom⟦(1 : ℤ)⟧') ≫ (r.map (I.map α.hom))⟦(1 : ℤ)⟧' =
      r.map (b ≪≫ α).inv ≫ fh.hom ≫ δ ≫
        (fh'.inv ≫ r.map (t ≫ I.map (b ≪≫ α).hom))⟦(1 : ℤ)⟧' := by
  have e₃ : v₃ = fh.symm ≪≫ r.mapIso b := Iso.ext (by rw [h₃]; rfl)
  subst e₃
  rw [h₁]
  simp

variable (ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
  (hι : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f) = 0)
  (hS : (idealSequenceOf f I₀ ι hι).ShortExact)

/-- **The connecting class of a lift, computed at a cellular model**: the connecting morphism of
the reduction sequence of the model, transported along the identifications of the reduction of
the model and of its ideal part with `K₀` and `K₀ ⊗^L_{O₀} I₀`. -/
theorem connectingClass_flatReduction_eq
    (L : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) K₀)
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (hP : IsFlatCellular P) (w : DerivedCategory.Q.obj P ≅ L.K.obj) :
    connectingClass (flatReduction.{d, d₀} f ι hι hS) L =
      (restrictionOnDerived.{d, d₀} f).map (liftModelIso.{d, d₀} f L hP w).inv ≫
        (restrictionFactors.{d, d₀} f).hom.app ((extensionOfScalarsCochainComplex J f).obj P) ≫
        DerivedCategory.triangleOfSESδ
          (shortExact_reductionSequence ι hι hS P (flatObjects_X_of_isFlatCellular hP)) ≫
        ((restrictionFactors.{d, d₀} f).inv.app
            (((tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((extensionOfScalarsCochainComplex J f).obj P)) ≫
          (restrictionOnDerived.{d, d₀} f).map
            (liftModelIdealIso.{d, d₀} f I₀ L hP w).hom)⟦(1 : ℤ)⟧' := by
  have := isIso_derivedTensorRightCounit_app_extensionOfScalars.{d, d₀} f I₀ P hP
  have e := transport_rearrange' (restrictionOnDerived.{d, d₀} f) (derivedTensorRight.{d₀} I₀)
    (liftIdentification.{d, d₀} f L) (baseModelIso.{d, d₀} f hP w)
    ((restrictionFactors.{d, d₀} f).app ((extensionOfScalarsCochainComplex J f).obj P))
    ((restrictionFactors.{d, d₀} f).app (((tensorRight O₀ I₀).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((extensionOfScalarsCochainComplex J f).obj P)))
    (inv ((derivedTensorRightCounit.{d₀} I₀).app ((extensionOfScalarsCochainComplex J f).obj P)))
    (DerivedCategory.triangleOfSESδ
      (shortExact_reductionSequence ι hι hS P (flatObjects_X_of_isFlatCellular hP)))
    (vertexThreeIso.{d, d₀} f hP w) (vertexOneIso.{d, d₀} f hP w)
    (vertexThreeIso_hom_eq.{d, d₀} f hP w) (vertexOneIso_hom_eq.{d, d₀} f I₀ hP w)
  rw [connectingClass, flatReduction_connecting.{d, d₀} f ι hι hS hP w]
  exact e

end Deformation.ComplexLift

end
