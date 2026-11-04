module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseChangeUnitor
public import StacksFrontier.Deformation.ToposThickening.DerivedIdealTensorIdentification
public import StacksFrontier.Deformation.ToposThickening.DerivedLiftAutomorphisms
public import StacksFrontier.Deformation.ToposThickening.DerivedReductionData
public import StacksFrontier.Deformation.ToposThickening.DerivedTensorBridge
public import StacksFrontier.Deformation.ToposThickening.DerivedTensorUnit

/-!
# The reduction triangle, transported onto the data a lift statement consumes

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site, let `I₀` be a sheaf
of `O₀`-modules and let

`0 ⟶ I₀|_O ⟶ O ⟶ O₀|_O ⟶ 0`

be a short exact sequence of sheaves of `O`-modules — the square-zero ideal sequence of a
thickening, with the ideal read through its `O₀`-module structure. Tensoring it with an object
`K` of `D(O)` gives the distinguished triangle
`Stacks.SheafOfModules.DerivedTensorProduct.tensorSingleTriangle`, whose three vertices are
`K ⊗^L_O I₀|_O`, `K ⊗^L_O O` and `K ⊗^L_O O₀|_O`, whereas a
`Deformation.ComplexLift.DerivedReduction` asks for the triangle with vertices
`(K ⊗^L_O O₀ ⊗^L_{O₀} I₀)|_O`, `K` and `(K ⊗^L_O O₀)|_O`. This file identifies the three
vertices and transports the triangle along those identifications, which produces the
`DerivedReduction` itself.

Each identification is a composite of two isomorphisms of *functors* already in the tree, so
the transported triangle is natural in `K`. The one step that is not mechanical — that the
second morphism of the triangle, the image of the surjection `O ⟶ O₀|_O`, is the unit of the
adjunction read through the first two identifications — is taken as a hypothesis.

## Main definitions

* `Deformation.ComplexLift.transportTriangleIso`: a triangle, transported along isomorphisms of
  its three vertices, is isomorphic to the original; stated for an arbitrary category with a
  shift.
* `Deformation.ComplexLift.idealSequenceOf`: the short exact sequence above, as a short complex
  of sheaves of `O`-modules.
* `Deformation.ComplexLift.idealVertexIso`, `Deformation.ComplexLift.unitVertexIso` and
  `Deformation.ComplexLift.quotientVertexIso`: the three vertex identifications, as isomorphisms
  of functors on `D(O)`.
* `Deformation.ComplexLift.derivedReductionOfTriangle`: **the `DerivedReduction` of a square-zero
  ideal sequence**, step (2) of the proof of [Stacks, Tag 0DIY].

## Main results

* `Deformation.ComplexLift.derivedReductionOfTriangle` carries the result in its `distinguished`
  field: the transport of
  `Stacks.SheafOfModules.DerivedTensorProduct.tensorSingleTriangle_distinguished` along an
  isomorphism of triangles whose three components are the vertex identifications.

## Implementation notes

The two spellings `Deformation.ComplexLift.Stacks.SheafOfModules.Tensor.ringSheaf O` and
`Stacks.SheafOfModules.Tensor.ringSheaf O` of the underlying sheaf of rings, and with them the
two spellings `AlgebraicGeometry.RingedSite.Modules (ringedSiteOf J O)` and
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf O)` of the category of sheaves of modules,
  are equal on the nose
(`Deformation.ComplexLift.modules_ringedSiteOf`) but not reducibly so. The discipline that makes
them compose is the one recorded in the implementation notes of
`StacksFrontier/Deformation/ToposThickening/DerivedTensorBridge.lean`: the derived-category
hypothesis is taken in the ringed-site spelling and re-seated onto the other one by the
reducible `Deformation.ComplexLift.hasDerivedCategoryRingSheafOf`, made an instance by
`attribute [local instance]` rather than declared as one. The three vertex identifications then
each have one spelling on the left and the other on the right, and the defeq check happens where
they are composed.

**Why the matching of the second morphism is a hypothesis.** The other two commuting squares of
the transporting isomorphism of triangles hold by the definitions of the `idealInclusion` and
`connecting` fields, which are written as the conjugates of the triangle's first and third
morphisms. The middle one is a genuine statement about the adjunction: it says that the unit of
`T.baseChange ⊣ restriction` is, after the first and third vertices are identified, the derived
tensor product of `K` with the surjection `O ⟶ O₀|_O`. Nothing about how the adjunction or the
identifications were built is visible from here, so it is an explicit argument, named `hmor`.

## References

* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated AlgebraicGeometry

universe d d₀ v' u u' w w'

namespace Deformation.ComplexLift

open AlgebraicGeometry.RingedSite Stacks.SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
variable [HasDerivedCategory.{d} (Modules.{u', v', u} (ringedSiteOf J O))]

attribute [local instance] hasDerivedCategoryRingSheafOf

variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} (ringedSiteOf J O).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u}
    (ringedSiteOf J O).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u', v', u} (ringedSiteOf J O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (ringedSiteOf J O).O) (ComplexShape.up ℤ)]
variable (I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
variable (T : DerivedExtensionOfScalars.{d, d₀} f)
variable (Tt : Stacks.SheafOfModules.DerivedTensorProduct.{u', v', u, d} (ringedSiteOf J O))

/-! ### Transport of a triangle along isomorphisms of its vertices -/

section Transport

variable {D : Type w} [Category.{w'} D] [HasShift D ℤ]

/-- **A triangle, transported along isomorphisms of its three vertices.** Given a triangle `B`,
isomorphisms `eᵢ` of its vertices with objects `Xᵢ`, and a morphism `m₂ : X₂ ⟶ X₃` that the
second morphism of `B` becomes under `e₂` and `e₃`, the triangle on the `Xᵢ` whose first and
third morphisms are the conjugates of those of `B` and whose second morphism is `m₂` is
isomorphic to `B`.

The statement is about an arbitrary category with a shift, with no reference to sheaves of
modules: that is what lets the three commuting squares be discharged by `simp`, and lets the
two spellings of the category of sheaves of modules meet only at the application. -/
def transportTriangleIso (B : Triangle D) {X₁ X₂ X₃ : D}
    (e₁ : B.obj₁ ≅ X₁) (e₂ : B.obj₂ ≅ X₂) (e₃ : B.obj₃ ≅ X₃) (m₂ : X₂ ⟶ X₃)
    (hm : B.mor₂ ≫ e₃.hom = e₂.hom ≫ m₂) :
    Triangle.mk (e₁.inv ≫ B.mor₁ ≫ e₂.hom) m₂
        (e₃.inv ≫ B.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧') ≅ B :=
  Triangle.isoMk _ _ e₁.symm e₂.symm e₃.symm
    (by simp)
    (by
      dsimp only [Triangle.mk_mor₂, Iso.symm_hom]
      rw [Iso.comp_inv_eq, Category.assoc, hm, Iso.inv_hom_id_assoc])
    (by
      dsimp only [Triangle.mk_mor₃, Iso.symm_hom]
      rw [Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.comp_id])

end Transport

/-! ### The square-zero ideal sequence -/

/-- **The square-zero ideal sequence `0 ⟶ I₀|_O ⟶ O ⟶ O₀|_O ⟶ 0`** of sheaves of `O`-modules,
as a short complex: the inclusion of the ideal is a parameter `ι`, and the surjection is the
canonical map `O ⟶ O₀|_O` of
`Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit`. Squareness of the ideal is what
puts the `O₀`-module structure on `I₀` that lets the first term be written `I₀|_O`. -/
abbrev idealSequenceOf
  (ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hι : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
      (ringSheafMapOf J f) = 0) :
    ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  ShortComplex.mk ι
    (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f)) hι

/-! ### The three vertex identifications -/

/-- **The first vertex: `K ⊗^L_O I₀|_O ≅ ((K ⊗^L_O O₀) ⊗^L_{O₀} I₀)|_O`**, as an isomorphism of
functors on `D(O)`. It is the comparison of the ringed site's derived tensor product with the one
built from flat resolutions, followed by
`Deformation.ComplexLift.derivedIdealTensorIsoOf`. -/
def idealVertexIso :
    Tt.tensor.flip.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor
          (Modules.{u', v', u} (ringedSiteOf J O)) 0).obj (restrictIdeal f I₀))) ≅
      T.baseChange ⋙ derivedTensorRight.{d₀} I₀ ⋙ restrictionOnDerived.{d, d₀} f :=
  singleTensorIsoDerivedTensorRight Tt (restrictIdeal f I₀) ≪≫
    (derivedIdealTensorIsoOf.{d, d₀} f I₀ T).symm

/-- **The middle vertex: `K ⊗^L_O O ≅ K`**, as an isomorphism of functors on `D(O)`. It is the
comparison of the two derived tensor products followed by the natural unit law
`Deformation.ComplexLift.derivedTensorRightUnitIso`. -/
def unitVertexIso :
    Tt.tensor.flip.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (Modules.{u', v', u} (ringedSiteOf J O)) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)))) ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))) :=
  singleTensorIsoDerivedTensorRight Tt
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) ≪≫
    derivedTensorRightUnitIso O

/-- **The third vertex: `K ⊗^L_O O₀|_O ≅ (K ⊗^L_O O₀)|_O`**, as an isomorphism of functors on
`D(O)`. It is the comparison of the two derived tensor products followed by
`Deformation.ComplexLift.derivedRestrictExtensionIsoOf`. -/
def quotientVertexIso :
    Tt.tensor.flip.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (Modules.{u', v', u} (ringedSiteOf J O)) 0).obj
          (restrictUnitOf f))) ≅
      T.baseChange ⋙ restrictionOnDerived.{d, d₀} f :=
  singleTensorIsoDerivedTensorRight Tt (restrictUnitOf f) ≪≫
    (derivedRestrictExtensionIsoOf.{d, d₀} f T).symm

/-! ### The transport -/

variable {ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)}
  {hι : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
    (ringSheafMapOf J f) = 0}

/-- **The `DerivedReduction` of a square-zero ideal sequence.** Step (2) of the proof of
[Stacks, Tag 0DIY]: the reduction triangle

`(K ⊗^L_O O₀ ⊗^L_{O₀} I₀)|_O ⟶ K ⟶ (K ⊗^L_O O₀)|_O ⟶ ((K ⊗^L_O O₀ ⊗^L_{O₀} I₀)|_O)⟦1⟧`,

natural in `K`, whose second morphism is the unit of the adjunction between derived base change
and derived restriction of scalars.

It is the triangle obtained by tensoring the ideal sequence with `K`, transported along the three
vertex identifications `Deformation.ComplexLift.idealVertexIso`,
`Deformation.ComplexLift.unitVertexIso` and `Deformation.ComplexLift.quotientVertexIso`. The
hypothesis `hmor` is the matching of the triangle's second morphism with the unit of the
adjunction; everything else is transport. -/
def derivedReductionOfTriangle (hS : (idealSequenceOf f I₀ ι hι).ShortExact)
    (hmor : ∀ K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)),
      (Tt.tensor.obj K).map ((DerivedCategory.singleFunctor
            (Modules.{u', v', u} (ringedSiteOf J O)) 0).map
          (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
            (ringSheafMapOf J f))) ≫
          (quotientVertexIso f T Tt).hom.app K =
        (unitVertexIso Tt).hom.app K ≫ (derivedAdjunctionOf.{d, d₀} f T).unit.app K) :
    DerivedReduction T (derivedTensorRight.{d₀} I₀) where
  restriction := restrictionOnDerived.{d, d₀} f
  additive := inferInstance
  commShift := inferInstance
  adjunction := derivedAdjunctionOf.{d, d₀} f T
  idealInclusion K :=
    (idealVertexIso f I₀ T Tt).inv.app K ≫ (Tt.tensorSingleTriangle hS K).mor₁ ≫
      (unitVertexIso Tt).hom.app K
  connecting K :=
    (quotientVertexIso f T Tt).inv.app K ≫ (Tt.tensorSingleTriangle hS K).mor₃ ≫
      (shiftFunctor
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
          (1 : ℤ)).map
        ((idealVertexIso f I₀ T Tt).hom.app K)
  distinguished K :=
    isomorphic_distinguished _ (Tt.tensorSingleTriangle_distinguished hS K) _
      (transportTriangleIso (Tt.tensorSingleTriangle hS K)
        ((idealVertexIso f I₀ T Tt).app K) ((unitVertexIso Tt).app K)
        ((quotientVertexIso f T Tt).app K) ((derivedAdjunctionOf.{d, d₀} f T).unit.app K)
        (hmor K))

end Deformation.ComplexLift

end
