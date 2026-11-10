module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseChangeUnitor
public import StacksFrontier.Deformation.ToposThickening.DerivedReductionFac
public import StacksFrontier.Deformation.ToposThickening.ExtensionUnitTensor

/-!
# The unit of the derived reduction

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site. The first morphism of
the reduction triangle of Tag 0DIY is the unit

`K ⟶ K ⊗^L_O O₀|_O`

of the derived adjunction between derived base change and derived restriction of scalars, read
through the identification of `(- ⊗^L_O O₀)|_O` with `- ⊗^L_O O₀|_O`. This file constructs that
natural transformation and identifies it with the derived tensor product of the structure map
`O ⟶ O₀|_O`: that identification is the content of the reduction triangle's first vertex.

## Main definitions

* `Deformation.ComplexLift.derivedReductionUnit`: **the unit** `𝟭 ⟶ - ⊗^L_O O₀|_O`.
* `Deformation.ComplexLift.tensorRightUnitToRestrictUnit`: the degreewise map
  `- ⊗_O O ⟶ - ⊗_O O₀|_O` the unit derives.

## Main results

* `Deformation.ComplexLift.derivedReductionUnit_app_comp_counitHomotopy`: the unit, read against
  the comparison of `- ⊗^L_O O₀|_O` on the homotopy category, is the degreewise unit of the
  adjunction of Stacks 03CZ.
* `Deformation.ComplexLift.derivedTensorRightCounit_app_comp`: the same computation read along
  the localization of cochain complexes instead of that of the homotopy category.
* `Deformation.ComplexLift.restrictionOnDerivedComparison_bookkeeping`: the comparison
  isomorphisms left over by that transport compose to the identity.
* `Deformation.ComplexLift.derivedReductionUnit_whiskerLeft_Q`: **the unit derives the
  degreewise structure map**, i.e. whiskered with the localization it is the degreewise map
  `- ⊗_O O ⟶ - ⊗_O O₀|_O` read through the unit law of the tensor product.
* `Deformation.ComplexLift.singleTensorIso_comp_quotientMap`: **the unit is the derived tensor
  product of the structure map**, for the derived tensor product of a ringed site: it is
  `- ⊗^L_O (O ⟶ O₀|_O)[0]` read through the unit law `- ⊗^L_O O ≅ 𝟭`.

## Implementation notes

**Why there are two levels.** `Deformation.ComplexLift.derivedTensorRight` is a left derived
functor along `Qh`, the localization of the *homotopy* category, while the comparisons of the
derived tensor product of a ringed site are stated along `Q`, the localization of cochain
complexes. The unit is computed first on the homotopy category, where the derived adjunction of
Stacks 09T5 lives, and then transported to complexes through
`CategoryTheory.DerivedCategory.quotientCompQhIso`; that transport is
`Deformation.ComplexLift.derivedTensorRightCounit_app_comp`, and the bookkeeping it leaves
behind is `Deformation.ComplexLift.restrictionOnDerivedComparison_bookkeeping`, which says that a
four-fold composite of comparison isomorphisms is the identity.

**The one module-level input.** That the unit of the adjunction of Stacks 03CZ, read through
`Deformation.ComplexLift.restrictExtensionIsoTensorRight`, is the tensor product of the
structure map `O ⟶ O₀|_O` is a computation on local sections, and it is
`Deformation.ComplexLift.unit_comp_restrictExtensionIsoTensorRight`. Everything below is the
transport of that one identity across the two localizations.

**Why the manipulations are written in term mode.** Several of the composites below are
type-correct only at default transparency: `Deformation.ComplexLift.ringSheafOf` and
`Stacks.SheafOfModules.Tensor.ringSheaf` are definitionally but not reducibly equal, and the
same holds for the two spellings of an object of the homotopy category. `rw` and `simp only`
check the rewritten target at `implicit` transparency, so inside such a composite they report
that the pattern was not found — notably `CategoryTheory.Category.comp_id` and
`CategoryTheory.Functor.map_id` never fire. Those steps are therefore written with
`congrArg`, `Eq.trans` and `have`s carrying an ascribed type, all of which check types once, at
default transparency; and the one long associativity computation is isolated at abstract
morphisms, where nothing is ill-typed.

**The spellings in the last statement.** It mixes the derived tensor product of
`Deformation.ComplexLift.ringedSiteOf` with the functors of the lift statements, so it is
placed in a second section whose derived-category instance is re-seated by the reducible
`abbrev` `Deformation.ComplexLift.hasDerivedCategoryRingSheafOf`, exactly as in
`StacksFrontier/Deformation/ToposThickening/DerivedReductionFac.lean`.

## References

* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe d d₀ v' u u' w w₀ t t₀ s s₀

namespace CategoryTheory.Functor

variable {A : Type t} [Category.{s} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type t₀} [Category.{s₀} B] [Abelian B] [HasDerivedCategory.{w₀} B]
  (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The comparison isomorphisms of an exact functor on derived categories telescope.** For an
exact functor `G` and a cochain complex `K`, the four-fold composite of

* the comparison `Q ≅ quotient ⋙ Qh` at `G(K)`,
* the comparison exhibiting `G` on derived categories as derived along `Qh`, at the class of `K`,
* the image under `G` of the comparison `quotient ⋙ Qh ≅ Q` at `K`, and
* the comparison exhibiting `G` on derived categories as derived along `Q`, at `K`

is the identity. This is `CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app`, whose
remaining factor `CategoryTheory.Functor.mapHomotopyCategoryFactors` has identity components. -/
theorem quotientCompQhIso_inv_comp_mapDerivedCategoryFactorsh_inv (K : CochainComplex B ℤ) :
    (DerivedCategory.quotientCompQhIso A).inv.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        G.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso B).hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app K =
      𝟙 (DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
  have hkey := G.mapDerivedCategoryFactorsh.inv_hom_id_app
    ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K)
  rw [G.mapDerivedCategoryFactorsh_hom_app K] at hkey
  have hv : DerivedCategory.Qh.map
      ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) = 𝟙 _ :=
    DerivedCategory.Qh.map_id _
  have huv : (DerivedCategory.quotientCompQhIso A).inv.app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) =
      (DerivedCategory.quotientCompQhIso A).inv.app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    (congrArg (fun k ↦ (DerivedCategory.quotientCompQhIso A).inv.app
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫ k) hv).trans (Category.comp_id _)
  rw [huv] at hkey
  have hkey2 : (G.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso B).hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app K) ≫
      (DerivedCategory.quotientCompQhIso A).inv.app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      𝟙 ((HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
    rw [Category.assoc, Category.assoc]
    exact hkey
  have hcancel : ((G.mapDerivedCategoryFactorsh.inv.app
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K) ≫
          G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso B).hom.app K) ≫
          G.mapDerivedCategoryFactors.hom.app K) ≫
        (DerivedCategory.quotientCompQhIso A).inv.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        (DerivedCategory.quotientCompQhIso A).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      G.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso B).hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app K := by
    rw [Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
  refine Eq.trans (congrArg (fun k ↦ (DerivedCategory.quotientCompQhIso A).inv.app
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫ k) hcancel).symm ?_
  refine Eq.trans (congrArg (fun k ↦ (DerivedCategory.quotientCompQhIso A).inv.app
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫ k ≫
      (DerivedCategory.quotientCompQhIso A).hom.app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) hkey2) ?_
  refine Eq.trans (congrArg (fun k ↦ (DerivedCategory.quotientCompQhIso A).inv.app
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫ k) (Category.id_comp
      ((DerivedCategory.quotientCompQhIso A).hom.app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))) ?_
  exact Iso.inv_hom_id_app _ _

end CategoryTheory.Functor

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-! ### The transformation -/

/-- **The unit of the derived reduction** `𝟭 ⟶ - ⊗^L_O O₀|_O`: the unit of the derived
adjunction of Stacks 09T5 between derived base change and derived restriction of scalars, read
through the identification `(- ⊗^L_O O₀)|_O ≅ - ⊗^L_O O₀|_O` of
`Deformation.ComplexLift.derivedRestrictExtensionIso`.

This is the first morphism of the reduction triangle of Tag 0DIY. -/
def derivedReductionUnit : 𝟭
  (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))) ⟶
    derivedTensorRight.{d} (restrictUnitOf f) :=
  (derivedAdjunction.{d, d₀} f).unit ≫ (derivedRestrictExtensionIso.{d, d₀} f).hom

/-! ### The homotopy-category identity -/

/-- **The unit derives the degreewise unit of the adjunction of Stacks 03CZ.** Read against the
comparison exhibiting `- ⊗^L_O O₀|_O` as a left derived functor along `Qh`, the unit above is
the unit of the adjunction between extension and restriction of scalars on the homotopy
categories, followed by the two comparison isomorphisms.

This is `CategoryTheory.Adjunction.derivedη_fac_app` — the defining property of the unit of a
derived adjunction — read through
`Deformation.ComplexLift.derivedRestrictExtensionIso_fac`. -/
theorem derivedReductionUnit_app_comp_counitHomotopy
    (X : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ)) :
    (derivedReductionUnit.{d, d₀} f).app (DerivedCategory.Qh.obj X) ≫
        (derivedTensorRightCounitHomotopy.{d} (restrictUnitOf f)).app X =
      DerivedCategory.Qh.map ((extendRestrictAdjunctionHomotopy f).unit.app X) ≫
        (restrictionOnDerivedComparison.{d, d₀} f).app
          (((extensionOfScalars f).mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        (restrictionCompHomotopyIso.{d, d₀} f).hom.app X := by
  have := isLeftDerivedFunctor_comp_derivedExtensionOfScalars.{d, d₀} f
    (restrictionOnDerived.{d, d₀} f)
  have hfac := NatTrans.congr_app (derivedRestrictExtensionIso_fac.{d, d₀} f) X
  rw [NatTrans.comp_app, Functor.whiskerLeft_app] at hfac
  have hu : (derivedAdjunction.{d, d₀} f).unit =
      (extendRestrictAdjunctionHomotopy f).derivedη
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
          (ComplexShape.up ℤ))
        (derivedExtensionOfScalarsCounitHomotopy f) (restrictionOnDerivedComparison f) := rfl
  dsimp only [derivedReductionUnit, NatTrans.comp_app]
  rw [Category.assoc, hfac]
  dsimp only [restrictExtensionCounitHomotopy, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_inv_app]
  rw [Category.id_comp, ← Category.assoc, hu, Adjunction.derivedη_fac_app, Category.assoc]

/-! ### Localization of complexes versus localization of the homotopy category -/

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The comparison of `- ⊗^L_O M` on complexes, computed through the homotopy category.** Any
natural transformation into `- ⊗^L_O M`, read against the comparison on cochain complexes, is
its reading against the comparison on the homotopy category, conjugated by the identification
of the two localizations. -/
theorem derivedTensorRightCounit_app_comp
  (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {G : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (γ : G ⟶ derivedTensorRight.{d} M)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    γ.app (DerivedCategory.Q.obj P) ≫ (derivedTensorRightCounit.{d} M).app P =
      G.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
        (γ.app (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
          (derivedTensorRightCounitHomotopy.{d} M).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
        (quotientCompTensorRightIso.{d} M).hom.app P := by
  have hnat := γ.naturality ((DerivedCategory.quotientCompQhIso
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))).inv.app P)
  dsimp only [derivedTensorRightCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  conv_lhs => rw [← Category.assoc, ← hnat]
  simp only [Category.assoc, Functor.comp_obj]

/-! ### The complex-level identity -/

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The comparison bookkeeping left over by the transport of
`Deformation.ComplexLift.derivedReductionUnit_app_comp_counitHomotopy` from the homotopy
category to cochain complexes: a four-fold composite of comparison isomorphisms is the
identity.

`Deformation.ComplexLift.quotientCompExtensionOfScalarsIso` is built from the comparison of
degreewise extension of scalars with its reading on the homotopy category, which has identity
components, so this is
`CategoryTheory.Functor.quotientCompQhIso_inv_comp_mapDerivedCategoryFactorsh_inv` for
restriction of scalars. -/
theorem restrictionOnDerivedComparison_bookkeeping
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))).inv.app
          (((extensionOfScalars f ⋙
            SheafOfModules.restrictScalars (ringSheafMapOf J f)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
        (restrictionOnDerivedComparison.{d, d₀} f).app
          (((extensionOfScalars f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
        (restrictionOnDerived.{d, d₀} f).map
          ((quotientCompExtensionOfScalarsIso.{d₀} f).hom.app P) ≫
        ((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f)).mapDerivedCategoryFactors).hom.app
            ((extensionOfScalarsCochainComplex J f).obj P) =
      𝟙 _ := by
  have h1 : DerivedCategory.Qh.map (((extensionOfScalars f).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).inv.app P) = 𝟙 _ := DerivedCategory.Qh.map_id _
  have he0 : (quotientCompExtensionOfScalarsIso.{d₀} f).hom.app P =
      DerivedCategory.Qh.map (((extensionOfScalars f).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).inv.app P) ≫
        (Functor.associator ((extensionOfScalars f).mapHomologicalComplex (ComplexShape.up ℤ))
            (HomotopyCategory.quotient
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
              (ComplexShape.up ℤ)) DerivedCategory.Qh).hom.app P ≫
          (DerivedCategory.quotientCompQhIso
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))).hom.app
            ((extensionOfScalarsCochainComplex J f).obj P) := rfl
  have h2 : (Functor.associator ((extensionOfScalars f).mapHomologicalComplex
          (ComplexShape.up ℤ))
          (HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
            (ComplexShape.up ℤ)) DerivedCategory.Qh).hom.app P ≫
        (DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))).hom.app
          ((extensionOfScalarsCochainComplex J f).obj P) =
      (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))).hom.app
        ((extensionOfScalarsCochainComplex J f).obj P) := Category.id_comp _
  have he : (quotientCompExtensionOfScalarsIso.{d₀} f).hom.app P =
      (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))).hom.app
        ((extensionOfScalarsCochainComplex J f).obj P) :=
    he0.trans ((congrArg (fun k ↦ DerivedCategory.Qh.map
        (((extensionOfScalars f).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).inv.app P) ≫ k) h2).trans
      ((congrArg (fun k ↦ k ≫ (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))).hom.app
            ((extensionOfScalarsCochainComplex J f).obj P)) h1).trans (Category.id_comp _)))
  refine Eq.trans (congrArg (fun k ↦
    (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))).inv.app
          (((extensionOfScalars f ⋙
            SheafOfModules.restrictScalars (ringSheafMapOf J f)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
        (restrictionOnDerivedComparison.{d, d₀} f).app
          (((extensionOfScalars f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
        (restrictionOnDerived.{d, d₀} f).map k ≫
        ((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f)).mapDerivedCategoryFactors).hom.app
            ((extensionOfScalarsCochainComplex J f).obj P)) he) ?_
  exact CategoryTheory.Functor.quotientCompQhIso_inv_comp_mapDerivedCategoryFactorsh_inv
    (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f))
    ((extensionOfScalarsCochainComplex J f).obj P)

/-- The degreewise map `- ⊗_O O ⟶ - ⊗_O O₀|_O` obtained by tensoring with the structure map
`O ⟶ O₀|_O` of `Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit`.

It is `Stacks.SheafOfModules.Tensor.sheafTensor` applied to that map in its second variable; the
type is ascribed at the spelling `Deformation.ComplexLift.ringSheafOf` of the underlying sheaf of
rings, which is what makes the additivity instances of
`Deformation.ComplexLift.tensorRight` apply to it. -/
abbrev tensorRightUnitToRestrictUnit :
    tensorRight O (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) ⟶ tensorRight O
      (restrictUnitOf f) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).flip.map
    (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f))

/-- The shape of the telescoping computation below, with the six morphisms abstract. Stating it
at abstract morphisms is what lets it be applied across the two spellings of the sheaf of rings:
the elaborator checks the types once, at the application, at default transparency, whereas a
rewrite inside the concrete composite is refused — the composite is type-correct only at default
transparency, so the pattern match silently fails. -/
private theorem comp_collapse_of_comp_id {D : Type*} [Category D]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : D} {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {c : X₂ ⟶ X₃} {e₁ : X₃ ⟶ X₄}
    {e₂ : X₄ ⟶ X₅} {g : X₅ ⟶ X₆} {q : X₀ ⟶ X₅} {w : X₅ ⟶ X₂}
    (hn : a ≫ b = q ≫ w) (hw : w ≫ c ≫ e₁ ≫ e₂ = 𝟙 X₅) :
    a ≫ b ≫ c ≫ e₁ ≫ e₂ ≫ g = q ≫ g := by
  rw [← Category.assoc, hn, Category.assoc, reassoc_of% hw]

/-- **The unit of the derived reduction derives the degreewise structure map.** Whiskered with
the localization of cochain complexes and read against the comparison of `- ⊗^L_O O₀|_O`, the
unit is the degreewise map `- ⊗_O O ⟶ - ⊗_O O₀|_O` of
`Deformation.ComplexLift.tensorRightUnitToRestrictUnit`, read through the unit law `- ⊗_O O ≅ 𝟭`.

The module-level input is
`Deformation.ComplexLift.unit_comp_restrictExtensionIsoTensorRight`: the unit of the adjunction
of Stacks 03CZ, read through `Deformation.ComplexLift.restrictExtensionIsoTensorRight`, is that
structure map tensored with the identity. -/
theorem derivedReductionUnit_whiskerLeft_Q :
    Functor.whiskerLeft DerivedCategory.Q (derivedReductionUnit.{d, d₀} f) ≫
        derivedTensorRightCounit.{d} (restrictUnitOf f) =
      identityTensorRightUnitCounit.{d} O ≫
        Functor.whiskerRight
          (NatTrans.mapHomologicalComplex (tensorRightUnitToRestrictUnit f)
            (ComplexShape.up ℤ))
          DerivedCategory.Q := by
  have hθ : (extendRestrictAdjunction f).unit ≫ (restrictExtensionIsoTensorRight f).hom =
      (tensorRightUnitIso O).inv ≫ tensorRightUnitToRestrictUnit f :=
    NatTrans.ext (funext (unit_comp_restrictExtensionIsoTensorRight f))
  refine NatTrans.ext (funext fun P ↦ ?_)
  have h2 := derivedReductionUnit_app_comp_counitHomotopy.{d, d₀} f
    ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ)).obj P)
  have h3 := derivedTensorRightCounit_app_comp (restrictUnitOf f)
    (derivedReductionUnit.{d, d₀} f) P
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [h3, h2]
  have ha : (restrictionCompHomotopyIso.{d, d₀} f).hom.app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
          (ComplexShape.up ℤ)).obj P) =
      (restrictionOnDerived.{d, d₀} f).map
            ((quotientCompExtensionOfScalarsIso.{d₀} f).hom.app P) ≫
          ((SheafOfModules.restrictScalars.{u}
            (ringSheafMapOf J f)).mapDerivedCategoryFactors).hom.app
              ((extensionOfScalarsCochainComplex J f).obj P) ≫
          DerivedCategory.Q.map ((restrictExtensionComplexIso f).hom.app P) ≫
          (quotientCompTensorRightIso.{d} (restrictUnitOf f)).inv.app P := rfl
  have hc : (extendRestrictAdjunctionHomotopy f).unit.app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
          (ComplexShape.up ℤ)).obj P) =
      (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
          (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (extendRestrictAdjunction f).unit
          (ComplexShape.up ℤ)).app P) := rfl
  rw [ha, hc]
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.id_map, restrictionOnDerived,
    restrictionOnDerivedComparison]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.comp_obj]
  have hnat2 : (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))).inv.app P ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (extendRestrictAdjunction f).unit
              (ComplexShape.up ℤ)).app P)) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (extendRestrictAdjunction f).unit (ComplexShape.up ℤ)).app P) ≫
        (DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))).inv.app
          (((extensionOfScalars f ⋙ SheafOfModules.restrictScalars
            (ringSheafMapOf J f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    (DerivedCategory.quotientCompQhIso_inv_naturality _).symm
  refine Eq.trans (comp_collapse_of_comp_id hnat2
    (restrictionOnDerivedComparison_bookkeeping.{d, d₀} f P)) ?_
  have hqid : DerivedCategory.Q.map ((Functor.mapHomologicalComplexIdIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ)).inv.app P) = 𝟙 _ :=
    DerivedCategory.Q.map_id _
  have h0 : (identityTensorRightUnitCounit.{d} O).app P =
      𝟙 _ ≫ 𝟙 _ ≫ DerivedCategory.Q.map ((Functor.mapHomologicalComplexIdIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
            (ComplexShape.up ℤ)).inv.app P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (tensorRightUnitIso O).inv
          (ComplexShape.up ℤ)).app P) := rfl
  have e1 : (NatTrans.mapHomologicalComplex (extendRestrictAdjunction f).unit
        (ComplexShape.up ℤ)).app P ≫ (restrictExtensionComplexIso f).hom.app P =
      (NatTrans.mapHomologicalComplex ((extendRestrictAdjunction f).unit ≫
        (restrictExtensionIsoTensorRight f).hom) (ComplexShape.up ℤ)).app P := by
    rw [NatTrans.mapHomologicalComplex_comp]
    rfl
  have hcomb : DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (extendRestrictAdjunction f).unit (ComplexShape.up ℤ)).app P) ≫
        DerivedCategory.Q.map ((restrictExtensionComplexIso f).hom.app P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (extendRestrictAdjunction f).unit (ComplexShape.up ℤ)).app P ≫
        (restrictExtensionComplexIso f).hom.app P) :=
    (DerivedCategory.Q.map_comp _ _).symm
  rw [h0, hqid]
  simp only [Category.id_comp, ← CategoryTheory.Functor.map_comp]
  refine Eq.trans hcomb ?_
  rw [e1, hθ, NatTrans.mapHomologicalComplex_comp]
  rfl

end Deformation.ComplexLift

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

/-- Cancelling a whiskered isomorphism against a factorization, with the three functors
abstract: in the concrete composite the two spellings of the category of sheaves of modules make
the goal type-correct only at default transparency, where `rw` refuses to work. -/
private theorem whiskerLeft_inv_comp {A B E : Type*} [Category A] [Category B] [Category E]
    (L : A ⥤ B) {F G : B ⥤ E} (iso : F ≅ G) {H : A ⥤ E} (α : L ⋙ G ⟶ H) (β : L ⋙ F ⟶ H)
    (h : Functor.whiskerLeft L iso.hom ≫ α = β) :
    Functor.whiskerLeft L iso.inv ≫ β = α := by
  rw [← h, ← Category.assoc, ← Functor.whiskerLeft_comp, Iso.inv_hom_id,
    Functor.whiskerLeft_id', Category.id_comp]

/-- The conjugation computation of the payoff below, with the five functors abstract. As with
`Deformation.ComplexLift.whiskerLeft_inv_comp`, the concrete composite mixes the two spellings
of the category of sheaves of modules and is type-correct only at default transparency, so the
rewriting is done here, where nothing is. -/
private theorem whiskerLeft_conj_comp {A B E : Type*} [Category A] [Category B] [Category E]
    (L : A ⥤ B) {T₁ T₂ G₁ G₂ : B ⥤ E} {H₁ H₂ : A ⥤ E} (i₁ : T₁ ≅ G₁) (i₂ : T₂ ≅ G₂)
    (b : T₁ ⟶ T₂) (c₁ : L ⋙ G₁ ⟶ H₁) (c₂ : L ⋙ G₂ ⟶ H₂) (s₁ : L ⋙ T₁ ⟶ H₁)
    (s₂ : L ⋙ T₂ ⟶ H₂) (m : H₁ ⟶ H₂)
    (h₁ : Functor.whiskerLeft L i₁.hom ≫ c₁ = s₁)
    (h₂ : Functor.whiskerLeft L i₂.hom ≫ c₂ = s₂)
    (hnat : Functor.whiskerLeft L b ≫ s₂ = s₁ ≫ m) :
    Functor.whiskerLeft L (i₁.inv ≫ b ≫ i₂.hom) ≫ c₂ = c₁ ≫ m := by
  rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp, Category.assoc, Category.assoc,
    h₂, hnat, ← Category.assoc, whiskerLeft_inv_comp L i₁ c₁ s₁ h₁]

/-- **The unit of the derived reduction is the derived tensor product of the structure map.**
Read through the identification of the ringed site's derived tensor product with the one built
from flat resolutions, and through the unit law `- ⊗^L_O O ≅ 𝟭`, the unit
`𝟭 ⟶ - ⊗^L_O O₀|_O` is `- ⊗^L_O (O ⟶ O₀|_O)[0]`.

This is what identifies the first morphism of the reduction triangle of Tag 0DIY with the
morphism the triangle of `Stacks.Sites.idealReductionTriangle` carries. Both sides are
natural transformations out of a left derived functor of `- ⊗_O O`, so it suffices to compare
them against the comparison of `- ⊗^L_O O₀|_O`, which is
`CategoryTheory.Functor.leftDerived_ext`. -/
theorem singleTensorIso_comp_quotientMap
    (Tt : Stacks.SheafOfModules.DerivedTensorProduct.{u', v', u, d} (ringedSiteOf J O)) :
    (singleTensorIsoDerivedTensorRight Tt
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).inv ≫
        Tt.tensor.flip.map (DerivedCategory.Q.map
          ((CochainComplex.singleFunctor (Modules.{u', v', u} (ringedSiteOf J O)) 0).map
            (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
              (ringSheafMapOf J f)))) ≫
        (singleTensorIsoDerivedTensorRight Tt (restrictUnitOf f)).hom =
      (derivedTensorRightUnitIso.{d} O).hom ≫ derivedReductionUnit.{d, d₀} f := by
  refine Functor.leftDerived_ext (derivedTensorRight.{d} (restrictUnitOf f))
    (derivedTensorRightCounit.{d} (restrictUnitOf f))
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ)) _ _ _ ?_
  refine Eq.trans (whiskerLeft_conj_comp DerivedCategory.Q
    (singleTensorIsoDerivedTensorRight Tt
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (singleTensorIsoDerivedTensorRight Tt (restrictUnitOf f)) _ _ _ _ _ _
    (singleTensorIsoDerivedTensorRight_fac Tt
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (singleTensorIsoDerivedTensorRight_fac Tt (restrictUnitOf f))
    (Stacks.SheafOfModules.DerivedTensorProduct.singleTensorComparison_naturality Tt
      (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
        (ringSheafMapOf J f)))) ?_
  rw [Functor.whiskerLeft_comp, Category.assoc,
    derivedReductionUnit_whiskerLeft_Q.{d, d₀} f, ← Category.assoc,
    derivedTensorRightUnitIso_fac.{d} O]

end Deformation.ComplexLift

end
