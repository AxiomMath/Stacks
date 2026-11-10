module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorUnitors
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaUnit
public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportUnitSourceConjugate
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp

/-!
# The projection formula at the structure sheaf, and the underived core of Stacks 0B4B

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces, with unit
`u : 𝒪_X ⟶ i_* 𝒪_Z` (`RingedSpaceModuleAdjunction.structureSheafModuleHom`). Two natural
transformations `𝟭 ⟶ (i_* 𝒪_Z) ⊗_{𝒪_X} -` present themselves:

* the unit `𝟭 ⟶ i_* i^*` of [Stacks, Tag 0096], followed by the inverse left unitor on `Z`
  whiskered into `i^*` and then by `i_*`, and then by the inverse of the projection formula
  `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`
  `.projectionFormulaLeftAdjointIso`;
* the inverse left unitor on `X`, followed by `u ⊗_{𝒪_X} -`.

This file proves that they agree, and deduces the identity

`0E2I at the source 𝒪_Z ≫ (trivialisation of ℰom_{𝒪_Z}(𝒪_Z, -)) ≫ (trace of 0A75)`
`= (restriction along u) ≫ (trivialisation of ℰom_{𝒪_X}(𝒪_X, -))`

of natural transformations `ℰom_{𝒪_X}(i_* 𝒪_Z, -) ⟶ 𝟭`.

## Main results

* `CategoryTheory.MonoidalCategory.reseat_leftUnitor_inv`: the inverse of the left unitor of a
  re-seated monoidal structure is the inverse left unitor of the given one, followed by the unit
  comparison whiskered on the right and by the component of the tensor comparison.
* `Stacks.RingedSpace.comparison_leftUnitor_inv`: the left-unitor coherence of
  [Stacks, Tag 01CD], inverted: the pullback of the inverse left unitor on the target, followed
  by the comparison morphism and by `ν ⊗ 𝟙`, is the inverse left unitor on the source.
* `Stacks.SheafOfModules.InternalHom.conjugateEquiv_symm_internalHomSecondFunctorUnitIso_app`:
  the conjugate preimage of the trivialisation of `ℰom_O(O, -)` is, componentwise, the inverse
  of the left unitor of the re-seated monoidal structure on `Mod(O)`.
* `Stacks.SheafOfModules.InternalHom.internalHomPrecompNatTrans_comp_unitIso_symm`: evaluation
  at the unit section along `u`, as a conjugate, with the inverse left unitor named as that
  conjugate preimage.
* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`
  `.unit_comp_whiskered_inverseLeftUnitor_comp_projectionFormulaLeftAdjointIso`: the projection
  formula at the structure sheaf, composed with the inverse unitors, is the unit of
  `i^* ⊣ i_*`.
* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`
  `.sheafHomPushforwardNatIso_comp_unitIso_comp_counit`: the underived [Stacks, Tag 0E2I]
  isomorphism at the source `𝒪_Z`, followed by the trivialisation of `ℰom_{𝒪_Z}(𝒪_Z, -)` and the
  trace of [Stacks, Tag 0A75], is restriction along the unit `𝒪_X ⟶ i_* 𝒪_Z` followed by the
  trivialisation of `ℰom_{𝒪_X}(𝒪_X, -)`.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open RingedSpaceModuleAdjunction
open Stacks.RingedSpace
open Stacks.AffineProjectionFormula
open scoped CategoryTheory.Prod

noncomputable section

namespace CategoryTheory.MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {T : C ⥤ C ⥤ C} {U : C}

/-- **The inverse of the left unitor of a re-seated monoidal structure.**  For
`e : curriedTensor C ≅ T` and `ε : 𝟙_ C ≅ U` the left unitor of
`CategoryTheory.MonoidalCategory.reseat e ε` at `X` is, by construction, the component of `e` at
`(U, X)` inverted, then `ε` inverted tensored with the identity, then the given left unitor; so
its inverse is the given inverse left unitor, then `ε` whiskered by `X`, then the component of
`e`. -/
theorem reseat_leftUnitor_inv (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) (X : C) :
    (@MonoidalCategoryStruct.leftUnitor _ _ (reseat e ε).toMonoidalCategoryStruct X).inv =
      (λ_ X).inv ≫ ((tensoringLeft C).map ε.hom).app X ≫ (reseatIso e U X).hom := by
  change (λ_ X).inv ≫ _ = _
  simp [tensorHom_id]

end CategoryTheory.MonoidalCategory

namespace Stacks.RingedSpace

universe u

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The isomorphism `f^*𝒪_Y ≅ 𝒪_X` of `Stacks.RingedSpace.pullbackObjUnitIso` has for its
forward map the transpose `RingedSpaceModuleAdjunction.modulePullbackUnitToUnit` of the
structure-sheaf map. -/
theorem pullbackObjUnitIso_hom :
    (pullbackObjUnitIso f).hom = modulePullbackUnitToUnit f := rfl

/-- **The left-unitor coherence of [Stacks, Tag 01CD], inverted.**  The pullback of the inverse
left unitor `A ≅ 𝒪_Y ⊗_{𝒪_Y} A` on the target, followed by the comparison morphism
`f^*(𝒪_Y ⊗_{𝒪_Y} A) ⟶ f^*𝒪_Y ⊗_{𝒪_X} f^*A` and by `ν ⊗ 𝟙`, is the inverse left unitor
`f^*A ≅ 𝒪_X ⊗_{𝒪_X} f^*A` on the source. -/
theorem comparison_leftUnitor_inv (A : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    (pullbackFunctor f).map (tensorSheafUnitLeftIso Y A).inv ≫
        comparison f (_root_.SheafOfModules.unit (structureRingSheaf Y)) A ≫
          ((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩))).map
            (((pullbackObjUnitIso f).hom ×ₘ 𝟙 ((pullbackFunctor f).obj A)) :
              (((pullbackFunctor f).obj (_root_.SheafOfModules.unit (structureRingSheaf Y)),
                  (pullbackFunctor f).obj A) : _ × _) ⟶
                (_root_.SheafOfModules.unit (structureRingSheaf X),
                  (pullbackFunctor f).obj A)) =
      (tensorSheafUnitLeftIso X ((pullbackFunctor f).obj A)).inv := by
  have h2 : comparison f (_root_.SheafOfModules.unit (structureRingSheaf Y)) A ≫
        ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩))).map
          (((pullbackObjUnitIso f).hom ×ₘ 𝟙 ((pullbackFunctor f).obj A)) :
            (((pullbackFunctor f).obj (_root_.SheafOfModules.unit (structureRingSheaf Y)),
                (pullbackFunctor f).obj A) : _ × _) ⟶
              (_root_.SheafOfModules.unit (structureRingSheaf X),
                (pullbackFunctor f).obj A)) =
      (pullbackFunctor f).map (tensorSheafUnitLeftIso Y A).hom ≫
        (tensorSheafUnitLeftIso X ((pullbackFunctor f).obj A)).inv :=
      (Iso.eq_comp_inv _).mpr ((Category.assoc _ _ _).trans (comparison_leftUnitor f A))
  rw [h2]
  exact Iso.inv_hom_id_map_assoc (tensorSheafUnitLeftIso Y A) (pullbackFunctor f) _

end Stacks.RingedSpace

namespace Stacks.SheafOfModules.InternalHom

universe u

variable {D : Type u} [Category.{u} D] (K : GrothendieckTopology D)
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (O : Sheaf K CommRingCat.{u})
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] _root_.SheafOfModules.monoidalCategory
  _root_.SheafOfModules.monoidalClosed

omit [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The conjugate preimage of the trivialisation of `ℰom_O(O, -)` is the inverse left unitor
of the tensor product sheaf**: componentwise, it is the inverse of the left unitor of the
re-seated monoidal structure `SheafOfModules.monoidalCategorySheafTensor`. -/
theorem conjugateEquiv_symm_internalHomSecondFunctorUnitIso_app
    (A : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O)) :
    ((conjugateEquiv
          (sheafTensorHomAdjunction O
            (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O)))
          Adjunction.id).symm (internalHomSecondFunctorUnitIso O).hom).app A =
      (@MonoidalCategoryStruct.leftUnitor _ _
        (_root_.SheafOfModules.monoidalCategorySheafTensor O).toMonoidalCategoryStruct
        A).inv := by
  rw [internalHomSecondFunctorUnitIso_hom_eq_sheafTensor O, Equiv.symm_apply_apply,
    MonoidalCategory.reseat_leftUnitor_inv]
  rfl

omit [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Evaluation at the unit section along `u : O ⟶ M`, as a conjugate, with the inverse left
unitor named as the conjugate preimage of the trivialisation.** -/
theorem internalHomPrecompNatTrans_comp_unitIso_symm
    {M : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O)}
    (u : _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O) ⟶ M) :
    internalHomPrecompNatTrans K O u ≫ (internalHomSecondFunctorUnitIso O).hom =
      conjugateEquiv (sheafTensorHomAdjunction O M) Adjunction.id
        ((conjugateEquiv
              (sheafTensorHomAdjunction O
                (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O)))
              Adjunction.id).symm (internalHomSecondFunctorUnitIso O).hom ≫
          (Stacks.SheafOfModules.Tensor.sheafTensor O).map u) := by
  have hUnitIso : conjugateEquiv
        (sheafTensorHomAdjunction O
          (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O)))
        Adjunction.id
        ((conjugateEquiv
            (sheafTensorHomAdjunction O
              (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O)))
            Adjunction.id).symm (internalHomSecondFunctorUnitIso O).hom) =
      (internalHomSecondFunctorUnitIso O).hom :=
    Equiv.apply_symm_apply _ _
  rw [← conjugateEquiv_comp (sheafTensorHomAdjunction O M)
      (sheafTensorHomAdjunction O
        (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O)))
      Adjunction.id,
    hUnitIso, conjugateEquiv_sheafTensor_map_precomp K O u]

end Stacks.SheafOfModules.InternalHom

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

open Stacks.SheafOfModules.InternalHom

universe u

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- The structure sheaf of the ambient space `X` as a module over itself, in the spelling of the
ringed site `siteX` — the spelling the trivialisation
`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctorUnitIso` is stated in. -/
abbrev structureSheafModuleX : SheafOfModules.{u} (structureSheafRing S.X) :=
  _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.siteX)) S.X.sheaf)

/-! ### Tensoring by the unit and the projection-formula map -/

/-- The unit `u : 𝒪_X ⟶ i_* 𝒪_Z` is the unit of `i^* ⊣ i_*` at `𝒪_X` followed by `i_*` of the
transpose `i^* 𝒪_X ⟶ 𝒪_Z`, so tensoring by it factors accordingly. -/
theorem sheafTensor_structureSheafModuleHom_app
    (F : SheafOfModules.{u} (structureSheafRing S.X)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.X).presheaf, (S.X).IsSheaf⟩).map
          (structureSheafModuleHom S.i)).app F =
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.X).presheaf, (S.X).IsSheaf⟩).map
            ((modulePullbackPushforwardAdjunction S.i).unit.app
              (_root_.SheafOfModules.unit (structureSheafRing S.X)))).app F ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.X).presheaf, (S.X).IsSheaf⟩).map
          ((modulePushforward S.i).map (modulePullbackUnitToUnit S.i))).app F :=
  Eq.trans
    (congrArg (fun k ↦
        ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.X).presheaf, (S.X).IsSheaf⟩).map k).app F)
      (Eq.trans (homEquiv_modulePullbackUnitToUnit S.i).symm
        (Adjunction.homEquiv_unit (modulePullbackPushforwardAdjunction S.i) _ _
          (modulePullbackUnitToUnit S.i))))
    (Eq.trans
      (congrArg (fun t ↦ NatTrans.app t F)
        ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.X).presheaf, (S.X).IsSheaf⟩).map_comp _ _))
      (NatTrans.comp_app _ _ F))

/-- **Tensoring the unit of `i^* ⊣ i_*` at `𝒪_X` and then applying the projection-formula map
is the transpose of the comparison morphism of [Stacks, Tag 01CD].** -/
theorem sheafTensor_unit_app_comp_projectionFormulaMap
    (F : SheafOfModules.{u} (structureSheafRing S.X)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.X).presheaf, (S.X).IsSheaf⟩).map
            ((modulePullbackPushforwardAdjunction S.i).unit.app
              (_root_.SheafOfModules.unit (structureSheafRing S.X)))).app F ≫
        projectionFormulaMap S.i
          ((modulePullback S.i).obj (_root_.SheafOfModules.unit (structureSheafRing S.X))) F =
      (modulePullbackPushforwardAdjunction S.i).unit.app
          (((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S.X)).presheaf, ((S.X)).IsSheaf⟩))).obj
            (_root_.SheafOfModules.unit (structureSheafRing S.X), F)) ≫
        (modulePushforward S.i).map
          (Stacks.RingedSpace.comparison S.i
            (_root_.SheafOfModules.unit (structureSheafRing S.X)) F) :=
  Eq.trans
    (congrArg
      (fun t ↦ t ≫ projectionFormulaMap S.i
        ((modulePullback S.i).obj (_root_.SheafOfModules.unit (structureSheafRing S.X))) F)
      (sheafTensor_map_app_eq S.X
        ((modulePullbackPushforwardAdjunction S.i).unit.app
          (_root_.SheafOfModules.unit (structureSheafRing S.X))) F))
    (Eq.trans
      (projectionFormulaMap_natural_unit S.i
        (_root_.SheafOfModules.unit (structureSheafRing S.X)) F)
      (Adjunction.homEquiv_unit (modulePullbackPushforwardAdjunction S.i) _ _ _))

/-- **Tensoring by the unit `u : 𝒪_X ⟶ i_* 𝒪_Z` and then applying the projection-formula map at
`𝒪_Z` is the unit of `i^* ⊣ i_*` followed by `i_*` of the comparison morphism of
[Stacks, Tag 01CD] and `ν ⊗ 𝟙`.** -/
theorem sheafTensor_structureSheafModuleHom_app_comp_projectionFormulaMap
    (F : SheafOfModules.{u} (structureSheafRing S.X)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.X).presheaf, (S.X).IsSheaf⟩).map
            (structureSheafModuleHom S.i)).app F ≫
        projectionFormulaMap S.i S.structureSheafModuleZ F =
      (modulePullbackPushforwardAdjunction S.i).unit.app
          (((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S.X)).presheaf, ((S.X)).IsSheaf⟩))).obj
            (_root_.SheafOfModules.unit (structureSheafRing S.X), F)) ≫
        (modulePushforward S.i).map
          (Stacks.RingedSpace.comparison S.i
              (_root_.SheafOfModules.unit (structureSheafRing S.X)) F ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.Z).presheaf, (S.Z).IsSheaf⟩).map
              (modulePullbackUnitToUnit S.i)).app ((modulePullback S.i).obj F)) := by
  refine Eq.trans
    (congrArg (fun t ↦ t ≫ projectionFormulaMap S.i S.structureSheafModuleZ F)
      (S.sheafTensor_structureSheafModuleHom_app F)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans
    (congrArg
      (fun t ↦ ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.X).presheaf, (S.X).IsSheaf⟩).map
          ((modulePullbackPushforwardAdjunction S.i).unit.app
            (_root_.SheafOfModules.unit (structureSheafRing S.X)))).app F ≫ t)
      (projectionFormulaMap_natural_first S.i (modulePullbackUnitToUnit S.i) F).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans
    (congrArg
      (fun t ↦ t ≫ (modulePushforward S.i).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.Z).presheaf, (S.Z).IsSheaf⟩).map
          (modulePullbackUnitToUnit S.i)).app ((modulePullback S.i).obj F)))
      (S.sheafTensor_unit_app_comp_projectionFormulaMap F)) ?_
  exact Eq.trans (Category.assoc _ _ _)
    (congrArg
      (fun t ↦ (modulePullbackPushforwardAdjunction S.i).unit.app
        (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S.X)).presheaf, ((S.X)).IsSheaf⟩))).obj
          (_root_.SheafOfModules.unit (structureSheafRing S.X), F)) ≫ t)
      ((modulePushforward S.i).map_comp _ _).symm)

/-! ### The projection formula at the structure sheaf -/

/-- **The left-unitor coherence of [Stacks, Tag 01CD] at a closed quotient morphism**, in the
`Stacks.SheafOfModules.Tensor.sheafTensor` spelling: the pullback of the inverse left unitor on
`X`, followed by the comparison morphism and by `ν ⊗ 𝟙`, is the inverse left unitor on `Z` at
`i^* F`. -/
theorem inverseLeftUnitor_pullback (F : SheafOfModules.{u} (structureSheafRing S.X)) :
    (modulePullback S.i).map (Stacks.RingedSpace.tensorSheafUnitLeftIso S.X F).inv ≫
        Stacks.RingedSpace.comparison S.i
            (_root_.SheafOfModules.unit (structureSheafRing S.X)) F ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.Z).presheaf, (S.Z).IsSheaf⟩).map
            (modulePullbackUnitToUnit S.i)).app ((modulePullback S.i).obj F) =
      (Stacks.RingedSpace.tensorSheafUnitLeftIso S.Z ((modulePullback S.i).obj F)).inv :=
  Eq.trans
    (congrArg
      (fun t ↦ (modulePullback S.i).map
          (Stacks.RingedSpace.tensorSheafUnitLeftIso S.X F).inv ≫
        Stacks.RingedSpace.comparison S.i
          (_root_.SheafOfModules.unit (structureSheafRing S.X)) F ≫ t)
      (sheafTensor_map_app_eq S.Z (modulePullbackUnitToUnit S.i)
        ((modulePullback S.i).obj F)))
    (Stacks.RingedSpace.comparison_leftUnitor_inv S.i F)

/-- The unit of `i^* ⊣ i_*` at `F`, followed by `i_*` of the inverse left unitor on `Z` at `i^* F`,
is the inverse left unitor on `X` at `F` followed by tensoring with the unit `u : 𝒪_X ⟶ i_* 𝒪_Z`
and the projection-formula map. -/
theorem unit_comp_inverseLeftUnitor_app (F : SheafOfModules.{u} (structureSheafRing S.X)) :
    (modulePullbackPushforwardAdjunction S.i).unit.app F ≫
        (modulePushforward S.i).map
          (Stacks.RingedSpace.tensorSheafUnitLeftIso S.Z
            ((modulePullback S.i).obj F)).inv =
      (Stacks.RingedSpace.tensorSheafUnitLeftIso S.X F).inv ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.X).presheaf, (S.X).IsSheaf⟩).map
              (structureSheafModuleHom S.i)).app F ≫
          projectionFormulaMap S.i S.structureSheafModuleZ F := by
  refine Eq.trans ?_
    (congrArg
      (fun t ↦ (Stacks.RingedSpace.tensorSheafUnitLeftIso S.X F).inv ≫ t)
      (S.sheafTensor_structureSheafModuleHom_app_comp_projectionFormulaMap F)).symm
  refine Eq.trans
    (congrArg
      (fun t ↦ (modulePullbackPushforwardAdjunction S.i).unit.app F ≫
        (modulePushforward S.i).map t)
      (S.inverseLeftUnitor_pullback F).symm) ?_
  refine Eq.trans
    (congrArg
      (fun t ↦ (modulePullbackPushforwardAdjunction S.i).unit.app F ≫ t)
      ((modulePushforward S.i).map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans
    (congrArg
      (fun t ↦ t ≫ (modulePushforward S.i).map
        (Stacks.RingedSpace.comparison S.i
            (_root_.SheafOfModules.unit (structureSheafRing S.X)) F ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.Z).presheaf, (S.Z).IsSheaf⟩).map
            (modulePullbackUnitToUnit S.i)).app ((modulePullback S.i).obj F)))
      ((modulePullbackPushforwardAdjunction S.i).unit_naturality
        (Stacks.RingedSpace.tensorSheafUnitLeftIso S.X F).inv)) ?_
  exact Category.assoc _ _ _

/-- The conjugate preimage of the trivialisation of `ℰom_{𝒪_W}(𝒪_W, -)` is the inverse left
unitor `Stacks.RingedSpace.tensorSheafUnitLeftIso` on a ringed space `W`. -/
private theorem conjugate_symm_unitIso_app_eq_inv_leftUnitor (W : RingedSpace.{u, u})
    (A : SheafOfModules.{u} (structureSheafRing W)) :
    ((conjugateEquiv (sheafTensorHomAdjunction W.sheaf
          (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
            (J := _root_.Opens.grothendieckTopology W.carrier)) W.sheaf)))
          Adjunction.id).symm (internalHomSecondFunctorUnitIso W.sheaf).hom).app A =
      (Stacks.RingedSpace.tensorSheafUnitLeftIso W A).inv :=
  Eq.trans
    (conjugateEquiv_symm_internalHomSecondFunctorUnitIso_app
      (_root_.Opens.grothendieckTopology W.carrier) W.sheaf A)
    (congrArg Iso.inv (Iso.ext (Stacks.RingedSpace.leftUnitor_sheafTensor_eq W A)))

/-- **The conjugate preimage of the trivialisation of `ℰom_{𝒪_Z}(𝒪_Z, -)` is the inverse left
unitor `Stacks.RingedSpace.tensorSheafUnitLeftIso` on `Z`.** -/
theorem inverseLeftUnitor_app_Z (A : SheafOfModules.{u} (structureSheafRing S.Z)) :
    ((conjugateEquiv (sheafTensorHomAdjunction S.Z.sheaf S.structureSheafModuleZ)
          Adjunction.id).symm (internalHomSecondFunctorUnitIso S.Z.sheaf).hom).app A =
      (Stacks.RingedSpace.tensorSheafUnitLeftIso S.Z A).inv :=
  conjugate_symm_unitIso_app_eq_inv_leftUnitor S.Z A

/-- **The conjugate preimage of the trivialisation of `ℰom_{𝒪_X}(𝒪_X, -)` is the inverse left
unitor `Stacks.RingedSpace.tensorSheafUnitLeftIso` on `X`.** -/
theorem inverseLeftUnitor_app_X (A : SheafOfModules.{u} (structureSheafRing S.X)) :
    ((conjugateEquiv (sheafTensorHomAdjunction S.X.sheaf S.structureSheafModuleX)
          Adjunction.id).symm (internalHomSecondFunctorUnitIso S.X.sheaf).hom).app A =
      (Stacks.RingedSpace.tensorSheafUnitLeftIso S.X A).inv :=
  conjugate_symm_unitIso_app_eq_inv_leftUnitor S.X A

/-- **The projection formula at the structure sheaf, composed with the inverse unitors, is the unit
of `i^* ⊣ i_*`.** Both sides are natural transformations `𝟭 ⟶ (i_* 𝒪_Z) ⊗_{𝒪_X} -`: on the left the
unit `𝟭 ⟶ i_* i^*` of [Stacks, Tag 0096] followed by the inverse left unitor on `Z` whiskered into
`i^*` and then by `i_*`, and then by the inverse of the projection formula
`projectionFormulaLeftAdjointIso`; on the right the inverse left unitor on `X` followed by
`u ⊗_{𝒪_X} -`, the inverse left unitors appearing as conjugate preimages of the trivialisations of
[Stacks, Tag 03EM]. -/
theorem unit_comp_whiskered_inverseLeftUnitor_comp_projectionFormulaLeftAdjointIso :
    ((modulePullbackPushforwardAdjunction S.i).unit ≫
          Functor.whiskerLeft (modulePullback S.i)
            (Functor.whiskerRight
              ((conjugateEquiv (sheafTensorHomAdjunction S.Z.sheaf S.structureSheafModuleZ)
                  Adjunction.id).symm (internalHomSecondFunctorUnitIso S.Z.sheaf).hom)
              (modulePushforward S.i))) ≫
        (S.projectionFormulaLeftAdjointIso S.structureSheafModuleZ).inv =
      (conjugateEquiv (sheafTensorHomAdjunction S.X.sheaf S.structureSheafModuleX)
            Adjunction.id).symm (internalHomSecondFunctorUnitIso S.X.sheaf).hom ≫
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.X).presheaf, (S.X).IsSheaf⟩).map
          (structureSheafModuleHom S.i) := by
  refine (Iso.comp_inv_eq _).mpr (NatTrans.ext (funext fun F ↦ ?_))
  change (modulePullbackPushforwardAdjunction S.i).unit.app F ≫
        (modulePushforward S.i).map
          (((conjugateEquiv (sheafTensorHomAdjunction S.Z.sheaf S.structureSheafModuleZ)
              Adjunction.id).symm
              (internalHomSecondFunctorUnitIso S.Z.sheaf).hom).app
            ((modulePullback S.i).obj F)) =
      (((conjugateEquiv (sheafTensorHomAdjunction S.X.sheaf S.structureSheafModuleX)
              Adjunction.id).symm
              (internalHomSecondFunctorUnitIso S.X.sheaf).hom).app F ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.X).presheaf, (S.X).IsSheaf⟩).map
            (structureSheafModuleHom S.i)).app F) ≫
        projectionFormulaMap S.i S.structureSheafModuleZ F
  refine Eq.trans
    (congrArg
      (fun t ↦ (modulePullbackPushforwardAdjunction S.i).unit.app F ≫
        (modulePushforward S.i).map t)
      (S.inverseLeftUnitor_app_Z ((modulePullback S.i).obj F))) ?_
  refine Eq.trans (S.unit_comp_inverseLeftUnitor_app F) ?_
  exact Eq.trans
    (congrArg
      (fun t ↦ t ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.X).presheaf, (S.X).IsSheaf⟩).map
            (structureSheafModuleHom S.i)).app F ≫
          projectionFormulaMap S.i S.structureSheafModuleZ F)
      (S.inverseLeftUnitor_app_X F).symm)
    (Category.assoc _ _ _).symm

/-! ### Restriction along the unit and the trace of Tag 0A75 -/

/-- The underived [Stacks, Tag 0E2I] isomorphism `sheafHomPushforwardNatIso` at the source `𝒪_Z`,
followed by the trivialisation of `ℰom_{𝒪_Z}(𝒪_Z, -)`
(`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctorUnitIso`, whiskered into the
exact-support functor of [Stacks, Tag 0A75] and then by `i_*`) and by the trace of
[Stacks, Tag 0A75], is restriction along the unit `u : 𝒪_X ⟶ i_* 𝒪_Z` followed by the
trivialisation of `ℰom_{𝒪_X}(𝒪_X, -)`. Both sides are natural transformations
`ℰom_{𝒪_X}(i_* 𝒪_Z, -) ⟶ 𝟭`. -/
theorem sheafHomPushforwardNatIso_comp_unitIso_comp_counit :
    (S.sheafHomPushforwardNatIso S.structureSheafModuleZ).hom ≫
        Functor.whiskerRight
              (Functor.whiskerLeft S.sheafHomExactSupport
                (internalHomSecondFunctorUnitIso S.Z.sheaf).hom) (modulePushforward S.i) ≫
            S.modulePushforwardSheafHomExactSupportAdjunction.counit =
      internalHomPrecompNatTrans S.siteX S.X.sheaf (structureSheafModuleHom S.i) ≫
        (internalHomSecondFunctorUnitIso S.X.sheaf).hom := by
  refine Eq.trans
    (congrArg
      (fun t ↦ t ≫
        Functor.whiskerRight
              (Functor.whiskerLeft S.sheafHomExactSupport
                (internalHomSecondFunctorUnitIso S.Z.sheaf).hom) (modulePushforward S.i) ≫
            S.modulePushforwardSheafHomExactSupportAdjunction.counit)
      (S.sheafHomPushforwardNatIso_hom S.structureSheafModuleZ)) ?_
  refine Eq.trans
    (congrArg
      (fun t ↦ conjugateEquiv (S.tensorPushforwardAdjunction S.structureSheafModuleZ)
        (S.pushforwardTensorPullbackAdjunction S.structureSheafModuleZ)
        (S.projectionFormulaLeftAdjointIso S.structureSheafModuleZ).inv ≫ t)
      S.internalHomSecondFunctorUnitIso_whiskered_comp_counit) ?_
  refine Eq.trans
    (conjugateEquiv_comp (S.tensorPushforwardAdjunction S.structureSheafModuleZ)
      (S.pushforwardTensorPullbackAdjunction S.structureSheafModuleZ) Adjunction.id
      (S.projectionFormulaLeftAdjointIso S.structureSheafModuleZ).inv
      ((modulePullbackPushforwardAdjunction S.i).unit ≫
        Functor.whiskerLeft (modulePullback S.i)
          (Functor.whiskerRight
            ((conjugateEquiv (sheafTensorHomAdjunction S.Z.sheaf S.structureSheafModuleZ)
                Adjunction.id).symm (internalHomSecondFunctorUnitIso S.Z.sheaf).hom)
            (modulePushforward S.i)))) ?_
  refine Eq.trans
    (congrArg
      (conjugateEquiv (S.tensorPushforwardAdjunction S.structureSheafModuleZ) Adjunction.id)
      S.unit_comp_whiskered_inverseLeftUnitor_comp_projectionFormulaLeftAdjointIso) ?_
  exact (internalHomPrecompNatTrans_comp_unitIso_symm S.siteX S.X.sheaf
    (structureSheafModuleHom S.i)).symm

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end

end
