module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProjectionFormulaUnitHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal

/-!
# The projection formula on morphisms out of the structure sheaf, with support

Let `X` be an algebraic space and `U ⊆ X` an open subspace whose closed complement `Z` lies in
the image of an étale `V ⟶ X`, i.e. `(U, V ⟶ X)` is an elementary distinguished square.

## Main results

* `AlgebraicGeometry.Space.cohomologySupportedOn_smallEtaleDerivedTensor_of_left`: if `A` is
  supported on `Z`, so is `A ⊗^L N` for every `N`.
* `AlgebraicGeometry.Space.isIso_unitHomProjectionFormulaEdsEtale_app`: the projection formula
  map on morphisms out of the structure sheaf is an isomorphism on `D_QCoh`.
* `AlgebraicGeometry.Space.isIso_unitHomRestrictProjectionEdsEtale_app`: for `A` supported on
  `Z`, restriction to `V` is an isomorphism on morphisms out of the structure sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Square

variable {W : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

include hsq in
/-- If `A` is supported on the complement `Z` of the open member `U` of the square, then so is
`A ⊗^L N` for every `N`: on `U` the restriction of `A ⊗^L N` is `A|_U ⊗^L N|_U`, which vanishes
with `A|_U`. -/
theorem cohomologySupportedOn_smallEtaleDerivedTensor_of_left
    (A N : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hA : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) A) :
    CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo)
      (((smallEtaleDerivedTensor B S hS W).obj A).obj N) := by
  let j := edsOpenHom B S hS hsq
  have hj := isEtale_edsOpenHom B S hS hsq
  have hA1 : IsZero ((smallEtaleDerivedModulePullback B S hS j).obj A) :=
    (isZero_etaleModulePullback_mapDerivedCategory_of_range_subset B S hS (Z := Uo.toFunctor)
      (i := Uo.ι) j hj A hA (range_pointsMap_edsOpenHom B S hS hsq).le).of_iso
      ((smallEtaleDerivedModulePullbackIsoEtale B S hS j hj).app A)
  have hT : IsZero (((smallEtaleDerivedTensor B S hS (edsOpen B S hS hsq)).obj
      ((smallEtaleDerivedModulePullback B S hS j).obj A)).obj
        ((smallEtaleDerivedModulePullback B S hS j).obj N)) := by
    have := (smallEtaleDerivedTensorSheafHomAdjunction B S hS (edsOpen B S hS hsq)
      ((smallEtaleDerivedModulePullback B S hS j).obj N)).isLeftAdjoint
    have := Functor.preservesZeroMorphisms_of_isLeftAdjoint
      ((smallEtaleDerivedTensor B S hS (edsOpen B S hS hsq)).flip.obj
        ((smallEtaleDerivedModulePullback B S hS j).obj N))
    exact Functor.map_isZero ((smallEtaleDerivedTensor B S hS (edsOpen B S hS hsq)).flip.obj
      ((smallEtaleDerivedModulePullback B S hS j).obj N)) hA1
  have hB : IsZero ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj
      (((smallEtaleDerivedTensor B S hS W).obj A).obj N)) :=
    hT.of_iso (((smallEtaleDerivedModulePullbackIsoEtale B S hS j hj).app _).symm ≪≫
      (smallEtaleDerivedPullbackTensorIso j).app (A, N))
  intro i x hx
  by_contra hxZ
  obtain ⟨y, rfl⟩ : x ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) := not_not.mp hxZ
  have hH : IsZero ((etaleModulePullback.{u, u} B S hS j hj).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS W.1 W.2) i).obj
        (((smallEtaleDerivedTensor B S hS W).obj A).obj N))) :=
    (Functor.map_isZero (DerivedCategory.homologyFunctor _ i) hB).of_iso
      (((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategoryHomologyIso i).app _).symm
  have hy := (supportOfSheaf_eq_empty_iff_isZero B S hS (edsOpen B S hS hsq) _).2 hH
  rw [supportOfSheaf_toSheaf_etaleModulePullback] at hy
  exact (Set.eq_empty_iff_forall_notMem.1 hy) y hx

/-- Étale restriction preserves `D_QCoh`. -/
theorem qcohDerived_etaleModulePullback_mapDerivedCategory {V : AlgebraicSpaces B S hS}
    (g : V ⟶ W) (hg : IsEtale B S hS g.hom)
    (A : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) (hA : QcohDerived B S hS W A) :
    QcohDerived B S hS V ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj A) :=
  fun n => SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategoryHomologyIso n).app A).symm
    (isQuasicoherentOnSite_etaleModulePullback B S hS g hg _ (hA n))

/-- **Restriction to the étale member of the square is bijective on morphisms into an object
supported on the complement of the open member**, read through `Lj^* ≅ j^*` and `Lj^*𝒪 ≅ 𝒪`:
`Hom(𝒪_W, E) ⟶ Hom(𝒪_V, Lj^*E)`, `g ↦ (Lj^*𝒪 ≅ 𝒪)⁻¹ ≫ Lj^* g`. -/
theorem bijective_unitHom_smallEtaleDerivedModulePullback_edsEtaleHom
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hE : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) E) :
    Function.Bijective (fun g : structureDerived W ⟶ E =>
      (smallEtaleDerivedPullbackUnitIso B S hS (edsEtaleHom B S hS hsq)).inv ≫
        (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).map g) := by
  let j := edsEtaleHom B S hS hsq
  have hj := isEtale_edsEtaleHom B S hS hsq
  let φ := smallEtaleDerivedModulePullbackIsoEtale B S hS j hj
  have h := isZero_edsOpen_and_edsInter_of_cohomologySupportedOn B S hS hsq E hE
  let e := Iso.homCongr ((φ.app (structureDerived W)).symm ≪≫
    smallEtaleDerivedPullbackUnitIso B S hS j) (φ.app E).symm
  have he : (fun g : structureDerived W ⟶ E =>
      (smallEtaleDerivedPullbackUnitIso B S hS j).inv ≫
        (smallEtaleDerivedModulePullback B S hS j).map g) =
      e ∘ (fun g : structureDerived W ⟶ E =>
        (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.map g) :=
    funext fun g => (congrArg (fun t => (smallEtaleDerivedPullbackUnitIso B S hS j).inv ≫ t)
      (NatIso.naturality_2 φ g).symm).trans (Category.assoc _ _ _).symm
  rw [he]
  exact e.bijective.comp
    (bijective_map_edsEtale_of_isZero_target B S hS hsq (structureDerived W) E h.1 h.2)

variable {Y : AlgebraicSpaces B S hS} (f : W ⟶ Y)
  (A : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W)))

/-- The restriction `Hom(𝒪_W, B) ⟶ Hom(𝒪_V, Lj^*B)` to the étale member of the square, as a
natural transformation of functors `D(𝒪_W) ⥤ AddCommGrpCat`. -/
def unitHomRestrictEdsEtale :
    preadditiveCoyoneda.obj (op (structureDerived W)) ⟶
      smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq) ⋙
        preadditiveCoyoneda.obj (op (structureDerived (edsEtale B S hS hsq))) where
  app E := AddCommGrpCat.ofHom
    ((Preadditive.leftComp _
      (smallEtaleDerivedPullbackUnitIso B S hS (edsEtaleHom B S hS hsq)).inv).comp
      ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).mapAddHom))
  naturality E E' k := by
    ext g
    exact ((Category.assoc _ _ _).trans (congrArg _
      ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).map_comp g k).symm)).symm

/-- `L(j ≫ f)^* ⋙ (Lj^*A ⊗^L -) ≅ Lf^* ⋙ (A ⊗^L -) ⋙ Lj^*`: the composition of derived
pullbacks and Stacks 07A4 for `j`. -/
def smallEtaleDerivedPullbackCompTensorIso :
    smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq ≫ f) ⋙
        (smallEtaleDerivedTensor B S hS (edsEtale B S hS hsq)).obj
          ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj A) ≅
      smallEtaleDerivedModulePullback B S hS f ⋙ (smallEtaleDerivedTensor B S hS W).obj A ⋙
        smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq) :=
  Functor.isoWhiskerRight (smallEtaleDerivedModulePullbackCompIso B S hS
      (edsEtaleHom B S hS hsq) f).symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (smallEtaleDerivedModulePullback B S hS f)
      (NatIso.ofComponents
        (F := smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq) ⋙
          (smallEtaleDerivedTensor B S hS (edsEtale B S hS hsq)).obj
            ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj A))
        (G := (smallEtaleDerivedTensor B S hS W).obj A ⋙
          smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq))
        (fun N => ((smallEtaleDerivedPullbackTensorIso (edsEtaleHom B S hS hsq)).app (A, N)).symm)
        (fun {N N'} g => by
          simpa using (smallEtaleDerivedPullbackTensorIso (edsEtaleHom B S hS hsq)).inv.naturality
            ((𝟙 A, g) : (A, N) ⟶ (A, N'))))

/-- `Hom(𝒪_Y, K ⊗^L M) ⟶ Hom(𝒪_V, Lj^*A ⊗^L L(j ≫ f)^*M)` for an identification
`K ≅ R(j ≫ f)_*(Lj^*A)`: the projection formula map of `j ≫ f`. -/
def unitHomProjectionFormulaEdsEtale
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (e : K ≅ (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _)
      (smallEtaleRingedToposHom B S hS (edsEtaleHom B S hS hsq ≫ f))).obj
        ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj A)) :
    (smallEtaleDerivedTensor B S hS Y).obj K ⋙ preadditiveCoyoneda.obj (op (structureDerived Y)) ⟶
      smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq ≫ f) ⋙
        (smallEtaleDerivedTensor B S hS (edsEtale B S hS hsq)).obj
          ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj A) ⋙
        preadditiveCoyoneda.obj (op (structureDerived (edsEtale B S hS hsq))) :=
  Functor.whiskerRight ((smallEtaleDerivedTensor B S hS Y).map e.hom)
      (preadditiveCoyoneda.obj (op (structureDerived Y))) ≫
    unitHomProjectionFormula B S hS (edsEtaleHom B S hS hsq ≫ f)
      ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj A)

/-- `Hom(𝒪_W, A ⊗^L Lf^*M) ⟶ Hom(𝒪_V, Lj^*A ⊗^L L(j ≫ f)^*M)`: restriction to `V`. -/
def unitHomRestrictProjectionEdsEtale :
    smallEtaleDerivedModulePullback B S hS f ⋙ (smallEtaleDerivedTensor B S hS W).obj A ⋙
        preadditiveCoyoneda.obj (op (structureDerived W)) ⟶
      smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq ≫ f) ⋙
        (smallEtaleDerivedTensor B S hS (edsEtale B S hS hsq)).obj
          ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj A) ⋙
        preadditiveCoyoneda.obj (op (structureDerived (edsEtale B S hS hsq))) :=
  Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS f ⋙
      (smallEtaleDerivedTensor B S hS W).obj A) (unitHomRestrictEdsEtale B S hS hsq) ≫
    Functor.whiskerRight (smallEtaleDerivedPullbackCompTensorIso B S hS hsq f A).inv
      (preadditiveCoyoneda.obj (op (structureDerived (edsEtale B S hS hsq))))

/-- For `j ≫ f` quasi-compact and quasi-separated, `Lj^*A` in `D_QCoh` and `M` in `D_QCoh(𝒪_Y)`,
the map `Hom(𝒪_Y, K ⊗^L M) ⟶ Hom(𝒪_V, Lj^*A ⊗^L L(j ≫ f)^*M)` is an isomorphism. -/
theorem isIso_unitHomProjectionFormulaEdsEtale_app
    (hfqc : IsQuasiCompact B S hS (edsEtaleHom B S hS hsq ≫ f).hom)
    (hfqs : IsQuasiSeparated B S hS (edsEtaleHom B S hS hsq ≫ f).hom)
    (hA : QcohDerived B S hS (edsEtale B S hS hsq)
      ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj A))
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (e : K ≅ (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _)
      (smallEtaleRingedToposHom B S hS (edsEtaleHom B S hS hsq ≫ f))).obj
        ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj A))
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hM : QcohDerived B S hS Y M) :
    IsIso ((unitHomProjectionFormulaEdsEtale B S hS hsq f A K e).app M) := by
  have := isIso_unitHomProjectionFormula_app B S hS (edsEtaleHom B S hS hsq ≫ f)
    hfqc hfqs _ hA M hM
  rw [unitHomProjectionFormulaEdsEtale, NatTrans.comp_app]
  infer_instance

/-- If `A` is supported on the complement of the open member of the square, then restriction
`Hom(𝒪_W, A ⊗^L Lf^*M) ⟶ Hom(𝒪_V, Lj^*A ⊗^L L(j ≫ f)^*M)` is an isomorphism for every `M`. -/
theorem isIso_unitHomRestrictProjectionEdsEtale_app
    (hA : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) A)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    IsIso ((unitHomRestrictProjectionEdsEtale B S hS hsq f A).app M) := by
  have : IsIso ((Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS f ⋙
      (smallEtaleDerivedTensor B S hS W).obj A) (unitHomRestrictEdsEtale B S hS hsq)).app M) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_unitHom_smallEtaleDerivedModulePullback_edsEtaleHom B S hS hsq _
        (cohomologySupportedOn_smallEtaleDerivedTensor_of_left B S hS hsq A
          ((smallEtaleDerivedModulePullback B S hS f).obj M) hA))
  rw [unitHomRestrictProjectionEdsEtale, NatTrans.comp_app]
  infer_instance

end Square

end AlgebraicGeometry.Space

end
