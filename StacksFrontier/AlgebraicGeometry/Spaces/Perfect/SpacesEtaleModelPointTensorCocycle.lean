module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointTensorPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelHomCompCocycle

/-!
# Inverse images to a point and base change: compatibility with composition

For a morphism `g : X' ⟶ X` of algebraic spaces and ring maps `ψ : A ⟶ Γ(X, 𝒪_X)`,
`ψ' : A' ⟶ Γ(X', 𝒪_{X'})`, `α : A ⟶ A'` with `ψ' ∘ α = g^* ∘ ψ`,
`AlgebraicGeometry.Space.spacesEtaleModelToPointPullbackCompIso` identifies
`g^*(𝒪_X ⊗_A M)` with `𝒪_{X'} ⊗_{A'} (A' ⊗_A M)` on the models of the spaces-étale sites.
This file proves that these identifications are compatible with composition: for a second
morphism `g' : X'' ⟶ X'` the two identifications of `g'^* g^* (𝒪_X ⊗_A M)` with
`𝒪_{X''} ⊗_{A''} (A'' ⊗_A M)`, one in two steps through `X'` and one through the composite
`g' ≫ g`, agree.

All the isomorphisms involved are comparisons of left adjoints, so the identity is checked on
the adjoint mates; these are maps between sections of a sheaf of modules over terminal objects of
the site of `X''`, given by restriction along maps into a terminal object, hence equal.

## Main results

* `CategoryTheory.Adjunction.comp_assoc_eq`: composition of adjunctions is associative.
* `AlgebraicGeometry.conjugateEquiv_toPointPullbackCompIso_hom`,
  `AlgebraicGeometry.Space.conjugateEquiv_spacesEtaleModelToPointPullbackCompIso_hom`: the adjoint
  mates of the identifications are the identifications of sections functors.
* `AlgebraicGeometry.Space.spacesEtaleModelToPointPullbackCompIso_comp`: the compatibility with
  composition.
* `DerivedPullbackOnRingedTopoi.derivedPullbackObjIsoOfIsIsoComparison_hom_naturality`:
  the computation of `Lf^*` on complexes with invertible comparison map is natural.
* `Space.spacesEtaleModelDerivedPullbackCompIso_hom_app_derivedPullbackObjIsoOfIsIsoComparison`:
  that computation is compatible with the composition isomorphisms of derived pullbacks.
* `AlgebraicGeometry.Space.derivedPullbackPointTensorIso_hom_naturality`: the identifications
  `Lg^* T_ψ(C) ≅ T_{ψ'}(A' ⊗_A C)` are natural in `C`.
* `AlgebraicGeometry.Space.derivedPullbackPointTensorIso_comp`: **the derived form**: the
  identifications `Lg^* T_ψ(C) ≅ T_{ψ'}(A' ⊗_A C)` for bounded complexes of finite projective
  modules are compatible with composition.

## References

* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Adjunction

variable {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
  {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃}
  {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₃₂ : C₃ ⥤ C₂}

/-- **Composition of adjunctions is associative.** -/
theorem comp_assoc_eq (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₂₃ : F₂₃ ⊣ G₃₂) :
    (adj₀₁.comp adj₁₂).comp adj₂₃ = adj₀₁.comp (adj₁₂.comp adj₂₃) := by
  ext X
  simp [Adjunction.comp_unit_app]

end CategoryTheory.Adjunction

namespace Stacks.Cohomology.DerivedPullbackOnRingedTopoi

open _root_.AlgebraicGeometry

universe u

section Naturality

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance high] HasDerivedCategory.standard

variable (f : RingedToposSiteHom X Y)
  [CategoryTheory.Functor.HasLeftDerivedFunctor
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy f)
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The computation of `Lf^*` on complexes with invertible comparison map is natural**: for a
map of complexes `φ : K ⟶ K'` on which the comparisons `Lf^* Q ⟶ Q f^*` are invertible, the
identifications `Lf^* Q(K) ≅ Q(f^* K)` and `Lf^* Q(K') ≅ Q(f^* K')` intertwine `Lf^* Q(φ)` and
`Q(f^* φ)`. -/
theorem derivedPullbackObjIsoOfIsIsoComparison_hom_naturality
    {K K' : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ} (φ : K ⟶ K')
    (hK : IsIso
      ((Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)))
    (hK' : IsIso
      ((Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K'))) :
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback f).map
        (DerivedCategory.Q.map φ) ≫ (derivedPullbackObjIsoOfIsIsoComparison f K' hK').hom =
      (derivedPullbackObjIsoOfIsIsoComparison f K hK).hom ≫
        DerivedCategory.Q.map
          ((f.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  have h2 := NatTrans.naturality
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison f)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map φ)
  have h3 := (f.pullbackTopos.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.naturality φ
  simp only [Functor.comp_map] at h2 h3
  simp only [derivedPullbackObjIsoOfIsIsoComparison, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [← Functor.map_comp_assoc, DerivedCategory.quotientCompQhIso_inv_naturality,
    Functor.map_comp_assoc, reassoc_of% h2, ← Functor.map_comp_assoc DerivedCategory.Qh, h3,
    Functor.map_comp_assoc, ← DerivedCategory.quotientCompQhIso_hom_naturality]

end Naturality

end Stacks.Cohomology.DerivedPullbackOnRingedTopoi

namespace CategoryTheory.Functor

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Preadditive C₁] [Preadditive C₂] [Preadditive C₃]
  {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₃} {H : C₁ ⥤ C₃} [F.Additive] [G.Additive] [H.Additive]

/-- The composition isomorphism of the functors induced on homotopy categories, read through the
factorizations `quotient ⋙ F_K ≅ F_C ⋙ quotient`, is the quotient of the composition isomorphism
of the functors induced on complexes. -/
theorem mapHomotopyCategoryCompIso_hom_app_comp_mapHomotopyCategoryFactors_hom_app
    (e : F ⋙ G ≅ H) (K : CochainComplex C₁ ℤ) :
    (mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) ≫
      (H.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K =
    (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
      (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      (HomotopyCategory.quotient C₃ (ComplexShape.up ℤ)).map
        ((mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app K) := by
  have h : (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) = 𝟙 _ :=
    (G.mapHomotopyCategory (ComplexShape.up ℤ)).map_id _
  rw [h]
  exact (Category.comp_id _).trans ((Category.id_comp _).trans (Category.id_comp _)).symm

end CategoryTheory.Functor

universe u

namespace AlgebraicGeometry

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

section

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) {TX : X.C} (hTX : IsTerminal TX) {TY : Y.C}
  (hu : IsTerminal (f.u.obj TY))
  {A A' : Type u} [CommRing A] [CommRing A'] (ψ : A →+* A')
  (φY : CommRingCat.of A ⟶ Y.O.obj.obj (op TY)) (φX : CommRingCat.of A' ⟶ X.O.obj.obj (op TX))
  (hφ : φY ≫ f.fSharp.hom.app (op TY) =
    CommRingCat.ofHom ψ ≫ φX ≫ X.O.obj.map (hTX.from (f.u.obj TY)).op)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The adjoint mate of `AlgebraicGeometry.toPointPullbackCompIso` is
`AlgebraicGeometry.toPointPushforwardCompIso`. -/
theorem conjugateEquiv_toPointPullbackCompIso_hom :
    conjugateEquiv ((ModuleCat.extendRestrictScalarsAdj ψ).comp
        ((Space.pointModuleCatEquiv (R := A')).symm.toAdjunction.comp
          ((Stacks.PointRingedSite.modulesEquiv (CommRingCat.of A')).symm.toAdjunction.comp
            (toPointRingedTopos X φX).pullbackPushforwardAdjunctionTopos)))
      ((Space.pointModuleCatEquiv (R := A)).symm.toAdjunction.comp
        ((Stacks.PointRingedSite.modulesEquiv (CommRingCat.of A)).symm.toAdjunction.comp
          ((toPointRingedTopos Y φY).pullbackPushforwardAdjunctionTopos.comp
            f.pullbackPushforwardAdjunctionTopos)))
      (toPointPullbackCompIso f hTX hu ψ φY φX hφ).hom =
    (toPointPushforwardCompIso f hTX hu ψ φY φX hφ).hom :=
  Stacks.Mates.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _

end

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' X'' : AlgebraicSpaces B S hS} (g : X' ⟶ X) (g' : X'' ⟶ X')
  {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A'']
  (ψ : A →+* (SpacesEtale.structurePresheaf B S hS X).obj (op (SpacesEtale.idObj B S hS X)))
  (ψ' : A' →+* (SpacesEtale.structurePresheaf B S hS X').obj (op (SpacesEtale.idObj B S hS X')))
  (ψ'' : A'' →+*
    (SpacesEtale.structurePresheaf B S hS X'').obj (op (SpacesEtale.idObj B S hS X'')))
  (α : A →+* A') (α' : A' →+* A'')
  (hψ : ∀ a, globalFunctionsMap B S hS g (ψ a) = ψ' (α a))
  (hψ' : ∀ a, globalFunctionsMap B S hS g' (ψ' a) = ψ'' (α' a))
  (hψ'' : ∀ a, globalFunctionsMap B S hS (g' ≫ g) (ψ a) = ψ'' ((α'.comp α) a))

include hψ in
/-- The adjoint mate of `AlgebraicGeometry.Space.spacesEtaleModelToPointPullbackCompIso` is the
identification `AlgebraicGeometry.toPointPushforwardCompIso` of the two sections functors. -/
theorem conjugateEquiv_spacesEtaleModelToPointPullbackCompIso_hom :
    conjugateEquiv ((ModuleCat.extendRestrictScalarsAdj α).comp
        (spacesEtaleModelPointTensorAdjunction B S hS ψ'))
      ((spacesEtaleModelPointTensorAdjunction B S hS ψ).comp
        (spacesEtaleModelHom B S hS g).pullbackPushforwardAdjunctionTopos)
      (spacesEtaleModelToPointPullbackCompIso B S hS g ψ ψ' α hψ).hom =
    (toPointPushforwardCompIso (spacesEtaleModelHom B S hS g)
      (isTerminal_spacesEtaleModelTerminal B S hS X')
      (isTerminal_smallModelBaseChange_obj_terminal B S hS g) α _ _
      (CommRingCat.hom_ext (RingHom.ext fun a =>
        fSharp_spacesEtaleModelGlobalHom_apply B S hS g ψ ψ' α hψ a))).hom := by
  have e : (spacesEtaleModelPointTensorAdjunction B S hS ψ).comp
        (spacesEtaleModelHom B S hS g).pullbackPushforwardAdjunctionTopos =
      (pointModuleCatEquiv (R := A)).symm.toAdjunction.comp
        ((Stacks.PointRingedSite.modulesEquiv (CommRingCat.of A)).symm.toAdjunction.comp
          ((spacesEtaleModelToPoint B S hS (R := CommRingCat.of A)
              ψ).pullbackPushforwardAdjunctionTopos.comp
            (spacesEtaleModelHom B S hS g).pullbackPushforwardAdjunctionTopos)) :=
    (Adjunction.comp_assoc_eq _ _ _).trans (congrArg _ (Adjunction.comp_assoc_eq _ _ _))
  rw [e]
  unfold spacesEtaleModelPointTensorAdjunction spacesEtaleModelToPointPullbackCompIso
    spacesEtaleModelToPoint
  exact conjugateEquiv_toPointPullbackCompIso_hom (spacesEtaleModelHom B S hS g)
    (isTerminal_spacesEtaleModelTerminal B S hS X')
    (isTerminal_smallModelBaseChange_obj_terminal B S hS g) α _ _ _

/-- **Inverse images to points and base change are compatible with composition**: for
`g' : X'' ⟶ X'`, `g : X' ⟶ X`, the identification
`g'^* g^*(𝒪_X ⊗_A M) ≅ g'^*(𝒪_{X'} ⊗_{A'} (A' ⊗_A M)) ≅ 𝒪_{X''} ⊗_{A''} (A'' ⊗_{A'} A' ⊗_A M)`
followed by `A'' ⊗_{A'} A' ⊗_A M ≅ A'' ⊗_A M` is the composition isomorphism
`g'^* g^* ≅ (g' ≫ g)^*` followed by the identification for `g' ≫ g`. -/
theorem spacesEtaleModelToPointPullbackCompIso_comp :
    Functor.whiskerRight (spacesEtaleModelToPointPullbackCompIso B S hS g ψ ψ' α hψ).hom
        (spacesEtaleModelHom B S hS g').pullbackTopos ≫
      Functor.whiskerLeft (ModuleCat.extendScalars.{u, u, u} α)
        (spacesEtaleModelToPointPullbackCompIso B S hS g' ψ' ψ'' α' hψ').hom ≫
      Functor.whiskerRight (ModuleCat.extendScalarsComp α α').inv
        (spacesEtaleModelPointTensor B S hS ψ'') =
    Functor.whiskerLeft (spacesEtaleModelPointTensor B S hS ψ)
        (spacesEtaleModelPullbackComp B S hS g' g).hom ≫
      (spacesEtaleModelToPointPullbackCompIso B S hS (g' ≫ g) ψ ψ'' (α'.comp α) hψ'').hom := by
  apply (conjugateEquiv
    ((ModuleCat.extendRestrictScalarsAdj (α'.comp α)).comp
      (spacesEtaleModelPointTensorAdjunction B S hS ψ''))
    (((spacesEtaleModelPointTensorAdjunction B S hS ψ).comp
      (spacesEtaleModelHom B S hS g).pullbackPushforwardAdjunctionTopos).comp
        (spacesEtaleModelHom B S hS g').pullbackPushforwardAdjunctionTopos)).injective
  rw [← conjugateEquiv_comp _
    (((ModuleCat.extendRestrictScalarsAdj α).comp
      (spacesEtaleModelPointTensorAdjunction B S hS ψ')).comp
        (spacesEtaleModelHom B S hS g').pullbackPushforwardAdjunctionTopos),
    ← conjugateEquiv_comp _
    (((ModuleCat.extendRestrictScalarsAdj α).comp (ModuleCat.extendRestrictScalarsAdj α')).comp
      (spacesEtaleModelPointTensorAdjunction B S hS ψ'')),
    ← conjugateEquiv_comp _
    ((spacesEtaleModelPointTensorAdjunction B S hS ψ).comp
      (spacesEtaleModelHom B S hS (g' ≫ g)).pullbackPushforwardAdjunctionTopos)]
  have ha := conjugateEquiv_whiskerRight
    ((ModuleCat.extendRestrictScalarsAdj α).comp (spacesEtaleModelPointTensorAdjunction B S hS ψ'))
    ((spacesEtaleModelPointTensorAdjunction B S hS ψ).comp
      (spacesEtaleModelHom B S hS g).pullbackPushforwardAdjunctionTopos)
    (spacesEtaleModelHom B S hS g').pullbackPushforwardAdjunctionTopos
    (spacesEtaleModelToPointPullbackCompIso B S hS g ψ ψ' α hψ).hom
  rw [conjugateEquiv_spacesEtaleModelToPointPullbackCompIso_hom] at ha
  have hb := conjugateEquiv_whiskerLeft
    ((ModuleCat.extendRestrictScalarsAdj α').comp
      (spacesEtaleModelPointTensorAdjunction B S hS ψ''))
    ((spacesEtaleModelPointTensorAdjunction B S hS ψ').comp
      (spacesEtaleModelHom B S hS g').pullbackPushforwardAdjunctionTopos)
    (ModuleCat.extendRestrictScalarsAdj α)
    (spacesEtaleModelToPointPullbackCompIso B S hS g' ψ' ψ'' α' hψ').hom
  rw [conjugateEquiv_spacesEtaleModelToPointPullbackCompIso_hom,
    ← Adjunction.comp_assoc_eq, ← Adjunction.comp_assoc_eq] at hb
  have hc := conjugateEquiv_whiskerRight
    (ModuleCat.extendRestrictScalarsAdj (α'.comp α))
    ((ModuleCat.extendRestrictScalarsAdj α).comp (ModuleCat.extendRestrictScalarsAdj α'))
    (spacesEtaleModelPointTensorAdjunction B S hS ψ'')
    (ModuleCat.extendScalarsComp α α').inv
  have hc' : conjugateEquiv (ModuleCat.extendRestrictScalarsAdj (α'.comp α))
      ((ModuleCat.extendRestrictScalarsAdj α).comp (ModuleCat.extendRestrictScalarsAdj α'))
      (ModuleCat.extendScalarsComp α α').inv = (ModuleCat.restrictScalarsComp α α').hom :=
    (conjugateEquiv _ _).apply_symm_apply (ModuleCat.restrictScalarsComp α α').symm.inv
  rw [hc'] at hc
  have hw := conjugateEquiv_whiskerLeft
    ((spacesEtaleModelHom B S hS (g' ≫ g)).pullbackPushforwardAdjunctionTopos)
    ((spacesEtaleModelHom B S hS g).pullbackPushforwardAdjunctionTopos.comp
      (spacesEtaleModelHom B S hS g').pullbackPushforwardAdjunctionTopos)
    (spacesEtaleModelPointTensorAdjunction B S hS ψ)
    (spacesEtaleModelPullbackComp B S hS g' g).hom
  rw [← Adjunction.comp_assoc_eq] at hw
  have hw' : conjugateEquiv
      ((spacesEtaleModelHom B S hS (g' ≫ g)).pullbackPushforwardAdjunctionTopos)
      ((spacesEtaleModelHom B S hS g).pullbackPushforwardAdjunctionTopos.comp
        (spacesEtaleModelHom B S hS g').pullbackPushforwardAdjunctionTopos)
      (spacesEtaleModelPullbackComp B S hS g' g).hom =
        (spacesEtaleModelPushforwardComp B S hS g' g).inv := by
    rw [spacesEtaleModelPullbackComp_eq_leftAdjointCompIso, Adjunction.leftAdjointCompIso_hom,
      Adjunction.leftAdjointCompNatTrans, Equiv.apply_symm_apply]
  rw [hw'] at hw
  rw [ha, hb, hc, hw, conjugateEquiv_spacesEtaleModelToPointPullbackCompIso_hom]
  ext M x
  let P : (SmallModel.{u} (SpacesEtale B S hS X''))ᵒᵖ ⥤ AddCommGrpCat.{u} := M.val.presheaf
  let T := spacesEtaleModelTerminal B S hS X
  let hT'' := isTerminal_spacesEtaleModelTerminal B S hS X''
  change (P.map (hT''.from ((smallModelBaseChange B S hS g').obj
        (spacesEtaleModelTerminal B S hS X'))).op ≫
      P.map ((smallModelBaseChange B S hS g').map
        ((isTerminal_spacesEtaleModelTerminal B S hS X').from
          ((smallModelBaseChange B S hS g).obj T))).op) x =
    (P.map (hT''.from ((smallModelBaseChange B S hS (g' ≫ g)).obj T)).op ≫
      P.map ((smallModelBaseChangeComp B S hS g' g).hom.app T).op) x
  rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp]
  exact congrArg (fun k => P.map k.op x) (hT''.hom_ext _ _)

section Derived

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi

attribute [local instance high] HasDerivedCategory.standard

/-- The comparison `Lg^* Q ⟶ Q g^*` is invertible at `T_ψ(D)` for a bounded above complex `D` of
finite projective modules. -/
private theorem isIso_derivedPullbackComparison_app_pointTensor
    (D : CochainComplex (ModuleCat.{u} A) ℤ) (d : ℤ) (hd : D.IsStrictlyLE d)
    (hdz : {i : ℤ | ¬ IsZero (D.X i)}.Finite) (hdf : ∀ i : ℤ, Module.Finite A (D.X i))
    (hdp : ∀ i : ℤ, Module.Projective A (D.X i)) :
    IsIso ((derivedPullbackComparison (spacesEtaleModelHom B S hS g)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj D))) :=
  isIso_derivedPullbackComparison_app_boundedAbove (spacesEtaleModelHom B S hS g)
    (isMorphismOfSites_spacesEtaleModelHom B S hS g) _
    ⟨d, by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      exact Functor.map_isZero (spacesEtaleModelPointTensor B S hS ψ)
        (CochainComplex.isZero_of_isStrictlyLE D d i hi)⟩
    (Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect
      (Y := (spacesEtaleModelRingedTopos B S hS X).toRingedSite)
      (Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex_of_finite_projective _
        (spacesEtaleModelPointTensorObjSelfIso B S hS ψ) hdz hdf hdp))

/-- **The computation of `Lg^*` on complexes is compatible with composition**: for
`g' : X'' ⟶ X'`, `g : X' ⟶ X` and a complex `K` on the model of `X` on which the comparisons for
`g`, `g' ≫ g` and (at `g^*K`) for `g'` are invertible, the composition isomorphism
`Lg'^* Lg^* ≅ L(g' ≫ g)^*` at `Q(K)` followed by `L(g' ≫ g)^* Q(K) ≅ Q((g' ≫ g)^* K)` is
`Lg'^* Q(K) ≅ ... ≅ Q(g'^* g^* K)` followed by the composition isomorphism of the inverse
images. -/
theorem spacesEtaleModelDerivedPullbackCompIso_hom_app_derivedPullbackObjIsoOfIsIsoComparison
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS X).O)) ℤ)
    (hK : IsIso ((derivedPullbackComparison (spacesEtaleModelHom B S hS g)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)))
    (hK' : IsIso ((derivedPullbackComparison (spacesEtaleModelHom B S hS g')).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((spacesEtaleModelHom B S hS g).pullbackTopos.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))))
    (hK'' : IsIso ((derivedPullbackComparison (spacesEtaleModelHom B S hS (g' ≫ g))).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) :
    (spacesEtaleModelDerivedPullbackCompIso B S hS g' g).hom.app (DerivedCategory.Q.obj K) ≫
        (derivedPullbackObjIsoOfIsIsoComparison (spacesEtaleModelHom B S hS (g' ≫ g)) K hK'').hom =
      (derivedPullback (spacesEtaleModelHom B S hS g')).map
          (derivedPullbackObjIsoOfIsIsoComparison (spacesEtaleModelHom B S hS g) K hK).hom ≫
        (derivedPullbackObjIsoOfIsIsoComparison (spacesEtaleModelHom B S hS g') _ hK').hom ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (spacesEtaleModelPullbackComp B S hS g' g) (ComplexShape.up ℤ)).hom.app K) := by
  have h2 := spacesEtaleModelDerivedPullbackCompIso_hom_app_comp_derivedPullbackComparison_app
    B S hS g' g ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)
  have h3 := (derivedPullbackComparison (spacesEtaleModelHom B S hS g')).naturality
    (((spacesEtaleModelHom B S hS g).pullbackTopos.mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).hom.app K)
  simp only [Functor.comp_map] at h3
  simp only [derivedPullbackObjIsoOfIsIsoComparison, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom, Iso.app_hom, Iso.app_inv, Category.assoc, Functor.map_comp]
  rw [← NatTrans.naturality_assoc]
  simp only [Functor.comp_obj, Functor.comp_map]
  rw [reassoc_of% h2]
  refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_)
  conv_rhs => rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
    Iso.hom_inv_id_app]
  conv_rhs => simp only [Functor.comp_obj, Category.comp_id]
  rw [reassoc_of% h3]
  refine congrArg (_ ≫ ·) ?_
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  exact congrArg (fun t => DerivedCategory.Qh.map t ≫ _)
    (Functor.mapHomotopyCategoryCompIso_hom_app_comp_mapHomotopyCategoryFactors_hom_app _ K)

include hψ hψ' in
/-- **The computation `Lg^* T_ψ(C) ≅ T_{ψ'}(A' ⊗_A C)` is compatible with composition**: for
`g' : X'' ⟶ X'`, `g : X' ⟶ X` and a bounded complex `C` of finite projective `A`-modules, the
composition isomorphism `Lg'^* Lg^* ≅ L(g' ≫ g)^*` followed by the computation for `g' ≫ g` and
`A'' ⊗_A C ≅ A'' ⊗_{A'} (A' ⊗_A C)` is the computation for `g` followed by the computation for
`g'` at `A' ⊗_A C`. -/
theorem derivedPullbackPointTensorIso_comp (C : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ)
    (hb : C.IsStrictlyLE b) (hbd : {i : ℤ | ¬ IsZero (C.X i)}.Finite)
    (hfin : ∀ i : ℤ, Module.Finite A (C.X i)) (hproj : ∀ i : ℤ, Module.Projective A (C.X i))
    (hb' : CochainComplex.IsStrictlyLE (((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C) b)
    (hbd' : {i : ℤ | ¬ IsZero ((((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C).X i)}.Finite)
    (hfin' : ∀ i : ℤ, Module.Finite A'
      ((((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C).X i))
    (hproj' : ∀ i : ℤ, Module.Projective A'
      ((((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C).X i)) :
    (spacesEtaleModelDerivedPullbackCompIso B S hS g' g).hom.app _ ≫
        (derivedPullbackPointTensorIso B S hS ψ (g' ≫ g) ψ'' (α'.comp α) hψ'' C b hb hbd hfin
          hproj).hom ≫
        DerivedCategory.Q.map (((spacesEtaleModelPointTensor B S hS ψ'').mapHomologicalComplex
          (ComplexShape.up ℤ)).map ((NatTrans.mapHomologicalComplex
            (ModuleCat.extendScalarsComp α α').hom (ComplexShape.up ℤ)).app C)) =
      (derivedPullback (spacesEtaleModelHom B S hS g')).map
          (derivedPullbackPointTensorIso B S hS ψ g ψ' α hψ C b hb hbd hfin hproj).hom ≫
        (derivedPullbackPointTensorIso B S hS ψ' g' ψ'' α' hψ' _ b hb' hbd' hfin' hproj').hom := by
  simp only [derivedPullbackPointTensorIso, derivedPullbackObjIsoOfFiniteProjective,
    derivedPullbackObjIsoOfFlat, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  have hT := isIso_derivedPullbackComparison_app_pointTensor B S hS g' ψ' _ b hb' hbd' hfin' hproj'
  have hK' : IsIso ((derivedPullbackComparison (spacesEtaleModelHom B S hS g')).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((spacesEtaleModelHom B S hS g).pullbackTopos.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C)))) :=
    (NatTrans.isIso_app_iff_of_iso _ ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((Functor.mapHomologicalComplexCompIso (F := spacesEtaleModelPointTensor B S hS ψ)
        (G := (spacesEtaleModelHom B S hS g).pullbackTopos)
        (H := ModuleCat.extendScalars.{u, u, u} α ⋙ spacesEtaleModelPointTensor B S hS ψ')
        (spacesEtaleModelToPointPullbackCompIso B S hS g ψ ψ' α hψ)
        (ComplexShape.up ℤ)).app C))).mpr hT
  rw [reassoc_of%
    (spacesEtaleModelDerivedPullbackCompIso_hom_app_derivedPullbackObjIsoOfIsIsoComparison
      B S hS g g' _ _ hK' _)]
  refine congrArg (_ ≫ ·) ?_
  rw [reassoc_of% (derivedPullbackObjIsoOfIsIsoComparison_hom_naturality
    (spacesEtaleModelHom B S hS g')
    (K' := ((spacesEtaleModelPointTensor B S hS ψ').mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex (ComplexShape.up ℤ)).obj C))
    ((Functor.mapHomologicalComplexCompIso (F := spacesEtaleModelPointTensor B S hS ψ)
        (G := (spacesEtaleModelHom B S hS g).pullbackTopos)
        (H := ModuleCat.extendScalars.{u, u, u} α ⋙ spacesEtaleModelPointTensor B S hS ψ')
        (spacesEtaleModelToPointPullbackCompIso B S hS g ψ ψ' α hψ) (ComplexShape.up ℤ)).app C).hom
    hK' hT)]
  refine congrArg (_ ≫ ·) ?_
  simp only [← Functor.map_comp]
  congr 1
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  have h := congrArg (fun t => NatTrans.app t (C.X n))
    (spacesEtaleModelToPointPullbackCompIso_comp B S hS g g' ψ ψ' ψ'' α α' hψ hψ' hψ'')
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f, Iso.app_hom,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f]
  rw [← Category.assoc]
  refine (congrArg (· ≫ _) h.symm).trans ?_
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  exact congrArg (_ ≫ ·) (Category.comp_id _)

include hψ in
/-- **The computation `Lg^* T_ψ(C) ≅ T_{ψ'}(A' ⊗_A C)` is natural in `C`**: for a map `u : C ⟶ C'`
of bounded complexes of finite projective `A`-modules, it intertwines `Lg^* T_ψ(u)` and
`T_{ψ'}(A' ⊗_A u)`. -/
theorem derivedPullbackPointTensorIso_hom_naturality {C C' : CochainComplex (ModuleCat.{u} A) ℤ}
    (v : C ⟶ C') (b b' : ℤ)
    (hb : C.IsStrictlyLE b) (hbd : {i : ℤ | ¬ IsZero (C.X i)}.Finite)
    (hfin : ∀ i : ℤ, Module.Finite A (C.X i)) (hproj : ∀ i : ℤ, Module.Projective A (C.X i))
    (hb' : C'.IsStrictlyLE b') (hbd' : {i : ℤ | ¬ IsZero (C'.X i)}.Finite)
    (hfin' : ∀ i : ℤ, Module.Finite A (C'.X i)) (hproj' : ∀ i : ℤ, Module.Projective A (C'.X i)) :
    (derivedPullback (spacesEtaleModelHom B S hS g)).map (DerivedCategory.Q.map
        (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
          (ComplexShape.up ℤ)).map v)) ≫
        (derivedPullbackPointTensorIso B S hS ψ g ψ' α hψ C' b' hb' hbd' hfin' hproj').hom =
      (derivedPullbackPointTensorIso B S hS ψ g ψ' α hψ C b hb hbd hfin hproj).hom ≫
        DerivedCategory.Q.map (((spacesEtaleModelPointTensor B S hS ψ').mapHomologicalComplex
          (ComplexShape.up ℤ)).map (((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
            (ComplexShape.up ℤ)).map v)) := by
  simp only [derivedPullbackPointTensorIso, derivedPullbackObjIsoOfFiniteProjective,
    derivedPullbackObjIsoOfFlat, Iso.trans_hom, Functor.mapIso_hom]
  have hn := derivedPullbackObjIsoOfIsIsoComparison_hom_naturality
    (spacesEtaleModelHom B S hS g)
    (K := ((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
    (K' :=
      ((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C')
    (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex (ComplexShape.up ℤ)).map v)
    (isIso_derivedPullbackComparison_app_pointTensor B S hS g ψ C b hb hbd hfin hproj)
    (isIso_derivedPullbackComparison_app_pointTensor B S hS g ψ C' b' hb' hbd' hfin' hproj')
  rw [reassoc_of% hn]
  rw [Category.assoc, cancel_epi]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
    (F := spacesEtaleModelPointTensor B S hS ψ) (G := (spacesEtaleModelHom B S hS g).pullbackTopos)
    (H := ModuleCat.extendScalars.{u, u, u} α ⋙ spacesEtaleModelPointTensor B S hS ψ')
    (spacesEtaleModelToPointPullbackCompIso B S hS g ψ ψ' α hψ)
    (ComplexShape.up ℤ)).hom.naturality v)

end Derived

end Space

end AlgebraicGeometry

end
