module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.NatIsoSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesBaseChangeAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelHomComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeCompositionOnRingedTopoi

/-!
# The cocycle identity for composition on spaces-étale models

For composable morphisms `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ W` of algebraic spaces, the
composition isomorphisms `Lf^* ∘ Lg^* ≅ L(f ≫ g)^*` of
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIso` on the `Type u`-presented models
of the ringed spaces-étale sites satisfy the cocycle identity: the two identifications of
`Lf^* ∘ Lg^* ∘ Lh^*` with `L(f ≫ g ≫ h)^*` agree.  Together with
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackIdIso` this makes `X ↦ D(𝒪_X)`,
`f ↦ Lf^*` a pseudofunctor on the models.

The proof goes through the layers in which the composition isomorphism is built.

* The base changes `V ↦ V ×_Y X` on the small models: the cocycle identity of
  `AlgebraicGeometry.Space.smallModelBaseChangeComp` is that of the spaces-étale base change
  (`AlgebraicGeometry.Space.spacesBaseChange_comp_assoc`, Stacks 03G2, part (2)), transported
  through the equivalences with the small models.
* Direct images: they are restrictions of sections along the base changes, so their cocycle
  identity is the previous one evaluated in a sheaf of modules.
* Inverse images: they are left adjoint to the direct images, and the composition isomorphisms
  are the adjoint mates (`CategoryTheory.Adjunction.leftAdjointCompIso_assoc`).
* Derived pullbacks: the composition isomorphism is pinned down by its compatibility with the
  comparison maps `Lf^* ∘ Q ⟶ Q ∘ f^*`, and the cocycle identity passes through the universal
  property of the left derived functor
  (`Stacks.Cohomology.DerivedBaseChangeComposition.leftDerived_comparison_assoc`).

## Main results

* `AlgebraicGeometry.Space.smallModelBaseChangeComp_assoc`,
  `AlgebraicGeometry.Space.spacesEtaleModelPushforwardComp_assoc`,
  `AlgebraicGeometry.Space.spacesEtaleModelPullbackComp_assoc`: the cocycle identities on the
  sites, on direct images and on inverse images.
* `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIso_assoc`: **the cocycle identity
  for derived pullback on the models.**

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Adjunction

variable {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]

/-- Replacing the right adjoint of the target of a mate by an isomorphic one: the composition
isomorphism of left adjoints induced by `e : G₂₁ ⋙ G₁₀ ≅ G₂₀'`, followed by the comparison of the
left adjoint `F₀₂'` of `G₂₀'` with a left adjoint `F₀₂` of `G₂₀ ≅ G₂₀'`, is the composition
isomorphism induced by `e ≪≫ φ`. -/
theorem leftAdjointCompIso_trans_leftAdjointUniq_ofNatIsoRight_symm
    {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ F₀₂' : C₀ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ G₂₀' : C₂ ⥤ C₀}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₀₂ : F₀₂ ⊣ G₂₀) (adj₀₂' : F₀₂' ⊣ G₂₀')
    (e : G₂₁ ⋙ G₁₀ ≅ G₂₀') (φ : G₂₀' ≅ G₂₀) :
    leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂' e ≪≫
        (adj₀₂.leftAdjointUniq (adj₀₂'.ofNatIsoRight φ)).symm =
      leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ (e ≪≫ φ) := by
  refine Iso.ext ((Iso.inv_eq_inv _ _).mp ?_)
  apply (conjugateEquiv (adj₀₁.comp adj₁₂) adj₀₂).injective
  rw [Iso.trans_inv, Iso.symm_inv, ← conjugateEquiv_comp (adj₀₁.comp adj₁₂) adj₀₂' adj₀₂,
    conjugateEquiv_leftAdjointCompIso_inv, conjugateEquiv_leftAdjointCompIso_inv,
    Stacks.Mates.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom, Iso.trans_hom]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z W : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)

/-- **The cocycle identity for base change on the models** (Stacks 03G2, part (2)): the two
identifications of the threefold iterated base change on the small models with the base change
along `f ≫ g ≫ h` agree.  This is `AlgebraicGeometry.Space.spacesBaseChange_comp_assoc`
transported through the equivalences with the small models. -/
theorem smallModelBaseChangeComp_assoc :
    Functor.isoWhiskerRight (smallModelBaseChangeComp B S hS g h)
          (smallModelBaseChange B S hS f) ≪≫ smallModelBaseChangeComp B S hS f (g ≫ h) =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (smallModelBaseChange B S hS h)
          (smallModelBaseChangeComp B S hS f g) ≪≫
        smallModelBaseChangeComp B S hS (f ≫ g) h := by
  refine Iso.ext (NatTrans.ext (funext fun V => ?_))
  have hb := congrArg
    (fun e => e.hom.app ((equivSmallModel.{u} (SpacesEtale B S hS W)).inverse.obj V))
    (spacesBaseChange_comp_assoc B S hS f g h)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToIso.hom, eqToHom_refl, Category.id_comp,
    Category.comp_id] at hb ⊢
  simp only [smallModelBaseChangeComp, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.comp_map,
    Functor.comp_obj, Equivalence.inv_fun_map]
  simp only [← Functor.map_comp, Category.assoc]
  congr 1
  have hnat := (spacesBaseChange_comp B S hS f g).hom.naturality
    ((equivSmallModel.{u} (SpacesEtale B S hS Z)).unitIso.inv.app
      ((spacesBaseChange B S hS h).functor.obj
        ((equivSmallModel.{u} (SpacesEtale B S hS W)).inverse.obj V)))
  simp only [Functor.comp_map] at hnat
  rw [← reassoc_of% hnat, ← hb]
  simp only [Functor.map_comp, Category.assoc, Equivalence.unit]
  rw [← Functor.map_comp_assoc (spacesBaseChange B S hS f).functor
      ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app _),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The composition isomorphism of the direct images along the morphisms of models, in the
order in which they compose as right adjoints: `g_* ∘ f_* ≅ (f ≫ g)_*`. -/
def spacesEtaleModelPushforwardComp :
    (spacesEtaleModelHom B S hS f).pushforwardTopos ⋙
        (spacesEtaleModelHom B S hS g).pushforwardTopos ≅
      (spacesEtaleModelHom B S hS (f ≫ g)).pushforwardTopos :=
  (RingedToposSiteHom.pushforwardToposCompIso (spacesEtaleModelHom B S hS f)
      (spacesEtaleModelHom B S hS g)).symm ≪≫
    (spacesEtaleModelPushforwardCompIso B S hS f g).symm

/-- **The cocycle identity for direct images on the models**: the two identifications of
`h_* ∘ g_* ∘ f_*` with `(f ≫ g ≫ h)_*` agree.  On sections both are restriction along the
two composites of the composition isomorphisms of the base changes, which agree by
`AlgebraicGeometry.Space.smallModelBaseChangeComp_assoc`. -/
theorem spacesEtaleModelPushforwardComp_assoc :
    Functor.isoWhiskerLeft (spacesEtaleModelHom B S hS f).pushforwardTopos
          (spacesEtaleModelPushforwardComp B S hS g h) ≪≫
        spacesEtaleModelPushforwardComp B S hS f (g ≫ h) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (spacesEtaleModelPushforwardComp B S hS f g)
          (spacesEtaleModelHom B S hS h).pushforwardTopos ≪≫
        spacesEtaleModelPushforwardComp B S hS (f ≫ g) h := by
  have hc : ∀ V : SmallModel.{u} (SpacesEtale B S hS W),
      (smallModelBaseChangeComp B S hS f (g ≫ h)).inv.app V ≫
          (smallModelBaseChange B S hS f).map ((smallModelBaseChangeComp B S hS g h).inv.app V) =
        (smallModelBaseChangeComp B S hS (f ≫ g) h).inv.app V ≫
          (smallModelBaseChangeComp B S hS f g).inv.app
            ((smallModelBaseChange B S hS h).obj V) := by
    intro V
    have := congrArg (fun e => e.inv.app V) (smallModelBaseChangeComp_assoc B S hS f g h)
    simpa using this
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  let P : (SmallModel.{u} (SpacesEtale B S hS X))ᵒᵖ ⥤ AddCommGrpCat.{u} := M.val.presheaf
  change (P.map ((smallModelBaseChange B S hS f).map
      ((smallModelBaseChangeComp B S hS g h).inv.app U.unop)).op ≫
      P.map ((smallModelBaseChangeComp B S hS f (g ≫ h)).inv.app U.unop).op) x =
    (P.map ((smallModelBaseChangeComp B S hS f g).inv.app
      ((smallModelBaseChange B S hS h).obj U.unop)).op ≫
      P.map ((smallModelBaseChangeComp B S hS (f ≫ g) h).inv.app U.unop).op) x
  rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, hc U.unop]


attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

/-- The composition isomorphism of the inverse images along the morphisms of models,
`f^* ∘ g^* ≅ (f ≫ g)^*`: the composition isomorphism of inverse images of morphisms of ringed
topoi, followed by `AlgebraicGeometry.Space.spacesEtaleModelPullbackCompIso`. -/
def spacesEtaleModelPullbackComp :
    (spacesEtaleModelHom B S hS g).pullbackTopos ⋙ (spacesEtaleModelHom B S hS f).pullbackTopos ≅
      (spacesEtaleModelHom B S hS (f ≫ g)).pullbackTopos :=
  RingedToposSiteHom.pullbackToposCompIso (spacesEtaleModelHom B S hS f)
      (spacesEtaleModelHom B S hS g) ≪≫
    (spacesEtaleModelPullbackCompIso B S hS f g).symm

/-- The composition isomorphism of inverse images on the models is the adjoint mate of the
composition isomorphism `AlgebraicGeometry.Space.spacesEtaleModelPushforwardComp` of direct
images. -/
theorem spacesEtaleModelPullbackComp_eq_leftAdjointCompIso :
    spacesEtaleModelPullbackComp B S hS f g =
      Adjunction.leftAdjointCompIso
        (spacesEtaleModelHom B S hS g).pullbackPushforwardAdjunctionTopos
        (spacesEtaleModelHom B S hS f).pullbackPushforwardAdjunctionTopos
        (spacesEtaleModelHom B S hS (f ≫ g)).pullbackPushforwardAdjunctionTopos
        (spacesEtaleModelPushforwardComp B S hS f g) :=
  Adjunction.leftAdjointCompIso_trans_leftAdjointUniq_ofNatIsoRight_symm _ _ _ _ _ _

/-- **The cocycle identity for inverse images on the models**: the two identifications of
`f^* ∘ g^* ∘ h^*` with `(f ≫ g ≫ h)^*` agree.  Both sides are adjoint mates, so this is the
cocycle identity `AlgebraicGeometry.Space.spacesEtaleModelPushforwardComp_assoc` for direct
images. -/
theorem spacesEtaleModelPullbackComp_assoc :
    Functor.isoWhiskerLeft (spacesEtaleModelHom B S hS h).pullbackTopos
          (spacesEtaleModelPullbackComp B S hS f g) ≪≫
        spacesEtaleModelPullbackComp B S hS (f ≫ g) h =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (spacesEtaleModelPullbackComp B S hS g h)
          (spacesEtaleModelHom B S hS f).pullbackTopos ≪≫
        spacesEtaleModelPullbackComp B S hS f (g ≫ h) := by
  simp only [spacesEtaleModelPullbackComp_eq_leftAdjointCompIso]
  exact Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _
    (spacesEtaleModelPushforwardComp_assoc B S hS f g h)

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi Stacks.Cohomology.DerivedPullbackCompositionOnTopoi
  Stacks.Cohomology.DerivedBaseChangeComposition

attribute [local instance] HasDerivedCategory.standard

/-- **The composition isomorphism of derived pullbacks on the models is the canonical one**:
followed by the comparison `L(f ≫ g)^* ∘ Q ⟶ Q ∘ (f ≫ g)^*`, it is the comparison for `g`, then
the one for `f`, then the composition isomorphism
`AlgebraicGeometry.Space.spacesEtaleModelPullbackComp` of the inverse images. -/
theorem spacesEtaleModelDerivedPullbackCompIso_hom_app_comp_derivedPullbackComparison_app
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS Z).O)) (ComplexShape.up ℤ)) :
    (spacesEtaleModelDerivedPullbackCompIso B S hS f g).hom.app (DerivedCategory.Qh.obj K) ≫
        (derivedPullbackComparison (spacesEtaleModelHom B S hS (f ≫ g))).app K =
      (derivedPullback (spacesEtaleModelHom B S hS f)).map
          ((derivedPullbackComparison (spacesEtaleModelHom B S hS g)).app K) ≫
        (derivedPullbackComparison (spacesEtaleModelHom B S hS f)).app
          (((spacesEtaleModelHom B S hS g).pullbackTopos.mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (spacesEtaleModelPullbackComp B S hS f g) (ComplexShape.up ℤ)).hom.app K) := by
  have := hasLeftDerivedFunctor_pullbackOnHomotopy
    ((spacesEtaleModelHom B S hS g).comp (spacesEtaleModelHom B S hS f))
    ((isMorphismOfSites_spacesEtaleModelHom B S hS g).comp
      (isMorphismOfSites_spacesEtaleModelHom B S hS f))
  have h1 := derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app
    (spacesEtaleModelHom B S hS f) (spacesEtaleModelHom B S hS g) K
  have h2 : (derivedPullbackIsoOfPullbackIso _ _
        (spacesEtaleModelPullbackCompIso B S hS f g)).inv.app (DerivedCategory.Qh.obj K) ≫
        (derivedPullbackComparison (spacesEtaleModelHom B S hS (f ≫ g))).app K =
      (derivedPullbackComparison
          ((spacesEtaleModelHom B S hS g).comp (spacesEtaleModelHom B S hS f))).app K ≫
        DerivedCategory.Qh.map ((Stacks.Homology.mapHomotopyCategoryIso
          (spacesEtaleModelPullbackCompIso B S hS f g) (ComplexShape.up ℤ)).inv.app K) :=
    Functor.leftDerivedNatTrans_app _ _ _ _ (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _ K
  have h3 : (Functor.mapHomotopyCategoryCompIso (spacesEtaleModelPullbackComp B S hS f g)
        (ComplexShape.up ℤ)).hom.app K =
      (pullbackOnHomotopyCompIso (spacesEtaleModelHom B S hS f)
          (spacesEtaleModelHom B S hS g)).hom.app K ≫
        (Stacks.Homology.mapHomotopyCategoryIso (spacesEtaleModelPullbackCompIso B S hS f g)
          (ComplexShape.up ℤ)).inv.app K := by
    rcases K with ⟨K⟩
    change (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (spacesEtaleModelPullbackComp B S hS f g)
          (ComplexShape.up ℤ)).hom.app K) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (RingedToposSiteHom.pullbackToposCompIso
            (spacesEtaleModelHom B S hS f) (spacesEtaleModelHom B S hS g))
              (ComplexShape.up ℤ)).hom.app K) ≫
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (spacesEtaleModelPullbackCompIso B S hS f g).inv
            (ComplexShape.up ℤ)).app K)
    rw [← Functor.map_comp]
    congr 1
  simp only [spacesEtaleModelDerivedPullbackCompIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, h2, derivedPullbackCompIso_hom]
  rw [reassoc_of% h1, h3, Functor.map_comp]

/-- **The cocycle identity for derived pullback on the models**: for composable morphisms
`f`, `g`, `h` of algebraic spaces, the two identifications of `Lf^* ∘ Lg^* ∘ Lh^*` with
`L(f ≫ g ≫ h)^*` built from `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIso`
agree. -/
theorem spacesEtaleModelDerivedPullbackCompIso_assoc :
    Functor.whiskerLeft (derivedPullback (spacesEtaleModelHom B S hS h))
          (spacesEtaleModelDerivedPullbackCompIso B S hS f g).hom ≫
        (spacesEtaleModelDerivedPullbackCompIso B S hS (f ≫ g) h).hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (spacesEtaleModelDerivedPullbackCompIso B S hS g h).hom
          (derivedPullback (spacesEtaleModelHom B S hS f)) ≫
        (spacesEtaleModelDerivedPullbackCompIso B S hS f (g ≫ h)).hom :=
  leftDerived_comparison_assoc (derivedPullbackComparison (spacesEtaleModelHom B S hS h))
    (derivedPullbackComparison (spacesEtaleModelHom B S hS g))
    (derivedPullbackComparison (spacesEtaleModelHom B S hS f))
    (derivedPullbackComparison (spacesEtaleModelHom B S hS (g ≫ h)))
    (derivedPullbackComparison (spacesEtaleModelHom B S hS (f ≫ g)))
    (derivedPullbackComparison (spacesEtaleModelHom B S hS ((f ≫ g) ≫ h)))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (Functor.mapHomotopyCategoryCompIso (spacesEtaleModelPullbackComp B S hS g h) _).hom
    (Functor.mapHomotopyCategoryCompIso (spacesEtaleModelPullbackComp B S hS f g) _).hom
    (Functor.mapHomotopyCategoryCompIso (spacesEtaleModelPullbackComp B S hS (f ≫ g) h) _).hom
    (Functor.mapHomotopyCategoryCompIso (spacesEtaleModelPullbackComp B S hS f (g ≫ h)) _).hom
    _ _ _ _
    (spacesEtaleModelDerivedPullbackCompIso_hom_app_comp_derivedPullbackComparison_app B S hS g h)
    (spacesEtaleModelDerivedPullbackCompIso_hom_app_comp_derivedPullbackComparison_app B S hS f g)
    (spacesEtaleModelDerivedPullbackCompIso_hom_app_comp_derivedPullbackComparison_app B S hS
      (f ≫ g) h)
    (spacesEtaleModelDerivedPullbackCompIso_hom_app_comp_derivedPullbackComparison_app B S hS
      f (g ≫ h))
    (mapHomotopyCategoryCompIso_assoc _ _ _ _
      (congrArg Iso.hom (spacesEtaleModelPullbackComp_assoc B S hS f g h)) _)

end AlgebraicGeometry.Space

end
