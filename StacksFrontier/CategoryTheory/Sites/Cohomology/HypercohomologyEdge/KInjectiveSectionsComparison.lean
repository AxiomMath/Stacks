module

public import StacksFrontier.Algebra.Homology.AdjunctionCounitHomology
public import StacksFrontier.Algebra.Homology.LeftExactHomologyComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.HomologyComparisonCounit

/-!
# The hypercohomology edge morphism at a K-injective complex, read on sections

Let `(C, O)` be a ringed site, `U` an object of `C` and `I` a K-injective complex of
`O`-modules.  Over `U` the degree-`q` hypercohomology of `I` is the cohomology of the complex of
sections `Γ(U, I)`, and the edge morphism `H^q(U, I) ⟶ Γ(U, H^q(I))` of
`Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge` becomes the canonical map
`H^q(Γ(U, I)) ⟶ Γ(U, H^q(I))` induced on cycles.  Consequently, if the edge morphism is invertible
at `I`, then so is the comparison `H^q(I) ⟶ H^q(I)` of the left exact forgetful functor from
sheaves to presheaves of modules, on sections over `U`.

## Main results

* `isIso_evaluation_map_homologyComparison_forget_kInjectiveSectionsComparison`: if the edge
  morphism at a K-injective complex `I` is invertible, then the comparison of the forgetful
  functor at `I` is invertible on sections over `U`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.HypercohomologyEdge

universe u v wRing wModule g

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] HomologyComparison.isIso_homologyComparison_of_exact

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{wRing})
  [HasSheafify J AddCommGrpCat.{wModule}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]

attribute [local instance] evaluation_additive sheafification_additive
  sheafification_preservesFiniteColimits

/-- The sheafification adjunction, with right adjoint the forgetful functor itself. -/
abbrev forgetAdjunctionKInjectiveSectionsComparison :
    PresheafOfModules.sheafification (𝟙 O.obj) ⊣ SheafOfModules.forget.{wModule} O :=
  PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)

/-- The degreewise counit of the sheafification adjunction, an isomorphism of complexes. -/
def forgetCounitIsoKInjectiveSectionsComparison
    (I : CochainComplex (SheafOfModules.{wModule} O) ℤ) :
    ((PresheafOfModules.sheafification (𝟙 O.obj)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((SheafOfModules.forget.{wModule} O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => asIso ((forgetAdjunctionKInjectiveSectionsComparison O).counit.app (I.X i)))
    (fun i j _ =>
      ((forgetAdjunctionKInjectiveSectionsComparison O).counit.naturality (I.d i j)).symm)

/-- **The edge morphism at a K-injective complex, read on sections.**  If the hypercohomology edge
morphism `H^q(U, I) ⟶ Γ(U, H^q(I))` is invertible at a K-injective complex `I`, then the
comparison `H^q(I) ⟶ H^q(I)` of the forgetful functor from sheaves to presheaves of modules,
from the cohomology presheaf of `I` to the presheaf underlying its cohomology sheaf, is
invertible on sections over `U`. -/
theorem isIso_evaluation_map_homologyComparison_forget_kInjectiveSectionsComparison
    (U : C) (q : ℤ) (I : CochainComplex (SheafOfModules.{wModule} O) ℤ) (hI : I.IsKInjective)
    (h : IsIso ((hypercohomologyEdge O U q).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))) :
    IsIso ((PresheafOfModules.evaluation O.obj (op U)).map
      (HomologyComparison.homologyComparison (SheafOfModules.forget.{wModule} O) I q)) := by
  rw [isIso_hypercohomologyEdge_app_iff, cohomologyPresheafUnit_app] at h
  have hα := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (homotopySectionsPresheaf O)
    (HomologyComparison.exists_quasiIso_isKInjective_sheafOfModules O)).2 DerivedCategory.Qh
    (derivedSectionsPresheaf O) ((homotopySectionsPresheaf O).totalRightDerivedUnit
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ))) I hI
  let e : (DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q).obj
        ((derivedSectionsPresheaf O).obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ≅
      (((SheafOfModules.forget.{wModule} O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        I).homology q :=
    (DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q).mapIso
        (@asIso _ _ _ _ _ hα).symm ≪≫
      (DerivedCategory.homologyFunctorFactorsh (PresheafOfModules.{wModule} O.obj) q).app _ ≪≫
      (HomotopyCategory.homologyFunctorFactors (PresheafOfModules.{wModule} O.obj)
        (ComplexShape.up ℤ) q).app _
  have hu : IsIso ((PresheafOfModules.evaluation O.obj (op U)).map
      ((forgetAdjunctionKInjectiveSectionsComparison O).unit.app
        ((((SheafOfModules.forget.{wModule} O).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I).homology q))) := by
    have hn := (forgetAdjunctionKInjectiveSectionsComparison O).unit.naturality e.hom
    rw [(Iso.eq_inv_comp e).2 hn, Functor.map_comp, Functor.map_comp]
    have h' : IsIso ((PresheafOfModules.evaluation O.obj (op U)).map
        ((forgetAdjunctionKInjectiveSectionsComparison O).unit.app
          ((DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q).obj
            ((derivedSectionsPresheaf O).obj (DerivedCategory.Qh.obj
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))))) := h
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h' inferInstance)
  rw [Adjunction.homologyComparison_eq_unit_comp_adjunctionCounitHomology
    (forgetAdjunctionKInjectiveSectionsComparison O) q
    (forgetCounitIsoKInjectiveSectionsComparison O I).hom (fun _ => rfl), Functor.map_comp]
  have := Functor.isIso_homologyComparison_of_preservesFiniteLimits_rightExactHomologyComparison
    (PresheafOfModules.sheafification (𝟙 O.obj))
    (((SheafOfModules.forget.{wModule} O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) q
  infer_instance

section Sheafification

variable {O}

omit [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)] in
/-- **Sheafifying the cohomology presheaf gives the cohomology sheaf.**  The comparison
`H^q(I) ⟶ H^q(I)` of the forgetful functor, from the cohomology presheaf of a complex of sheaves
of modules to the presheaf underlying its cohomology sheaf, becomes an isomorphism after
sheafification: sheafification is exact and sheafifying a sheaf gives it back. -/
instance isIso_sheafification_map_homologyComparison_forget_kInjectiveSectionsComparison
    (I : CochainComplex (SheafOfModules.{wModule} O) ℤ) (q : ℤ) :
    IsIso ((PresheafOfModules.sheafification (𝟙 O.obj)).map
      (HomologyComparison.homologyComparison (SheafOfModules.forget.{wModule} O) I q)) := by
  have : IsIso (forgetAdjunctionKInjectiveSectionsComparison O).counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro G
    exact Adjunction.instIsIsoAppCounitOfFullOfFaithful _ G
  let e : SheafOfModules.forget.{wModule} O ⋙ PresheafOfModules.sheafification (𝟙 O.obj) ≅
      𝟭 _ := asIso (forgetAdjunctionKInjectiveSectionsComparison O).counit
  exact (HomologyComparison.isIso_map_homologyComparison_iff_leftExactHomologyComparison
    (SheafOfModules.forget.{wModule} O) (PresheafOfModules.sheafification (𝟙 O.obj)) (𝟭 _) e I
    q).2 inferInstance

end Sheafification

section Pushforward

universe u' v'

variable {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
  {O₀ : Sheaf J RingCat.{wModule}} {O' : Sheaf J' RingCat.{wModule}}
  [HasSheafify J' AddCommGrpCat.{wModule}] [J'.WEqualsLocallyBijective AddCommGrpCat.{wModule}]

/-- The comparison of the forgetful functor, on sections over `W`, is the comparison of the
functor of sections over `W` with values in abelian groups. -/
theorem isIso_evaluation_map_homologyComparison_forget_iff_kInjectiveSectionsComparison
    {R : Sheaf J RingCat.{wModule}}
    (I : CochainComplex (SheafOfModules.{wModule} R) ℤ) (q : ℤ) (W : C) :
    IsIso ((PresheafOfModules.evaluation R.obj (op W)).map
        (HomologyComparison.homologyComparison (SheafOfModules.forget.{wModule} R) I q)) ↔
      IsIso (HomologyComparison.homologyComparison
        (SheafOfModules.evaluation R (op W) ⋙ forget₂ _ AddCommGrpCat.{wModule}) I q) := by
  have h := HomologyComparison.isIso_map_homologyComparison_iff_leftExactHomologyComparison
    (SheafOfModules.forget.{wModule} R)
    (PresheafOfModules.evaluation R.obj (op W) ⋙ forget₂ _ AddCommGrpCat.{wModule})
    (SheafOfModules.evaluation R (op W) ⋙ forget₂ _ AddCommGrpCat.{wModule}) (Iso.refl _) I q
  rw [← h, Functor.comp_map]
  exact ⟨fun _ => inferInstance, fun _ => isIso_of_reflects_iso _
    (forget₂ (ModuleCat.{wModule} (R.obj.obj (op W))) AddCommGrpCat.{wModule})⟩

/-- **A local criterion for the comparison of a left exact functor between sheaves of modules.**
Let `G : Mod(O) ⥤ Mod(O')` be left exact, and suppose that for each member `W` of a family of
objects covering the target site the sections of `G(-)` over `W` are, as abelian groups, the
sections of `-` over an object `u(W)` of the source site.  If the comparison
`H^q(I) ⟶ H^q(I)` of the forgetful functor is invertible on sections over every `u(W)`, then
the comparison `H^q(G I) ⟶ G(H^q I)` of `G` is an isomorphism. -/
theorem isIso_homologyComparison_of_isIso_evaluation_kInjectiveSectionsComparison
    (G : SheafOfModules.{wModule} O₀ ⥤ SheafOfModules.{wModule} O') [G.Additive]
    [PreservesFiniteLimits G]
    (I : CochainComplex (SheafOfModules.{wModule} O₀) ℤ) (q : ℤ) {B : ObjectProperty C'}
    (hB : J'.HasEnoughObjects B) (u : ∀ ⦃W : C'⦄, B W → C)
    (e : ∀ ⦃W : C'⦄ (hW : B W), G ⋙ SheafOfModules.evaluation O' (op W) ⋙
        forget₂ _ AddCommGrpCat.{wModule} ≅
      SheafOfModules.evaluation O₀ (op (u hW)) ⋙ forget₂ _ AddCommGrpCat.{wModule})
    (h : ∀ ⦃W : C'⦄ (hW : B W), IsIso ((PresheafOfModules.evaluation O₀.obj (op (u hW))).map
      (HomologyComparison.homologyComparison (SheafOfModules.forget.{wModule} O₀) I q))) :
    IsIso (HomologyComparison.homologyComparison G I q) := by
  let f := HomologyComparison.homologyComparison (SheafOfModules.forget.{wModule} O')
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) q ≫
    (SheafOfModules.forget.{wModule} O').map (HomologyComparison.homologyComparison G I q)
  have hf : ∀ ⦃W : C'⦄, B W → IsIso ((PresheafOfModules.evaluation O'.obj (op W)).map f) := by
    intro W hW
    let ev' := PresheafOfModules.evaluation O'.obj (op W) ⋙ forget₂ _ AddCommGrpCat.{wModule}
    let F := SheafOfModules.forget.{wModule} O' ⋙ ev'
    let GI := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
    have h₁ :=
      (isIso_evaluation_map_homologyComparison_forget_iff_kInjectiveSectionsComparison I q
        (u hW)).1 (h hW)
    have h₂ := (HomologyComparison.isIso_map_homologyComparison_iff_leftExactHomologyComparison
      (G ⋙ F) (𝟭 _) (SheafOfModules.evaluation O₀ (op (u hW)) ⋙ forget₂ _ AddCommGrpCat.{wModule})
      (Functor.rightUnitor _ ≪≫ e hW) I q).2 h₁
    have h₃ := HomologyComparison.homologyComparison_comp_of_iso_leftExactHomologyComparison G F
      (G ⋙ F) (Iso.refl _) I q
    have h₄ := HomologyComparison.homologyComparison_comp_of_iso_leftExactHomologyComparison
      (SheafOfModules.forget.{wModule} O') ev' F (Iso.refl _) GI q
    rw [Iso.refl_inv, NatTrans.id_app, Category.comp_id] at h₃ h₄
    rw [← h₄] at h₃
    have h₅ : IsIso (ev'.map f) := by
      rw [Functor.map_comp]
      have : IsIso ((HomologicalComplex.homologyMap
          (Functor.mapHomologicalComplexCompIsoOfIsoRightExactHomologyComparison G F (G ⋙ F)
            (Iso.refl _) I).hom q ≫
          (HomologicalComplex.homologyMap
            (Functor.mapHomologicalComplexCompIsoOfIsoRightExactHomologyComparison
              (SheafOfModules.forget.{wModule} O') ev' F (Iso.refl _) GI).hom q ≫
          HomologyComparison.homologyComparison ev'
            (((SheafOfModules.forget.{wModule} O').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj GI) q)) ≫
          (ev'.map
            (HomologyComparison.homologyComparison (SheafOfModules.forget.{wModule} O') GI q) ≫
          F.map (HomologyComparison.homologyComparison G I q))) := by
        simp only [Category.assoc] at h₃ ⊢
        rw [h₃]
        exact h₂
      exact @IsIso.of_isIso_comp_left _ _ _ _ _ (HomologicalComplex.homologyMap
          (Functor.mapHomologicalComplexCompIsoOfIsoRightExactHomologyComparison G F (G ⋙ F)
            (Iso.refl _) I).hom q ≫
          (HomologicalComplex.homologyMap
            (Functor.mapHomologicalComplexCompIsoOfIsoRightExactHomologyComparison
              (SheafOfModules.forget.{wModule} O') ev' F (Iso.refl _) GI).hom q ≫
          HomologyComparison.homologyComparison ev'
            (((SheafOfModules.forget.{wModule} O').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj GI) q)) _ inferInstance this
    have h₆ : IsIso ((forget₂ _ AddCommGrpCat.{wModule}).map
      ((PresheafOfModules.evaluation O'.obj (op W)).map f)) := h₅
    exact isIso_of_reflects_iso _ (forget₂ _ AddCommGrpCat.{wModule})
  have hL : IsIso ((PresheafOfModules.sheafification (𝟙 O'.obj)).map f) :=
    PresheafOfModules.isIso_sheafification_map_of_isIso_evaluation hB f hf
  have hL' : IsIso ((PresheafOfModules.sheafification (𝟙 O'.obj)).map
      ((SheafOfModules.forget.{wModule} O').map
        (HomologyComparison.homologyComparison G I q))) := by
    rw [Functor.map_comp] at hL
    exact IsIso.of_isIso_comp_left ((PresheafOfModules.sheafification (𝟙 O'.obj)).map
      (HomologyComparison.homologyComparison (SheafOfModules.forget.{wModule} O')
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) q)) _
  have : IsIso (forgetAdjunctionKInjectiveSectionsComparison O').counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro G
    exact Adjunction.instIsIsoAppCounitOfFullOfFaithful _ G
  have hn := (forgetAdjunctionKInjectiveSectionsComparison O').counit.naturality
    (HomologyComparison.homologyComparison G I q)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [← IsIso.inv_comp_eq] at hn
  rw [← hn]
  infer_instance

end Pushforward

end Stacks.Cohomology.HypercohomologyEdge
