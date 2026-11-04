module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.AbelianDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.SuccUniverseCoefficients
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImageComparison
public import StacksFrontier.CategoryTheory.Sites.PullbackSheafComposeMate
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ModuleSheafAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeTransformationAcyclic
public import StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategoriesApp
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.BoundedBelowComparison
public import StacksFrontier.CategoryTheory.Sites.PushforwardSquareSheafCompose

/-!
# The pro-étale base change map and the underlying abelian sheaves

For a commutative square of schemes, the base change map `g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹` of pro-étale
sheaves of `Λ`-modules, at a bounded below complex `I` of injective sheaves of `Λ`-modules, is
invertible if and only if the base change map of pro-étale abelian sheaves is invertible at the
underlying complex of abelian sheaves of `I`. Indeed passing to underlying abelian sheaves is
exact and conservative, commutes on the nose with direct images, commutes with inverse images
(`CategoryTheory.Functor.isIso_sheafPullbackConstructionSheafComposeMate`), the two base change
maps are mates of the comparisons of composite direct images, and the underlying abelian sheaf of
an injective sheaf of `Λ`-modules is acyclic for every direct image (Stacks 03FD).

## Main results

* `AlgebraicGeometry.ProEtale.isIso_proetaleModuleDerivedBaseChange_app_iff_forget`: for a
  bounded below complex `I` of injective sheaves of `Λ`-modules, the base change map of abelian
  sheaves is invertible at the underlying complex of `I` if and only if the base change map of
  sheaves of `Λ`-modules at `I` becomes invertible on underlying abelian sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasSheafify_proEt_moduleCat_succ
  isGrothendieckAbelian_proetaleModuleSheaf_succ hasSheafify_proetale_addCommGrpCat_succ
  isGrothendieckAbelian_proetale_ab_succ preservesSheafification_forget₂_proetale_succ
  enoughInjectives_proetale_ab_succ enoughInjectives_proetaleModuleSheaf_succ

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The underlying abelian sheaf of a pro-étale sheaf of `Λ`-modules. -/
abbrev proetaleForget (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) ⥤
      Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

/-- Passing to underlying abelian sheaves preserves finite limits. -/
instance preservesFiniteLimits_proetaleForget (X : Scheme.{u}) :
    PreservesFiniteLimits (proetaleForget Λ X) :=
  Stacks.Cohomology.ModuleSheaf.preservesFiniteLimits_sheafCompose_forget₂.{0, u + 1, u, u + 1} _ Λ

/-- Passing to underlying abelian sheaves preserves finite colimits. -/
instance preservesFiniteColimits_proetaleForget (X : Scheme.{u}) :
    PreservesFiniteColimits (proetaleForget Λ X) :=
  Stacks.Cohomology.ModuleSheaf.preservesFiniteColimits_sheafCompose_forget₂.{0, u + 1, u, u + 1}
    _ Λ

/-- Passing to underlying abelian sheaves is an additive functor. -/
instance additive_proetaleForget (X : Scheme.{u}) : (proetaleForget Λ X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Pullback commutes with passing to underlying abelian sheaves: the mate of the identity
`h_* ⋙ forget = forget ⋙ h_*`. -/
def proetaleForgetInverseImage {Z X : Scheme.{u}} (h : Z ⟶ X) :
    TwoSquare (proetaleForget Λ X) (proetaleModuleInverseImage.{u, u + 1, 0} h Λ)
      (proetaleAbelianInverseImage h) (proetaleForget Λ Z) :=
  Functor.sheafPullbackConstructionSheafComposeMate (Scheme.proetaleBaseChange h)
    (ModuleCat.{u + 1} Λ) (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

/-- The comparison `proetaleForgetInverseImage` between inverse images of sheaves of `Λ`-modules
and of their underlying abelian sheaves is an isomorphism. -/
instance isIso_proetaleForgetInverseImage {Z X : Scheme.{u}} (h : Z ⟶ X) :
    IsIso (proetaleForgetInverseImage Λ h).natTrans := by
  have hcolim (W : Z.ProEtᵒᵖ) : PreservesColimitsOfShape
      (CostructuredArrow (Scheme.proetaleBaseChange h).op W)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := by
    have : PreservesColimitsOfSize.{u, u + 1}
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
      ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u, u + 1} Λ
    exact @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _ this _ _
  exact Functor.isIso_sheafPullbackConstructionSheafComposeMate (Scheme.proetaleBaseChange h)
    (ModuleCat.{u + 1} Λ) (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

/-- Direct image commutes with passing to underlying abelian sheaves, on the nose. -/
abbrev proetaleForgetDirectImage {Z X : Scheme.{u}} (h : Z ⟶ X) :
    proetaleForget Λ Z ⋙ proetaleAbelianDirectImage h ≅
      proetaleModuleDirectImage.{u, u + 1, 0} (Λ := Λ) h ⋙ proetaleForget Λ X :=
  Functor.sheafComposeSheafPushforwardIso (Scheme.proetaleBaseChange h) (ModuleCat.{u + 1} Λ)
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

section BaseChange

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (w : f' ≫ g = g' ≫ f)

open TwoSquare in
/-- **The cube identity**: the base change map of sheaves of `Λ`-modules, followed by passage to
underlying abelian sheaves, is the base change map of the underlying abelian sheaves, up to the
comparisons of inverse images with passage to underlying abelian sheaves. -/
theorem proetaleForget_baseChange_cube (S : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    (proetaleForgetInverseImage Λ g).natTrans.app
          ((proetaleModuleDirectImage.{u, u + 1, 0} f).obj S) ≫
        (proetaleForget Λ Y').map ((proetaleModuleBaseChange.{u, u + 1, 0} f g f' g' w).app S) =
      (proetaleAbelianInverseImage g).map ((proetaleForgetDirectImage Λ f).inv.app S) ≫
        (proetaleAbelianBaseChange f g f' g' w).app ((proetaleForget Λ X).obj S) ≫
        (proetaleAbelianDirectImage f').map ((proetaleForgetInverseImage Λ g').natTrans.app S) ≫
        (proetaleForgetDirectImage Λ f').hom.app
          ((proetaleModuleInverseImage.{u, u + 1, 0} g' Λ).obj S) := by
  have key {Z W : Scheme.{u}} (k : Z ⟶ W) :
      mateEquiv (proetaleModuleInverseImageAdjunction.{u, u + 1, 0} Λ k)
        (proetaleAbelianInverseImageAdjunction k) (proetaleForgetInverseImage Λ k) =
      TwoSquare.mk _ _ _ _ (proetaleForgetDirectImage Λ k).inv :=
    Equiv.apply_symm_apply _ _
  have h := Functor.sheafPushforwardSquare_vComp_sheafCompose (Scheme.ProEt.topology X')
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y') (Scheme.ProEt.topology Y)
    (Scheme.proetaleBaseChangeCompIso g' f ≪≫
      eqToIso (congrArg Scheme.proetaleBaseChange w.symm) ≪≫
      (Scheme.proetaleBaseChangeCompIso f' g).symm)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  rw [← key g', ← key g] at h
  exact Stacks.CategoryTheory.mateEquiv_symm_hComp_eq_app
    (proetaleModuleInverseImageAdjunction.{u, u + 1, 0} Λ g')
    (proetaleModuleInverseImageAdjunction.{u, u + 1, 0} Λ g)
    (proetaleAbelianInverseImageAdjunction g') (proetaleAbelianInverseImageAdjunction g)
    (proetaleForgetInverseImage Λ g') (proetaleForgetInverseImage Λ g)
    (proetaleForgetDirectImage Λ f).inv (proetaleForgetDirectImage Λ f').hom
    (TwoSquare.mk _ _ _ _ (proetaleModuleDirectImageSquare.{u, u + 1, 0} (Λ := Λ) f g f' g' w).hom)
    (TwoSquare.mk _ _ _ _ (proetaleAbelianDirectImageSquare f g f' g' w).hom) h S

omit [CommRing Λ] in
/-- An additive functor sends a cochain complex that is strictly concentrated in degrees `≥ n` to
a cochain complex strictly concentrated in degrees `≥ n`. -/
theorem isStrictlyGE_mapHomologicalComplex_obj {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ]
    [Preadditive 𝒜] [Preadditive ℬ] (F : 𝒜 ⥤ ℬ) [F.Additive] (K : CochainComplex 𝒜 ℤ) (n : ℤ)
    [K.IsStrictlyGE n] :
    CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact F.map_isZero (K.isZero_of_isStrictlyGE n i hi)

/-- The direct image of pro-étale abelian sheaves preserves finite limits. -/
instance preservesFiniteLimits_proetaleAbelianDirectImage {Z X : Scheme.{u}} (h : Z ⟶ X) :
    PreservesFiniteLimits (proetaleAbelianDirectImage h) :=
  have := (proetaleAbelianInverseImageAdjunction h).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _

/-- The underlying complex of abelian sheaves of a bounded below complex of injective sheaves of
`Λ`-modules computes the derived direct image of abelian sheaves (Stacks 03FD and Leray's
acyclicity lemma). -/
theorem isIso_proetaleAbelianDerivedDirectImageUnit_app_forget {Z X : Scheme.{u}} (h : Z ⟶ X)
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)) ℤ) (n : ℤ)
    [I.IsStrictlyGE n] [∀ k, Injective (I.X k)] :
    IsIso ((proetaleAbelianDerivedDirectImageUnit h).app ((HomotopyCategory.quotient _ _).obj
      (((proetaleForget Λ Z).mapHomologicalComplex _).obj I))) := by
  have := isStrictlyGE_mapHomologicalComplex_obj (proetaleForget Λ Z) I n
  refine Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic (proetaleAbelianDirectImage h)
    (proetaleAbelianDerivedDirectImage h) (proetaleAbelianDerivedDirectImageUnit h) _ ⟨n, this⟩
    fun k => ?_
  exact Stacks.Cohomology.ModuleSheaf.rightAcyclic_sheafPushforwardContinuous_of_injective.{0,
    u + 1, u, u + 1, u, u + 1} (Scheme.proetaleBaseChange h) Λ (I.X k)

/-- **The pro-étale base change map is detected on underlying abelian sheaves**, at a bounded
below complex of injective sheaves of `Λ`-modules. -/
theorem isIso_proetaleModuleDerivedBaseChange_app_iff_forget
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ) (n : ℤ)
    [I.IsStrictlyGE n] [∀ k, Injective (I.X k)] :
    IsIso ((proetaleAbelianDerivedBaseChange f g f' g' w).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
          (((proetaleForget Λ X).mapHomologicalComplex _).obj I)))) ↔
      IsIso ((proetaleForget Λ Y').mapDerivedCategory.map
        ((proetaleModuleDerivedBaseChange.{u, u + 1, 0} f g f' g' w).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)))) := by
  have := isStrictlyGE_mapHomologicalComplex_obj (proetaleModuleInverseImage.{u, u + 1, 0} g' Λ) I n
  obtain ⟨J, t, ht, hJ, hJge⟩ := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
    (((proetaleModuleInverseImage.{u, u + 1, 0} g' Λ).mapHomologicalComplex _).obj I) n
  have unit_iso {Z W : Scheme.{u}} (k : Z ⟶ W)
      (K : CochainComplex (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)) ℤ)
      [K.IsStrictlyGE n] [∀ i, Injective (K.X i)] :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective
      (proetaleModulePushforwardToDerivedCategory.{u, u + 1, 0} (Λ := Λ) k) DerivedCategory.Qh
      (proetaleModuleDerivedDirectImage.{u, u + 1, 0} k)
      (proetaleModuleDerivedDirectImageUnit.{u, u + 1, 0} k) K
      (CochainComplex.isKInjective_of_injective K n)
  have hI := unit_iso f I
  have hJ' := unit_iso f' J
  exact Stacks.Cohomology.UnboundedComplexes.isIso_derivedBaseChangeMap_app_iff_of_cube_of_isIso
    (proetaleModuleInverseImage.{u, u + 1, 0} g' Λ) (proetaleModuleInverseImage.{u, u + 1, 0} g Λ)
    (proetaleModuleDirectImage.{u, u + 1, 0} (Λ := Λ) f)
    (proetaleModuleDirectImage.{u, u + 1, 0} (Λ := Λ) f')
    (proetaleModuleDerivedDirectImage.{u, u + 1, 0} f)
    (proetaleModuleDerivedDirectImage.{u, u + 1, 0} f')
    (proetaleModuleDerivedDirectImageUnit.{u, u + 1, 0} f)
    (proetaleModuleDerivedDirectImageUnit.{u, u + 1, 0} f')
    (proetaleModuleBaseChange.{u, u + 1, 0} f g f' g' w)
    (proetaleAbelianInverseImage g') (proetaleAbelianInverseImage g)
    (proetaleAbelianDirectImage f) (proetaleAbelianDirectImage f')
    (proetaleAbelianDerivedDirectImage f) (proetaleAbelianDerivedDirectImage f')
    (proetaleAbelianDerivedDirectImageUnit f) (proetaleAbelianDerivedDirectImageUnit f')
    (proetaleAbelianBaseChange f g f' g' w)
    (proetaleForget Λ X) (proetaleForget Λ X') (proetaleForget Λ Y) (proetaleForget Λ Y')
    (proetaleForgetInverseImage Λ g').natTrans (proetaleForgetInverseImage Λ g).natTrans
    (proetaleForgetDirectImage Λ f).inv (proetaleForgetDirectImage Λ f').hom
    (proetaleForget_baseChange_cube Λ f g f' g' w) I hI
    (isIso_proetaleAbelianDerivedDirectImageUnit_app_forget Λ f I n) t hJ'
    (isIso_proetaleAbelianDerivedDirectImageUnit_app_forget Λ f' J n)

end BaseChange

end AlgebraicGeometry.ProEtale
