module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelEtaleKInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelHomCompCocycle
public import StacksFrontier.CategoryTheory.Adjunction.InvertibleMateHomEquiv
public import StacksFrontier.CategoryTheory.Sites.ContinuousPushforwardMates
public import StacksFrontier.CategoryTheory.Localization.MapHomotopyCategoryAdjunctionCounit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence

/-!
# The derived base change of a square with étale horizontal arrows, on the spaces-étale models

Consider a commutative square of algebraic spaces
```
  Y' --j'--> W'
  |h         |g
  v          v
  Y  --j-->  W
```
with `j` and `j'` étale. On the spaces-étale models the inverse images give a 2-cell
`j^* ⋙ h^* ⟶ g^* ⋙ j'^*` (the composition isomorphisms of inverse images around the square), and
its mate along `g^* ⊣ g_*` and `h^* ⊣ h_*` is the base change morphism
`g_* ⋙ j^* ⟶ j'^* ⋙ h_*` (`AlgebraicGeometry.Space.spacesEtaleModelPushforwardBaseChange`). The
same construction with derived functors gives the derived base change morphism
`Rg_* ⋙ Lj^* ⟶ Lj'^* ⋙ Rh_*`.

The derived base change morphism is invertible as soon as the underived one is
(`AlgebraicGeometry.Space.isIso_spacesEtaleModelDerivedPushforwardBaseChange`): computing on a
K-injective complex `I`, the derived pushforward is computed by `g_* I`, restriction along `j` is
exact so needs no derivation, and `j'^* I` is K-injective again
(`AlgebraicGeometry.Space.isKInjective_spacesEtaleModelHom_pullbackTopos`), so `Rh_*` is computed
by `h_*` on it; the comparison of the two mates is
`CategoryTheory.Adjunction.isIso_mateEquiv_of_fac`.

## Main results

* `CategoryTheory.Adjunction.exists_mateEquiv_mapHomotopyCategoryAdjunction_app_quotient`: the
  mate of a 2-cell induced on homotopy categories is induced by the mate.
* `CategoryTheory.Adjunction.isIso_mateEquiv_symm_iff_of_rightAdjoint`: the invertibility of the
  mate of a 2-cell between right adjoints does not depend on the choice of the left adjoints.
* `AlgebraicGeometry.Space.isIso_spacesEtaleModelDerivedPushforwardBaseChange`: the derived base
  change morphism is invertible if the underived one is.
* `AlgebraicGeometry.Space.isIso_spacesEtaleModelPushforwardBaseChange_iff`: the underived one is
  invertible exactly when the mate of the conjugate square of direct images along the adjunctions
  of restriction along postcomposition is.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Adjunction

variable {ι : Type*} {A : Type*} {B : Type*} {C : Type*} {D : Type*} [Category* A] [Category* B]
  [Category* C] [Category* D] [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
  {G₁ : A ⥤ B} {R₁ : B ⥤ A} {G₂ : C ⥤ D} {R₂ : D ⥤ C} {T : A ⥤ C} {Bo : B ⥤ D}
  [G₁.Additive] [R₁.Additive] [G₂.Additive] [R₂.Additive] [T.Additive] [Bo.Additive]

/-- **The mate of a 2-cell induced on homotopy categories is induced by the mate**: if a 2-cell
`e₀` between the functors induced on homotopy categories is, at the class of each complex, the
class of the degreewise 2-cell `e`, then its mate along the induced adjunctions is, at the class
of each complex, the class of a morphism of complexes whose components are those of the mate of
`e`. -/
theorem exists_mateEquiv_mapHomotopyCategoryAdjunction_app_quotient (adj₁ : G₁ ⊣ R₁)
    (adj₂ : G₂ ⊣ R₂) (c : ComplexShape ι) (e : TwoSquare T G₁ G₂ Bo)
    (e₀ : TwoSquare (T.mapHomotopyCategory c) (G₁.mapHomotopyCategory c)
      (G₂.mapHomotopyCategory c) (Bo.mapHomotopyCategory c))
    (he₀ : ∀ K : HomologicalComplex A c, e₀.app ((HomotopyCategory.quotient A c).obj K) =
      (HomotopyCategory.quotient D c).map ((NatTrans.mapHomologicalComplex e c).app K))
    (K : HomologicalComplex B c) :
    ∃ φ : (T.mapHomologicalComplex c).obj ((R₁.mapHomologicalComplex c).obj K) ⟶
        (R₂.mapHomologicalComplex c).obj ((Bo.mapHomologicalComplex c).obj K),
      (∀ n, φ.f n = (mateEquiv adj₁ adj₂ e).app (K.X n)) ∧
      (mateEquiv (mapHomotopyCategoryAdjunction adj₁ c) (mapHomotopyCategoryAdjunction adj₂ c)
        e₀).app ((HomotopyCategory.quotient B c).obj K) =
        (HomotopyCategory.quotient C c).map φ := by
  refine ⟨(mapHomologicalComplexAdjunction adj₂ c).unit.app _ ≫
      (R₂.mapHomologicalComplex c).map
        ((NatTrans.mapHomologicalComplex e c).app ((R₁.mapHomologicalComplex c).obj K)) ≫
      (R₂.mapHomologicalComplex c).map ((Bo.mapHomologicalComplex c).map
        ((mapHomologicalComplexAdjunction adj₁ c).counit.app K)), fun n => ?_, ?_⟩
  · have hθ : (mateEquiv adj₁ adj₂ e).app (K.X n) =
        adj₂.unit.app (T.obj (R₁.obj (K.X n))) ≫ R₂.map (e.app (R₁.obj (K.X n))) ≫
          R₂.map (Bo.map (adj₁.counit.app (K.X n))) := by
      simp [mateEquiv_apply]
    rw [hθ]
    simp [mapHomologicalComplexAdjunction]
  · have hθ : (mateEquiv (mapHomotopyCategoryAdjunction adj₁ c)
        (mapHomotopyCategoryAdjunction adj₂ c) e₀).app
          ((HomotopyCategory.quotient B c).obj K) =
        (mapHomotopyCategoryAdjunction adj₂ c).unit.app ((T.mapHomotopyCategory c).obj
          ((R₁.mapHomotopyCategory c).obj ((HomotopyCategory.quotient B c).obj K))) ≫
        (R₂.mapHomotopyCategory c).map (e₀.app ((R₁.mapHomotopyCategory c).obj
          ((HomotopyCategory.quotient B c).obj K))) ≫
        (R₂.mapHomotopyCategory c).map ((Bo.mapHomotopyCategory c).map
          ((mapHomotopyCategoryAdjunction adj₁ c).counit.app
            ((HomotopyCategory.quotient B c).obj K))) := by
      simp [mateEquiv_apply]
    have hu : (mapHomotopyCategoryAdjunction adj₂ c).unit.app ((T.mapHomotopyCategory c).obj
        ((R₁.mapHomotopyCategory c).obj ((HomotopyCategory.quotient B c).obj K))) =
        (HomotopyCategory.quotient C c).map ((mapHomologicalComplexAdjunction adj₂ c).unit.app
          ((T.mapHomologicalComplex c).obj ((R₁.mapHomologicalComplex c).obj K))) := rfl
    have hc : (mapHomotopyCategoryAdjunction adj₁ c).counit.app
        ((HomotopyCategory.quotient B c).obj K) =
        (HomotopyCategory.quotient B c).map
          ((mapHomologicalComplexAdjunction adj₁ c).counit.app K) :=
      rfl
    have he : e₀.app ((R₁.mapHomotopyCategory c).obj
        ((HomotopyCategory.quotient B c).obj K)) =
        (HomotopyCategory.quotient D c).map
          ((NatTrans.mapHomologicalComplex e c).app
            ((R₁.mapHomologicalComplex c).obj K)) :=
      he₀ _
    rw [hθ, hu, he, hc]
    rfl

/-- The mate of a 2-cell induced on homotopy categories by a 2-cell with invertible mate is
invertible at every object. -/
theorem isIso_mateEquiv_mapHomotopyCategoryAdjunction_app (adj₁ : G₁ ⊣ R₁) (adj₂ : G₂ ⊣ R₂)
    (c : ComplexShape ι) (e : TwoSquare T G₁ G₂ Bo)
    (e₀ : TwoSquare (T.mapHomotopyCategory c) (G₁.mapHomotopyCategory c)
      (G₂.mapHomotopyCategory c) (Bo.mapHomotopyCategory c))
    (he₀ : ∀ K : HomologicalComplex A c, e₀.app ((HomotopyCategory.quotient A c).obj K) =
      (HomotopyCategory.quotient D c).map ((NatTrans.mapHomologicalComplex e c).app K))
    [IsIso (mateEquiv adj₁ adj₂ e)] (K : HomotopyCategory B c) :
    IsIso ((mateEquiv (mapHomotopyCategoryAdjunction adj₁ c)
      (mapHomotopyCategoryAdjunction adj₂ c) e₀).app K) := by
  obtain ⟨K⟩ := K
  obtain ⟨φ, hφ, h⟩ :=
    exists_mateEquiv_mapHomotopyCategoryAdjunction_app_quotient adj₁ adj₂ c e e₀ he₀ K
  change IsIso ((mateEquiv (mapHomotopyCategoryAdjunction adj₁ c)
      (mapHomotopyCategoryAdjunction adj₂ c) e₀).app
        ((HomotopyCategory.quotient B c).obj K))
  rw [h]
  have : ∀ n, IsIso (φ.f n) := fun n => by rw [hφ n]; infer_instance
  have : IsIso φ := HomologicalComplex.Hom.isIso_of_components φ
  exact Functor.map_isIso _ φ


section ChangeOfLeftAdjoints

variable {A : Type*} {B : Type*} {C : Type*} {D : Type*} [Category* A] [Category* B]
  [Category* C] [Category* D] {G : A ⥤ C} {H : B ⥤ D} {L₁ L₁' : A ⥤ B} {R₁ : B ⥤ A}
  {L₂ L₂' : C ⥤ D} {R₂ : D ⥤ C}

/-- **The mate of a 2-cell between right adjoints does not depend on the choice of the left
adjoints, up to the identifications of left adjoints**: it is invertible for one choice of left
adjoints of `R₁` and `R₂` exactly when it is for another. -/
theorem isIso_mateEquiv_symm_iff_of_rightAdjoint (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁)
    (adj₂ : L₂ ⊣ R₂) (adj₂' : L₂' ⊣ R₂) (π : TwoSquare R₁ H G R₂) :
    IsIso ((mateEquiv adj₁ adj₂).symm π) ↔
      IsIso ((mateEquiv adj₁' adj₂').symm π) := by
  suffices key : ∀ {L₁ L₁' : A ⥤ B} {L₂ L₂' : C ⥤ D} (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁)
      (adj₂ : L₂ ⊣ R₂) (adj₂' : L₂' ⊣ R₂),
      IsIso ((mateEquiv adj₁' adj₂').symm π) →
        IsIso ((mateEquiv adj₁ adj₂).symm π) from
    ⟨key adj₁' adj₁ adj₂' adj₂, key adj₁ adj₁' adj₂ adj₂'⟩
  intro L₁ L₁' L₂ L₂' adj₁ adj₁' adj₂ adj₂' hπ
  let β₂ := (adj₂.leftAdjointUniq adj₂').hom
  let β₁ := (adj₁'.leftAdjointUniq adj₁).hom
  have hβ₂ : conjugateEquiv adj₂' adj₂ β₂ = 𝟙 R₂ := by
    simp only [β₂, leftAdjointUniq_eq_conjugateEquiv_symm_id adj₂' adj₂, Equiv.apply_symm_apply]
  have hβ₁ : conjugateEquiv adj₁ adj₁' β₁ = 𝟙 R₁ := by
    simp only [β₁, leftAdjointUniq_eq_conjugateEquiv_symm_id adj₁ adj₁', Equiv.apply_symm_apply]
  have h₁ : mateEquiv adj₁' adj₂ (((mateEquiv adj₁' adj₂').symm π).whiskerRight β₂) = π := by
    rw [mateEquiv_conjugateEquiv_vcomp adj₁' adj₂' adj₂ ((mateEquiv adj₁' adj₂').symm π) β₂, hβ₂,
      Equiv.apply_symm_apply]
    ext X
    simp [TwoSquare.whiskerBottom]
  have h₂ : mateEquiv adj₁ adj₂
      ((((mateEquiv adj₁' adj₂').symm π).whiskerRight β₂).whiskerLeft β₁) = π := by
    rw [conjugateEquiv_mateEquiv_vcomp adj₁ adj₁' adj₂ β₁
      (((mateEquiv adj₁' adj₂').symm π).whiskerRight β₂), hβ₁, h₁]
    ext X
    simp [TwoSquare.whiskerTop]
  have h₃ : (mateEquiv adj₁ adj₂).symm π =
      (((mateEquiv adj₁' adj₂').symm π).whiskerRight β₂).whiskerLeft β₁ :=
    (Equiv.symm_apply_eq _).2 h₂.symm
  rw [h₃]
  dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight]
  infer_instance

end ChangeOfLeftAdjoints

end CategoryTheory.Adjunction

namespace CategoryTheory

variable {ι : Type*} {𝒜 : Type*} {ℬ : Type*} {𝒞' : Type*} {𝒟 : Type*} [Category* 𝒜] [Category* ℬ]
  [Category* 𝒞'] [Category* 𝒟] [Preadditive 𝒜] [Preadditive ℬ] [Preadditive 𝒞'] [Preadditive 𝒟]
  {F : 𝒜 ⥤ ℬ} {G : ℬ ⥤ 𝒟} {H : 𝒜 ⥤ 𝒟} {F' : 𝒜 ⥤ 𝒞'} {G' : 𝒞' ⥤ 𝒟} {H' : 𝒜 ⥤ 𝒟}
  [F.Additive] [G.Additive] [H.Additive] [F'.Additive] [G'.Additive] [H'.Additive]

/-- A 2-cell between composites of functors induced on homotopy categories, assembled from the
composition isomorphisms and a transformation `t₀` induced by `t`, is induced by the
corresponding 2-cell between composites of the functors themselves. -/
theorem Functor.mapHomotopyCategoryCompIso_hom_comp_comp_inv_app_quotient (c : ComplexShape ι)
    (e : F ⋙ G ≅ H) (e' : F' ⋙ G' ≅ H') (t : H ⟶ H')
    (t₀ : H.mapHomotopyCategory c ⟶ H'.mapHomotopyCategory c)
    (ht : ∀ K, t₀.app ((HomotopyCategory.quotient 𝒜 c).obj K) =
      (HomotopyCategory.quotient 𝒟 c).map ((NatTrans.mapHomologicalComplex t c).app K))
    (K : HomologicalComplex 𝒜 c) :
    ((Functor.mapHomotopyCategoryCompIso e c).hom ≫ t₀ ≫
        (Functor.mapHomotopyCategoryCompIso e' c).inv).app
          ((HomotopyCategory.quotient 𝒜 c).obj K) =
      (HomotopyCategory.quotient 𝒟 c).map
        ((NatTrans.mapHomologicalComplex (e.hom ≫ t ≫ e'.inv) c).app K) := by
  simp only [NatTrans.comp_app, ht, NatTrans.mapHomologicalComplex_comp, Functor.map_comp]
  rfl

end CategoryTheory

namespace AlgebraicGeometry.Space

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi

attribute [local instance high] HasDerivedCategory.standard

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Generic

variable {X Y : AlgebraicSpaces B S hS}

/-- The identification of the inverse images of modules along equal morphisms of algebraic
spaces. (It is defined by recursion on the equality of morphisms, not of functors, so that
checking it never compares the two inverse images.) -/
def spacesEtaleModelPullbackCongr {k₁ k₂ : X ⟶ Y} (hk : k₁ = k₂) :
    (spacesEtaleModelHom B S hS k₁).pullbackTopos ≅ (spacesEtaleModelHom B S hS k₂).pullbackTopos :=
  Eq.rec (motive := fun k _ => (spacesEtaleModelHom B S hS k₁).pullbackTopos ≅
    (spacesEtaleModelHom B S hS k).pullbackTopos) (Iso.refl _) hk

/-- The identification of the inverse images on homotopy categories along equal morphisms. -/
def spacesEtaleModelHomotopyPullbackCongr {k₁ k₂ : X ⟶ Y} (hk : k₁ = k₂) :
    (spacesEtaleModelHom B S hS k₁).pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (spacesEtaleModelHom B S hS k₂).pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ) :=
  Eq.rec (motive := fun k _ =>
    (spacesEtaleModelHom B S hS k₁).pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (spacesEtaleModelHom B S hS k).pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ))
    (Iso.refl _) hk

/-- The identification of the derived pullbacks along equal morphisms. -/
def spacesEtaleModelDerivedPullbackCongr {k₁ k₂ : X ⟶ Y} (hk : k₁ = k₂) :
    derivedPullback (spacesEtaleModelHom B S hS k₁) ≅
      derivedPullback (spacesEtaleModelHom B S hS k₂) :=
  Eq.rec (motive := fun k _ => derivedPullback (spacesEtaleModelHom B S hS k₁) ≅
    derivedPullback (spacesEtaleModelHom B S hS k)) (Iso.refl _) hk

/-- The identification of derived pullbacks along equal morphisms is compatible with the
comparison maps. -/
theorem spacesEtaleModelDerivedPullbackCongr_hom_app_comp_derivedPullbackComparison
    {k₁ k₂ : X ⟶ Y} (hk : k₁ = k₂)
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS Y).O)) (ComplexShape.up ℤ)) :
    (spacesEtaleModelDerivedPullbackCongr B S hS hk).hom.app (DerivedCategory.Qh.obj K) ≫
      (derivedPullbackComparison (spacesEtaleModelHom B S hS k₂)).app K =
    (derivedPullbackComparison (spacesEtaleModelHom B S hS k₁)).app K ≫
      DerivedCategory.Qh.map ((spacesEtaleModelHomotopyPullbackCongr B S hS hk).hom.app K) := by
  subst hk
  simp only [spacesEtaleModelDerivedPullbackCongr, spacesEtaleModelHomotopyPullbackCongr,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

/-- The identification on homotopy categories is induced by the identification of inverse
images. -/
theorem spacesEtaleModelHomotopyPullbackCongr_hom_app_quotient {k₁ k₂ : X ⟶ Y} (hk : k₁ = k₂)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS Y).O)) ℤ) :
    (spacesEtaleModelHomotopyPullbackCongr B S hS hk).hom.app
        ((HomotopyCategory.quotient _ _).obj K) =
      (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
        (spacesEtaleModelPullbackCongr B S hS hk).hom (ComplexShape.up ℤ)).app K) := by
  subst hk
  simp only [spacesEtaleModelHomotopyPullbackCongr, spacesEtaleModelPullbackCongr, Iso.refl_hom,
    NatTrans.id_app, NatTrans.mapHomologicalComplex_id]
  rfl

include hS in
/-- Along an étale morphism of algebraic spaces the comparison map of the derived pullback on the
models is invertible: the inverse image is exact. -/
theorem isIso_derivedPullbackComparison_spacesEtaleModelHom_of_isEtale (j : X ⟶ Y)
    (hj : IsEtale B S hS j.hom) :
    IsIso (derivedPullbackComparison (spacesEtaleModelHom B S hS j)) :=
  have := preservesFiniteLimits_spacesEtaleModelHom_pullbackTopos B S hS j hj
  Functor.isIso_of_isLeftDerivedFunctor_of_inverts (derivedPullback _)
    (derivedPullbackComparison _)
    (Stacks.DerivedFunctor.HigherDerivedOfExact.mapHomotopyCategory_inverts_quasiIso _)

end Generic

variable {W W' Y Y' : AlgebraicSpaces B S hS} (g : W' ⟶ W) (h : Y' ⟶ Y) (j : Y ⟶ W)
  (j' : Y' ⟶ W') (comm : h ≫ j = j' ≫ g)

/-- The 2-cell `j^* ⋙ h^* ⟶ g^* ⋙ j'^*` of inverse images of modules on the models around a
commutative square: the composition isomorphisms of inverse images around both sides. -/
def spacesEtaleModelPullbackSquare :
    TwoSquare (spacesEtaleModelHom B S hS j).pullbackTopos
      (spacesEtaleModelHom B S hS g).pullbackTopos
      (spacesEtaleModelHom B S hS h).pullbackTopos (spacesEtaleModelHom B S hS j').pullbackTopos :=
  .mk _ _ _ _ ((spacesEtaleModelPullbackComp B S hS h j).hom ≫
    (spacesEtaleModelPullbackCongr B S hS comm).hom ≫
    (spacesEtaleModelPullbackComp B S hS j' g).inv)

/-- **The base change morphism `g_* ⋙ j^* ⟶ j'^* ⋙ h_*` of modules on the models**: the mate of
`AlgebraicGeometry.Space.spacesEtaleModelPullbackSquare` along `g^* ⊣ g_*` and `h^* ⊣ h_*`. -/
def spacesEtaleModelPushforwardBaseChange :
    TwoSquare (spacesEtaleModelHom B S hS g).pushforwardTopos
      (spacesEtaleModelHom B S hS j').pullbackTopos (spacesEtaleModelHom B S hS j).pullbackTopos
      (spacesEtaleModelHom B S hS h).pushforwardTopos :=
  mateEquiv (spacesEtaleModelHom B S hS g).pullbackPushforwardAdjunctionTopos
    (spacesEtaleModelHom B S hS h).pullbackPushforwardAdjunctionTopos
    (spacesEtaleModelPullbackSquare B S hS g h j j' comm)

/-- The 2-cell `Lj^* ⋙ Lh^* ⟶ Lg^* ⋙ Lj'^*` of derived pullbacks on the models around a
commutative square: the composition isomorphisms of derived pullbacks around both sides. -/
def spacesEtaleModelDerivedPullbackSquare :
    TwoSquare (derivedPullback (spacesEtaleModelHom B S hS j))
      (derivedPullback (spacesEtaleModelHom B S hS g))
      (derivedPullback (spacesEtaleModelHom B S hS h))
      (derivedPullback (spacesEtaleModelHom B S hS j')) :=
  .mk _ _ _ _ ((spacesEtaleModelDerivedPullbackCompIso B S hS h j).hom ≫
    (spacesEtaleModelDerivedPullbackCongr B S hS comm).hom ≫
    (spacesEtaleModelDerivedPullbackCompIso B S hS j' g).inv)

/-- **The derived base change morphism `Rg_* ⋙ Lj^* ⟶ Lj'^* ⋙ Rh_*` on the models**: the mate of
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackSquare` along `Lg^* ⊣ Rg_*` and
`Lh^* ⊣ Rh_*` (Stacks 07A6). -/
def spacesEtaleModelDerivedPushforwardBaseChange :=
  mateEquiv (derivedAdjunction (spacesEtaleModelHom B S hS g)
      (isMorphismOfSites_spacesEtaleModelHom B S hS g))
    (derivedAdjunction (spacesEtaleModelHom B S hS h)
      (isMorphismOfSites_spacesEtaleModelHom B S hS h))
    (spacesEtaleModelDerivedPullbackSquare B S hS g h j j' comm)

/-- The 2-cell of `AlgebraicGeometry.Space.spacesEtaleModelPullbackSquare` on homotopy
categories. -/
def spacesEtaleModelHomotopyPullbackSquare :
    TwoSquare ((spacesEtaleModelHom B S hS j).pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ))
      ((spacesEtaleModelHom B S hS g).pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ))
      ((spacesEtaleModelHom B S hS h).pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ))
      ((spacesEtaleModelHom B S hS j').pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)) :=
  .mk _ _ _ _ ((Functor.mapHomotopyCategoryCompIso (spacesEtaleModelPullbackComp B S hS h j)
      (ComplexShape.up ℤ)).hom ≫
    (spacesEtaleModelHomotopyPullbackCongr B S hS comm).hom ≫
    (Functor.mapHomotopyCategoryCompIso (spacesEtaleModelPullbackComp B S hS j' g)
      (ComplexShape.up ℤ)).inv)

/-- The 2-cell `AlgebraicGeometry.Space.spacesEtaleModelHomotopyPullbackSquare` at the class of a
complex `K` is the class of the 2-cell `AlgebraicGeometry.Space.spacesEtaleModelPullbackSquare`
applied termwise to `K`. -/
theorem spacesEtaleModelHomotopyPullbackSquare_app_quotient
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS W).O)) ℤ) :
    (spacesEtaleModelHomotopyPullbackSquare B S hS g h j j' comm).app
        ((HomotopyCategory.quotient _ _).obj K) =
      (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
        (spacesEtaleModelPullbackSquare B S hS g h j j' comm)
          (ComplexShape.up ℤ)).app K) :=
  Functor.mapHomotopyCategoryCompIso_hom_comp_comp_inv_app_quotient (ComplexShape.up ℤ)
    (spacesEtaleModelPullbackComp B S hS h j) (spacesEtaleModelPullbackComp B S hS j' g) _ _
    (spacesEtaleModelHomotopyPullbackCongr_hom_app_quotient B S hS comm) K

/-- The derived 2-cell and the homotopy 2-cell of a commutative square are compatible with the
comparison maps of the derived pullbacks. -/
theorem spacesEtaleModelDerivedPullbackSquare_app_comp_derivedPullbackComparison
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS W).O)) (ComplexShape.up ℤ)) :
    (spacesEtaleModelDerivedPullbackSquare B S hS g h j j' comm).app
        (DerivedCategory.Qh.obj K) ≫
      (derivedPullback (spacesEtaleModelHom B S hS j')).map
        ((derivedPullbackComparison (spacesEtaleModelHom B S hS g)).app K) ≫
      (derivedPullbackComparison (spacesEtaleModelHom B S hS j')).app
        (((spacesEtaleModelHom B S hS g).pullbackTopos.mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) =
    (derivedPullback (spacesEtaleModelHom B S hS h)).map
        ((derivedPullbackComparison (spacesEtaleModelHom B S hS j)).app K) ≫
      (derivedPullbackComparison (spacesEtaleModelHom B S hS h)).app
        (((spacesEtaleModelHom B S hS j).pullbackTopos.mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        ((spacesEtaleModelHomotopyPullbackSquare B S hS g h j j' comm).app K) := by
  have h₁ := spacesEtaleModelDerivedPullbackCompIso_hom_app_comp_derivedPullbackComparison_app
    B S hS h j K
  have h₂ := spacesEtaleModelDerivedPullbackCompIso_hom_app_comp_derivedPullbackComparison_app
    B S hS j' g K
  have h₃ := spacesEtaleModelDerivedPullbackCongr_hom_app_comp_derivedPullbackComparison
    B S hS comm K
  have hh : DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (spacesEtaleModelPullbackComp B S hS j' g) (ComplexShape.up ℤ)).hom.app K) ≫
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (spacesEtaleModelPullbackComp B S hS j' g) (ComplexShape.up ℤ)).inv.app K) = 𝟙 _ :=
    (DerivedCategory.Qh.mapIso ((Functor.mapHomotopyCategoryCompIso
        (spacesEtaleModelPullbackComp B S hS j' g) (ComplexShape.up ℤ)).app K)).hom_inv_id
  have h₂' : (spacesEtaleModelDerivedPullbackCompIso B S hS j' g).inv.app
        (DerivedCategory.Qh.obj K) ≫
      (derivedPullback (spacesEtaleModelHom B S hS j')).map
        ((derivedPullbackComparison (spacesEtaleModelHom B S hS g)).app K) ≫
      (derivedPullbackComparison (spacesEtaleModelHom B S hS j')).app
        (((spacesEtaleModelHom B S hS g).pullbackTopos.mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) =
      (derivedPullbackComparison (spacesEtaleModelHom B S hS (j' ≫ g))).app K ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (spacesEtaleModelPullbackComp B S hS j' g) (ComplexShape.up ℤ)).inv.app K) := by
    rw [← cancel_epi ((spacesEtaleModelDerivedPullbackCompIso B S hS j' g).hom.app
      (DerivedCategory.Qh.obj K)), Iso.hom_inv_id_app_assoc, reassoc_of% h₂, hh]
    exact (congrArg (fun φ => (derivedPullback (spacesEtaleModelHom B S hS j')).map
        ((derivedPullbackComparison (spacesEtaleModelHom B S hS g)).app K) ≫ φ)
      (Category.comp_id ((derivedPullbackComparison (spacesEtaleModelHom B S hS j')).app
        (((spacesEtaleModelHom B S hS g).pullbackTopos.mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K)))).symm
  change ((spacesEtaleModelDerivedPullbackCompIso B S hS h j).hom ≫
      (spacesEtaleModelDerivedPullbackCongr B S hS comm).hom ≫
      (spacesEtaleModelDerivedPullbackCompIso B S hS j' g).inv).app (DerivedCategory.Qh.obj K) ≫
      _ ≫ _ = _ ≫ _ ≫ DerivedCategory.Qh.map (((Functor.mapHomotopyCategoryCompIso
        (spacesEtaleModelPullbackComp B S hS h j) (ComplexShape.up ℤ)).hom ≫
      (spacesEtaleModelHomotopyPullbackCongr B S hS comm).hom ≫
      (Functor.mapHomotopyCategoryCompIso (spacesEtaleModelPullbackComp B S hS j' g)
        (ComplexShape.up ℤ)).inv).app K)
  rw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, h₂', reassoc_of% h₃,
    reassoc_of% h₁]

/-- Every object of the derived category of the model of `W'` is the class of a K-injective
complex `I`, at which all the comparison maps of the base change square are invertible. -/
theorem exists_isKInjective_isIso_comparisons (hj : IsEtale B S hS j.hom)
    (hj' : IsEtale B S hS j'.hom)
    [IsIso (spacesEtaleModelPushforwardBaseChange B S hS g h j j' comm)]
    (X : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS W').O))) :
    ∃ K, Nonempty (DerivedCategory.Qh.obj K ≅ X) ∧
      IsIso ((Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforwardUnit
        (spacesEtaleModelHom B S hS g)).app K) ∧
      IsIso ((derivedPullbackComparison (spacesEtaleModelHom B S hS j)).app
        (((spacesEtaleModelHom B S hS g).pushforwardTopos.mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K)) ∧
      IsIso ((mateEquiv (homotopyPullbackPushforwardAdjunction (spacesEtaleModelHom B S hS g))
        (homotopyPullbackPushforwardAdjunction (spacesEtaleModelHom B S hS h))
        (spacesEtaleModelHomotopyPullbackSquare B S hS g h j j' comm)).app K) ∧
      IsIso ((Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforwardUnit
        (spacesEtaleModelHom B S hS h)).app
        (((spacesEtaleModelHom B S hS j').pullbackTopos.mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K)) ∧
      IsIso ((derivedPullbackComparison (spacesEtaleModelHom B S hS j')).app K) := by
  have hcj := isIso_derivedPullbackComparison_spacesEtaleModelHom_of_isEtale B S hS j hj
  have hcj' := isIso_derivedPullbackComparison_spacesEtaleModelHom_of_isEtale B S hS j' hj'
  have hγ : IsIso (mateEquiv (spacesEtaleModelHom B S hS g).pullbackPushforwardAdjunctionTopos
      (spacesEtaleModelHom B S hS h).pullbackPushforwardAdjunctionTopos
      (spacesEtaleModelPullbackSquare B S hS g h j j' comm)) :=
    ‹IsIso (spacesEtaleModelPushforwardBaseChange B S hS g h j j' comm)›
  obtain ⟨I, f, hI, hf⟩ := exists_quasiIso_isKInjective (spacesEtaleModelRingedTopos B S hS W')
    (DerivedCategory.Q.objPreimage X)
  have := hI
  have : IsIso (DerivedCategory.Q.map f) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hf
  exact ⟨(HomotopyCategory.quotient _ _).obj I,
    ⟨(DerivedCategory.quotientCompQhIso _).app I ≪≫ (asIso (DerivedCategory.Q.map f)).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso X⟩,
    isIso_derivedPushforwardUnit_app_of_isKInjective (spacesEtaleModelHom B S hS g) I hI,
    inferInstance,
    Adjunction.isIso_mateEquiv_mapHomotopyCategoryAdjunction_app _ _ _ _ _
      (spacesEtaleModelHomotopyPullbackSquare_app_quotient B S hS g h j j' comm) _,
    isIso_derivedPushforwardUnit_app_of_isKInjective (spacesEtaleModelHom B S hS h)
      (((spacesEtaleModelHom B S hS j').pullbackTopos.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)
      (isKInjective_spacesEtaleModelHom_pullbackTopos B S hS j' hj' I), inferInstance⟩

/-- **The derived base change morphism is invertible as soon as the underived one is**, for a
commutative square whose horizontal arrows `j`, `j'` are étale. -/
theorem isIso_spacesEtaleModelDerivedPushforwardBaseChange (hj : IsEtale B S hS j.hom)
    (hj' : IsEtale B S hS j'.hom)
    [IsIso (spacesEtaleModelPushforwardBaseChange B S hS g h j j' comm)] :
    IsIso (spacesEtaleModelDerivedPushforwardBaseChange B S hS g h j j' comm) :=
  Adjunction.isIso_mateEquiv_of_fac
    (QW := DerivedCategory.Qh) (QW' := DerivedCategory.Qh) (QY := DerivedCategory.Qh)
    (QY' := DerivedCategory.Qh)
    (homotopyPullbackPushforwardAdjunction (spacesEtaleModelHom B S hS g))
    (homotopyPullbackPushforwardAdjunction (spacesEtaleModelHom B S hS h))
    (spacesEtaleModelHomotopyPullbackSquare B S hS g h j j' comm) _ _ _
    (fun M => (derivedPullbackComparison (spacesEtaleModelHom B S hS g)).app M)
    (fun M => (derivedPullbackComparison (spacesEtaleModelHom B S hS h)).app M)
    (fun M => (derivedPullbackComparison (spacesEtaleModelHom B S hS j)).app M)
    (fun M => (derivedPullbackComparison (spacesEtaleModelHom B S hS j')).app M)
    (fun K => (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforwardUnit
      (spacesEtaleModelHom B S hS g)).app K)
    (fun K => (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforwardUnit
      (spacesEtaleModelHom B S hS h)).app K)
    (fun φ => (derivedPullbackComparison (spacesEtaleModelHom B S hS j')).naturality φ)
    (fun φ => (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforwardUnit
      (spacesEtaleModelHom B S hS h)).naturality φ)
    (fun M => derivedPullbackPushforwardAdjunctionOfKFlat_unit_fac
      (spacesEtaleModelHom B S hS h) (isMorphismOfSites_spacesEtaleModelHom B S hS h)
      (fun hh => pullbackInvertsQuasiIso_isKFlat _ hh) M)
    (fun K => derivedPullbackPushforwardAdjunctionOfKFlat_counit_fac
      (spacesEtaleModelHom B S hS g) (isMorphismOfSites_spacesEtaleModelHom B S hS g)
      (fun hh => pullbackInvertsQuasiIso_isKFlat _ hh) K)
    (spacesEtaleModelDerivedPullbackSquare_app_comp_derivedPullbackComparison B S hS g h j j' comm)
    (exists_isKInjective_isIso_comparisons B S hS g h j j' comm hj hj')

/-- The conjugate `j'_* ⋙ g_* ⟶ h_* ⋙ j_*` of
`AlgebraicGeometry.Space.spacesEtaleModelPullbackSquare` is the composite of the composition
isomorphisms of direct images (`AlgebraicGeometry.Space.spacesEtaleModelPushforwardComp`) with the
conjugate of the identification of inverse images along `h ≫ j = j' ≫ g`. -/
theorem conjugateEquiv_spacesEtaleModelPullbackSquare :
    conjugateEquiv ((spacesEtaleModelHom B S hS g).pullbackPushforwardAdjunctionTopos.comp
        (spacesEtaleModelHom B S hS j').pullbackPushforwardAdjunctionTopos)
      ((spacesEtaleModelHom B S hS j).pullbackPushforwardAdjunctionTopos.comp
        (spacesEtaleModelHom B S hS h).pullbackPushforwardAdjunctionTopos)
      (spacesEtaleModelPullbackSquare B S hS g h j j' comm) =
    (spacesEtaleModelPushforwardComp B S hS j' g).hom ≫
      conjugateEquiv (spacesEtaleModelHom B S hS (j' ≫ g)).pullbackPushforwardAdjunctionTopos
        (spacesEtaleModelHom B S hS (h ≫ j)).pullbackPushforwardAdjunctionTopos
        (spacesEtaleModelPullbackCongr B S hS comm).hom ≫
      (spacesEtaleModelPushforwardComp B S hS h j).inv := by
  have hz : conjugateEquiv ((spacesEtaleModelHom B S hS g).pullbackPushforwardAdjunctionTopos.comp
        (spacesEtaleModelHom B S hS j').pullbackPushforwardAdjunctionTopos)
      (spacesEtaleModelHom B S hS (j' ≫ g)).pullbackPushforwardAdjunctionTopos
      (spacesEtaleModelPullbackComp B S hS j' g).inv =
      (spacesEtaleModelPushforwardComp B S hS j' g).hom := by
    rw [spacesEtaleModelPullbackComp_eq_leftAdjointCompIso]
    exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
  have hx : conjugateEquiv (spacesEtaleModelHom B S hS (h ≫ j)).pullbackPushforwardAdjunctionTopos
      ((spacesEtaleModelHom B S hS j).pullbackPushforwardAdjunctionTopos.comp
        (spacesEtaleModelHom B S hS h).pullbackPushforwardAdjunctionTopos)
      (spacesEtaleModelPullbackComp B S hS h j).hom =
      (spacesEtaleModelPushforwardComp B S hS h j).inv := by
    rw [spacesEtaleModelPullbackComp_eq_leftAdjointCompIso]
    exact Equiv.apply_symm_apply _ _
  rw [← hz, ← hx, conjugateEquiv_comp, conjugateEquiv_comp, Category.assoc]
  rfl

/-- **The underived base change morphism of the models, through restriction along
postcomposition**: `g_* ⋙ j^* ⟶ j'^* ⋙ h_*` is invertible exactly when the mate, along the
adjunctions `P_j ⊣ j_*` and `P_{j'} ⊣ j'_*` of restriction along postcomposition, of the conjugate
`j'_* ⋙ g_* ⟶ h_* ⋙ j_*` of `AlgebraicGeometry.Space.spacesEtaleModelPullbackSquare` is
invertible. -/
theorem isIso_spacesEtaleModelPushforwardBaseChange_iff (hj : IsEtale B S hS j.hom)
    (hj' : IsEtale B S hS j'.hom) :
    IsIso (spacesEtaleModelPushforwardBaseChange B S hS g h j j' comm) ↔
      IsIso ((mateEquiv (smallModelPostcompPushforwardAdjunction B S hS j' hj')
        (smallModelPostcompPushforwardAdjunction B S hS j hj)).symm
          (conjugateEquiv ((spacesEtaleModelHom B S hS g).pullbackPushforwardAdjunctionTopos.comp
              (spacesEtaleModelHom B S hS j').pullbackPushforwardAdjunctionTopos)
            ((spacesEtaleModelHom B S hS j).pullbackPushforwardAdjunctionTopos.comp
              (spacesEtaleModelHom B S hS h).pullbackPushforwardAdjunctionTopos)
            (spacesEtaleModelPullbackSquare B S hS g h j j' comm))) := by
  have h : spacesEtaleModelPushforwardBaseChange B S hS g h j j' comm =
      (mateEquiv (spacesEtaleModelHom B S hS j').pullbackPushforwardAdjunctionTopos
        (spacesEtaleModelHom B S hS j).pullbackPushforwardAdjunctionTopos).symm
          (conjugateEquiv ((spacesEtaleModelHom B S hS g).pullbackPushforwardAdjunctionTopos.comp
              (spacesEtaleModelHom B S hS j').pullbackPushforwardAdjunctionTopos)
            ((spacesEtaleModelHom B S hS j).pullbackPushforwardAdjunctionTopos.comp
              (spacesEtaleModelHom B S hS h).pullbackPushforwardAdjunctionTopos)
            (spacesEtaleModelPullbackSquare B S hS g h j j' comm)) := by
    apply (mateEquiv (spacesEtaleModelHom B S hS j').pullbackPushforwardAdjunctionTopos
      (spacesEtaleModelHom B S hS j).pullbackPushforwardAdjunctionTopos).injective
    refine Eq.trans ?_ (Equiv.apply_symm_apply (mateEquiv
      (spacesEtaleModelHom B S hS j').pullbackPushforwardAdjunctionTopos
      (spacesEtaleModelHom B S hS j).pullbackPushforwardAdjunctionTopos) _).symm
    exact iterated_mateEquiv_conjugateEquiv _ _ _ _ _
  rw [h]
  exact Adjunction.isIso_mateEquiv_symm_iff_of_rightAdjoint _ _ _ _ _

end AlgebraicGeometry.Space

end
