module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.GlobalDerivedSectionsBaseChangeComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.InterfaceShiftedUnit

/-!
# Cohomology and base change over an affine base: a finite projective model

Let `U` have affine underlying scheme `Spec R`, let `f : X ⟶ U` be a morphism of algebraic spaces
and `𝒢^•` a complex of `𝒪_X`-modules. For a commutative square over `g : U' ⟶ U` with `U'` affine,
`R' = Γ(U', 𝒪)`, the *pullback map*

`RΓ(X, 𝒢^•) ⊗ᴸ_R R' ⟶ RΓ(X', (g')^*𝒢^•)`

is the base change map of `RΓ` followed by `RΓ(X', -)` of the comparison `L(g')^*𝒢^• ⟶ (g')^*𝒢^•`
of the derived with the degreewise pullback. These maps are transitive along stacked squares.

When `RΓ(X, 𝒢^•) ≅ M^•` for a bounded complex `M^•` of finite projective `R`-modules and every
pullback map is invertible, the isomorphisms `RΓ(X', (g')^*𝒢^•) ≅ M^• ⊗_R R'` they induce are
functorial in `R'`. This is the form of Stacks 0A1Q.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackQComparison`: `Lg^*𝒢^• ⟶ g^*𝒢^•`.
* `AlgebraicGeometry.Space.affineBaseDerivedSectionsPullbackMap`: the pullback map.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackQComparison_comp`: the comparisons compose.
* `AlgebraicGeometry.Space.affineBaseDerivedSectionsPullbackMap_comp`: transitivity of the
  pullback maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

namespace Stacks.CategoryTheory.BaseChange

/-- Bookkeeping for the composition of comparisons of derived with degreewise pullbacks. -/
theorem comparison_comp_assemble {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D)
    {A B C₁ E : C} {F T Z P Bc Cc : D} (x₁ : A ⟶ B) (ℓ₁ : B ⟶ C₁) (y₁ : C₁ ≅ E)
    (ℓ₂ : L.obj C₁ ⟶ F) (y₂ : F ⟶ T) (z : T ⟶ Z) (c₀ : L.obj A ⟶ P) (xc : P ⟶ Bc)
    (c₁ : L.obj B ⟶ Bc) (ℓc : Bc ⟶ Cc) (γ : F ⟶ Cc) (yc : Cc ⟶ Z)
    (hn : L.map x₁ ≫ c₁ = c₀ ≫ xc) (hc : c₁ ≫ ℓc = L.map ℓ₁ ≫ ℓ₂ ≫ γ)
    (hq : γ ≫ yc = y₂ ≫ z) :
    L.map (x₁ ≫ ℓ₁ ≫ y₁.hom) ≫ (L.map y₁.inv ≫ ℓ₂ ≫ y₂) ≫ z = c₀ ≫ xc ≫ ℓc ≫ yc := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← L.map_comp_assoc y₁.hom, Iso.hom_inv_id, L.map_id, Category.id_comp, ← hq,
    ← reassoc_of% hc, reassoc_of% hn]

/-- `Stacks.CategoryTheory.BaseChange.comp_assemble` with a single comparison `y` and the second
factors read through two functors. -/
theorem comp_assemble₁ {C D E E' : Type*} [Category* C] [Category* D] [Category* E]
    [Category* E'] (L : C ⥤ D) (R₁ : E ⥤ E') (R₂ : E' ⥤ D) {A : D} {B₀ B₁ B₂ : C}
    {E₀ E₁ E₂ E₃ E₅ : E} (i : A ⟶ L.obj B₀)
    {bc₁ : B₀ ⟶ B₂} {r₁ : B₀ ⟶ B₁} {b₁ : B₁ ⟶ B₂} (hb₁ : bc₁ = r₁ ≫ b₁)
    {bc₂ : L.obj B₂ ⟶ R₂.obj (R₁.obj E₂)} {r₂ : L.obj B₂ ⟶ R₂.obj (R₁.obj E₁)} {v : E₁ ⟶ E₂}
    (hb₂ : bc₂ = r₂ ≫ R₂.map (R₁.map v)) (x : E₂ ⟶ E₃) {r₂' : L.obj B₁ ⟶ R₂.obj (R₁.obj E₀)}
    {u' : E₀ ⟶ E₁}
    (hn : L.map b₁ ≫ r₂ = r₂' ≫ R₂.map (R₁.map u')) {y : E₀ ⟶ E₅} {z : E₅ ⟶ E₃}
    (hh : u' ≫ v ≫ x = y ≫ z) {r₃ : A ⟶ R₂.obj (R₁.obj E₅)}
    (ha : i ≫ L.map r₁ ≫ r₂' ≫ R₂.map (R₁.map y) = r₃) {bc₃ : A ⟶ R₂.obj (R₁.obj E₃)}
    (hb₃ : bc₃ = r₃ ≫ R₂.map (R₁.map z)) :
    i ≫ L.map bc₁ ≫ bc₂ ≫ R₂.map (R₁.map x) = bc₃ := by
  subst hb₁ hb₂ hb₃ ha
  rw [L.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  simp only [← R₂.map_comp, ← R₁.map_comp, hh]

/-- **Isomorphisms induced by invertible transitive maps are natural.** If `t₃` is `i⁻¹`, then
`L(t₁)`, then `t₂` (all invertible), `φ₁ = t₁⁻¹ ≫ L₁(e)` and `φ₃ = t₃⁻¹ ≫ L₃(e)`, then
`t₂ ≫ φ₃ = L(φ₁) ≫ i`, as soon as `i` is natural. -/
theorem comp_inv_naturality {C C' D : Type*} [Category* C] [Category* C'] [Category* D]
    (L : C' ⥤ D) (L₁ : C ⥤ C') (L₃ : C ⥤ D) (c : L₁ ⋙ L ≅ L₃) {K M : C} (e : K ≅ M) {P : C'}
    {Q : D}
    (t₁ : L₁.obj K ⟶ P) [IsIso t₁] (t₂ : L.obj P ⟶ Q) (t₃ : L₃.obj K ⟶ Q) [IsIso t₃]
    (ht : c.inv.app K ≫ L.map t₁ ≫ t₂ = t₃) :
    t₂ ≫ inv t₃ ≫ L₃.map e.hom = L.map (inv t₁ ≫ L₁.map e.hom) ≫ c.hom.app M := by
  have : IsIso (L.map t₁ ≫ t₂) := by
    have : IsIso (c.inv.app K ≫ L.map t₁ ≫ t₂) := ht ▸ inferInstance
    exact IsIso.of_isIso_comp_left (c.inv.app K) _
  have : IsIso t₂ := IsIso.of_isIso_comp_left (L.map t₁) t₂
  subst ht
  have hn := c.hom.naturality e.hom
  simp only [Functor.comp_map] at hn
  simp only [IsIso.inv_comp, Functor.map_comp, Functor.map_inv, Category.assoc,
    IsIso.hom_inv_id_assoc]
  simp only [← Category.assoc]
  rw [IsIso.inv_eq_of_hom_inv_id (c.inv_hom_id_app K), Category.assoc, Category.assoc, hn]

/-- A map factoring as `r ≫ R(u)`, followed by `R(v)`, is `r ≫ R(u ≫ v)`. -/
theorem comp_map_eq_of_eq {C D : Type*} [Category* C] [Category* D] (R : C ⥤ D) {A : D}
    {E₀ E₁ E₂ : C} {bc : A ⟶ R.obj E₁} {r : A ⟶ R.obj E₀} {u : E₀ ⟶ E₁} (hb : bc = r ≫ R.map u)
    (v : E₁ ⟶ E₂) : bc ≫ R.map v = r ≫ R.map (u ≫ v) := by
  rw [hb, Category.assoc, R.map_comp]

end Stacks.CategoryTheory.BaseChange

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section ComparisonComp

variable {X X' X'' : AlgebraicSpaces B S hS}

/-- **The comparisons of derived with degreewise pullbacks compose**: along `h ≫ g`, the
comparison is `Lh^*` of the one along `g` followed by the one along `h`, through the composition
laws of derived and of degreewise pullbacks. -/
theorem smallEtaleDerivedPullbackQComparison_comp (h : X'' ⟶ X') (g : X' ⟶ X)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (smallEtaleDerivedModulePullback B S hS h).map (smallEtaleDerivedPullbackQComparison g G) ≫
        smallEtaleDerivedPullbackQComparison h
          (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
            (smallEtaleRingedToposHom B S hS g).toModulesHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj G) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (smallEtaleModulePullbackCompIso B S hS h g) (ComplexShape.up ℤ)).hom.app G) =
      (smallEtaleDerivedModulePullbackCompIso B S hS h g).hom.app (DerivedCategory.Q.obj G) ≫
        smallEtaleDerivedPullbackQComparison (h ≫ g) G := by
  have hc := smallEtaleDerivedModulePullbackCompIso_hom_app_comparison B S hS h g
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj G)
  rw [smallEtaleUnderivedPullbackCompIso_eq] at hc
  have hq : DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
      (smallEtaleModulePullbackCompIso B S hS h g) (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj G)) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app _ =
      (DerivedCategory.quotientCompQhIso _).hom.app _ ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (smallEtaleModulePullbackCompIso B S hS h g) (ComplexShape.up ℤ)).hom.app G) :=
    DerivedCategory.quotientCompQhIso_hom_naturality _
  exact Stacks.CategoryTheory.BaseChange.comparison_comp_assemble
    (smallEtaleDerivedModulePullback B S hS h)
    ((smallEtaleDerivedModulePullback B S hS g).map
      ((DerivedCategory.quotientCompQhIso _).inv.app G))
    ((smallEtaleDerivedModulePullbackComparison B S hS g).app
      ((HomotopyCategory.quotient _ _).obj G))
    ((DerivedCategory.quotientCompQhIso _).app _)
    _ _ _ _ _ _ _ _ _
    ((smallEtaleDerivedModulePullbackCompIso B S hS h g).hom.naturality
      ((DerivedCategory.quotientCompQhIso _).inv.app G)) hc hq

end ComparisonComp


section Bridge

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X)

/-- The composite of Stacks 0DKH attached to `φ`, followed by `Rf'_*ψ`, is the one attached to
`φ ≫ ψ`. -/
theorem smallEtaleDerivedBaseChangeComp_comp (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    {K₁ K₂ : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))}
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K₁) (ψ : K₁ ⟶ K₂) :
    smallEtaleDerivedBaseChangeComp B S hS f g f' g' w K K₁ φ ≫
        (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f')).map ψ =
      smallEtaleDerivedBaseChangeComp B S hS f g f' g' w K K₂ (φ ≫ ψ) := by
  unfold smallEtaleDerivedBaseChangeComp
  rw [Functor.map_comp, Category.assoc]

/-- The composite of Stacks 0DKH attached to `φ` is invertible when the one attached to `φ ≫ ψ`
is, for `ψ` invertible. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_of_comp (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    {K₁ K₂ : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))}
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K₁) (ψ : K₁ ⟶ K₂) (hψ : IsIso ψ)
    (h : IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w K K₂ (φ ≫ ψ))) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w K K₁ φ) := by
  rw [← smallEtaleDerivedBaseChangeComp_comp] at h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
    (Functor.map_isIso (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f')) ψ) h

/-- **The two comparisons of derived with degreewise pullbacks give the same composite of
Stacks 0DKH, up to isomorphism**: the composite attached to
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackQComparison` is invertible as soon as the one
attached to `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackQComparison` is. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_pullbackQComparison (w : g' ≫ f = f' ≫ g)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (h : IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w (DerivedCategory.Q.obj G) _
      (smallEtaleDerivedModulePullbackQComparison g' G))) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w (DerivedCategory.Q.obj G) _
      (smallEtaleDerivedPullbackQComparison g' G)) := by
  unfold smallEtaleDerivedModulePullbackQComparison at h
  exact isIso_smallEtaleDerivedBaseChangeComp_of_comp B S hS f g f' g' w _ _ _
    (@Functor.map_isIso _ _ _ _ _ _ DerivedCategory.Q _ (NatIso.hom_app_isIso _ _)) h

end Bridge

section PullbackMap

variable {U U' U'' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')] (g : U' ⟶ U) (g₂ : U'' ⟶ U')
  {X X' X'' : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)
  (f'' : X'' ⟶ ⟨yoneda.obj U'', isAlgebraicSpace_yoneda B S hS U''⟩) (g' : X' ⟶ X)
  (g₂' : X'' ⟶ X') (w : g' ≫ f = f' ≫ representedSpaceMap B S hS g)
  (w₂ : g₂' ≫ f' = f'' ≫ representedSpaceMap B S hS g₂)
  (w₃ : (g₂' ≫ g') ≫ f = f'' ≫ representedSpaceMap B S hS (g₂ ≫ g))

/-- **The pullback map on cohomology over an affine base**,
`RΓ(X, 𝒢^•) ⊗ᴸ_R R' ⟶ RΓ(X', (g')^*𝒢^•)` in `D(R')`, with `RΓ(X, -) = RΓ(U, Rf_* -)`: the base
change map of `RΓ` followed by `RΓ(X', -)` of the comparison `L(g')^*𝒢^• ⟶ (g')^*𝒢^•`. -/
def affineBaseDerivedSectionsPullbackMap
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (representedAffineDerivedExtension B S hS g).functor.obj
        ((representedAffineDerivedSections B S hS U).obj
          ((derivedModulePushforward B S hS f).obj (DerivedCategory.Q.obj G))) ⟶
      (representedAffineDerivedSections B S hS U').obj
        ((derivedModulePushforward B S hS f').obj (DerivedCategory.Q.obj
          (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
            (smallEtaleRingedToposHom B S hS g').toModulesHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj G))) :=
  affineBaseDerivedSectionsBaseChangeMap B S hS g f f' g' w (DerivedCategory.Q.obj G) ≫
    (representedAffineDerivedSections B S hS U').map ((derivedModulePushforward B S hS f').map
      (smallEtaleDerivedPullbackQComparison g' G))

/-- **Transitivity of the pullback maps on cohomology over an affine base**: for two stacked
squares, `- ⊗ᴸ_{R'} R''` of the pullback map of the right square followed by the one of the left
square is the one of the outer rectangle, through the composition laws of derived extensions of
scalars and of pullbacks of modules. -/
theorem affineBaseDerivedSectionsPullbackMap_comp
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
        (representedAffineCommRingCatHom B S hS g).hom
        (representedAffineCommRingCatHom B S hS g₂).hom
        (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
        (representedAffineRingHom_comp B S hS g₂ g).symm).inv.app
        ((representedAffineDerivedSections B S hS U).obj
          ((derivedModulePushforward B S hS f).obj (DerivedCategory.Q.obj G))) ≫
      (representedAffineDerivedExtension B S hS g₂).functor.map
        (affineBaseDerivedSectionsPullbackMap B S hS g f f' g' w G) ≫
      affineBaseDerivedSectionsPullbackMap B S hS g₂ f' f'' g₂' w₂
        (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS g').toModulesHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G) ≫
      (representedAffineDerivedSections B S hS U'').map ((derivedModulePushforward B S hS f'').map
        (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (smallEtaleModulePullbackCompIso B S hS g₂' g') (ComplexShape.up ℤ)).hom.app G))) =
    affineBaseDerivedSectionsPullbackMap B S hS (g₂ ≫ g) f f'' (g₂' ≫ g') w₃ G :=
  Stacks.CategoryTheory.BaseChange.comp_assemble₁ _ (derivedModulePushforward B S hS f'')
    (representedAffineDerivedSections B S hS U'') _ rfl rfl _
    (Stacks.CategoryTheory.BaseChange.map_naturality
      (affineBaseDerivedSectionsAdjunction B S hS f')
      (affineBaseDerivedSectionsAdjunction B S hS f'')
      (affineBaseDerivedSectionsSquareIso B S hS g₂ f' f'' g₂' w₂) (Iso.refl _)
      (smallEtaleDerivedPullbackQComparison g' G))
    (smallEtaleDerivedPullbackQComparison_comp B S hS g₂' g' G)
    (affineBaseDerivedSectionsBaseChangeMap_comp B S hS g g₂ f f' f'' g' g₂' w w₂ w₃ _) rfl

end PullbackMap


section Model

variable {U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  {X : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)

/-- The pullback map is invertible when the base change map of Stacks 07A7 followed by the
comparison `L(g')^*𝒢^• ⟶ (g')^*𝒢^•` is, as soon as `Rf_*𝒢^•` lies in `D_QCoh`. -/
theorem isIso_affineBaseDerivedSectionsPullbackMap {U' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g : U' ⟶ U) {X' : AlgebraicSpaces B S hS}
    (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) (g' : X' ⟶ X)
    (w : g' ≫ f = f' ≫ representedSpaceMap B S hS g)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hG : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
      ((derivedModulePushforward B S hS f).obj (DerivedCategory.Q.obj G)))
    (h : IsIso (smallEtaleDerivedBaseChangeComp B S hS f (representedSpaceMap B S hS g) f' g' w
      (DerivedCategory.Q.obj G) _ (smallEtaleDerivedPullbackQComparison g' G))) :
    IsIso (affineBaseDerivedSectionsPullbackMap B S hS g f f' g' w G) := by
  have h₁ := isIso_representedAffineDerivedSectionsBaseChangeMap B S hS g _ hG
  refine (congrArg IsIso (Stacks.CategoryTheory.BaseChange.comp_map_eq_of_eq
    (representedAffineDerivedSections B S hS U')
    (affineBaseDerivedSectionsBaseChangeMap_eq B S hS g f f' g' w _)
    ((derivedModulePushforward B S hS f').map
      (smallEtaleDerivedPullbackQComparison g' G)))).mpr ?_
  exact IsIso.comp_isIso' h₁ (@Functor.map_isIso _ _ _ _ _ _ _ _ h)

/-- **Isomorphisms induced by invertible pullback maps are functorial.**  If
`e : RΓ(X, 𝒢^•) ≅ M^•` in `D(R)` and the pullback maps of the right square and of the outer
rectangle are invertible, then the isomorphisms
`RΓ(X', (g')^*𝒢^•) ≅ M^• ⊗ᴸ_R R'` they induce are compatible with the pullback maps of stacked
squares and the composition law of derived extensions of scalars. -/
theorem affineBaseDerivedSectionsPullbackMap_inv_naturality
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    {M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))}
    (e : (representedAffineDerivedSections B S hS U).obj
      ((derivedModulePushforward B S hS f).obj (DerivedCategory.Q.obj G)) ≅ M)
    {U' U'' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')] (g : U' ⟶ U) (g₂ : U'' ⟶ U')
    {X' X'' : AlgebraicSpaces B S hS} (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)
    (f'' : X'' ⟶ ⟨yoneda.obj U'', isAlgebraicSpace_yoneda B S hS U''⟩) (g' : X' ⟶ X)
    (g₂' : X'' ⟶ X') (w : g' ≫ f = f' ≫ representedSpaceMap B S hS g)
    (w₂ : g₂' ≫ f' = f'' ≫ representedSpaceMap B S hS g₂)
    (w₃ : (g₂' ≫ g') ≫ f = f'' ≫ representedSpaceMap B S hS (g₂ ≫ g))
    [h₁ : IsIso (affineBaseDerivedSectionsPullbackMap B S hS g f f' g' w G)]
    [h₃ : IsIso (affineBaseDerivedSectionsPullbackMap B S hS (g₂ ≫ g) f f'' (g₂' ≫ g') w₃ G)] :
    affineBaseDerivedSectionsPullbackMap B S hS g₂ f' f'' g₂' w₂
      (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS g').toModulesHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G) ≫
        (representedAffineDerivedSections B S hS U'').map ((derivedModulePushforward B S hS f'').map
          (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (smallEtaleModulePullbackCompIso B S hS g₂' g') (ComplexShape.up ℤ)).hom.app G))) ≫
        inv (affineBaseDerivedSectionsPullbackMap B S hS (g₂ ≫ g) f f'' (g₂' ≫ g') w₃ G) ≫
        (representedAffineDerivedExtension B S hS (g₂ ≫ g)).functor.map e.hom =
      (representedAffineDerivedExtension B S hS g₂).functor.map
          (inv (affineBaseDerivedSectionsPullbackMap B S hS g f f' g' w G) ≫
            (representedAffineDerivedExtension B S hS g).functor.map e.hom) ≫
        (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
          (representedAffineCommRingCatHom B S hS g).hom
          (representedAffineCommRingCatHom B S hS g₂).hom
          (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
          (representedAffineRingHom_comp B S hS g₂ g).symm).hom.app M := by
  simpa only [Category.assoc] using Stacks.CategoryTheory.BaseChange.comp_inv_naturality
    (representedAffineDerivedExtension B S hS g₂).functor
    (representedAffineDerivedExtension B S hS g).functor
    (representedAffineDerivedExtension B S hS (g₂ ≫ g)).functor
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
      (representedAffineCommRingCatHom B S hS g).hom (representedAffineCommRingCatHom B S hS g₂).hom
      (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
      (representedAffineRingHom_comp B S hS g₂ g).symm) e
    (affineBaseDerivedSectionsPullbackMap B S hS g f f' g' w G) _ _
    (affineBaseDerivedSectionsPullbackMap_comp B S hS g g₂ f f' f'' g' g₂' w w₂ w₃ G)

end Model


section FiniteProjectiveModel

/-- **Stacks 0A1Q, from Stacks 0A1P and 0A1K.**  Let `U` have affine underlying scheme `Spec R`,
`f : X ⟶ U` of finite presentation and `𝒢` an `𝒪_X`-module of finite presentation, flat over `U`,
with support proper over `U`. If the perfectness part of Stacks 0A1P holds and the base change
map of Stacks 0A1K for `f` and `𝒢` is invertible for every cartesian square over an affine
`U' ⟶ U`, then there is a bounded complex `M^•` of finite projective `R`-modules (so that
`M^• ⊗ᴸ_R R' = M^• ⊗_R R'`) and isomorphisms `RΓ(X_{R'}, 𝒢_{R'}) ≅ M^• ⊗ᴸ_R R'`, functorial in the
`R`-algebra `R' = Γ(U', 𝒪)`: compatible with the pullback maps and the composition law of
derived extensions of scalars. -/
theorem exists_finiteProjective_model_derivedSections_of_perfectness
    (h0A1P : ∀ {X' Y' : AlgebraicSpaces B S hS} (f' : X' ⟶ Y')
      (hf' : IsFinitePresentation B S hS f'.hom)
      (E' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))),
      RingedSite.IsPerfect (smallEtaleRingedSite B S hS X'.1 X'.2) E' →
      ∀ G' : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')) ℤ,
      {i : ℤ | ¬ IsZero (G'.X i)}.Finite → (∀ n, (G'.X n).IsFinitePresentation) →
      (∀ n, IsFlatOver B S hS X'.2 f'.hom (G'.X n)) →
      (∀ n, HasProperSupport B S hS X'.2 Y'.2 f'.hom
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf'.1)
        ((SheafOfModules.toSheaf _).obj (G'.X n))) →
      RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y'.1 Y'.2)
        ((derivedModulePushforward B S hS f').obj
          (((smallEtaleDerivedTensor B S hS X').obj E').obj (DerivedCategory.Q.obj G'))))
    {U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (hf : IsFinitePresentation B S hS f.hom)
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hGfp : G.IsFinitePresentation) (hGflat : IsFlatOver B S hS X.2 f.hom G)
    (hGsupp : HasProperSupport B S hS X.2 (isAlgebraicSpace_yoneda B S hS U) f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1)
      ((SheafOfModules.toSheaf _).obj G))
    (h0A1K : ∀ {U' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
      (g : U' ⟶ U) {X' : AlgebraicSpaces B S hS}
      (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) (g' : X' ⟶ X)
      (sq : IsPullback g' f' f (representedSpaceMap B S hS g)),
      IsIso (smallEtaleDerivedBaseChangeComp B S hS f (representedSpaceMap B S hS g) f' g' sq.w
        (DerivedCategory.Q.obj ((HomologicalComplex.single
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
          (ComplexShape.up ℤ) 0).obj G)) _
        (smallEtaleDerivedModulePullbackQComparison g' ((HomologicalComplex.single
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
          (ComplexShape.up ℤ) 0).obj G)))) :
    ∃ (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) (a b : ℤ),
      M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧
      (∀ i, Module.Finite Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (M.X i)) ∧
      (∀ i, Module.Projective Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (M.X i)) ∧
      (∀ {U' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
        (g : U' ⟶ U), IsIso ((representedAffineDerivedExtension B S hS g).comparison.app M)) ∧
      ∃ φ : ∀ {U' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
          (g : U' ⟶ U) {X' : AlgebraicSpaces B S hS}
          (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) (g' : X' ⟶ X),
          IsPullback g' f' f (representedSpaceMap B S hS g) →
          ((representedAffineDerivedSections B S hS U').obj
            ((derivedModulePushforward B S hS f').obj (DerivedCategory.Q.obj
              (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS X)
                (smallEtaleRingedToposHom B S hS g').toModulesHom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj ((HomologicalComplex.single
                  (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
                  (ComplexShape.up ℤ) 0).obj G)))) ≅
            (representedAffineDerivedExtension B S hS g).functor.obj (DerivedCategory.Q.obj M)),
        ∀ {U' U'' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
          [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')] (g : U' ⟶ U) (g₂ : U'' ⟶ U')
          {X' X'' : AlgebraicSpaces B S hS}
          (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)
          (f'' : X'' ⟶ ⟨yoneda.obj U'', isAlgebraicSpace_yoneda B S hS U''⟩) (g' : X' ⟶ X)
          (g₂' : X'' ⟶ X') (sq : IsPullback g' f' f (representedSpaceMap B S hS g))
          (sq₂ : IsPullback g₂' f'' f' (representedSpaceMap B S hS g₂))
          (sq₃ : IsPullback (g₂' ≫ g') f'' f (representedSpaceMap B S hS (g₂ ≫ g))),
          affineBaseDerivedSectionsPullbackMap B S hS g₂ f' f'' g₂' sq₂.w
              (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS X)
                (smallEtaleRingedToposHom B S hS g').toModulesHom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj ((HomologicalComplex.single
                  (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
                  (ComplexShape.up ℤ) 0).obj G)) ≫
            (representedAffineDerivedSections B S hS U'').map
              ((derivedModulePushforward B S hS f'').map (DerivedCategory.Q.map
                ((NatIso.mapHomologicalComplex (smallEtaleModulePullbackCompIso B S hS g₂' g')
                  (ComplexShape.up ℤ)).hom.app ((HomologicalComplex.single
                    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
                    (ComplexShape.up ℤ) 0).obj G)))) ≫
            (φ (g₂ ≫ g) f'' (g₂' ≫ g') sq₃).hom =
          (representedAffineDerivedExtension B S hS g₂).functor.map (φ g f' g' sq).hom ≫
            (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
              (representedAffineCommRingCatHom B S hS g).hom
              (representedAffineCommRingCatHom B S hS g₂).hom
              (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
              (representedAffineRingHom_comp B S hS g₂ g).symm).hom.app
                (DerivedCategory.Q.obj M) := by
  have hG0 : ∀ n, n ≠ 0 → IsZero (((HomologicalComplex.single
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (ComplexShape.up ℤ) 0).obj G).X n) := fun n hn =>
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
  have hft := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1
  -- the perfectness of `Rf_*𝒢` (Stacks 0A1P at `E = 𝒪_X`)
  have hperf : RingedSite.IsPerfect (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
      ((derivedModulePushforward B S hS f).obj (DerivedCategory.Q.obj ((HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
        (ComplexShape.up ℤ) 0).obj G))) := by
    have h := h0A1P f hf _ (isPerfect_unit X) ((HomologicalComplex.single
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ) 0).obj G)
      ((Set.finite_singleton (0 : ℤ)).subset fun i hi => by
        by_contra h'
        exact hi (hG0 i h'))
      (fun n => by
        by_cases hn : n = 0
        · subst hn
          exact (SheafOfModules.isFinitePresentation _).prop_of_iso
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).symm hGfp
        · exact isFinitePresentation_of_isZero B S hS (hG0 n hn))
      (fun n => by
        by_cases hn : n = 0
        · subst hn
          exact IsFlatOver.of_iso B S hS _
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).symm hGflat
        · exact isFlatOver_of_isZero B S hS _ (hG0 n hn))
      (fun n => by
        by_cases hn : n = 0
        · subst hn
          exact hasProperSupport_of_iso (isAlgebraicSpace_yoneda B S hS U) _ _
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).symm hGsupp
        · exact hasProperSupport_of_isZero B S hS _ _ _ _ (hG0 n hn))
    let T := smallEtaleDerivedTensorProduct B S hS X
    let e₀ := (smallEtaleDerivedTensor B S hS X).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app
          (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))) ≪≫
      T.leftSingleUnitNatIso 0 ≪≫ shiftFunctorZero' _ (-0 : ℤ) (by simp)
    exact RingedSite.IsPerfect.of_iso _ h
      ((derivedModulePushforward B S hS f).mapIso (e₀.app (DerivedCategory.Q.obj
        ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
          (ComplexShape.up ℤ) 0).obj G))))
  have hQ := qcohDerived_of_isPerfect_derivedCategoryB
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ _ hperf
  have hP : StacksDraft.Perfect.IsPerfect ((representedAffineDerivedSections B S hS U).obj
      ((derivedModulePushforward B S hS f).obj (DerivedCategory.Q.obj ((HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
        (ComplexShape.up ℤ) 0).obj G)))) :=
    isPerfect_representedAffineDerivedSections_obj B S hS U _ hperf
  unfold StacksDraft.Perfect.IsPerfect at hP
  obtain ⟨P, a, b, hPa, hPb, hfin, hproj, ⟨e⟩⟩ := hP
  have hiso : ∀ {U' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
      (g : U' ⟶ U) {X' : AlgebraicSpaces B S hS}
      (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) (g' : X' ⟶ X)
      (sq : IsPullback g' f' f (representedSpaceMap B S hS g)),
      IsIso (affineBaseDerivedSectionsPullbackMap B S hS g f f' g' sq.w ((HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
        (ComplexShape.up ℤ) 0).obj G)) :=
    fun g _ f' g' sq => isIso_affineBaseDerivedSectionsPullbackMap B S hS f g f' g' sq.w _ hQ
      (isIso_smallEtaleDerivedBaseChangeComp_pullbackQComparison B S hS f _ f' g' sq.w _
        (h0A1K g f' g' sq))
  refine ⟨P, a, b, hPa, hPb, hfin, hproj, ?_,
    @fun U' _ g X' f' g' sq => (@asIso _ _ _ _ _ (hiso g f' g' sq)).symm ≪≫
      (representedAffineDerivedExtension B S hS g).functor.mapIso e, ?_⟩
  · intro U' _ g
    have : ∀ i, Projective (P.X i) := fun i => (IsProjective.iff_projective _).1 (hproj i)
    exact (representedAffineDerivedExtension B S hS g).comparison_isIso_of_projective P b
  · intro U' U'' _ _ g g₂ X' X'' f' f'' g' g₂' sq sq₂ sq₃
    have key := affineBaseDerivedSectionsPullbackMap_inv_naturality (h₁ := hiso g f' g' sq)
      (h₃ := hiso (g₂ ≫ g) f'' (g₂' ≫ g') sq₃) B S hS f ((HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
        (ComplexShape.up ℤ) 0).obj G) e g g₂ f' f'' g' g₂'
      sq.w sq₂.w sq₃.w
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom]
    convert key using 2

end FiniteProjectiveModel

end AlgebraicGeometry.Space

end
