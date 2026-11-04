module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentDerivedSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentDerivedSquareComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.FlatPullback

/-!
# `Lε^*` of the derived associated module on an affine representable algebraic space

Let `U` be an object of the big fppf site over `S` whose underlying scheme `X_0` is affine, with
ring of global functions `A`, and let `ε : (X_étale, 𝒪_X) ⟶ (X_{0,Zar}, 𝒪_{X_0})` be the comparison
morphism for the algebraic space `X = yoneda.obj U`. For `M ∈ D(A)`, the derived associated module
`M^~` on `Spec A`, pulled back to `X_0` along `X_0 ≅ Spec A` and then along `ε`, is the derived
associated module `Φ(M)` on the small étale site of `X`:

`Lε^* (L(X_0 ≅ Spec A)^* M^~) ≅ Φ(M)`.

All functors involved are induced by exact functors, so this is the isomorphism induced by the
degreewise one, `ε^*(M^~|_{X_0}) ≅ Φ(M)`, which is
`representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction`.

## Main definitions

* `AlgebraicGeometry.Space.representedAffineZariskiAssociatedIso`

## Main results

* `AlgebraicGeometry.Space.representedAffineZariskiAssociatedIso_hom_app`: the isomorphism on
  complexes.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open AlgebraicGeometry.RingedToposHom

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace CategoryTheory.Functor

variable {V W W' : Type*} [Category* V] [Category* W] [Category* W'] {_ : Preadditive V}
  {_ : Preadditive W} {_ : Preadditive W'}

/-- An isomorphism `F ⋙ G ≅ H` of additive functors, read on complexes: degreewise `F`, then
`G` on homotopy categories, is degreewise `H`. -/
def mapHomotopyCategoryCompFactorsIso (F : V ⥤ W) (G : W ⥤ W') (H : V ⥤ W') {_ : F.Additive}
    {_ : G.Additive} {_ : H.Additive} (ρ : F ⋙ G ≅ H) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _ ⋙
        G.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _ :=
  Functor.isoWhiskerLeft _ (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso ρ (ComplexShape.up ℤ)) _

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- Pullback of modules along `X_0 ≅ Spec A` preserves finite limits. -/
instance preservesFiniteLimits_pullback_isoSpec_hom :
    PreservesFiniteLimits (Scheme.Modules.pullback
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom) :=
  pullback_preservesFiniteLimits_of_isOpenImmersion _

/-- Pullback of modules along `X_0 ≅ Spec A` preserves finite colimits. -/
instance preservesFiniteColimits_pullback_isoSpec_hom :
    PreservesFiniteColimits (Scheme.Modules.pullback
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom) :=
  preservesFiniteColimits_modulesPullback _

/-- The degreewise isomorphism `ε^*(M^~|_{X_0}) ≅ Φ(M)`. -/
def representedAffineZariskiAssociatedModuleIso :
    tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⋙
        Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom ⋙
        representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U ≅
      representedAffineToposAssociated B S hS U :=
  Functor.isoWhiskerLeft _
    (Functor.isoWhiskerLeft _
      (representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
        B S hS U))

/-- The composite `D(A) ⥤ D(𝒪_X)`: the derived associated module on `Spec A`, its pullback to
`X_0`, and its pullback along `ε`, all through the comparison of models. -/
abbrev representedAffineZariskiAssociated :=
  (Stacks.Injectives.grothendieckModelEquiv.{u}
      (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))).functor ⋙
    (tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).mapDerivedCategory ⋙
    Stacks.Duality.derivedPullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom ⋙
    (StacksDraft.DerivedModel.schemeModulesComparison
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U)).inverse ⋙
    representedZariskiDerivedPullback B S hS U

section Chase

variable {D₁ D₂ E' : Type*} [Category D₁] [Category D₂] [Category E']

private theorem chase_square_four {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : D₁} (z : X₀ ⟶ X₁) (zf : X₀ ⟶ Y₀)
    (zf' : X₁ ⟶ Y₁) (t : Y₀ ⟶ Y₁) (qi : Y₀ ⟶ Z₀) (qi' : Y₁ ⟶ Z₁) (x : Z₀ ⟶ Z₁)
    (h₁ : z ≫ zf' = zf ≫ t) (h₂ : t ≫ qi' = qi ≫ x) : z ≫ zf' ≫ qi' = (zf ≫ qi) ≫ x := by
  rw [reassoc_of% h₁, h₂, Category.assoc]

private theorem chase_functor_three (F : D₁ ⥤ D₂) {A₀ A₁ B B' : D₁} {M M' N N' : D₂}
    (z : A₀ ⟶ A₁) (f : A₀ ⟶ B) (f' : A₁ ⟶ B') (x : B ⟶ B') (l : F.obj B ⟶ M) (l' : F.obj B' ⟶ M')
    (y : M ⟶ M') (s : M ⟶ N) (s' : M' ⟶ N') (w : N ⟶ N') (hf : z ≫ f' = f ≫ x)
    (hl : F.map x ≫ l' = l ≫ y) (hs : y ≫ s' = s ≫ w) :
    F.map z ≫ F.map f' ≫ l' ≫ s' = (F.map f ≫ l ≫ s) ≫ w := by
  rw [← Functor.map_comp_assoc, hf, Functor.map_comp_assoc, reassoc_of% hl, hs]
  simp

private theorem chase_unit (Ci : D₁ ⥤ D₂) (Cf : D₂ ⥤ D₁) (un : 𝟭 D₂ ≅ Cf ⋙ Ci) (Le : D₂ ⥤ E')
    {X X' : D₁} {Y Y' : D₂} {Z Z' : E'} (a : X ⟶ X') (ω : X ⟶ Cf.obj Y) (ω' : X' ⟶ Cf.obj Y')
    (b : Y ⟶ Y') (ℓ : Le.obj Y ⟶ Z) (ℓ' : Le.obj Y' ⟶ Z') (d : Z ⟶ Z')
    (hω : a ≫ ω' = ω ≫ Cf.map b) (hℓ : Le.map b ≫ ℓ' = ℓ ≫ d) :
    Le.map (Ci.map a) ≫ (Le.map (Ci.map ω' ≫ un.inv.app Y') ≫ ℓ') =
      (Le.map (Ci.map ω ≫ un.inv.app Y) ≫ ℓ) ≫ d := by
  have hu := un.inv.naturality b
  simp only [Functor.comp_map, Functor.id_map] at hu
  rw [← Functor.map_comp_assoc, ← Category.assoc, ← Ci.map_comp, hω, Ci.map_comp, Category.assoc,
    hu, ← Category.assoc, Functor.map_comp_assoc, hℓ, Category.assoc]

end Chase

/-- The derived pullback along `X_0 ≅ Spec A` is computed by degreewise pullback. -/
instance isIso_derivedPullbackComparison_isoSpec_hom :
    IsIso (Stacks.Duality.derivedPullbackComparison
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom) :=
  haveI : (Stacks.Duality.derivedPullback
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).IsLeftDerivedFunctor
      (Stacks.Duality.derivedPullbackComparison ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom)
      (HomotopyCategory.quasiIso (Spec Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).Modules
        Stacks.DerivedFunctor.HigherDerivedOfExact.shape) :=
    inferInstanceAs ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom.toLRSHom.toShHom).IsLeftDerivedFunctor
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison _)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing
        (Spec Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).toRingedSpace)) (ComplexShape.up ℤ)))
  Functor.isIso_of_isLeftDerivedFunctor_of_inverts _ _
    (Stacks.DerivedFunctor.HigherDerivedOfExact.mapHomotopyCategory_inverts_quasiIso
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom))

/-- `L(X_0 ≅ Spec A)^* M^~ ≅ (M^~|_{X_0})` at the locally small model, for a complex `M` of
`A`-modules, read at the standard model. -/
def representedAffineZariskiPullbackTildeIso
    (P : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (Stacks.Duality.derivedPullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).obj
        ((tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).mapDerivedCategory.obj
          (DerivedCategory.Q.obj P)) ≅
      (StacksDraft.DerivedModel.schemeModulesComparison
        (representedSchemeRepresentedZariskiRingedToposHom B S hS U)).functor.obj
        (@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _) |>.obj
          (((Scheme.Modules.pullback
            ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj
              (((tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)))) :=
  (Stacks.Duality.derivedPullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapIso
      ((tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).mapDerivedCategoryFactors.app P ≪≫
        (DerivedCategory.quotientCompQhIso
          (Spec Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).Modules).symm.app
          _) ≪≫
    asIso ((Stacks.Duality.derivedPullbackComparison
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).app _) ≪≫
    (StacksDraft.DerivedModel.shrinkComparisonQhIso
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules).app _

/-- The forward map of `representedAffineZariskiPullbackTildeIso` is the composite of the
factorization of the derived associated module, the derived pullback comparison and the change
of model. -/
theorem representedAffineZariskiPullbackTildeIso_hom
    (P : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (representedAffineZariskiPullbackTildeIso U P).hom =
      ((Stacks.Duality.derivedPullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).map
          ((tilde.functor
            Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).mapDerivedCategoryFactors.hom.app P ≫
            (DerivedCategory.quotientCompQhIso
              (Spec Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).Modules).inv.app _) ≫
        (Stacks.Duality.derivedPullbackComparison
          ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).app _) ≫
        (StacksDraft.DerivedModel.shrinkComparisonQhIso
          (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules).hom.app _ :=
  (Category.assoc _ _ _).symm

/-- `representedAffineZariskiPullbackTildeIso` is natural in the complex `M`. -/
theorem representedAffineZariskiPullbackTildeIso_naturality
    {P P' : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ}
    (φ : P ⟶ P') :
    (Stacks.Duality.derivedPullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).map
        ((tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).mapDerivedCategory.map
          ((Stacks.Injectives.grothendieckModelEquiv.{u}
            (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))).functor.map
            ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).map φ))) ≫
        (representedAffineZariskiPullbackTildeIso U P').hom =
      (representedAffineZariskiPullbackTildeIso U P).hom ≫
        (StacksDraft.DerivedModel.schemeModulesComparison
          (representedSchemeRepresentedZariskiRingedToposHom B S hS U)).functor.map
          ((@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).map
            (((Scheme.Modules.pullback
              ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapHomotopyCategory
              (ComplexShape.up ℤ)).map ((HomotopyCategory.quotient _ _).map
                (((tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).map φ)))) :=
  chase_functor_three (Stacks.Duality.derivedPullback
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom) _ _ _ _ _ _ _ _ _ _
    (chase_square_four _ _ _ _ _ _ _
      ((tilde.functor
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).mapDerivedCategoryFactors.hom.naturality φ)
      ((DerivedCategory.quotientCompQhIso
        (Spec Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).Modules).inv.naturality _))
    ((Stacks.Duality.derivedPullbackComparison
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).naturality _)
    ((StacksDraft.DerivedModel.shrinkComparisonQhIso
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules).hom.naturality _)

/-- The degreewise isomorphism `ε^*(M^~|_{X_0}) ≅ Φ(M)` on complexes, in the homotopy category. -/
def representedAffineZariskiAssociatedHomotopyIsoh :
    (tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (Scheme.Modules.pullback
          ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _ ⋙
        Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
          (X := smallEtaleRingedTopos B S hS (representedSpace U))
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U) ≅
      representedAffineToposHomotopyAssociated B S hS U :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso
      (Iso.refl (tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⋙
        Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom))
      (ComplexShape.up ℤ)) _ ≪≫
    @Functor.mapHomotopyCategoryCompFactorsIso _ _ _ _ _ _ _ _ _
      (tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⋙
        Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom)
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U)
      (representedAffineToposAssociated B S hS U) inferInstance
      (RingedToposHom.pullbackModules_additive
        (X := smallEtaleRingedTopos B S hS (representedSpace U))
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
        (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U))
      (additive_representedAffineToposAssociated B S hS U)
      (Functor.associator _ _ _ ≪≫ representedAffineZariskiAssociatedModuleIso U)

/-- The degreewise isomorphism `ε^*(M^~|_{X_0}) ≅ Φ(M)` on complexes, read in the homotopy
category and localized. -/
def representedAffineZariskiAssociatedHomotopyIso :
    (tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (Scheme.Modules.pullback
          ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _ ⋙
        Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
          (X := smallEtaleRingedTopos B S hS (representedSpace U))
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U) ⋙
        @DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _) ≅
      representedAffineToposHomotopyAssociated B S hS U ⋙
        @DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _) :=
  Functor.isoWhiskerRight (representedAffineZariskiAssociatedHomotopyIsoh U) _

section

attribute [local instance 10000] HasDerivedCategory.standard

/-- The component at a complex `M` of `representedAffineZariskiAssociatedFactors`. -/
def representedAffineZariskiAssociatedFactorsApp
    (P : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _) ⋙
        representedAffineZariskiAssociated U).obj P ≅
      ((tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (Scheme.Modules.pullback
          ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _ ⋙
        Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
          (X := smallEtaleRingedTopos B S hS (representedSpace U))
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U) ⋙
        @DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).obj P :=
    (representedZariskiDerivedPullback B S hS U).mapIso
      ((StacksDraft.DerivedModel.schemeModulesComparison
        (representedSchemeRepresentedZariskiRingedToposHom B S hS U)).inverse.mapIso
          (representedAffineZariskiPullbackTildeIso U P) ≪≫
        (StacksDraft.DerivedModel.schemeModulesComparison
          (representedSchemeRepresentedZariskiRingedToposHom B S hS U)).unitIso.symm.app _) ≪≫
      (@asIso _ _ _ _ (derivedPullbackComparison
        (X := smallEtaleRingedTopos B S hS (representedSpace U))
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
        (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U))
        (isIso_representedZariskiDerivedPullbackComparison B S hS U)).app
          (((Scheme.Modules.pullback
            ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj
            (((tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)))

/-- `representedAffineZariskiAssociatedFactorsApp` is natural in the complex `M`. -/
theorem representedAffineZariskiAssociatedFactorsApp_naturality
    {P P' : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ}
    (φ : P ⟶ P') :
    (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _) ⋙
        representedAffineZariskiAssociated U).map φ ≫
        (representedAffineZariskiAssociatedFactorsApp U P').hom =
      (representedAffineZariskiAssociatedFactorsApp U P).hom ≫
        ((tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (Scheme.Modules.pullback
          ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _ ⋙
        Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
          (X := smallEtaleRingedTopos B S hS (representedSpace U))
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U) ⋙
        @DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).map φ :=
  chase_unit
      (StacksDraft.DerivedModel.schemeModulesComparison
        (representedSchemeRepresentedZariskiRingedToposHom B S hS U)).inverse
      (StacksDraft.DerivedModel.schemeModulesComparison
        (representedSchemeRepresentedZariskiRingedToposHom B S hS U)).functor
      (StacksDraft.DerivedModel.schemeModulesComparison
        (representedSchemeRepresentedZariskiRingedToposHom B S hS U)).unitIso
      (representedZariskiDerivedPullback B S hS U) _ _ _ _ _ _ _
      (representedAffineZariskiPullbackTildeIso_naturality U φ)
      ((derivedPullbackComparison (X := smallEtaleRingedTopos B S hS (representedSpace U))
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
        (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)).naturality _)

/-- The composite `M ↦ Lε^*(L(X_0 ≅ Spec A)^* M^~)` on a complex `M` of `A`-modules: degreewise
associated module, pullback to `X_0` and pullback along `ε`, read in the homotopy category. -/
def representedAffineZariskiAssociatedFactors :
    @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _) ⋙
        representedAffineZariskiAssociated U ≅
      (tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (Scheme.Modules.pullback
          ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _ ⋙
        Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
          (X := smallEtaleRingedTopos B S hS (representedSpace U))
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U) ⋙
        @DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _) :=
  NatIso.ofComponents (representedAffineZariskiAssociatedFactorsApp U)
    (representedAffineZariskiAssociatedFactorsApp_naturality U)

/-- The component of `representedAffineZariskiAssociatedFactors` at a complex `M`, as the
composite of the change of model, the inverse unit of the model comparison and the derived pullback
comparison along `ε`. -/
theorem representedAffineZariskiAssociatedFactors_hom_app
    (P : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (representedAffineZariskiAssociatedFactors U).hom.app P =
      (representedZariskiDerivedPullback B S hS U).map
          ((StacksDraft.DerivedModel.schemeModulesComparison
            (representedSchemeRepresentedZariskiRingedToposHom B S hS U)).inverse.map
              (representedAffineZariskiPullbackTildeIso U P).hom ≫
            (StacksDraft.DerivedModel.schemeModulesComparison
              (representedSchemeRepresentedZariskiRingedToposHom B S hS U)).unitIso.inv.app _) ≫
        (derivedPullbackComparison (X := smallEtaleRingedTopos B S hS (representedSpace U))
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)).app
          (((Scheme.Modules.pullback
            ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj
            (((tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P))) :=
  rfl

/-- **`Lε^*(L(X_0 ≅ Spec A)^* M^~) ≅ Φ(M)`** for `M ∈ D(A)`: the isomorphism induced by the
degreewise one. -/
def representedAffineZariskiAssociatedIso :
    representedAffineZariskiAssociated U ≅ representedAffineToposDerivedAssociated B S hS U :=
  (Localization.whiskeringLeftFunctor' DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _).preimageIso
    (representedAffineZariskiAssociatedFactors U ≪≫
      representedAffineZariskiAssociatedHomotopyIso U ≪≫
      (representedAffineToposDerivedFactors B S hS U).symm)

/-- **`representedAffineZariskiAssociatedIso` on complexes**: it is the composite of the
comparisons of the derived functors with the degreewise ones and the degreewise isomorphism. -/
theorem representedAffineZariskiAssociatedIso_hom_app
    (P : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (representedAffineZariskiAssociatedIso U).hom.app (DerivedCategory.Q.obj P) ≫
        (representedAffineToposDerivedFactors B S hS U).hom.app P =
      (representedAffineZariskiAssociatedFactors U).hom.app P ≫
        (representedAffineZariskiAssociatedHomotopyIso U).hom.app P := by
  have h : (representedAffineZariskiAssociatedIso U).hom.app (DerivedCategory.Q.obj P) =
      (representedAffineZariskiAssociatedFactors U ≪≫
        representedAffineZariskiAssociatedHomotopyIso U ≪≫
        (representedAffineToposDerivedFactors B S hS U).symm).hom.app P :=
    NatTrans.congr_app ((Localization.whiskeringLeftFunctor' DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _).map_preimage
      (representedAffineZariskiAssociatedFactors U ≪≫
        representedAffineZariskiAssociatedHomotopyIso U ≪≫
        (representedAffineToposDerivedFactors B S hS U).symm).hom) P
  rw [h]
  simp

end

end AlgebraicGeometry.Space
