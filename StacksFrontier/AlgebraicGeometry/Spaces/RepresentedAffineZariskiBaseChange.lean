module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineZariskiPathComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineZariskiAssociated
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentDerivedSquareComparison
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsModel
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# The base change of the derived associated module along a morphism of affine representables

For a morphism `g : U' ⟶ U` of objects of the big fppf site over `S` with affine underlying
schemes, there are two ways to pass from `Lε_U^*(M^~)` (`M ∈ D(Γ(U))`) to the derived associated
module of `M ⊗ᴸ Γ(U')` on `U'`: through `Φ` and the affine base change isomorphism of
`AlgebraicGeometry.Space.representedAffineToposDerivedBaseChangeIso`, or through Stacks 08GH and
the affine comparison square of Stacks 08DW. This file computes both paths on complexes.

## Main results

* `AlgebraicGeometry.Space.isoSpec_hom_square`: `X'_0 ⟶ X_0 ⟶ Spec Γ(U)` is
  `X'_0 ⟶ Spec Γ(U') ⟶ Spec Γ(U)`.
* `AlgebraicGeometry.Space.representedAffineZariskiAssociated_pathβ`: the path through `Φ`, on
  complexes.
* `AlgebraicGeometry.Space.representedAffineZariskiAssociated_pathZ`: the path through Stacks 08GH
  and Stacks 08DW, on complexes.
* `AlgebraicGeometry.Space.representedAffineZariskiAssociated_pathβ_comparison`: the path through
  `Φ` in the same form.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {U' U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  (g : U' ⟶ U)

/-- The square `X'_0 ⟶ X_0 ⟶ Spec Γ(U) = X'_0 ⟶ Spec Γ(U') ⟶ Spec Γ(U)` of the canonical maps to
the spectra of the rings of global functions. -/
theorem isoSpec_hom_square :
    (B.inclusion.map g.left) ≫ ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom =
      ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom ≫
        Spec.map (representedAffineCommRingCatHom B S hS g) :=
  (Scheme.isoSpec_hom_naturality ((BigFppfOver.toScheme B S hS).map g)).symm

section

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] additive_extendScalars_representedAffineRingHom

/-- **The path through `Φ`, on complexes.** `Lf^*` of the isomorphism
`representedAffineZariskiAssociatedIso`, then the affine base change isomorphism, then `Φ` of the
comparison of derived extension of scalars, is the degreewise composite. -/
theorem representedAffineZariskiAssociated_pathβ
    (P : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    letI := pullbackModules_smallEtale_additive (representedSpaceMap B S hS g)
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
        ((representedAffineZariskiAssociatedIso U).hom.app (DerivedCategory.Q.obj P)) ≫
      (representedAffineToposDerivedBaseChangeIso B S hS g).hom.app (DerivedCategory.Q.obj P) ≫
      (representedAffineToposDerivedAssociated B S hS U').map
        ((representedAffineDerivedExtension B S hS g).comparison.app P) =
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
        ((representedAffineZariskiAssociatedFactors U).hom.app P ≫
          (representedAffineZariskiAssociatedHomotopyIso U).hom.app P) ≫
      (smallEtaleDerivedModulePullbackComparison B S hS (representedSpaceMap B S hS g)).app
        ((representedAffineToposHomotopyAssociated B S hS U).obj P) ≫
      DerivedCategory.Qh.map ((Stacks.Homology.homotopyEdgeIso
        (representedAffineToposPullbackIso B S hS g)).hom.app P) ≫
      (representedAffineToposDerivedFactors B S hS U').inv.app
        (((ModuleCat.extendScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) := by
  have hβ := representedAffineToposDerivedBaseChangeIso_hom_app_comparison B S hS g P
  have hτ := representedAffineZariskiAssociatedIso_hom_app U P
  refine (whisker_eq _ hβ).trans ?_
  refine Eq.trans ?_ (eq_whisker (congrArg (smallEtaleDerivedModulePullback B S hS
    (representedSpaceMap B S hS g)).map hτ) _)
  exact (Functor.map_comp_assoc _ _ _ _).symm

end

section Chase

variable {D₀ D₀s D₁ D₁s E₀ E₁ D₂ : Type*} [Category D₀] [Category D₀s] [Category D₁] [Category D₁s]
  [Category E₀] [Category E₁] [Category D₂]

/-- The diagram chase behind `representedAffineZariskiAssociated_pathZ`, in arbitrary
categories. -/
private theorem representedAffineZariskiAssociated_pathZ_chase (Ci : D₀ ⥤ D₀s) (Cf : D₀s ⥤ D₀)
    (un : 𝟭 D₀s ≅ Cf ⋙ Ci) (Le : D₀s ⥤ E₀)
    (Lf : E₀ ⥤ E₁) (Lg : D₀ ⥤ D₁) (Ci' : D₁ ⥤ D₁s) (Cf' : D₁s ⥤ D₁) (un' : 𝟭 D₁s ≅ Cf' ⋙ Ci')
    (Le' : D₁s ⥤ E₁) (F : D₂ ⥤ D₁)
    {X Kls : D₀} {S₁ S₂ : D₁} {V₀ V₁ V₂ V₃ V₄ V₅ : D₂} {M₃ : D₁} {N₁ N₂ : E₁} {Y : D₀s}
    {Yz Qz Q₂ Y' : D₁s} {R : D₁} {Zz Z' T Tf : E₁} {W₀ : E₀}
    (ω : X ⟶ Cf.obj Y) (wls : X ⟶ Kls) (sh : Kls ⟶ Cf.obj Y) (shi : Cf.obj Y ⟶ Kls)
    (ω' : F.obj V₃ ⟶ Cf'.obj Y') (c₁ : Lg.obj X ⟶ S₁) (c₂ : S₁ ⟶ S₂) (c₃ : S₂ ⟶ F.obj V₀)
    (d : V₀ ⟶ V₁) (m : V₁ ⟶ V₂)
    (k : V₂ ⟶ V₃) (f : V₃ ⟶ V₄) (q : V₄ ⟶ V₅) (l : F.obj V₅ ⟶ M₃) (sh' : M₃ ⟶ Cf'.obj Y')
    (lg : Lg.obj Kls ⟶ R) (qv : R ⟶ M₃)
    (gMh : Cf'.obj Yz ⟶ Lg.obj (Cf.obj Y)) (gM : Lg.obj (Cf.obj Y) ⟶ Cf'.obj Yz)
    (lz : Yz ⟶ Qz) (qζ : Qz ⟶ Q₂) (sha : R ⟶ Cf'.obj Q₂) (shai : Cf'.obj Q₂ ⟶ R)
    (qvs : Q₂ ⟶ Y') (qζv : Qz ⟶ Y') (ℓe' : Le'.obj Y' ⟶ Z') (ℓez : Le'.obj Qz ⟶ Zz) (pm : Zz ⟶ Z')
    (hη : Z' ⟶ T)
    (G8 : Lf.obj (Le.obj (Ci.obj X)) ⟶ Le'.obj (Ci'.obj (Lg.obj X)))
    (G8Y : Lf.obj (Le.obj (Ci.obj (Cf.obj Y))) ⟶ Le'.obj (Ci'.obj (Lg.obj (Cf.obj Y))))
    (ZC : Lf.obj (Le.obj Y) ⟶ Le'.obj Yz) (ℓe : Le.obj Y ⟶ W₀) (lf : Lf.obj W₀ ⟶ Tf)
    (qs : Tf ⟶ Zz) (t₁ : Le'.obj (Ci'.obj (F.obj V₂)) ⟶ N₁) (φκ : N₁ ⟶ N₂)
    (fac : N₂ ⟶ T) (τq : Le'.obj (Ci'.obj (F.obj V₃)) ⟶ N₂)
    (hω : ω = wls ≫ sh) (hsh : sh ≫ shi = 𝟙 _) (hgM : gM ≫ gMh = 𝟙 _) (hsha : shai ≫ sha = 𝟙 _)
    (hn : t₁ ≫ φκ = Le'.map (Ci'.map (F.map k)) ≫ τq)
    (hω' : ω' = F.map (f ≫ q) ≫ l ≫ sh')
    (hf : τq ≫ fac = Le'.map (Ci'.map ω' ≫ un'.inv.app Y') ≫ ℓe' ≫ hη)
    (h3 : c₁ ≫ c₂ ≫ c₃ ≫ F.map (d ≫ m ≫ k ≫ f ≫ q) ≫ l = Lg.map wls ≫ lg ≫ qv)
    (h7 : gMh ≫ Lg.map shi ≫ lg = Cf'.map (lz ≫ qζ) ≫ shai)
    (h8 : qv ≫ sh' = sha ≫ Cf'.map qvs) (hqv : qζ ≫ qvs = qζv)
    (h9 : Le'.map qζv ≫ ℓe' = ℓez ≫ pm)
    (h4 : G8 ≫ Le'.map (Ci'.map (Lg.map ω)) = Lf.map (Le.map (Ci.map ω)) ≫ G8Y)
    (h5 : G8Y ≫ Le'.map (Ci'.map gM) ≫ Le'.map (un'.inv.app Yz) =
      Lf.map (Le.map (un.inv.app Y)) ≫ ZC)
    (h6 : ZC ≫ Le'.map lz ≫ ℓez = Lf.map ℓe ≫ lf ≫ qs) :
    G8 ≫ Le'.map (Ci'.map (c₁ ≫ c₂ ≫ c₃ ≫ F.map (d ≫ m))) ≫ t₁ ≫ φκ ≫ fac =
      Lf.map (Le.map (Ci.map ω ≫ un.inv.app Y) ≫ ℓe) ≫ lf ≫ qs ≫ pm ≫ hη := by
  have h7' : Lg.map wls ≫ lg = Lg.map ω ≫ gM ≫ Cf'.map (lz ≫ qζ) ≫ shai := by
    rw [← h7, reassoc_of% hgM, hω, Lg.map_comp wls sh, Category.assoc,
      ← Lg.map_comp_assoc sh shi lg, hsh, CategoryTheory.Functor.map_id, Category.id_comp]
  have h3' : (c₁ ≫ c₂ ≫ c₃ ≫ F.map (d ≫ m)) ≫ F.map k ≫ F.map (f ≫ q) ≫ l ≫ sh' =
      Lg.map wls ≫ lg ≫ qv ≫ sh' := by
    rw [← reassoc_of% h3]
    simp
  have e1 : (c₁ ≫ c₂ ≫ c₃ ≫ F.map (d ≫ m)) ≫ F.map k ≫ F.map (f ≫ q) ≫ l ≫ sh' =
      (Lg.map ω ≫ gM) ≫ Cf'.map (lz ≫ qζ ≫ qvs) := by
    rw [h3', h8, reassoc_of% h7']
    simp [reassoc_of% hsha]
  have hu := un'.inv.naturality (lz ≫ qζ ≫ qvs)
  simp only [Functor.comp_map, Functor.id_map] at hu
  have e2 : Ci'.map ((c₁ ≫ c₂ ≫ c₃ ≫ F.map (d ≫ m)) ≫ F.map k ≫ F.map (f ≫ q) ≫ l ≫ sh') ≫
      un'.inv.app Y' = Ci'.map (Lg.map ω ≫ gM) ≫ un'.inv.app Yz ≫ lz ≫ qζv := by
    rw [e1, Ci'.map_comp_assoc, hu, ← hqv]
  have e3 := congrArg Le'.map e2
  rw [reassoc_of% hn, hf, hω']
  simp only [Functor.map_comp, Category.assoc] at e3 h9 h4 h5 h6 ⊢
  rw [reassoc_of% e3, reassoc_of% h9, reassoc_of% h4, reassoc_of% h5, reassoc_of% h6]

end Chase

/-- `L(X_0 ≅ Spec A)^* M^~` at the locally small model, for `M` in the standard model of `D(A)`. -/
def representedAffineZariskiPullbackTilde
    (N : @DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) _ _
      (HasDerivedCategory.standard _)) :
    DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules :=
  (Stacks.Duality.derivedPullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).obj
    ((tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).mapDerivedCategory.obj
      ((Stacks.Injectives.grothendieckModelEquiv.{u}
        (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))).functor.obj N))

/-- The Zariski chain of the path through Stacks 08GH, on derived categories:
`L g_0^* L j^* M^~ ≅ L j'^* (A' ⊗^L_A M)^~` at the locally small model. -/
def representedAffineZariskiPathDerived
    (N : @DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) _ _
      (HasDerivedCategory.standard _)) :
    (Stacks.Duality.derivedPullback (B.inclusion.map g.left)).obj
        ((Stacks.Duality.derivedPullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).obj
          ((tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).mapDerivedCategory.obj
            ((Stacks.Injectives.grothendieckModelEquiv.{u}
              (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))).functor.obj N))) ⟶
      (Stacks.Duality.derivedPullback ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom).obj
        ((tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).mapDerivedCategory.obj
          ((Stacks.Injectives.grothendieckModelEquiv.{u}
            (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))).functor.obj
            ((@CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.functor.{u, u, u}
              _ _ _ _ (representedAffineCommRingCatHom B S hS g).hom (HasDerivedCategory.standard _)
              (HasDerivedCategory.standard _)
              (@CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                _ _ _ _ (representedAffineCommRingCatHom B S hS g).hom
                (HasDerivedCategory.standard _) (HasDerivedCategory.standard _))).obj N))) :=
  (Stacks.Duality.derivedPullbackCompIso (B.inclusion.map g.left)
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).hom.app _ ≫
    eqToHom (congrArg (fun t => (Stacks.Duality.derivedPullback t).obj
      ((tilde.functor _).mapDerivedCategory.obj
        ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} _)).functor.obj N)))
      (isoSpec_hom_square g)) ≫
    (Stacks.Duality.derivedPullbackCompIso
      ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom
      (Spec.map (representedAffineCommRingCatHom B S hS g))).inv.app _ ≫
    (Stacks.Duality.derivedPullback ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom).map
      ((affinePullbackComparison _ _ (representedAffineCommRingCatHom B S hS g)).hom.app _ ≫
        (tilde.functor _).mapDerivedCategory.map
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso
            (representedAffineCommRingCatHom B S hS g).hom).inv.app N))

section

attribute [local instance 10000] HasDerivedCategory.standard

/-- Naturality of the comparison of `Lε^*` with degreewise pullback, with `Lε^*` applied to the
localization of the morphism. -/
theorem representedZariskiDerivedPullbackComparison_naturality (W : BigFppfOver B S hS)
    {K₁ K₂ : HomotopyCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (representedSchemeRepresentedZariskiRingedToposHom B S hS W).zariskiRingedTopos.J)
      (representedSchemeRepresentedZariskiRingedToposHom B S hS W).zariskiRingedTopos.O)))
      (ComplexShape.up ℤ)} (x : K₁ ⟶ K₂) :
    (representedZariskiDerivedPullback B S hS W).map (DerivedCategory.Qh.map x) ≫
        (derivedPullbackComparison (X := smallEtaleRingedTopos B S hS (representedSpace W))
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS W).zariskiRingedTopos)
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS W)).app K₂ =
      (derivedPullbackComparison (X := smallEtaleRingedTopos B S hS (representedSpace W))
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS W).zariskiRingedTopos)
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS W)).app K₁ ≫
        DerivedCategory.Qh.map ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
          (X := smallEtaleRingedTopos B S hS (representedSpace W))
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS W).zariskiRingedTopos)
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS W)).map x) :=
  (derivedPullbackComparison (X := smallEtaleRingedTopos B S hS (representedSpace W))
    (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS W).zariskiRingedTopos)
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS W)).naturality x

attribute [local instance 10000] AlgebraicGeometry.Space.hasSheafCompose_smallEtale_forget₂_ringCat

attribute [local instance 20000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize

/-- **The path through Stacks 08GH, on complexes.** The first square of Stacks 08GH at
`L(X_0 ≅ Spec A)^* M^~`, then `Lε_{U'}^*` of the Zariski chain, then the isomorphism
`representedAffineZariskiAssociatedIso` at `U'` and `Φ'` of the comparison of derived extension of
scalars, is the degreewise composite. -/
theorem representedAffineZariskiAssociated_pathZ
    (P : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (representedDerivedPullbackSquareIso g).hom.app
        (representedAffineZariskiPullbackTilde (DerivedCategory.Q.obj P)) ≫
      (representedZariskiDerivedPullback B S hS U').map
        ((StacksDraft.DerivedModel.schemeModulesComparison
          (representedSchemeRepresentedZariskiRingedToposHom B S hS U')).inverse.map
          (representedAffineZariskiPathDerived g (DerivedCategory.Q.obj P))) ≫
      (representedAffineZariskiAssociatedIso U').hom.app _ ≫
      (representedAffineToposDerivedAssociated B S hS U').map
        ((representedAffineDerivedExtension B S hS g).comparison.app P) ≫
      (representedAffineToposDerivedFactors B S hS U').hom.app _ =
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
        ((representedZariskiDerivedPullback B S hS U).map
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
            (((tilde.functor _).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))) ≫
      (smallEtaleDerivedModulePullbackComparison B S hS (representedSpaceMap B S hS g)).app
        ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
          (X := smallEtaleRingedTopos B S hS (representedSpace U))
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)).obj
          (((Scheme.Modules.pullback
            ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj
            (((tilde.functor _).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))) ≫
      DerivedCategory.Qh.map ((pullbackMapHomotopySquareIso
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))
        (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)
        (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U')
        (B.inclusion.map g.left).zariskiRingedToposHom
        (representedZariskiPullbackModulesCompIso B S hS g)).hom.app
          (((Scheme.Modules.pullback
            ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj
            (((tilde.functor _).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))) ≫
      DerivedCategory.Qh.map ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
        (X := smallEtaleRingedTopos B S hS (representedSpace U'))
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U').zariskiRingedTopos)
        (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U')).map
          ((@Stacks.Homology.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
            (RingedToposHom.pullbackModules_additive
              (B.inclusion.map g.left).zariskiRingedToposHom)
            (RingedSpaceModuleAdjunction.modulePullback_additive
              (B.inclusion.map g.left).toLRSHom.toShHom)
            (B.inclusion.map g.left).zariskiPullbackModulesIsoModulePullback
              (ComplexShape.up ℤ)).hom.app _ ≫
          affineZariskiPathHomotopy (B.inclusion.map g.left)
            ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom
            ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom
            (representedAffineCommRingCatHom B S hS g) (isoSpec_hom_square g) P)) ≫
      DerivedCategory.Qh.map
        ((representedAffineZariskiAssociatedHomotopyIsoh U').hom.app
          (((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) := by
  have h4 := ((representedDerivedPullbackSquareIso g).hom.naturality
    (representedAffineZariskiPullbackTildeIso U P).hom).symm
  have h5 := representedDerivedPullbackSquareIso_hom_app_functor_obj g
      ((DerivedCategory.Qh (C := SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (J := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos.J)
        (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos.O)))).obj
          (((Scheme.Modules.pullback
            ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj
            (((tilde.functor _).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))))
  have h6 := representedZariskiToposDerivedPullbackCompIso_hom_app_comparison g
      (((Scheme.Modules.pullback
        ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj
            (((tilde.functor _).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
  have h7 := Scheme.Hom.zariskiDerivedPullbackModelIso_hom_app_comparison (B.inclusion.map g.left)
      (((Scheme.Modules.pullback
        ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj
            (((tilde.functor _).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
  have h3 := affineZariskiPath_comparison (B.inclusion.map g.left)
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom
      ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom
      (representedAffineCommRingCatHom B S hS g) (isoSpec_hom_square g) P
  refine representedAffineZariskiAssociated_pathZ_chase
    (Ci := (StacksDraft.DerivedModel.schemeModulesComparison
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U)).inverse)
    (Cf := (StacksDraft.DerivedModel.schemeModulesComparison
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U)).functor)
    (un := (StacksDraft.DerivedModel.schemeModulesComparison
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U)).unitIso)
    (Le := representedZariskiDerivedPullback B S hS U)
    (Lf := smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g))
    (Lg := Stacks.Duality.derivedPullback (B.inclusion.map g.left))
    (Ci' := (StacksDraft.DerivedModel.schemeModulesComparison
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U')).inverse)
    (Cf' := (StacksDraft.DerivedModel.schemeModulesComparison
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U')).functor)
    (un' := (StacksDraft.DerivedModel.schemeModulesComparison
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U')).unitIso)
    (Le' := representedZariskiDerivedPullback B S hS U')
    (F := Stacks.Duality.derivedPullback ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom)
    (hsh := (StacksDraft.DerivedModel.shrinkComparisonQhIso
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules).hom_inv_id_app _)
    (hgM := (B.inclusion.map g.left).zariskiDerivedPullbackModelIso.inv_hom_id_app _)
    (hsha := (StacksDraft.DerivedModel.shrinkComparisonQhIso
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U').Modules).inv_hom_id_app _)
    (hn := ((representedAffineZariskiAssociatedIso U').hom.naturality _).symm)
    (hω := representedAffineZariskiPullbackTildeIso_hom U P)
    (hω' := (representedAffineZariskiPullbackTildeIso_hom U' (((ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)).trans (Category.assoc _ _ _))
    (hf := (representedAffineZariskiAssociatedIso_hom_app U' (((ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)).trans
      ((congrArg (· ≫ (representedAffineZariskiAssociatedHomotopyIso U').hom.app
        (((ModuleCat.extendScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P))
        (representedAffineZariskiAssociatedFactors_hom_app U' (((ModuleCat.extendScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P))).trans (Category.assoc _ _ _)))
    (h3 := h3)
    (h7 := h7)
    (h8 := (StacksDraft.DerivedModel.shrinkComparisonQhIso
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U').Modules).hom.naturality _)
    (hqv := (DerivedCategory.Qh.map_comp _ _).symm)
    (h9 := ?h9)
    (ℓez := (derivedPullbackComparison (X := smallEtaleRingedTopos B S hS (representedSpace U'))
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U').zariskiRingedTopos)
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U')).app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
            (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS U').zariskiRingedTopos)
            (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
            (B.inclusion.map g.left).zariskiRingedToposHom).obj
          (((Scheme.Modules.pullback
            ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj
            (((tilde.functor _).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))))
    (h4 := h4)
    (h5 := h5)
    (h6 := ?h6)
  case h6 =>
    exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq h6) (by heq_congr)))
  case h9 =>
    have n := representedZariskiDerivedPullbackComparison_naturality U'
      ((@Stacks.Homology.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
          (RingedToposHom.pullbackModules_additive (B.inclusion.map g.left).zariskiRingedToposHom)
          (RingedSpaceModuleAdjunction.modulePullback_additive
            (B.inclusion.map g.left).toLRSHom.toShHom)
          (B.inclusion.map g.left).zariskiPullbackModulesIsoModulePullback
            (ComplexShape.up ℤ)).hom.app _ ≫
        affineZariskiPathHomotopy (B.inclusion.map g.left)
          ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom
          ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom
          (representedAffineCommRingCatHom B S hS g) (isoSpec_hom_square g) P)
    exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq n) (by heq_congr)))

end

section ChaseB

variable {E₀ E₁ D₁ : Type*} [Category E₀] [Category E₁] [Category D₁]

/-- The diagram chase behind `representedAffineZariskiAssociated_pathβ_comparison`. -/
private theorem representedAffineZariskiAssociated_pathβ_chase (Lf : E₀ ⥤ E₁)
    {X₀ X₁ X₂ : E₀} {Y₀ Y₁ Y₂ Y₃ Y₄ Y₅ : E₁} {a : Lf.obj X₀ ⟶ Y₀} {b : Y₀ ⟶ Y₁} {c : Y₁ ⟶ Y₂}
    (c₀ : X₀ ⟶ X₁) (hi : X₁ ⟶ X₂) (l₁ : Lf.obj X₁ ⟶ Y₃) (l₂ : Lf.obj X₂ ⟶ Y₄) (m : Y₃ ⟶ Y₄)
    (q : Y₄ ⟶ Y₅) (r : Y₃ ⟶ Y₅) (fi : Y₅ ⟶ Y₂) (fh : Y₂ ⟶ Y₅)
    (h₁ : a ≫ b ≫ c = Lf.map (c₀ ≫ hi) ≫ l₂ ≫ q ≫ fi) (hfi : fi ≫ fh = 𝟙 _)
    (hn : Lf.map hi ≫ l₂ = l₁ ≫ m) (hq : m ≫ q = r) :
    a ≫ b ≫ c ≫ fh = Lf.map c₀ ≫ l₁ ≫ r := by
  rw [reassoc_of% h₁, ← hq, Lf.map_comp, Category.assoc, reassoc_of% hn, hfi]
  simp

end ChaseB

section

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] additive_extendScalars_representedAffineRingHom

/-- **The path through `Φ`, on complexes**, in the form of
`representedAffineZariskiAssociated_pathZ`: after the comparison of derived extension of scalars
and `Φ'` on complexes, it is `Lf^*` of the comparison for `Lε_U^*`, the comparison for `Lf^*`, and
the degreewise composite. -/
theorem representedAffineZariskiAssociated_pathβ_comparison
    (P : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    letI := pullbackModules_smallEtale_additive (representedSpaceMap B S hS g)
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
        ((representedAffineZariskiAssociatedIso U).hom.app (DerivedCategory.Q.obj P)) ≫
      (representedAffineToposDerivedBaseChangeIso B S hS g).hom.app (DerivedCategory.Q.obj P) ≫
      (representedAffineToposDerivedAssociated B S hS U').map
        ((representedAffineDerivedExtension B S hS g).comparison.app P) ≫
      (representedAffineToposDerivedFactors B S hS U').hom.app
        (((ModuleCat.extendScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) =
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
        ((representedAffineZariskiAssociatedFactors U).hom.app P) ≫
      (smallEtaleDerivedModulePullbackComparison B S hS (representedSpaceMap B S hS g)).app
        ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
          (X := smallEtaleRingedTopos B S hS (representedSpace U))
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)).obj
            (((Scheme.Modules.pullback
                ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj
                (((tilde.functor _).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))) ≫
      (smallEtaleModulePullbackOnHomotopy B S hS (representedSpaceMap B S hS g)).map
        ((representedAffineZariskiAssociatedHomotopyIsoh U).hom.app P) ≫
      DerivedCategory.Qh.map
        ((Stacks.Homology.homotopyEdgeIso
          (representedAffineToposPullbackIso B S hS g)).hom.app P) :=
  representedAffineZariskiAssociated_pathβ_chase
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)) _ _ _ _ _ _ _ _ _
    (representedAffineZariskiAssociated_pathβ g P)
    ((representedAffineToposDerivedFactors B S hS U').inv_hom_id_app _)
    ((smallEtaleDerivedModulePullbackComparison B S hS (representedSpaceMap B S hS g)).naturality
      ((representedAffineZariskiAssociatedHomotopyIsoh U).hom.app P))
    rfl

end

end AlgebraicGeometry.Space
