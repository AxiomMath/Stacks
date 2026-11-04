module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.DerivedPullbackCompCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineZariskiPathUnit
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# The two derived base change paths of an affine representable differ by a unit

For a morphism `g : U' ⟶ U` of objects of the big fppf site over `S` with affine underlying schemes
and `M ∈ D(Γ(U))`, there are two isomorphisms from `Lf^* Lε_U^* (L(X_0 ≅ Spec A)^* M^~)` to
`Φ_{U'}(M ⊗ᴸ Γ(U'))`: through Stacks 08GH and the affine comparison of Stacks 08DW, or through
`Φ_U` and the affine base change isomorphism. They differ by multiplication by a unit of
`Γ(U')`: both are natural, they are compared on complexes, and there the module-level paths differ
by a unit.

## Main results

* `CategoryTheory.Functor.leftDerived_comp_app_ext`: natural families into a left derived functor
  are determined by their values after the comparison morphism on localized objects.
* `AlgebraicGeometry.Space.representedAffineZariskiPathDerived_naturality`: naturality of the
  Zariski chain of the path through Stacks 08GH.
* `AlgebraicGeometry.Space.exists_isUnit_representedAffineZariskiBaseChange`: the two derived
  paths differ by a unit.
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

namespace CategoryTheory.Functor

variable {C D D' E : Type*} [Category C] [Category D] [Category D'] [Category E]

/-- Two natural families of morphisms into a left derived functor `L ⋙ Φ` agree as soon as they
agree after its comparison morphism at every localized object. -/
theorem leftDerived_comp_app_ext {Q : C ⥤ D} (W : MorphismProperty C) [Q.IsLocalization W]
    (L : D ⥤ D') {F : C ⥤ D'} (cmp : Q ⋙ L ⟶ F) (Φ : D' ⥤ E)
    [(L ⋙ Φ).IsLeftDerivedFunctor ((Functor.associator _ _ _).inv ≫ whiskerRight cmp Φ) W]
    (G : D ⥤ E) (a b : ∀ N, G.obj N ⟶ Φ.obj (L.obj N))
    (ha : ∀ ⦃N N' : D⦄ (f : N ⟶ N'), G.map f ≫ a N' = a N ≫ Φ.map (L.map f))
    (hb : ∀ ⦃N N' : D⦄ (f : N ⟶ N'), G.map f ≫ b N' = b N ≫ Φ.map (L.map f))
    (h : ∀ P, a (Q.obj P) ≫ Φ.map (cmp.app P) = b (Q.obj P) ≫ Φ.map (cmp.app P)) (N : D) :
    a N = b N := by
  have e := Functor.leftDerived_ext (L ⋙ Φ) ((Functor.associator _ _ _).inv ≫ whiskerRight cmp Φ) W
    G ⟨a, ha⟩ ⟨b, hb⟩ (by
      ext P
      simpa using h P)
  exact congrArg (fun t => NatTrans.app t N) e

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

section Chase

variable {E M K : Type*} [Category E] [Category M] [Category K]

/-- The naturality chase behind `representedAffineZariskiPathDerived_naturality`. -/
private theorem pathDerived_naturality_chase (F : M ⥤ E) (H : K ⥤ M)
    {A₀ A₁ B₀ B₁ C₀ C₁ : E} {M₀ M₁ : M} {P₀ P₁ R₀ R₁ : K}
    (p : A₀ ⟶ A₁) (c₁ : A₀ ⟶ B₀) (c₁' : A₁ ⟶ B₁) (l₁ : B₀ ⟶ B₁) (e : B₀ ⟶ C₀) (e' : B₁ ⟶ C₁)
    (l₂ : C₀ ⟶ C₁) (c₂ : C₀ ⟶ F.obj M₀) (c₂' : C₁ ⟶ F.obj M₁) (l₃ : M₀ ⟶ M₁)
    (a : M₀ ⟶ H.obj P₀) (a' : M₁ ⟶ H.obj P₁) (k₄ : P₀ ⟶ P₁) (m : P₀ ⟶ R₀) (m' : P₁ ⟶ R₁)
    (k₅ : R₀ ⟶ R₁)
    (h₁ : p ≫ c₁' = c₁ ≫ l₁) (h₂ : l₁ ≫ e' = e ≫ l₂) (h₃ : l₂ ≫ c₂' = c₂ ≫ F.map l₃)
    (h₄ : l₃ ≫ a' = a ≫ H.map k₄) (h₅ : k₄ ≫ m' = m ≫ k₅) :
    p ≫ c₁' ≫ e' ≫ c₂' ≫ F.map (a' ≫ H.map m') = (c₁ ≫ e ≫ c₂ ≫ F.map (a ≫ H.map m)) ≫
      F.map (H.map k₅) := by
  have h₄' : l₃ ≫ a' ≫ H.map m' = a ≫ H.map m ≫ H.map k₅ := by
    rw [reassoc_of% h₄, ← H.map_comp, h₅, H.map_comp]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, ← F.map_comp, h₄']
  simp only [Category.assoc, Functor.map_comp]

end Chase

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {U' U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  (g : U' ⟶ U)

/-- Naturality of `representedAffineZariskiPathDerived`. -/
theorem representedAffineZariskiPathDerived_naturality
    {N N' : @DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) _ _
      (HasDerivedCategory.standard _)} (f : N ⟶ N') :
    (Stacks.Duality.derivedPullback (B.inclusion.map g.left)).map
        ((Stacks.Duality.derivedPullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).map
          ((tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).mapDerivedCategory.map
            ((Stacks.Injectives.grothendieckModelEquiv.{u}
              (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))).functor.map f))) ≫
      representedAffineZariskiPathDerived g N' =
    representedAffineZariskiPathDerived g N ≫
      (Stacks.Duality.derivedPullback ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom).map
        ((tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).mapDerivedCategory.map
          ((Stacks.Injectives.grothendieckModelEquiv.{u}
            (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))).functor.map
            ((@CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.functor.{u, u, u}
              _ _ _ _ (representedAffineCommRingCatHom B S hS g).hom (HasDerivedCategory.standard _)
              (HasDerivedCategory.standard _)
              (@CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                _ _ _ _ (representedAffineCommRingCatHom B S hS g).hom
                  (HasDerivedCategory.standard _)
                (HasDerivedCategory.standard _))).map f))) :=
  pathDerived_naturality_chase
    (Stacks.Duality.derivedPullback ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom)
    (tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).mapDerivedCategory
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((Stacks.Duality.derivedPullbackCompIso (B.inclusion.map g.left)
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).hom.naturality _)
    (Stacks.Duality.derivedPullback_map_comp_eqToHom (isoSpec_hom_square g) _)
    ((Stacks.Duality.derivedPullbackCompIso
      ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom
      (Spec.map (representedAffineCommRingCatHom B S hS g))).inv.naturality _)
    ((affinePullbackComparison _ _ (representedAffineCommRingCatHom B S hS g)).hom.naturality _)
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso
      (representedAffineCommRingCatHom B S hS g).hom).inv.naturality f)

section ChaseC

variable {D₁ D₁s E₁ : Type*} [Category D₁] [Category D₁s] [Category E₁]

/-- The naturality chase behind `representedAffineZariskiPathZ_naturality`. -/
private theorem pathZ_naturality_chase (Ci' : D₁ ⥤ D₁s) (LZ' : D₁s ⥤ E₁) {X X' Z Z' : E₁}
    {Y₀ Y₀' Y₁ Y₁' : D₁} (p : X ⟶ X') (s : X ⟶ LZ'.obj (Ci'.obj Y₀))
    (s' : X' ⟶ LZ'.obj (Ci'.obj Y₀')) (q : Y₀ ⟶ Y₀') (d : Y₀ ⟶ Y₁) (d' : Y₀' ⟶ Y₁')
    (y : Y₁ ⟶ Y₁') (t : LZ'.obj (Ci'.obj Y₁) ⟶ Z) (t' : LZ'.obj (Ci'.obj Y₁') ⟶ Z') (z : Z ⟶ Z')
    (hs : p ≫ s' = s ≫ LZ'.map (Ci'.map q)) (hd : q ≫ d' = d ≫ y)
    (ht : LZ'.map (Ci'.map y) ≫ t' = t ≫ z) :
    p ≫ s' ≫ LZ'.map (Ci'.map d') ≫ t' = (s ≫ LZ'.map (Ci'.map d) ≫ t) ≫ z := by
  rw [reassoc_of% hs, ← LZ'.map_comp_assoc, ← Ci'.map_comp, hd, Ci'.map_comp,
    LZ'.map_comp_assoc, ht]
  simp

/-- The naturality chase behind `representedAffineZariskiPathβ_naturality`. -/
private theorem pathβ_naturality_chase {E₀ : Type*} [Category E₀] (Lf : E₀ ⥤ E₁) {X X' V V' : E₀}
    {W W' Y Y' : E₁} (w : X ⟶ X') (τ : X ⟶ V) (τ' : X' ⟶ V') (v : V ⟶ V') (β : Lf.obj V ⟶ W)
    (β' : Lf.obj V' ⟶ W') (l : W ⟶ W') (μ : W ⟶ Y) (μ' : W' ⟶ Y') (l' : Y ⟶ Y')
    (hτ : w ≫ τ' = τ ≫ v) (hβ : Lf.map v ≫ β' = β ≫ l) (hμ : l ≫ μ' = μ ≫ l') :
    Lf.map w ≫ Lf.map τ' ≫ β' ≫ μ' = (Lf.map τ ≫ β ≫ μ) ≫ l' := by
  rw [← Lf.map_comp_assoc, hτ, Lf.map_comp_assoc, reassoc_of% hβ, hμ]
  simp

/-- The diagram chase behind `representedAffineZariskiBaseChange_comparison`. -/
private theorem pathComparison_chase {A B₁ B₂ B₃ B₄ B₅ C D₁ D₂ D₃ D₄ D₃' : E₁}
    (s : A ⟶ B₁) (k : B₁ ⟶ B₂) (t : B₂ ⟶ B₃) (φ : B₃ ⟶ B₄) (fac : B₄ ⟶ B₅) (x : A ⟶ C)
    (y : C ⟶ B₃) (u : B₃ ⟶ B₃) (u' : B₄ ⟶ B₄) (za zb : A ⟶ D₁) (ℓ : D₁ ⟶ D₂) (z₁ : D₂ ⟶ D₃)
    (z₂ : D₃ ⟶ D₄) (z₃ : D₄ ⟶ B₅) (w₁ : D₂ ⟶ D₃') (w₂ : D₃' ⟶ B₅) (w₃ : B₅ ⟶ B₅)
    (h₃ : s ≫ k ≫ t ≫ φ ≫ fac = za ≫ ℓ ≫ z₁ ≫ z₂ ≫ z₃) (h₅ : z₁ ≫ z₂ ≫ z₃ = w₁ ≫ w₂ ≫ w₃)
    (h₄ : x ≫ y ≫ φ ≫ fac = zb ≫ ℓ ≫ w₁ ≫ w₂) (hz : za = zb) (hu : u ≫ φ = φ ≫ u')
    (hf : u' ≫ fac = fac ≫ w₃) :
    ((s ≫ k ≫ t) ≫ φ) ≫ fac = ((x ≫ y ≫ u) ≫ φ) ≫ fac := by
  simp only [Category.assoc]
  rw [h₃, h₅, reassoc_of% hu, hf, reassoc_of% h₄, hz]

end ChaseC

section

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

attribute [local instance] additive_extendScalars_representedAffineRingHom

attribute [local instance 10000] HasDerivedCategory.standard

/-- Naturality of the path through Stacks 08GH. -/
theorem representedAffineZariskiPathZ_naturality
    {N N' : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))}
    (f : N ⟶ N') :
    (representedAffineZariskiAssociated U ⋙
        smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map f ≫
      (representedDerivedPullbackSquareIso g).hom.app (representedAffineZariskiPullbackTilde N') ≫
        (representedZariskiDerivedPullback B S hS U').map
          ((StacksDraft.DerivedModel.schemeModulesComparison
            (representedSchemeRepresentedZariskiRingedToposHom B S hS U')).inverse.map
            (representedAffineZariskiPathDerived g N')) ≫
        (representedAffineZariskiAssociatedIso U').hom.app _ =
    ((representedDerivedPullbackSquareIso g).hom.app (representedAffineZariskiPullbackTilde N) ≫
        (representedZariskiDerivedPullback B S hS U').map
          ((StacksDraft.DerivedModel.schemeModulesComparison
            (representedSchemeRepresentedZariskiRingedToposHom B S hS U')).inverse.map
            (representedAffineZariskiPathDerived g N)) ≫
        (representedAffineZariskiAssociatedIso U').hom.app _) ≫
      (representedAffineToposDerivedAssociated B S hS U').map
        ((representedAffineDerivedExtension B S hS g).functor.map f) :=
  pathZ_naturality_chase
    (StacksDraft.DerivedModel.schemeModulesComparison
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U')).inverse
    (representedZariskiDerivedPullback B S hS U') _ _ _ _ _ _ _ _ _ _
    ((representedDerivedPullbackSquareIso g).hom.naturality _)
    (representedAffineZariskiPathDerived_naturality g f)
    ((representedAffineZariskiAssociatedIso U').hom.naturality _)

/-- Naturality of the path through `Φ`, followed by a central automorphism. -/
theorem representedAffineZariskiPathβ_naturality
    (t : 𝟭 (DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))) ≅ 𝟭 _)
    {N N' : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))}
    (f : N ⟶ N') :
    (representedAffineZariskiAssociated U ⋙
        smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map f ≫
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
          ((representedAffineZariskiAssociatedIso U).hom.app N') ≫
        (representedAffineToposDerivedBaseChangeIso B S hS g).hom.app N' ≫
        (representedAffineToposDerivedAssociated B S hS U').map
          (t.hom.app ((representedAffineDerivedExtension B S hS g).functor.obj N')) =
    ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
          ((representedAffineZariskiAssociatedIso U).hom.app N) ≫
        (representedAffineToposDerivedBaseChangeIso B S hS g).hom.app N ≫
        (representedAffineToposDerivedAssociated B S hS U').map
          (t.hom.app ((representedAffineDerivedExtension B S hS g).functor.obj N))) ≫
      (representedAffineToposDerivedAssociated B S hS U').map
        ((representedAffineDerivedExtension B S hS g).functor.map f) :=
  pathβ_naturality_chase (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g))
    _ _ _ _ _ _ _ _ _ _
    ((representedAffineZariskiAssociatedIso U).hom.naturality f)
    ((representedAffineToposDerivedBaseChangeIso B S hS g).hom.naturality f)
    (((Functor.map_comp _ _ _).symm.trans
      (congrArg (representedAffineToposDerivedAssociated B S hS U').map
        (t.hom.naturality ((representedAffineDerivedExtension B S hS g).functor.map f)))).trans
      (Functor.map_comp _ _ _))

/-- **The two paths agree after the comparison of derived extension of scalars**, up to the unit
by which the module-level paths differ. -/
theorem representedAffineZariskiBaseChange_comparison
    (c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) (hc : IsUnit c)
    (hch : ∀ M, (representedAffinePathModuleZ g).hom.app M =
        (representedAffinePathModuleβ g).hom.app M ≫
          (representedAffineToposAssociated B S hS U').map
            ((c • 𝟙
              (ModuleCat.extendScalars.{u, u, u}
                (representedAffineCommRingCatHom B S hS g).hom)).app M))
    (P : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    ((representedDerivedPullbackSquareIso g).hom.app
        (representedAffineZariskiPullbackTilde (DerivedCategory.Q.obj P)) ≫
      (representedZariskiDerivedPullback B S hS U').map
        ((StacksDraft.DerivedModel.schemeModulesComparison
          (representedSchemeRepresentedZariskiRingedToposHom B S hS U')).inverse.map
          (representedAffineZariskiPathDerived g (DerivedCategory.Q.obj P))) ≫
      (representedAffineZariskiAssociatedIso U').hom.app _) ≫
      (representedAffineToposDerivedAssociated B S hS U').map
        ((representedAffineDerivedExtension B S hS g).comparison.app P) =
    ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
        ((representedAffineZariskiAssociatedIso U).hom.app (DerivedCategory.Q.obj P)) ≫
      (representedAffineToposDerivedBaseChangeIso B S hS g).hom.app (DerivedCategory.Q.obj P) ≫
      (representedAffineToposDerivedAssociated B S hS U').map
        ((unitCentralIso c hc).hom.app
          ((representedAffineDerivedExtension B S hS g).functor.obj (DerivedCategory.Q.obj P)))) ≫
      (representedAffineToposDerivedAssociated B S hS U').map
        ((representedAffineDerivedExtension B S hS g).comparison.app P) := by
  refine (cancel_mono ((representedAffineToposDerivedFactors B S hS U').hom.app
    (((ModuleCat.extendScalars.{u, u, u}
      (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P))).1 ?_
  have hq : DerivedCategory.Q.map (c • 𝟙 (((ModuleCat.extendScalars.{u, u, u}
      (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)) =
      (unitCentralIso c hc).hom.app (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    rfl
  exact pathComparison_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (representedAffineZariskiAssociated_pathZ g P)
    (eq_of_heq (HEq.trans (by heq_congr)
      (HEq.trans (heq_of_eq (representedAffineZariskiPathTail_of_module g c hch P))
        (by heq_congr))))
    (representedAffineZariskiAssociated_pathβ_comparison g P)
    (congrArg (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
      (representedAffineZariskiAssociatedFactors_hom_app U P).symm)
    (((Functor.map_comp _ _ _).symm.trans
      (congrArg (representedAffineToposDerivedAssociated B S hS U').map
        ((unitCentralIso c hc).hom.naturality
          ((representedAffineDerivedExtension B S hS g).comparison.app P)).symm)).trans
      (Functor.map_comp _ _ _))
    ((eq_whisker (congrArg (representedAffineToposDerivedAssociated B S hS U').map hq).symm _).trans
      ((representedAffineToposDerivedFactors B S hS U').hom.naturality _))

/-- **C-nat**: the two derived base change paths differ by a unit. -/
theorem exists_isUnit_representedAffineZariskiBaseChange :
    ∃ c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)ˣ,
      ∀ N : @DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) _ _
          (HasDerivedCategory.standard _),
        (representedDerivedPullbackSquareIso g).hom.app (representedAffineZariskiPullbackTilde N) ≫
          (representedZariskiDerivedPullback B S hS U').map
            ((StacksDraft.DerivedModel.schemeModulesComparison
              (representedSchemeRepresentedZariskiRingedToposHom B S hS U')).inverse.map
              (representedAffineZariskiPathDerived g N)) ≫
          (representedAffineZariskiAssociatedIso U').hom.app _ =
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
            ((representedAffineZariskiAssociatedIso U).hom.app N) ≫
          (representedAffineToposDerivedBaseChangeIso B S hS g).hom.app N ≫
          (representedAffineToposDerivedAssociated B S hS U').map
            ((unitCentralIso (c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))
              c.isUnit).hom.app _) := by
  refine (exists_isUnit_representedAffinePathModuleZ g).elim fun c hc => ?_
  refine ⟨hc.1.unit, fun N => ?_⟩
  have := isLeftDerivedFunctor_representedAffineToposDerivedExtension_comp B S hS g
  exact Functor.leftDerived_comp_app_ext (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (representedAffineDerivedExtension B S hS g).functor
    (representedAffineDerivedExtension B S hS g).comparison
    (representedAffineToposDerivedAssociated B S hS U')
    (representedAffineZariskiAssociated U ⋙
      smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g))
    _ _ (fun _ _ f => representedAffineZariskiPathZ_naturality g f)
    (fun _ _ f => representedAffineZariskiPathβ_naturality g (unitCentralIso c hc.1) f)
    (fun P => representedAffineZariskiBaseChange_comparison g c hc.1 hc.2 P) N

end

end AlgebraicGeometry.Space
