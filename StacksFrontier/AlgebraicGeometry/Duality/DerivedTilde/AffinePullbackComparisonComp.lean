module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.DerivedPullbackCompCoherence
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTildeComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineZariskiPathComparison
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionComplexLevel

/-!
# The composition law for the affine comparison of Stacks 08DW

For ring maps `f : R ⟶ S` and `g : S ⟶ T`, the comparison
`L(Spec f)^* ∘ (~) ≅ (~) ∘ (S ⊗ᴸ_R -)` of [Stacks, Tag 08DW] for `f ≫ g` is the one for `f`
followed by the one for `g`, modulo the composition isomorphisms of derived pullback
([Stacks, Tag 0D5S]) and of derived extension of scalars. The proof is uniqueness of the left
derived functor `(T ⊗ᴸ_R -) ⋙ (~)`, reducing the claim to the underived composition law
`AlgebraicGeometry.pullbackTildeIso_comp` of [Stacks, Tag 01I9].

## Main results

* `AlgebraicGeometry.tildePullbackComplexIso_comp_hom_app` — the composition law of Stacks 01I9
  on complexes.
* `AlgebraicGeometry.affinePullbackComparison_comp_derivedPullbackCompIso` — the composition law of
  Stacks 08DW.
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex.DerivedExtensionScalars

universe u

namespace AlgebraicGeometry

section Chase

variable {𝒟S 𝒟 : Type*} [Category 𝒟S] [Category 𝒟]

/-- The chase behind `affinePullbackComparison_comp_derivedPullbackCompIso` on a complex. -/
theorem affinePullbackComparison_comp_chase (Lg : 𝒟S ⥤ 𝒟)
    {A₀ A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ B₆ B₇ B₈ : 𝒟} {Y₀ Y₁ Y₂ Y₃ Y₄ Y₅ : 𝒟S}
    (l₁ : A₀ ⟶ A₁) (l₂ : A₁ ⟶ A₂) (qm : A₂ ⟶ A₃)
    (e₁ : A₀ ⟶ B₁) (c : B₁ ⟶ Lg.obj Y₀) (af : Y₀ ⟶ Y₁) (gG : Lg.obj Y₁ ⟶ B₂) (k : B₂ ⟶ B₃)
    (cmp : B₃ ⟶ A₃) (t₁ : B₂ ⟶ B₄) (t₂ : B₄ ⟶ B₅) (fT : B₅ ⟶ B₆) (qe : B₆ ⟶ A₃)
    (s : Y₁ ⟶ Y₂) (gG' : Lg.obj Y₂ ⟶ B₄) (fS : Y₂ ⟶ Y₃) (dg : Lg.obj Y₃ ⟶ B₇) (qg : B₇ ⟶ B₆)
    (lfr : Y₀ ⟶ Y₄) (df : Y₄ ⟶ Y₅) (qf : Y₅ ⟶ Y₃) (dg' : Lg.obj Y₅ ⟶ B₈) (qg' : B₈ ⟶ B₇)
    (l₁' : B₁ ⟶ A₄) (c' : A₄ ⟶ Lg.obj Y₄) (dgf : A₄ ⟶ A₅) (qpc : A₅ ⟶ B₈) (qeq : A₂ ⟶ A₅)
    (hκ : k ≫ cmp = t₁ ≫ t₂ ≫ fT ≫ qe) (hG : gG ≫ t₁ = Lg.map s ≫ gG')
    (hg : gG' ≫ t₂ ≫ fT = Lg.map fS ≫ dg ≫ qg) (hf : af ≫ s ≫ fS = lfr ≫ df ≫ qf)
    (hdg : Lg.map qf ≫ dg = dg' ≫ qg') (hC : c ≫ Lg.map lfr = l₁' ≫ c')
    (hfac : c' ≫ Lg.map df ≫ dg' = dgf ≫ qpc) (hE : e₁ ≫ l₁' ≫ dgf = l₁ ≫ l₂ ≫ qeq)
    (hdeg : qm = qeq ≫ qpc ≫ qg' ≫ qg ≫ qe) :
    (l₁ ≫ l₂) ≫ qm = e₁ ≫ c ≫ Lg.map af ≫ gG ≫ k ≫ cmp := by
  have h₁ : Lg.map af ≫ gG ≫ k ≫ cmp = Lg.map lfr ≫ Lg.map df ≫ dg' ≫ qg' ≫ qg ≫ qe := by
    rw [hκ, reassoc_of% hG, reassoc_of% hg, ← Lg.map_comp_assoc, ← Lg.map_comp_assoc,
      Category.assoc, hf]
    simp only [Functor.map_comp, Category.assoc, reassoc_of% hdg]
  rw [h₁, reassoc_of% hC, reassoc_of% hfac, reassoc_of% hE, hdeg, Category.assoc]

/-- The naturality chase behind `affinePullbackComparison_comp_derivedPullbackCompIso`. -/
theorem affinePullbackComparison_comp_naturality_chase (Lg : 𝒟S ⥤ 𝒟)
    {A₀ A₀' B₀ B₀' B₁ B₁' B₂ B₂' : 𝒟} {Y₀ Y₀' Y₁ Y₁' : 𝒟S}
    (x : A₀ ⟶ A₀') (x' : B₀ ⟶ B₀') (e₁ : A₀ ⟶ B₀) (e₁' : A₀' ⟶ B₀') (c : B₀ ⟶ Lg.obj Y₀)
    (c' : B₀' ⟶ Lg.obj Y₀') (x'' : Y₀ ⟶ Y₀') (af : Y₀ ⟶ Y₁) (af' : Y₀' ⟶ Y₁') (y : Y₁ ⟶ Y₁')
    (gG : Lg.obj Y₁ ⟶ B₁) (gG' : Lg.obj Y₁' ⟶ B₁') (z : B₁ ⟶ B₁') (k : B₁ ⟶ B₂)
    (k' : B₁' ⟶ B₂') (w : B₂ ⟶ B₂')
    (h₁ : x ≫ e₁' = e₁ ≫ x') (h₂ : x' ≫ c' = c ≫ Lg.map x'') (h₃ : x'' ≫ af' = af ≫ y)
    (h₄ : Lg.map y ≫ gG' = gG ≫ z) (h₅ : z ≫ k' = k ≫ w) :
    x ≫ e₁' ≫ c' ≫ Lg.map af' ≫ gG' ≫ k' = (e₁ ≫ c ≫ Lg.map af ≫ gG ≫ k) ≫ w := by
  rw [reassoc_of% h₁, reassoc_of% h₂, ← Lg.map_comp_assoc, h₃, Lg.map_comp_assoc,
    reassoc_of% h₄, h₅]
  simp only [Category.assoc]

/-- Transport along an equality of morphisms of schemes commutes with the comparison of derived
pullback with degreewise pullback. -/
theorem eqToHom_derivedPullback_complexComparison {X Y : Scheme.{u}} {t t' : X ⟶ Y} (h : t = t')
    {E : DerivedCategory Y.Modules} {K : CochainComplex Y.Modules ℤ}
    (φ : E ⟶ DerivedCategory.Q.obj K) :
    eqToHom (congrArg (fun t => (Stacks.Duality.derivedPullback t).obj E) h) ≫
        (Stacks.Duality.derivedPullback t').map φ ≫
        (Stacks.DerivedPullback.derivedPullbackComplexComparison t'.toLRSHom.toShHom).app K =
      (Stacks.Duality.derivedPullback t).map φ ≫
        (Stacks.DerivedPullback.derivedPullbackComplexComparison t.toLRSHom.toShHom).app K ≫
        DerivedCategory.Q.map (eqToHom (congrArg (fun t =>
          ((Scheme.Modules.pullback t).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) h)) := by
  subst h
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id]
  exact (Category.id_comp _).trans (congrArg (_ ≫ ·) (Category.comp_id _).symm)

/-- A functor applied to a morphism equal to a fivefold composite. -/
theorem map_eq_comp₅ {𝒞 : Type*} [Category* 𝒞] (F : 𝒞 ⥤ 𝒟) {X₀ X₁ X₂ X₃ X₄ X₅ : 𝒞}
    {x : X₀ ⟶ X₅} {x₁ : X₀ ⟶ X₁} {x₂ : X₁ ⟶ X₂} {x₃ : X₂ ⟶ X₃} {x₄ : X₃ ⟶ X₄} {x₅ : X₄ ⟶ X₅}
    (h : x = x₁ ≫ x₂ ≫ x₃ ≫ x₄ ≫ x₅) :
    F.map x = F.map x₁ ≫ F.map x₂ ≫ F.map x₃ ≫ F.map x₄ ≫ F.map x₅ := by
  subst h
  simp only [Functor.map_comp]

/-- The transport `Scheme.Modules.pullbackCongr` is an `eqToHom`. -/
theorem pullbackCongr_hom_app_eq {X Y : Scheme.{u}} {t t' : X ⟶ Y} (h : t = t') (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app M =
      eqToHom (congrArg (fun t => (Scheme.Modules.pullback t).obj M) h) := by
  subst h
  rfl

end Chase

/-- The comparison of derived pullback with degreewise pullback at a complex, written out. -/
theorem derivedPullbackComplexComparison_app_factors {X Y : RingedSpace.{u, u}} (a : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    (Stacks.DerivedPullback.derivedPullbackComplexComparison a).app K =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback a).map
          ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (structureSheafRing Y))).inv.app K) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison a).app
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          (((RingedSpaceModuleAdjunction.modulePullback a).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).hom.app K) ≫
        (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom.app
          (((RingedSpaceModuleAdjunction.modulePullback a).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) := by
  dsimp only [Stacks.DerivedPullback.derivedPullbackComplexComparison]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]

/-- **Stacks 0D5S at the presentation `DerivedCategory.Q`, for schemes**: the inverse of the
composition isomorphism followed by the iterated comparison with degreewise pullback is the
comparison for the composite followed by the degreewise composition isomorphism. -/
theorem derivedPullbackCompIso_inv_app_complexComparison {X Y Z : Scheme.{u}} (a : X ⟶ Y)
    (b : Y ⟶ Z) [(RingedSpaceModuleAdjunction.modulePullback a.toLRSHom.toShHom).Additive]
    [(RingedSpaceModuleAdjunction.modulePullback b.toLRSHom.toShHom).Additive]
    [(RingedSpaceModuleAdjunction.modulePullback
      (a.toLRSHom.toShHom ≫ b.toLRSHom.toShHom)).Additive]
    (K : CochainComplex Z.Modules ℤ) :
    (Stacks.Duality.derivedPullbackCompIso a b).inv.app (DerivedCategory.Q.obj K) ≫
        (Stacks.Duality.derivedPullback a).map
          ((Stacks.DerivedPullback.derivedPullbackComplexComparison b.toLRSHom.toShHom).app K) ≫
        (Stacks.DerivedPullback.derivedPullbackComplexComparison a.toLRSHom.toShHom).app
          (((Scheme.Modules.pullback b).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (Stacks.DerivedPullback.derivedPullbackComplexComparison
          (a.toLRSHom.toShHom ≫ b.toLRSHom.toShHom)).app K ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (Stacks.DerivedPullback.Composition.modulePullbackComp a.toLRSHom.toShHom
            b.toLRSHom.toShHom) (ComplexShape.up ℤ)).inv.app K) :=
  (Stacks.DerivedPullback.ComplexLevel.comparison_comp_of_homotopyPinning
    (DerivedCategory.quotientCompQhIso X.Modules)
    (DerivedCategory.quotientCompQhIso Y.Modules)
    (DerivedCategory.quotientCompQhIso Z.Modules)
    ((RingedSpaceModuleAdjunction.modulePullback a.toLRSHom.toShHom).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ))
    ((RingedSpaceModuleAdjunction.modulePullback b.toLRSHom.toShHom).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ))
    ((RingedSpaceModuleAdjunction.modulePullback
      (a.toLRSHom.toShHom ≫ b.toLRSHom.toShHom)).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison a.toLRSHom.toShHom)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison b.toLRSHom.toShHom)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      (a.toLRSHom.toShHom ≫ b.toLRSHom.toShHom))
    (Stacks.Duality.derivedPullbackCompIso a b)
    (Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso a.toLRSHom.toShHom
      b.toLRSHom.toShHom)
    (Functor.mapHomologicalComplexCompIso
      (Stacks.DerivedPullback.Composition.modulePullbackComp a.toLRSHom.toShHom
        b.toLRSHom.toShHom) (ComplexShape.up ℤ))
    (Stacks.DerivedPullback.derivedPullbackComplexComparison a.toLRSHom.toShHom)
    (Stacks.DerivedPullback.derivedPullbackComplexComparison b.toLRSHom.toShHom)
    (Stacks.DerivedPullback.derivedPullbackComplexComparison
      (a.toLRSHom.toShHom ≫ b.toLRSHom.toShHom))
    (derivedPullbackComplexComparison_app_factors _)
    (derivedPullbackComplexComparison_app_factors _)
    (derivedPullbackComplexComparison_app_factors _)
    (Stacks.Duality.derivedPullbackCompIso_hom_app_comparison a b)
    (fun M => @StacksDraft.MapHomotopyCategory.mapHomotopyCategoryCompIso_hom_app_comp_factors
      _ _ _ _ _ _ _ _ _ _ _ _ _
      (Stacks.DerivedPullback.Composition.modulePullbackComp a.toLRSHom.toShHom
        b.toLRSHom.toShHom) ‹_› ‹_› ‹_› (ComplexShape.up ℤ) M) K).symm

/-- `derivedPullbackCompIso_inv_app_complexComparison` with the degreewise composition
isomorphism of `AlgebraicGeometry.Scheme.Modules`. -/
theorem derivedPullbackCompIso_inv_app_complexComparison' {X Y Z : Scheme.{u}} (a : X ⟶ Y)
    (b : Y ⟶ Z) [(RingedSpaceModuleAdjunction.modulePullback a.toLRSHom.toShHom).Additive]
    [(RingedSpaceModuleAdjunction.modulePullback b.toLRSHom.toShHom).Additive]
    [(RingedSpaceModuleAdjunction.modulePullback
      (a.toLRSHom.toShHom ≫ b.toLRSHom.toShHom)).Additive]
    (K : CochainComplex Z.Modules ℤ) :
    (Stacks.Duality.derivedPullbackCompIso a b).inv.app (DerivedCategory.Q.obj K) ≫
        (Stacks.Duality.derivedPullback a).map
          ((Stacks.DerivedPullback.derivedPullbackComplexComparison b.toLRSHom.toShHom).app K) ≫
        (Stacks.DerivedPullback.derivedPullbackComplexComparison a.toLRSHom.toShHom).app
          (((Scheme.Modules.pullback b).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (Stacks.DerivedPullback.derivedPullbackComplexComparison
          (a.toLRSHom.toShHom ≫ b.toLRSHom.toShHom)).app K ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (Scheme.Modules.pullbackComp a b) (ComplexShape.up ℤ)).inv.app K) := by
  refine (derivedPullbackCompIso_inv_app_complexComparison a b K).trans
    (congrArg (_ ≫ DerivedCategory.Q.map ·) ?_)
  rw [Stacks.Scheme.Modules.pullbackComp_eq_modulePullbackComp]
  ext n : 2
  rfl


/-- The isomorphism of complexes induced by `e : F ⋙ G ≅ H ⋙ K`, conjugated by the canonical
identifications of `F.mapHomologicalComplex ⋙ G.mapHomologicalComplex` with
`(F ⋙ G).mapHomologicalComplex`. -/
abbrev mapHomologicalComplexCompIsoOf {ι V W W' V₂ : Type*} {_ : Category V}
    {_ : Category W} {_ : Category W'} {_ : Category V₂} {_ : Preadditive V} {_ : Preadditive W}
    {_ : Preadditive W'} {_ : Preadditive V₂} {F : V ⥤ W} {G : W ⥤ W'} {H : V ⥤ V₂} {K : V₂ ⥤ W'}
    [F.Additive] [G.Additive] [H.Additive] [K.Additive] [(F ⋙ G).Additive]
    [(H ⋙ K).Additive] (e : F ⋙ G ≅ H ⋙ K) (c : ComplexShape ι) :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c) ≪≫
    NatIso.mapHomologicalComplex e c ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ K)) c).symm

/-- Generic form of `tildePullbackComplexIso_comp_hom_app`: a composition law
`eFG = (σ ≪≫ β⁻¹) ∘ eF ∘ eG ∘ κ⁻¹` for isomorphisms `tR ⋙ p ≅ e ⋙ tS` passes to complexes. -/
theorem mapHomologicalComplexCompIsoOf_comp_hom_app {ι J V W W₁ W' V₁ V₂ : Type*}
    {_ : Category V} {_ : Category W} {_ : Category W₁} {_ : Category W'} {_ : Category V₁}
    {_ : Category V₂} {_ : Preadditive V} {_ : Preadditive W} {_ : Preadditive W₁}
    {_ : Preadditive W'} {_ : Preadditive V₁} {_ : Preadditive V₂} {c : ComplexShape ι}
    {tR : V ⥤ W} {pf : W ⥤ W₁} {ef : V ⥤ V₁} {tS : V₁ ⥤ W₁} {pg : W₁ ⥤ W'} {eg : V₁ ⥤ V₂}
    {tT : V₂ ⥤ W'} {efg : V ⥤ V₂} {pb : J → (W ⥤ W')}
    {_ : tR.Additive} {_ : pf.Additive} {_ : ef.Additive} {_ : tS.Additive} {_ : pg.Additive}
    {_ : eg.Additive} {_ : tT.Additive} {_ : efg.Additive} {_ : ∀ t, (pb t).Additive}
    {_ : (tR ⋙ pf).Additive} {_ : (ef ⋙ tS).Additive} {_ : (tS ⋙ pg).Additive}
    {_ : (eg ⋙ tT).Additive} {t₀ t₁ : J} {_ : (tR ⋙ pb t₀).Additive} {_ : (efg ⋙ tT).Additive}
    (h : t₀ = t₁) (σ : pb t₀ ≅ pb t₁)
    (hσ : ∀ M, σ.hom.app M = eqToHom (congrArg (fun t => (pb t).obj M) h))
    (β : pf ⋙ pg ≅ pb t₁) (eF : tR ⋙ pf ≅ ef ⋙ tS) (eG : tS ⋙ pg ≅ eg ⋙ tT)
    (eFG : tR ⋙ pb t₀ ≅ efg ⋙ tT) (κ : efg ≅ ef ⋙ eg)
    (H : eFG = Functor.isoWhiskerLeft tR (σ ≪≫ β.symm) ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eF pg ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ef eG ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight κ.symm tT)
    (P : HomologicalComplex V c) :
    (mapHomologicalComplexCompIsoOf eFG c).hom.app P =
      eqToHom (congrArg (fun t => ((pb t).mapHomologicalComplex c).obj
        ((tR.mapHomologicalComplex c).obj P)) h) ≫
      (NatIso.mapHomologicalComplex β c).inv.app ((tR.mapHomologicalComplex c).obj P) ≫
      (pg.mapHomologicalComplex c).map ((mapHomologicalComplexCompIsoOf eF c).hom.app P) ≫
      (mapHomologicalComplexCompIsoOf eG c).hom.app ((ef.mapHomologicalComplex c).obj P) ≫
      (tT.mapHomologicalComplex c).map ((NatIso.mapHomologicalComplex κ c).inv.app P) := by
  subst H h
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  simp [hσ]

variable (R S T : CommRingCat.{u}) (f : R ⟶ S) (g : S ⟶ T)

/-- Stacks 01I9 on complexes is compatible with composition. -/
theorem tildePullbackComplexIso_comp_hom_app (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tildePullbackComplexIso R T (f ≫ g)).hom.app P =
      eqToHom (congrArg (fun t => ((Scheme.Modules.pullback t).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (Spec.map_comp f g)) ≫
      (NatIso.mapHomologicalComplex (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f))
        (ComplexShape.up ℤ)).inv.app
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
      ((Scheme.Modules.pullback (Spec.map g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((tildePullbackComplexIso R S f).hom.app P) ≫
      (tildePullbackComplexIso S T g).hom.app
        (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≫
      ((tilde.functor T).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} f.hom g.hom)
          (ComplexShape.up ℤ)).inv.app P) :=
  mapHomologicalComplexCompIsoOf_comp_hom_app (pb := Scheme.Modules.pullback) (Spec.map_comp f g)
    (Scheme.Modules.pullbackCongr (Spec.map_comp f g)) (pullbackCongr_hom_app_eq _)
    (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)) (pullbackTildeIso R S f)
    (pullbackTildeIso S T g) (pullbackTildeIso R T (f ≫ g))
    (ModuleCat.extendScalarsComp.{u, u} f.hom g.hom) (pullbackTildeIso_comp R S T f g) P

/-- **The composition law of Stacks 08DW.** For ring maps `f : R ⟶ S` and `g : S ⟶ T`, the
affine comparison for `f ≫ g` is the comparison for `f` pulled back along `Spec g`, followed by the
comparison for `g`, modulo the composition isomorphisms of derived pullback and of derived
extension of scalars. -/
theorem affinePullbackComparison_comp_derivedPullbackCompIso
    (N : DerivedCategory (ModuleCat.{u} R)) :
    (affinePullbackComparison R T (f ≫ g)).hom.app N =
      eqToHom (congrArg (fun t => (Stacks.Duality.derivedPullback t).obj
        ((tilde.functor R).mapDerivedCategory.obj N)) (Spec.map_comp f g)) ≫
      (Stacks.Duality.derivedPullbackCompIso (Spec.map g) (Spec.map f)).inv.app _ ≫
      (Stacks.Duality.derivedPullback (Spec.map g)).map
        ((affinePullbackComparison R S f).hom.app N) ≫
      (affinePullbackComparison S T g).hom.app _ ≫
      (tilde.functor T).mapDerivedCategory.map
        ((totalDerivedExtensionScalarsComp.{u, u} f.hom g.hom).hom.app N) := by
  have := isLeftDerivedFunctor_extendScalarsTilde R T (f ≫ g)
  have e := Functor.leftDerived_ext
    ((totalDerivedExtensionScalars.{u, u, u} (f ≫ g).hom).functor ⋙
      (tilde.functor T).mapDerivedCategory)
    (extendScalarsTildeComparison R T (f ≫ g))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    ((tilde.functor R).mapDerivedCategory ⋙ Stacks.Duality.derivedPullback (Spec.map (f ≫ g)))
    (affinePullbackComparison R T (f ≫ g)).hom
    { app := fun N => eqToHom (congrArg (fun t => (Stacks.Duality.derivedPullback t).obj
          ((tilde.functor R).mapDerivedCategory.obj N)) (Spec.map_comp f g)) ≫
        (Stacks.Duality.derivedPullbackCompIso (Spec.map g) (Spec.map f)).inv.app _ ≫
        (Stacks.Duality.derivedPullback (Spec.map g)).map
          ((affinePullbackComparison R S f).hom.app N) ≫
        (affinePullbackComparison S T g).hom.app _ ≫
        (tilde.functor T).mapDerivedCategory.map
          ((totalDerivedExtensionScalarsComp.{u, u} f.hom g.hom).hom.app N)
      naturality := fun N N' φ =>
        affinePullbackComparison_comp_naturality_chase
          (Stacks.Duality.derivedPullback (Spec.map g)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (Stacks.Duality.derivedPullback_map_comp_eqToHom (Spec.map_comp f g) _)
          ((Stacks.Duality.derivedPullbackCompIso (Spec.map g) (Spec.map f)).inv.naturality _)
          ((affinePullbackComparison R S f).hom.naturality φ)
          ((affinePullbackComparison S T g).hom.naturality
            ((totalDerivedExtensionScalars.{u, u, u} f.hom).functor.map φ))
          (((tilde.functor T).mapDerivedCategory.map_comp _ _).symm.trans
            ((congrArg (tilde.functor T).mapDerivedCategory.map
              ((totalDerivedExtensionScalarsComp.{u, u} f.hom g.hom).hom.naturality φ)).trans
              ((tilde.functor T).mapDerivedCategory.map_comp _ _))) } ?_
  · exact congrArg (fun t => NatTrans.app t N) e
  ext P
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [affinePullbackComparison_fac, tildeDerivedPullbackComparison_app,
    tildePullbackComplexCompQIso_hom_app]
  simp only [Category.assoc]
  refine affinePullbackComparison_comp_chase (Stacks.Duality.derivedPullback (Spec.map g))
    _ _ _ _ _ _ _ _ _
    (t₁ := (tilde.functor T).mapDerivedCategory.map
      ((totalDerivedExtensionScalars.{u, u, u} g.hom).functor.map
        ((totalDerivedExtensionScalars.{u, u, u} f.hom).comparison.app P)))
    (t₂ := (tilde.functor T).mapDerivedCategory.map
      ((totalDerivedExtensionScalars.{u, u, u} g.hom).comparison.app
        (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)))
    (fT := (tilde.functor T).mapDerivedCategoryFactors.hom.app
      (((ModuleCat.extendScalars.{u, u, u} g.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)))
    (qe := DerivedCategory.Q.map (((tilde.functor T).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} f.hom g.hom)
        (ComplexShape.up ℤ)).inv.app P)))
    (s := (tilde.functor S).mapDerivedCategory.map
      ((totalDerivedExtensionScalars.{u, u, u} f.hom).comparison.app P))
    (gG' := (affinePullbackComparison S T g).hom.app (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)))
    (fS := (tilde.functor S).mapDerivedCategoryFactors.hom.app
      (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (dg := (Stacks.DerivedPullback.derivedPullbackComplexComparison
      (Spec.map g).toLRSHom.toShHom).app (((tilde.functor S).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)))
    (qg := DerivedCategory.Q.map ((tildePullbackComplexIso S T g).hom.app
      (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)))
    (lfr := (Stacks.Duality.derivedPullback (Spec.map f)).map
      ((tilde.functor R).mapDerivedCategoryFactors.hom.app P))
    (df := (Stacks.DerivedPullback.derivedPullbackComplexComparison
      (Spec.map f).toLRSHom.toShHom).app (((tilde.functor R).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P))
    (qf := DerivedCategory.Q.map ((tildePullbackComplexIso R S f).hom.app P))
    (dg' := (Stacks.DerivedPullback.derivedPullbackComplexComparison
      (Spec.map g).toLRSHom.toShHom).app
        (((Scheme.Modules.pullback (Spec.map f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
    (qg' := DerivedCategory.Q.map (((Scheme.Modules.pullback (Spec.map g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ((tildePullbackComplexIso R S f).hom.app P)))
    (l₁' := (Stacks.Duality.derivedPullback (Spec.map g ≫ Spec.map f)).map
      ((tilde.functor R).mapDerivedCategoryFactors.hom.app P))
    (c' := (Stacks.Duality.derivedPullbackCompIso (Spec.map g) (Spec.map f)).inv.app
      (DerivedCategory.Q.obj (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
    (dgf := (Stacks.DerivedPullback.derivedPullbackComplexComparison
      (Spec.map g ≫ Spec.map f).toLRSHom.toShHom).app (((tilde.functor R).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P))
    (qpc := DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
      (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)) (ComplexShape.up ℤ)).inv.app
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
    (qeq := DerivedCategory.Q.map (eqToHom (congrArg
      (fun t => ((Scheme.Modules.pullback t).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
      (Spec.map_comp f g))))
    ?hκ ?hG ?hg ?hf ?hdg ?hC ?hfac ?hE ?hdeg
  case hκ =>
    refine (congrArg (_ ≫ ·) (extendScalarsTildeComparison_app R T (f ≫ g) P)).trans ?_
    refine (Functor.map_comp_assoc _ _ _ _).symm.trans ?_
    have hc := totalDerivedExtensionScalarsComp_comparison.{u, u} f.hom g.hom P
    have hn := (tilde.functor T).mapDerivedCategoryFactors.hom.naturality
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} f.hom g.hom)
        (ComplexShape.up ℤ)).inv.app P)
    refine (congrArg (fun x => (tilde.functor T).mapDerivedCategory.map x ≫
      (tilde.functor T).mapDerivedCategoryFactors.hom.app _) hc.symm).trans ?_
    exact (Functor.map_comp_assoc _ _ _ _).trans (congrArg (_ ≫ ·)
      ((Functor.map_comp_assoc _ _ _ _).trans (congrArg (_ ≫ ·) hn)))
  case hG => exact ((affinePullbackComparison S T g).hom.naturality
      ((totalDerivedExtensionScalars.{u, u, u} f.hom).comparison.app P)).symm
  case hg | hf =>
    erw [← extendScalarsTildeComparison_app, affinePullbackComparison_fac,
      tildeDerivedPullbackComparison_app, tildePullbackComplexCompQIso_hom_app, Category.assoc]
    rfl
  case hdg => exact (Stacks.DerivedPullback.derivedPullbackComplexComparison
      (Spec.map g).toLRSHom.toShHom).naturality ((tildePullbackComplexIso R S f).hom.app P)
  case hC => exact ((Stacks.Duality.derivedPullbackCompIso (Spec.map g) (Spec.map f)).inv.naturality
      ((tilde.functor R).mapDerivedCategoryFactors.hom.app P)).symm
  case hfac => exact derivedPullbackCompIso_inv_app_complexComparison' (Spec.map g) (Spec.map f) _
  case hE => exact eqToHom_derivedPullback_complexComparison (Spec.map_comp f g) _
  case hdeg =>
    exact map_eq_comp₅ DerivedCategory.Q (tildePullbackComplexIso_comp_hom_app R S T f g P)

end AlgebraicGeometry
