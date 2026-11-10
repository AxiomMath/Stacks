module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LimitConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ChangeOfRings
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZariskiDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekInputs
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.Separated
public import StacksFrontier.AlgebraicGeometry.Limits.EventuallySeparatedOverBase
public import StacksFrontier.AlgebraicGeometry.Limits.CoproductSeparated
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Examples

/-!
# Constructibility of `Rf_!` over an arbitrary base

Let `f : X ⟶ Y` be separated, locally of finite presentation and quasi-compact, `Λ` a Noetherian
ring and `F` a constructible sheaf of `Λ`-modules on `X`. If `Λ` is torsion, then every cohomology
sheaf of `Rf_! F` is constructible; if `X` is quasi-compact and quasi-separated (for instance if
`Y` is Noetherian), the same holds for every Noetherian `Λ` and every torsion constructible `F`.
This is the passage from a Nagata base to an arbitrary base in
the proofs of Stacks 0GKZ and 0GL0.

The question is local on `Y` (Stacks 095F and base change, Stacks 0F7L), so `Y = Spec R` is
affine. Write `R` as the union of its finitely generated subrings `ℤ[s]`. Then `f` descends to a
model over some `Spec ℤ[s₀]` (Stacks 01ZM), the model becomes separated over a later stage (its
limit is separated, Stacks 086Q), and the stages of the base change system of the model are
Noetherian Nagata schemes (Stacks 035B); so
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_stage`
applies. On a quasi-compact quasi-separated `X` a torsion constructible sheaf is annihilated by an
integer `N`, and `Λ` is replaced by `Λ/NΛ`
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_quotient`).

Stacks 0GKV enters as the hypothesis `h0GKV`, and Stacks 09YU (essential surjectivity for the
colimit of the categories of constructible sheaves) as `h09YU`, until they land.

The statements are made in the standard model of the derived category
(`HasDerivedCategory.standard`), in which `Rf_!` and
`Stacks.EtaleCohomology.LowerShriekConstructibilityInput` are stated.

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_isAffine_base`.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_torsion`.
* `Stacks.EtaleCohomology.lowerShriekConstructibilityInput_of_stages`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Opposite

universe u

namespace AlgebraicGeometry

/-- The cone exhibiting an affine scheme `Y` as the limit of the spectra of the finitely
generated subrings of `Γ(Y, ⊤)`, with vertex `Y` itself. -/
def affineAdjoinFinsetCone (Y : Scheme.{u}) [IsAffine Y] :
    Cone (specAdjoinFinsetDiagram Γ(Y, ⊤)) :=
  (specAdjoinFinsetCone Γ(Y, ⊤)).extend Y.isoSpec.hom

/-- `AlgebraicGeometry.affineAdjoinFinsetCone` is a limit cone. -/
def isLimitAffineAdjoinFinsetCone (Y : Scheme.{u}) [IsAffine Y] :
    IsLimit (affineAdjoinFinsetCone Y) :=
  IsLimit.ofIsoLimit (isLimit_specAdjoinFinsetCone Γ(Y, ⊤))
    (Cone.extendIso (specAdjoinFinsetCone Γ(Y, ⊤))
      (Y.isoSpec.symm : (specAdjoinFinsetCone Γ(Y, ⊤)).pt ≅ Y))

/-- The spectrum of a finitely generated subring of a ring of global sections is an object of every
big étale site, being of finite type over `Spec ℤ`. -/
theorem BigEtaleSite.contains_specAdjoinFinsetDiagram_obj (B : BigEtaleSite.{u}) {R : Type u}
    [CommRing R] (i : (Finset R)ᵒᵖ) : B.Contains ((specAdjoinFinsetDiagram R).obj i) := by
  have := locallyOfFiniteType_terminalFrom_specAdjoinFinsetDiagram_obj R i
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
    (terminal.from ((specAdjoinFinsetDiagram R).obj i)) B.contains_terminal

/-- The spectrum of a finitely generated subring of a ring is a Nagata scheme (Stacks 035B). -/
theorem isNagataScheme_specAdjoinFinsetDiagram_obj {R : Type u} [CommRing R]
    (i : (Finset R)ᵒᵖ) : IsNagataScheme ((specAdjoinFinsetDiagram R).obj i) := by
  have := locallyOfFiniteType_terminalFrom_specAdjoinFinsetDiagram_obj R i
  exact isNagataScheme_of_locallyOfFiniteType_over_uliftInt
    (terminal.from _ ≫ (terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal).hom)

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

variable (B : BigEtaleSite.{u})

/-- The pullback of a quasi-compact morphism along a map from a compact space is compact. -/
private theorem compactSpace_pullback {A S T : Scheme.{u}} (a : A ⟶ S) (P : T ⟶ S)
    [QuasiCompact P] [CompactSpace A] : CompactSpace ↑(pullback a P) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.fst a P)

/-- The pullback of a quasi-separated morphism along a map from a quasi-separated space is
quasi-separated. -/
private theorem quasiSeparatedSpace_pullback {A S T : Scheme.{u}} (a : A ⟶ S) (P : T ⟶ S)
    [QuasiSeparated P] [QuasiSeparatedSpace A] : QuasiSeparatedSpace ↑(pullback a P) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst a P)

/-- **`Rf_! F` is constructible when `f` has a separated model over a stage of the Noetherian
approximation of a base.** Let `Y` be the limit, with limit cone `c₀`, of the spectra of the
finitely generated subrings `ℤ[t]` of a ring `R`, `f : X ⟶ Y` separated of finite type, and
suppose `f` is the base change of a separated morphism `P : X₁ ⟶ Spec ℤ[s]` of
finite type along `Y ⟶ Spec ℤ[s]`, for a finite subset `s` of `R`. The base changes
`X_t = X₁ ×_{Spec ℤ[s]} Spec ℤ[t]`, `t ⊇ s`, form an inverse system with limit `X` whose stages are
separated of finite type over the Noetherian Nagata schemes `Spec ℤ[t]`, so
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_stage` applies.
`h0GKV` is Stacks 0GKV and `h09YU` is Stacks 09YU. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_separated_model
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (h09YU : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt), IsLimit c →
      (∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e))) →
      (∀ p : I, CompactSpace (Dg.obj (op p)).obj) →
      (∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) →
      SmallEtaleStagesEssSurj B (ModuleCat.{u + 1} Λ) Dg c hX
        (fun Z => IsConstructibleModuleSheaf B Z Λ))
    (R : Type u) [CommRing R] (c₀ : Cone (specAdjoinFinsetDiagram R)) (hc₀ : IsLimit c₀)
    (hY : B.Contains c₀.pt) [CompactSpace c₀.pt] [QuasiSeparatedSpace c₀.pt]
    (X : B.Scheme) (f : X.obj ⟶ c₀.pt) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (s : Finset R)
    (P : Over ((specAdjoinFinsetDiagram R).obj (op s))) [IsSeparated P.hom]
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] (g : X.obj ⟶ P.left)
    (hsq : IsPullback g f P.hom (c₀.π.app (op s)))
    (j : CompactificationOf (Over.mk f)) (F : EtaleModules.{u, 0} Λ X.obj)
    (hF : IsBigSiteConstructibleEtaleModule B X Λ F) (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B (B.obj c₀.pt hY) Λ
      ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          F))) := by
  classical
  have : IsCofiltered (Finset R)ᵒᵖ := isCofiltered_op_of_isFiltered _
  have : QuasiSeparated P.hom := IsSeparated.instQuasiSeparated _
  let Φ := finsetAboveToOver R s
  let DXs : (FinsetAbove R
      s)ᵒᵖ ⥤ Scheme.{u} := Φ ⋙ Scheme.baseChangeDiagram (specAdjoinFinsetDiagram R) (op s) P
  let DYs : (FinsetAbove R s)ᵒᵖ ⥤ Scheme.{u} := Φ ⋙ Over.forget (op s) ⋙ (specAdjoinFinsetDiagram R)
  -- the stages
  have hsqt : ∀ t : (FinsetAbove R s)ᵒᵖ, IsPullback (pullback.snd ((specAdjoinFinsetDiagram R).map
      (Φ.obj t).hom) P.hom)
      (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom)
          P.hom) P.hom ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) := fun t =>
    (IsPullback.of_hasPullback ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) P.hom).flip
  have hlft : ∀ t : (FinsetAbove R s)ᵒᵖ,
      LocallyOfFiniteType (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom)
          P.hom) := fun t =>
    MorphismProperty.of_isPullback (hsqt t) ‹_›
  have hqc : ∀ t : (FinsetAbove R s)ᵒᵖ,
      QuasiCompact (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) P.hom) := fun t =>
    MorphismProperty.of_isPullback (hsqt t) ‹_›
  have hsep : ∀ t : (FinsetAbove R s)ᵒᵖ,
      IsSeparated (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) P.hom) := fun t =>
    MorphismProperty.of_isPullback (hsqt t) ‹_›
  have hYB : ∀ t : (FinsetAbove R s)ᵒᵖ, B.Contains (DYs.obj t) := fun t =>
    B.contains_specAdjoinFinsetDiagram_obj _
  have hXB : ∀ t : (FinsetAbove R s)ᵒᵖ, B.Contains (DXs.obj t) := fun t => by
    have := hlft t
    have := hqc t
    have h := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
      (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) P.hom) (hYB t)
    exact h
  have hXc : ∀ t : (FinsetAbove R s)ᵒᵖ, CompactSpace (DXs.obj t) := fun t =>
    have := hqc t
    compactSpace_pullback ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) P.hom
  have hXq : ∀ t : (FinsetAbove R s)ᵒᵖ, QuasiSeparatedSpace (DXs.obj t) := fun t =>
    quasiSeparatedSpace_pullback ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) P.hom
  let DX : (FinsetAbove R s)ᵒᵖ ⥤ B.Scheme := ObjectProperty.lift _ DXs hXB
  let DY : (FinsetAbove R s)ᵒᵖ ⥤ B.Scheme := ObjectProperty.lift _ DYs hYB
  let φ : DX ⟶ DY :=
    { app := fun t => ObjectProperty.homMk (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj
        t).hom) P.hom)
      naturality := fun t t' e => B.inclusion.map_injective
        (by exact Scheme.baseChangeDiagram_map_fst (specAdjoinFinsetDiagram R) (op s) P (Φ.map e)) }
  -- the limit cone with vertex `X`
  let c' : Cone DXs := (Scheme.baseChangeCone (specAdjoinFinsetDiagram R) (op s) P c₀).whisker Φ
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv Φ _).symm
    (Scheme.isLimitBaseChangeCone (specAdjoinFinsetDiagram R) (op s) P c₀ hc₀)
  let eX : X.obj ≅ pullback (c₀.π.app (op s)) P.hom := hsq.flip.isoPullback
  let cX : Cone (DX ⋙ B.inclusion) := c'.extend eX.hom
  have hcX : IsLimit cX := IsLimit.ofIsoLimit hc' (Cone.extendIso c' eX.symm)
  have hleg_fst : ∀ t : (FinsetAbove R s)ᵒᵖ,
      cX.π.app t ≫ pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj
          t).hom) P.hom = f ≫ c₀.π.app (Φ.obj t).left := by
    intro t
    exact (Category.assoc _ _ _).trans
      ((congrArg (eX.hom ≫ ·) (Scheme.baseChangeCone_π_fst _ _ _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hsq.flip.isoPullback_hom_fst)))
  have hleg_snd : ∀ t : (FinsetAbove R s)ᵒᵖ,
      cX.π.app t ≫ pullback.snd ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) P.hom = g := by
    intro t
    exact (Category.assoc _ _ _).trans
      ((congrArg (eX.hom ≫ ·) (Scheme.baseChangeCone_π_snd _ _ _ _ _)).trans
        hsq.flip.isoPullback_hom_snd)
  have hsqs : ∀ t : FinsetAbove R s, IsPullback (cX.π.app (op t)) f
      (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj (op t)).hom) P.hom) (c₀.π.app (Φ.obj
          (op t)).left) := by
    intro t
    refine IsPullback.of_right ?_ (hleg_fst (op t)) (hsqt (op t))
    rw [hleg_snd, c₀.w]
    exact hsq
  have haff : ∀ {t t' : (FinsetAbove R s)ᵒᵖ} (e : t ⟶ t'),
      IsAffineHom (B.inclusion.map (DX.map e)) := fun e =>
    Scheme.isAffineHom_baseChangeDiagram_map (specAdjoinFinsetDiagram R) (op s) P (Φ.map e)
  exact isConstructibleEtaleModule_homology_derivedLowerShriek_of_stage B Λ m hm hΛ h0GKV DX DY φ
    cX X.property (fun t => isNoetherian_specAdjoinFinsetDiagram_obj R _)
    (fun t => isNagataScheme_specAdjoinFinsetDiagram_obj _)
    (fun t => ⟨hsep (op t), hlft (op t), hqc (op t)⟩) (B.obj c₀.pt hY) f
    (fun t => ObjectProperty.homMk (c₀.π.app (op t.1))) hsqs j
    (h09YU DX cX X.property hcX haff (fun t => hXc (op t)) (fun t => hXq (op t))) F hF k

/-- **Stacks 0GL0 over the limit `Y` of the spectra of the finitely generated subrings of a ring
`R`, for a torsion coefficient ring, from Stacks 0GKV and Stacks 09YU.** Let `Y` (separated,
quasi-compact) be the vertex of a limit cone `c₀` over the spectra `Spec ℤ[t]`, `f : X ⟶ Y`
separated, locally of finite presentation and quasi-compact, `Λ` a Noetherian ring with `m = 0` in
`Λ` for some `m > 0`, and `F` a constructible sheaf of `Λ`-modules on `X`. Then every cohomology
sheaf of `Rf_! F` is constructible. `f` descends to a model over a stage `Spec ℤ[s₀]` (Stacks
01ZM); the model's base change system has limit `X`, which is separated, so a later stage is
separated (Stacks 086Q) and
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_separated_model`
applies to it. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_adjoinFinset_limit
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (h09YU : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt), IsLimit c →
      (∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e))) →
      (∀ p : I, CompactSpace (Dg.obj (op p)).obj) →
      (∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) →
      SmallEtaleStagesEssSurj B (ModuleCat.{u + 1} Λ) Dg c hX
        (fun Z => IsConstructibleModuleSheaf B Z Λ))
    (R : Type u) [CommRing R] (c₀ : Cone (specAdjoinFinsetDiagram R)) (hc₀ : IsLimit c₀)
    (hY : B.Contains c₀.pt) [CompactSpace c₀.pt] [QuasiSeparatedSpace c₀.pt] [c₀.pt.IsSeparated]
    (X : B.Scheme) (f : X.obj ⟶ c₀.pt) [IsSeparated f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] (j : CompactificationOf (Over.mk f))
    (F : EtaleModules.{u, 0} Λ X.obj) (hF : IsBigSiteConstructibleEtaleModule B X Λ F) (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B (B.obj c₀.pt hY) Λ
      ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          F))) := by
  classical
  have : IsCofiltered (Finset R)ᵒᵖ := isCofiltered_op_of_isFiltered _
  have : QuasiSeparated f := IsSeparated.instQuasiSeparated f
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X.obj := quasiSeparatedSpace_of_quasiSeparated f
  have hfp := finitePresentation_of_compactSpace f inferInstance
  obtain ⟨i, X₀, p, g, hp, hpb⟩ :=
    LimitDescent.exists_isPullback_of_finitePresentation_of_essentiallySmall
      (specAdjoinFinsetDiagram R) c₀ hc₀ f hfp
  let s₀ : Finset R := i.unop
  let Φ := finsetAboveToOver R s₀
  let P₀ : Over ((specAdjoinFinsetDiagram R).obj (op s₀)) := Over.mk p
  have : LocallyOfFinitePresentation P₀.hom := hp.1
  have : LocallyOfFiniteType P₀.hom := inferInstance
  have : QuasiCompact P₀.hom := hp.2.1
  have : QuasiSeparated P₀.hom := hp.2.2
  have hpb' : IsPullback g f P₀.hom (c₀.π.app (op s₀)) := hpb
  have hXc : ∀ t : FinsetAbove R s₀,
      CompactSpace ((Φ ⋙ Scheme.baseChangeDiagram (specAdjoinFinsetDiagram R) (op s₀) P₀).obj (op
          t)) := fun t =>
    compactSpace_pullback ((specAdjoinFinsetDiagram R).map (Φ.obj (op t)).hom) P₀.hom
  have hXq : ∀ t : FinsetAbove R s₀,
      QuasiSeparatedSpace ((Φ ⋙ Scheme.baseChangeDiagram (specAdjoinFinsetDiagram R) (op s₀)
          P₀).obj (op t)) := fun t =>
    quasiSeparatedSpace_pullback ((specAdjoinFinsetDiagram R).map (Φ.obj (op t)).hom) P₀.hom
  let d : DescentSituation.{u, u} (FinsetAbove R s₀) :=
    { system := Φ ⋙ Scheme.baseChangeDiagram (specAdjoinFinsetDiagram R) (op s₀) P₀
      transition_affine := fun e =>
        Scheme.isAffineHom_baseChangeDiagram_map (specAdjoinFinsetDiagram R) (op s₀) P₀ (Φ.map e)
      quasiCompact := hXc
      quasiSeparated := hXq
      limitCone := (Scheme.baseChangeCone (specAdjoinFinsetDiagram R) (op s₀) P₀ c₀).whisker Φ
      isLimit := (Functor.Initial.isLimitWhiskerEquiv Φ _).symm
        (Scheme.isLimitBaseChangeCone (specAdjoinFinsetDiagram R) (op s₀) P₀ c₀ hc₀)
      base := ⟨s₀, le_rfl⟩ }
  -- the limit `X ×_{Spec ℤ[s₀]} Y ≅ X` is separated, so a later stage is separated
  have : X.obj.IsSeparated := Scheme.IsSeparated.of_isSeparated f
  have : d.limitCone.pt.IsSeparated := Scheme.IsSeparated.of_iso hpb'.flip.isoPullback
  obtain ⟨t₁, ht₁⟩ := eventually_isSeparated d
  let h₁ : op t₁.1 ⟶ op s₀ := (homOfLE t₁.2).op
  let P₁ : Over ((specAdjoinFinsetDiagram R).obj (op t₁.1)) :=
    Over.mk (pullback.fst ((specAdjoinFinsetDiagram R).map h₁) P₀.hom)
  have : P₁.left.IsSeparated := ht₁ t₁ le_rfl
  have hsq₁ := (IsPullback.of_hasPullback ((specAdjoinFinsetDiagram R).map h₁) P₀.hom).flip
  have : IsSeparated P₁.hom := isSeparated_of_isSeparated_source _
  have : LocallyOfFiniteType P₁.hom := MorphismProperty.of_isPullback hsq₁ ‹_›
  have : QuasiCompact P₁.hom := MorphismProperty.of_isPullback hsq₁ ‹_›
  let g₁ : X.obj ⟶ P₁.left :=
    pullback.lift (f ≫ c₀.π.app (op t₁.1)) g (by rw [Category.assoc, c₀.w]; exact hpb'.w.symm)
  have hg₁ : IsPullback g₁ f P₁.hom (c₀.π.app (op t₁.1)) := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) hsq₁
    rw [pullback.lift_snd, c₀.w]
    exact hpb'
  exact isConstructibleEtaleModule_homology_derivedLowerShriek_of_separated_model B Λ m hm hΛ h0GKV
    h09YU R c₀ hc₀ hY X f t₁.1 P₁ g₁ hg₁ j F hF k

/-- **Stacks 0GL0 over an affine base, for a torsion coefficient ring, from Stacks 0GKV and Stacks
09YU.** Let `Y` be an affine scheme of `B`, `f : X ⟶ Y` separated, locally of finite presentation
and quasi-compact, `Λ` a Noetherian ring with `m = 0` in `Λ` for some `m > 0`, and `F` a
constructible sheaf of `Λ`-modules on `X`. Then every cohomology sheaf of `Rf_! F` is
constructible: `Y` is the limit of the spectra of the finitely generated subrings of `Γ(Y, ⊤)`
(`isConstructibleEtaleModule_homology_derivedLowerShriek_of_adjoinFinset_limit`). -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_isAffine_base
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (h09YU : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt), IsLimit c →
      (∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e))) →
      (∀ p : I, CompactSpace (Dg.obj (op p)).obj) →
      (∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) →
      SmallEtaleStagesEssSurj B (ModuleCat.{u + 1} Λ) Dg c hX
        (fun Z => IsConstructibleModuleSheaf B Z Λ))
    (Y : B.Scheme) [IsAffine Y.obj] (X : B.Scheme) (f : X.obj ⟶ Y.obj) [IsSeparated f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] (j : CompactificationOf (Over.mk f))
    (F : EtaleModules.{u, 0} Λ X.obj) (hF : IsBigSiteConstructibleEtaleModule B X Λ F) (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          F))) := by
  have : CompactSpace (affineAdjoinFinsetCone Y.obj).pt := inferInstanceAs (CompactSpace Y.obj)
  have : QuasiSeparatedSpace (affineAdjoinFinsetCone Y.obj).pt :=
    inferInstanceAs (QuasiSeparatedSpace Y.obj)
  have : (affineAdjoinFinsetCone Y.obj).pt.IsSeparated := inferInstanceAs Y.obj.IsSeparated
  have : @IsSeparated X.obj (affineAdjoinFinsetCone Y.obj).pt f := ‹IsSeparated f›
  have : @LocallyOfFinitePresentation X.obj (affineAdjoinFinsetCone Y.obj).pt f :=
    ‹LocallyOfFinitePresentation f›
  have : @QuasiCompact X.obj (affineAdjoinFinsetCone Y.obj).pt f := ‹QuasiCompact f›
  exact isConstructibleEtaleModule_homology_derivedLowerShriek_of_adjoinFinset_limit B Λ m hm hΛ
    h0GKV h09YU Γ(Y.obj, ⊤) (affineAdjoinFinsetCone Y.obj) (isLimitAffineAdjoinFinsetCone Y.obj)
    Y.property X f j F hF k

/-- **Stacks 0GL0 for sheaves, for a torsion coefficient ring, from Stacks 0GKV and Stacks 09YU.**
Let `f : X ⟶ Y` be a separated, locally finitely presented, quasi-compact morphism of schemes of
`B`, `j` a compactification of `f`, `Λ` a Noetherian ring with `m = 0` in `Λ` for some `m > 0`,
and `F` a constructible sheaf of `Λ`-modules on `X`. Then every cohomology sheaf of `Rf_! F` is
constructible. The question is local on `Y` (Stacks 095F): over an affine open `W ⊆ Y` base change
(Stacks 0F7L) identifies the restriction of `Rf_! F` with `R(f_W)_!(F|_{X_W})`, constructible by
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_isAffine_base`. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_torsion
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (h09YU : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt), IsLimit c →
      (∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e))) →
      (∀ p : I, CompactSpace (Dg.obj (op p)).obj) →
      (∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) →
      SmallEtaleStagesEssSurj B (ModuleCat.{u + 1} Λ) Dg c hX
        (fun Z => IsConstructibleModuleSheaf B Z Λ))
    {X Y : B.Scheme} (f : X.obj ⟶ Y.obj) [IsSeparated f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] (j : CompactificationOf (Over.mk f)) (F : EtaleModules.{u, 0} Λ X.obj)
    (hF : IsBigSiteConstructibleEtaleModule B X Λ F) (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          F))) := by
  let H := (DerivedCategory.Plus.homologyFunctor _ k).obj
    ((derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
  have hWB : ∀ W : Y.obj.affineOpens, B.Contains W.1.toScheme := fun W =>
    (Scheme.size_coe_opens_le Y.obj W.1).trans_lt Y.property
  let U : Y.obj.affineOpens → B.Scheme := fun W => B.obj _ (hWB W)
  let ι : ∀ W, U W ⟶ Y := fun W => ObjectProperty.homMk (Scheme.Opens.ι W.1)
  change IsConstructibleModuleSheaf B Y Λ ((etaleModulesToSmallEtale B Y Λ).obj H)
  refine isConstructibleModuleSheaf_of_openCover B Λ Y ((etaleModulesToSmallEtale B Y Λ).obj H) U ι
    (fun W => inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι W.1))) ?_ (fun W => ?_)
  · refine (Set.eq_univ_of_forall fun y => ?_).symm
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
      Y.obj.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact Set.mem_iUnion.2 ⟨⟨W, hW⟩, by
      change y ∈ Set.range (Scheme.Opens.ι W).base
      rw [Scheme.Opens.range_ι]
      exact hyW⟩
  let v : W.1.toScheme ⟶ Y.obj := Scheme.Opens.ι W.1
  have : IsAffine (U W).obj := W.2
  have sq := IsPullback.of_hasPullback f v
  let fW := pullback.snd f v
  have : IsSeparated fW := MorphismProperty.of_isPullback sq ‹IsSeparated f›
  have : LocallyOfFinitePresentation fW := MorphismProperty.of_isPullback sq ‹_›
  have : QuasiCompact fW := MorphismProperty.of_isPullback sq ‹_›
  have : LocallyOfFiniteType fW := inferInstance
  have hXW : B.Contains (pullback f v) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact fW (hWB W)
  let XW : B.Scheme := B.obj (pullback f v) hXW
  let gB : XW ⟶ X := ObjectProperty.homMk (pullback.fst f v)
  have hFW := isConstructibleEtaleModule_inverseImage B Λ gB hF
  have hc := isConstructibleEtaleModule_homology_derivedLowerShriek_of_isAffine_base B Λ m hm hΛ
    h0GKV h09YU (U W) XW fW (j.baseChange sq) _ hFW k
  -- base change (Stacks 0F7L)
  let K := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X.obj) 0).obj F
  have hKt : isTorsionPlus.{u, 0} Λ X.obj K := fun _ =>
    isTorsionEtaleModule_of_natCast_eq_zero Λ m hm hΛ _
  have := isIso_derivedLowerShriekBaseChange_app Λ sq j K hKt
  let eBC := asIso ((derivedLowerShriekBaseChange.{u, 0} Λ sq j).app K)
  obtain ⟨e₁⟩ := nonempty_homology_etaleModuleDerivedInverseImagePlus_iso Λ v
    ((derivedLowerShriek.{u, 0} f j Λ).obj K) k
  obtain ⟨e₂⟩ := nonempty_inverseImage_singleFunctor_iso (Λ := Λ) (pullback.fst f v) F
  have hU : IsBigSiteConstructibleEtaleModule B (U W) Λ
      ((etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map (ι W))).obj H) :=
    IsBigSiteConstructibleEtaleModule.of_iso B Λ
      (((DerivedCategory.Plus.homologyFunctor _ k).mapIso
        (eBC ≪≫ (derivedLowerShriek.{u, 0} fW (j.baseChange sq) Λ).mapIso e₂)).symm ≪≫ e₁) hc
  exact isConstructibleModuleSheaf_congr B Λ (U W) (etaleModulesToSmallEtalePullbackIso B Λ (ι W) H)
    hU

/-- **`Stacks.EtaleCohomology.LowerShriekConstructibilityInput` from Stacks 0GKV and Stacks
09YU** (Stacks 0GL0 for sheaves over a Noetherian base): for `f : X ⟶ Y` separated of finite type
with `Y` Noetherian, a Noetherian ring `Λ` and a constructible torsion sheaf `F` of `Λ`-modules on
`X`, every cohomology sheaf of `Rf_! F` is constructible. `X` is quasi-compact and
quasi-separated, so `F` is annihilated by an integer `N > 0` and `Λ` may be replaced by `Λ/NΛ`
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_quotient`), and
`f` is of finite presentation, so
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_torsion`
applies. -/
theorem lowerShriekConstructibilityInput_of_stages
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (h09YU : ∀ (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] {I : Type u} [Preorder I] [Nonempty I]
      [IsDirected I (· ≤ ·)] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
      (hX : B.Contains c.pt), IsLimit c →
      (∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e))) →
      (∀ p : I, CompactSpace (Dg.obj (op p)).obj) →
      (∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) →
      SmallEtaleStagesEssSurj B (ModuleCat.{u + 1} Λ) Dg c hX
        (fun Z => IsConstructibleModuleSheaf B Z Λ)) :
    LowerShriekConstructibilityInput B := by
  intro X Y _ f _ _ _ j Λ _ _ F hF ht n
  have : IsLocallyNoetherian Y.obj := IsNoetherian.toIsLocallyNoetherian
  have : IsLocallyNoetherian X.obj := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparated f := IsSeparated.instQuasiSeparated f
  have : QuasiSeparatedSpace X.obj := quasiSeparatedSpace_of_quasiSeparated f
  have : LocallyOfFinitePresentation f := inferInstance
  exact isConstructibleEtaleModule_homology_derivedLowerShriek_of_quotient B f j
    (fun Λ' _ _ m hm hΛ' G hG p => isConstructibleEtaleModule_homology_derivedLowerShriek_of_torsion
      B Λ' m hm hΛ' h0GKV (h09YU Λ') f j G hG p) Λ F hF ht n

end Stacks.EtaleCohomology

end
