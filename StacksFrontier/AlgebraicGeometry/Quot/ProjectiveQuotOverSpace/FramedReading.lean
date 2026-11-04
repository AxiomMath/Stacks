/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.Bridge
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.BaseReading
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SiteBridgeNaturality
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorSurjection
public meta import StacksFrontier.Tactic.KernelApply
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# Quotients over a framed base `h_W`, read on `ℙⁿ_W`

Let `F/X/B` be a Quot situation over `Spec ℤ` with a projective frame `X = B × ℙⁿ_ℤ` and an
identification `B ≅ h_W` with the algebraic space of a scheme `W`, so that `X ≅ h_{ℙⁿ_W}`
(`AlgebraicGeometry.ProjectiveQuotOverSpace.baseSpaceIso`).  Suppose the module is pulled back
from a module `F₀` on `h_{ℙⁿ_W}`, and write `G₀` for the Zariski reading of `F₀` on `ℙⁿ_W`.

For a test scheme `T` over `B` with structure morphism `a : T ⟶ W`, the reading of `F_T` on
`ℙⁿ_T` is identified with the inverse image of `G₀` along `ℙⁿ_T ⟶ ℙⁿ_W`
(`AlgebraicGeometry.ProjectiveQuotOverSpace.framedReadingIso`), and a submodule `K ⊆ F_T` is read
as a submodule of that inverse image (`AlgebraicGeometry.ProjectiveQuotOverSpace.framedSubobject`).
The main result is that this reading commutes with pullback of quotients: for `g : T ⟶ T''` over
`W`, the reading of the pullback of `K` along `g` is the base change along `ℙⁿ_T ⟶ ℙⁿ_{T''}` of
the reading of `K`.  The comparisons of inverse images are those of
`AlgebraicGeometry.ProjectiveQuot.readingFree_bracket`, whose spelling every statement here keeps.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuotOverSpace.framedReadingIso`
* `AlgebraicGeometry.ProjectiveQuotOverSpace.framedSubobject`

## Main results

* `AlgebraicGeometry.ProjectiveQuotOverSpace.framedSubobject_quotientPullback`

## Implementation notes

The comparisons pasted in the proofs come from different library lemmas, which spell the same
morphisms with differently written implicit categories and objects (for instance a scheme of the
site through `B` or through `AlgebraicGeometry.associatedBigEtaleSite B`).  The elaborator cannot
unify these spellings within its heartbeats, and the kernel unfolds rather than compares them at
projections such as `CategoryTheory.NatTrans.app`.  The pastings are therefore applied with
`kernel_have`, which reads the implicit arguments off the hypotheses without unification, and the
result is identified with the goal by `kernel_congr` or `heq_congr`, which hand the kernel the
spellings argument by argument (`StacksFrontier.Tactic.KernelApply`).

## References

* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

variable {B : BigFppfSite.{u}} {n : ℕ}
  {D : Space.QuotSituation B integerBase B.contains_integerBase} (E : ProjectiveFrame B n D)
  {W : BigFppfOver B integerBase B.contains_integerBase}
  (φ : schemeSpace W ≅ D.Y)

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-! ### Pasting lemmas in arbitrary categories -/

/-- Three functors carry an equation `a ≫ b = c ≫ d` to the same equation. -/
theorem map₃_comp_eq {𝒜 ℬ 𝒞 𝒟 : Type*} [Category* 𝒜] [Category* ℬ] [Category* 𝒞] [Category* 𝒟]
    {X Y Y' Z : 𝒜} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Y'} {d : Y' ⟶ Z} (h : a ≫ b = c ≫ d)
    (Z₀ : 𝒜 ⥤ ℬ) (Z₁ : ℬ ⥤ 𝒞) (Z₂ : 𝒞 ⥤ 𝒟) :
    Z₂.map (Z₁.map (Z₀.map a)) ≫ Z₂.map (Z₁.map (Z₀.map b)) =
      Z₂.map (Z₁.map (Z₀.map c)) ≫ Z₂.map (Z₁.map (Z₀.map d)) := by
  simp only [← Functor.map_comp, h]

/-- Four functors carry a composite to the composite. -/
theorem map₄_comp {𝒜' 𝒜 ℬ 𝒞 𝒟 : Type*} [Category* 𝒜'] [Category* 𝒜] [Category* ℬ] [Category* 𝒞]
    [Category* 𝒟] (Z' : 𝒜' ⥤ 𝒜) (Z₀ : 𝒜 ⥤ ℬ) (Z₁ : ℬ ⥤ 𝒞) (Z₂ : 𝒞 ⥤ 𝒟) {X Y Z : 𝒜'}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Z₂.map (Z₁.map (Z₀.map (Z'.map (f ≫ g)))) =
      Z₂.map (Z₁.map (Z₀.map (Z'.map f))) ≫ Z₂.map (Z₁.map (Z₀.map (Z'.map g))) := by
  simp only [Functor.map_comp]

/-- Kernels compared through an equation `M ≫ ci = Pb(z) ≫ Pb(t) ≫ Pb(u) ≫ Pb(x) ≫ dd` with
`ci`, `dd`, `z`, `t`, `u` invertible and `x` an epimorphism. -/
theorem kernelSubobject_eq_of_key' {C C₂ : Type*} [Category* C] [Category* C₂] [Abelian C]
    [Abelian C₂] (Pb : C₂ ⥤ C) {A₄ A₅ : C} {H H₁ H₂ H₃ H₄ : C₂} (M : Pb.obj H ⟶ A₄)
    (ci : A₄ ⟶ A₅) [IsIso ci] (z : H ⟶ H₁) (t : H₁ ⟶ H₂) (u : H₂ ⟶ H₃) (x : H₃ ⟶ H₄)
    [IsIso z] [IsIso t] [IsIso u] [Epi x] (dd : Pb.obj H₄ ⟶ A₅) [IsIso dd]
    (key : M ≫ ci = Pb.map z ≫ Pb.map t ≫ Pb.map u ≫ Pb.map x ≫ dd) :
    kernelSubobject M =
      kernelSubobject (Pb.map (cokernel.π (kernelSubobject ((z ≫ t ≫ u) ≫ x)).arrow)) := by
  have h₁ : M ≫ ci ≫ inv dd = Pb.map ((z ≫ t ≫ u) ≫ x) := by
    rw [← Category.assoc, IsIso.comp_inv_eq, key]
    simp only [Functor.map_comp, Category.assoc]
  have h₂ : Pb.map ((z ≫ t ≫ u) ≫ x) =
      Pb.map (cokernel.π (kernelSubobject ((z ≫ t ≫ u) ≫ x)).arrow) ≫
        Pb.map (Abelian.cokernelKernelSubobjectIso ((z ≫ t ≫ u) ≫ x)).hom := by
    rw [← Pb.map_comp]
    congr 1
    rw [← Abelian.cokernelKernelSubobjectIso_inv_comp ((z ≫ t ≫ u) ≫ x)]
    simp
  refine (kernelSubobject_comp_mono M (ci ≫ inv dd)).symm.trans ?_
  simp only [h₁, h₂, kernelSubobject_comp_mono]

/-- The equation chase behind `AlgebraicGeometry.ProjectiveQuotOverSpace.absSub_pullback`. -/
theorem key_of_paste' {C C₂ : Type*} [Category* C] [Category* C₂] (Pb : C₂ ⥤ C)
    {G A₁ A₂ A₃ A₄ A₅ A₆ A₇ B₁ B₂ : C} {H H₁ H₂ H₃ H₄ : C₂}
    {c₀ : Pb.obj H ⟶ G} {z : G ⟶ A₁} {t : A₁ ⟶ A₂} {u : A₂ ⟶ A₃} {x : A₃ ⟶ A₄} {ci : A₄ ⟶ A₅}
    {cm : A₃ ⟶ A₆} {rp : A₆ ⟶ A₅} {tr : A₂ ⟶ A₇} {rt : A₇ ⟶ A₆} {rf : A₇ ⟶ A₅}
    {z₂ : H ⟶ H₁} {t₂ : H₁ ⟶ H₂} {u₂ : H₂ ⟶ H₃} {x₂ : H₃ ⟶ H₄}
    {c₁ : Pb.obj H₂ ⟶ B₁} {c₂ : B₁ ⟶ A₇} {F₂ : Pb.obj H₂ ⟶ Pb.obj H₄} {d₁ : Pb.obj H₄ ⟶ B₂}
    {d₂ : B₂ ⟶ A₅}
    (hA : x ≫ ci = cm ≫ rp) (hB : u ≫ cm = tr ≫ rt) (hF : rf = rt ≫ rp)
    (hC : (Pb.map z₂ ≫ Pb.map t₂) ≫ (c₁ ≫ c₂) = c₀ ≫ z ≫ t ≫ tr)
    (hD : F₂ ≫ d₁ ≫ d₂ = (c₁ ≫ c₂) ≫ rf) (hF₂ : F₂ = Pb.map u₂ ≫ Pb.map x₂) :
    (c₀ ≫ (z ≫ t ≫ u) ≫ x) ≫ ci =
      Pb.map z₂ ≫ Pb.map t₂ ≫ Pb.map u₂ ≫ Pb.map x₂ ≫ d₁ ≫ d₂ := by
  subst hF hF₂
  simp only [Category.assoc] at hC hD ⊢
  rw [hA, reassoc_of% hB, ← reassoc_of% hC, ← hD]

/-- The chase behind
`AlgebraicGeometry.ProjectiveQuotOverSpace.framedModuleIso_hom_baseChangeComparison`, in arbitrary
categories: a coherence of comparisons `Fr ≅ Fp ⋙ Fk`, `Fk ≅ Fg ⋙ Ff`, `Fr ≅ Fq ⋙ Ff`,
`Fq ≅ Fp ⋙ Fg`, evaluated at `X` and followed by an isomorphism `Fp X ≅ M`. -/
theorem triangle_comp_app_mapIso {𝒜 ℬ 𝒞 𝒟 : Type*} [Category* 𝒜] [Category* ℬ] [Category* 𝒞]
    [Category* 𝒟] {Fp : 𝒜 ⥤ ℬ} {Fg : ℬ ⥤ 𝒞} {Ff : 𝒞 ⥤ 𝒟} {Fk : ℬ ⥤ 𝒟} {Fq : 𝒜 ⥤ 𝒞}
    {Fr : 𝒜 ⥤ 𝒟} {tkr : Fr ≅ Fp ⋙ Fk} {tk : Fk ≅ Fg ⋙ Ff} {tr : Fr ≅ Fq ⋙ Ff}
    {tq : Fq ≅ Fp ⋙ Fg}
    (h : tkr ≪≫ Functor.isoWhiskerLeft Fp tk =
      tr ≪≫ Functor.isoWhiskerRight tq Ff ≪≫ Functor.associator Fp Fg Ff) (X : 𝒜) {M : ℬ}
    (κ : M ≅ Fp.obj X) :
    (tkr.app X ≪≫ Fk.mapIso κ.symm).hom ≫ tk.hom.app M =
      tr.hom.app X ≫ Ff.map (tq.app X ≪≫ Fg.mapIso κ.symm).hom := by
  have coh := ProjectiveQuot.triangle_comp_app h X
  have hn := tk.hom.naturality κ.inv
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    Functor.comp_map] at hn coh ⊢
  rw [hn, ← Category.assoc, coh, Category.assoc, Functor.map_comp]

/-- Kernels of morphisms out of the two ends of an isomorphism `c`. -/
theorem kernelSubobject_eq_inv_comp_of_comp {C : Type*} [Category* C] [Abelian C] {X' X Y Y' : C}
    {c : X' ⟶ X} [IsIso c] {M : X ⟶ Y} {N : X' ⟶ Y'}
    (h : kernelSubobject (c ≫ M) = kernelSubobject N) :
    kernelSubobject M = kernelSubobject (inv c ≫ N) := by
  have L : ∀ {Z : C} (f : X ⟶ Z), (Subobject.map c).obj (kernelSubobject (c ≫ f)) =
      kernelSubobject f := fun f => by
    show (Subobject.map c).obj (Subobject.mk (kernel.ι (c ≫ f))) = Subobject.mk (kernel.ι f)
    rw [Subobject.map_mk]
    exact Subobject.mk_eq_mk_of_comm _ _ (kernelIsIsoComp c f) (by simp)
  rw [← L M, h, ← L (inv c ≫ N)]
  simp only [IsIso.hom_inv_id_assoc]

/-- The represented algebraic space of a scheme of the site, in the spelling of
`AlgebraicGeometry.Space.representedSpaceMap`. -/
abbrev repSpace (V : BigFppfOver B integerBase B.contains_integerBase) :
    AlgebraicSpaces B integerBase B.contains_integerBase :=
  ⟨yoneda.obj V, isAlgebraicSpace_yoneda B integerBase B.contains_integerBase V⟩

/-- `h_{ℙⁿ_W} ≅ X`, with the source spelled as a represented algebraic space. -/
abbrev baseSpaceIsoY : repSpace (projectiveSite B n W) ≅ D.X :=
  baseSpaceIso E φ

/-- `h_{ℙⁿ_T} ≅ X_T`, with the source spelled as a represented algebraic space. -/
abbrev spaceIsoY (T : Space.SchemesOver D.Y) : repSpace (projectiveSite B n T.left) ≅ D.space T :=
  spaceIso E T

/-- The Zariski reading on a scheme `V` of the site of a module on `h_V`. -/
abbrev zariskiReading (V : BigFppfOver B integerBase B.contains_integerBase) :
    Space.Modules.{u, u} B integerBase B.contains_integerBase (repSpace V).1 (repSpace V).2 ⥤
      ((𝒯).obj V).Modules :=
  (Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase V).inverse ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj V) V.left.property

/-- The projection `X_T ⟶ X ≅ h_{ℙⁿ_W}`. -/
abbrev framedProjection (T : Space.SchemesOver D.Y) :
    D.space T ⟶ repSpace (projectiveSite B n W) :=
  D.sourceProjection T ≫ (baseSpaceIsoY E φ).inv

/-- `h_{ℙⁿ_T} ≅ X_T ⟶ h_{ℙⁿ_W}` is represented by `ℙⁿ_T ⟶ ℙⁿ_W`. -/
theorem spaceIsoY_hom_framedProjection (T : Space.SchemesOver D.Y) (a : T.left ⟶ W)
    (ha : T.hom = schemeSpaceMap a ≫ φ.hom) :
    (spaceIsoY E T).hom ≫ framedProjection E φ T =
      Space.representedSpaceMap B integerBase B.contains_integerBase (projectiveSiteMap B n a) := by
  have h : ((spaceIsoY E T).hom ≫ D.sourceProjection T) ≫ (baseSpaceIsoY E φ).inv =
      (schemeSpaceMap (projectiveSiteMap B n a) ≫ (baseSpaceIso E φ).hom) ≫
        (baseSpaceIso E φ).inv :=
    congrArg (· ≫ (baseSpaceIso E φ).inv) (spaceIso_hom_sourceProjection_eq E φ T a ha)
  rw [Category.assoc] at h
  rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]


/-! ### Readings over represented spaces, in the spelling of `readingFree_bracket` -/

section Abstract

variable {W₀ : BigFppfOver B integerBase B.contains_integerBase}

/-- The Zariski reading on `V` of the inverse image along `Y ≅ h_V` of a module on `Y`. -/
abbrev absReading {V : BigFppfOver B integerBase B.contains_integerBase}
    {Y : AlgebraicSpaces B integerBase B.contains_integerBase}
    (φV : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B integerBase B.contains_integerBase V⟩ :
      AlgebraicSpaces B integerBase B.contains_integerBase) ≅ Y)
    (N : Space.Modules.{u, u} B integerBase B.contains_integerBase Y.1 Y.2) :
    ((𝒯).obj V).Modules :=
  (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj V) V.left.property).obj
    ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
        V).inverse.obj
      ((Space.modulePullback B integerBase B.contains_integerBase φV.hom).obj N))

/-- **The reading of a module `N ≅ (Y ⟶ h_{W₀})^* F₀` on `V`, for `Y ≅ h_V`, is the inverse
image along `m : V ⟶ W₀` of the reading of `F₀`**, when `h_V ≅ Y ⟶ h_{W₀}` is represented by
`m`. -/
def absReadingHom {V : BigFppfOver B integerBase B.contains_integerBase}
    {Y : AlgebraicSpaces B integerBase B.contains_integerBase}
    (φV : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B integerBase B.contains_integerBase V⟩ :
      AlgebraicSpaces B integerBase B.contains_integerBase) ≅ Y)
    (spV : Y ⟶ (⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W₀⟩ :
      AlgebraicSpaces B integerBase B.contains_integerBase))
    (m : V ⟶ W₀)
    (hm : φV.hom ≫ spV = Space.representedSpaceMap B integerBase B.contains_integerBase m)
    (F₀ : Space.Modules.{u, u} B integerBase B.contains_integerBase (yoneda.obj W₀)
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W₀))
    (hF₀ : F₀.IsQuasicoherentOnSite)
    {N : Space.Modules.{u, u} B integerBase B.contains_integerBase Y.1 Y.2}
    (τ : (Space.modulePullback B integerBase B.contains_integerBase spV).obj F₀ ≅ N) :
    (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) m.left)).obj
      (Space.representedZariskiModule B integerBase B.contains_integerBase W₀ F₀) ⟶
      absReading φV N :=
  (Space.representedZariskiModulePullbackIso B integerBase B.contains_integerBase m
      (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase _)
      F₀ hF₀).hom ≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj V) V.left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
          V).inverse.map
        ((Space.modulePullbackTriangle B integerBase B.contains_integerBase hm).hom.app F₀)) ≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj V) V.left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
          V).inverse.map
        ((Space.modulePullback B integerBase B.contains_integerBase φV.hom).map τ.hom))

/-- **The reading of a pulled-back quotient is the pullback of the reading**, over represented
spaces. -/
theorem absSub_pullback {W W' : BigFppfOver B integerBase B.contains_integerBase}
    {X X' : AlgebraicSpaces B integerBase B.contains_integerBase}
    (pg : W' ⟶ W) (pa : W ⟶ W₀)
    (φ : (⟨yoneda.obj W, isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W⟩ :
      AlgebraicSpaces B integerBase B.contains_integerBase) ≅ X)
    (φ' : (⟨yoneda.obj W', isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W'⟩ :
      AlgebraicSpaces B integerBase B.contains_integerBase) ≅ X') (ρ : X' ⟶ X)
    (k : (⟨yoneda.obj W', isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W'⟩ :
      AlgebraicSpaces B integerBase B.contains_integerBase) ⟶ X)
    (hk : Space.representedSpaceMap B integerBase B.contains_integerBase pg ≫ φ.hom = k)
    (hsq : φ'.hom ≫ ρ = k)
    (sp : X ⟶ (⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W₀⟩ :
      AlgebraicSpaces B integerBase B.contains_integerBase))
    (sp' : X' ⟶ (⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W₀⟩ :
      AlgebraicSpaces B integerBase B.contains_integerBase))
    (hrel : ρ ≫ sp = sp')
    (hT : φ.hom ≫ sp = Space.representedSpaceMap B integerBase B.contains_integerBase pa)
    (hTc : φ'.hom ≫ sp' = Space.representedSpaceMap B integerBase B.contains_integerBase (pg ≫ pa))
    (F₀ : Space.Modules.{u, u} B integerBase B.contains_integerBase (yoneda.obj W₀)
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W₀))
    (hF₀ : F₀.IsQuasicoherentOnSite)
    {N : Space.Modules.{u, u} B integerBase B.contains_integerBase X.1 X.2}
    {N' : Space.Modules.{u, u} B integerBase B.contains_integerBase X'.1 X'.2}
    (τ : (Space.modulePullback B integerBase B.contains_integerBase sp).obj F₀ ≅ N)
    (τ' : (Space.modulePullback B integerBase B.contains_integerBase sp').obj F₀ ≅ N')
    (cmp : N' ≅ (Space.modulePullback B integerBase B.contains_integerBase ρ).obj N)
    (hB : τ'.hom ≫ cmp.hom = (Space.modulePullbackTriangle B integerBase B.contains_integerBase
      hrel).hom.app F₀ ≫ (Space.modulePullback B integerBase B.contains_integerBase ρ).map τ.hom)
    (K : Subobject N) (hK : (cokernel K.arrow).IsQuasicoherentOnSite) (K' : Subobject N')
    (ciso : cokernel K'.arrow ≅
      (Space.modulePullback B integerBase B.contains_integerBase ρ).obj (cokernel K.arrow))
    (hA : cokernel.π K'.arrow ≫ ciso.hom =
      cmp.hom ≫ (Space.modulePullback B integerBase B.contains_integerBase ρ).map
        (cokernel.π K.arrow))
    [Epi ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj W) W.left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
          W).inverse.map
        ((Space.modulePullback B integerBase B.contains_integerBase φ.hom).map
          (cokernel.π K.arrow))))] :
    kernelSubobject ((Scheme.Modules.pullbackComp
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) pg.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            pa.left)).hom.app
            (Space.representedZariskiModule B integerBase B.contains_integerBase W₀ F₀) ≫
      absReadingHom φ' sp' (pg ≫ pa) hTc F₀ hF₀ τ' ≫
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj W') W'.left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
          W').inverse.map
        ((Space.modulePullback B integerBase B.contains_integerBase φ'.hom).map
          (cokernel.π K'.arrow)))) =
      kernelSubobject ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) pg.left)).map
          (cokernel.π (kernelSubobject (absReadingHom φ sp pa hT F₀ hF₀ τ ≫
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj W) W.left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
          W).inverse.map
        ((Space.modulePullback B integerBase B.contains_integerBase φ.hom).map
          (cokernel.π K.arrow))))).arrow)) := by
  have bracket := readingFree_bracket (pg := pg) (pa := pa) (φ := φ) (φ' := φ') (ρ := ρ)
    (k := k) (hk := hk) (hsq := hsq) (sp := sp) (sp' := sp') (hrel := hrel) (hT := hT)
    (F₀ := F₀) (hF₀ := hF₀) hTc
  have hS₁ : ((Space.modulePullback B integerBase B.contains_integerBase sp).obj
      F₀).IsQuasicoherentOnSite :=
    Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
      B.contains_integerBase sp F₀ hF₀
  have nat := readingPullback_naturality (pg := pg) (φ := φ) (φ' := φ') (ρ := ρ)
    (k := k) (hk := hk) (hsq := hsq) hS₁ hK (τ.hom ≫ cokernel.π K.arrow)
  have hA_C := map₃_comp_eq hA (Space.modulePullback B integerBase B.contains_integerBase φ'.hom)
    (Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase W').inverse
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj W') W'.left.property)
  have hB_C := map₃_comp_eq hB (Space.modulePullback B integerBase B.contains_integerBase φ'.hom)
    (Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase W').inverse
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj W') W'.left.property)
  have hF_C := map₄_comp (Space.modulePullback B integerBase B.contains_integerBase ρ)
    (Space.modulePullback B integerBase B.contains_integerBase φ'.hom)
    (Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase W').inverse
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj W') W'.left.property) τ.hom (cokernel.π K.arrow)
  have hF₂_Pb := map₄_comp (Space.modulePullback B integerBase B.contains_integerBase φ.hom)
    (Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase W).inverse
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj W) W.left.property)
    (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
      (associatedBigEtaleSite B) pg.left)) τ.hom (cokernel.π K.arrow)
  have : IsIso (absReadingHom φ sp pa hT F₀ hF₀ τ) := by
    unfold absReadingHom
    infer_instance
  have := epi_comp (absReadingHom φ sp pa hT F₀ hF₀ τ)
    ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj W) W.left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
          W).inverse.map
        ((Space.modulePullback B integerBase B.contains_integerBase φ.hom).map
          (cokernel.π K.arrow))))
  unfold absReadingHom
  refine kernelSubobject_eq_of_key' (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) pg.left)) _
    ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj W') W'.left.property).map
    ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
        W').inverse.map
      ((Space.modulePullback B integerBase B.contains_integerBase φ'.hom).map ciso.hom)))
    _ _ _ _
    ((Space.representedZariskiModulePullbackIso B integerBase B.contains_integerBase pg
      (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase _)
      ((Space.modulePullback B integerBase B.contains_integerBase φ.hom).obj (cokernel K.arrow))
      (Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
        B.contains_integerBase φ.hom _ hK)).hom ≫
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj W') W'.left.property).map
        ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
            W').inverse.map
          (((Space.modulePullbackTriangle B integerBase B.contains_integerBase hk).symm ≪≫
          Space.modulePullbackTriangle B integerBase B.contains_integerBase
            hsq).hom.app (cokernel K.arrow)))) ?_
  kernel_have key := key_of_paste' (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) pg.left))
    hA_C hB_C hF_C bracket nat hF₂_Pb
  refine Stacks.KernelApply.eq_of_heq_of_eq_of_heq ?_ key ?_ <;> heq_congr

end Abstract

/-! ### The situation of a module pulled back from `h_{ℙⁿ_W}` -/

variable (F₀ : Space.Modules.{u, u} B integerBase B.contains_integerBase
  (repSpace (projectiveSite B n W)).1 (repSpace (projectiveSite B n W)).2)
  (hF₀ : F₀.IsQuasicoherentOnSite)

/-- The module `F = (X ≅ h_{ℙⁿ_W})^{-1, *} F₀` on `X`. -/
abbrev framedModule : Space.Modules.{u, u} B integerBase B.contains_integerBase D.X.1 D.X.2 :=
  (Space.modulePullback B integerBase B.contains_integerBase (baseSpaceIsoY E φ).inv).obj F₀

include hF₀ in
/-- If `F₀` is quasi-coherent, then so is the module `F = (X ≅ h_{ℙⁿ_W})^{-1, *} F₀` on `X`. -/
theorem isQuasicoherentOnSite_framedModule : (framedModule E φ F₀).IsQuasicoherentOnSite :=
  Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
    B.contains_integerBase _ F₀ hF₀

variable (κ : D.F ≅ framedModule E φ F₀)

/-- The Zariski reading `G₀` of `F₀` on `ℙⁿ_W`. -/
abbrev framedBaseReading : ((𝒯).obj (projectiveSite B n W)).Modules :=
  Space.representedZariskiModule B integerBase B.contains_integerBase (projectiveSite B n W) F₀

/-- `(X_T ⟶ h_{ℙⁿ_W})^* F₀ ≅ F_T`. -/
abbrev framedModuleIso (T : Space.SchemesOver D.Y) :
    (Space.modulePullback B integerBase B.contains_integerBase (framedProjection E φ T)).obj F₀ ≅
      D.baseChangeModule T :=
  (Space.modulePullbackTriangle B integerBase B.contains_integerBase
    (rfl : D.sourceProjection T ≫ (baseSpaceIsoY E φ).inv = framedProjection E φ T)).app F₀ ≪≫
  (Space.modulePullback B integerBase B.contains_integerBase (D.sourceProjection T)).mapIso κ.symm

/-- **The reading of `F_T` on `ℙⁿ_T` is the inverse image of `G₀`** along a morphism
`m : ℙⁿ_T ⟶ ℙⁿ_W` representing `h_{ℙⁿ_T} ≅ X_T ⟶ h_{ℙⁿ_W}`. -/
def framedReadingIso (T : Space.SchemesOver D.Y)
    (m : projectiveSite B n T.left ⟶ projectiveSite B n W)
    (hm : (spaceIsoY E T).hom ≫ framedProjection E φ T =
      Space.representedSpaceMap B integerBase B.contains_integerBase m) :
    (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) m.left)).obj (framedBaseReading F₀) ≅
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property).obj
        ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
          (projectiveSite B n T.left)).inverse.obj
          ((Space.modulePullback B integerBase B.contains_integerBase (spaceIsoY E T).hom).obj
            (D.baseChangeModule T))) :=
  Space.representedZariskiModulePullbackIso B integerBase B.contains_integerBase m
      (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase _) F₀ hF₀ ≪≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property).mapIso
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
          (projectiveSite B n T.left)).inverse.mapIso
        ((Space.modulePullbackTriangle B integerBase B.contains_integerBase hm).app F₀)) ≪≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property).mapIso
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
          (projectiveSite B n T.left)).inverse.mapIso
        ((Space.modulePullback B integerBase B.contains_integerBase (spaceIsoY E T).hom).mapIso
          (framedModuleIso E φ F₀ κ T)))

/-- **A submodule `K ⊆ F_T` read on the inverse image of `G₀` along `m : ℙⁿ_T ⟶ ℙⁿ_W`**: the
kernel of the reading of `F_T ⟶ F_T / K`, read through
`AlgebraicGeometry.ProjectiveQuotOverSpace.framedReadingIso`. -/
def framedSubobject (T : Space.SchemesOver D.Y)
    (m : projectiveSite B n T.left ⟶ projectiveSite B n W)
    (hm : (spaceIsoY E T).hom ≫ framedProjection E φ T =
      Space.representedSpaceMap B integerBase B.contains_integerBase m)
    (K : Subobject (D.baseChangeModule T)) :
    Subobject ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) m.left)).obj (framedBaseReading F₀)) :=
  kernelSubobject ((framedReadingIso E φ F₀ hF₀ κ T m hm).hom ≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
          (projectiveSite B n T.left)).inverse.map
        ((Space.modulePullback B integerBase B.contains_integerBase (spaceIsoY E T).hom).map
          (cokernel.π K.arrow))))

/-- The reading morphism, explicitly. -/
def framedReadingHom (T : Space.SchemesOver D.Y)
    (m : projectiveSite B n T.left ⟶ projectiveSite B n W)
    (hm : (spaceIsoY E T).hom ≫ framedProjection E φ T =
      Space.representedSpaceMap B integerBase B.contains_integerBase m) :
    (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) m.left)).obj (framedBaseReading F₀) ⟶
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property).obj
        ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
          (projectiveSite B n T.left)).inverse.obj
          ((Space.modulePullback B integerBase B.contains_integerBase (spaceIsoY E T).hom).obj
            (D.baseChangeModule T))) :=
  (Space.representedZariskiModulePullbackIso B integerBase B.contains_integerBase m
      (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase _)
      F₀ hF₀).hom ≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
          (projectiveSite B n T.left)).inverse.map
        ((Space.modulePullbackTriangle B integerBase B.contains_integerBase hm).hom.app F₀)) ≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
          (projectiveSite B n T.left)).inverse.map
        ((Space.modulePullback B integerBase B.contains_integerBase (spaceIsoY E T).hom).map
          (framedModuleIso E φ F₀ κ T).hom))

/-- The forward map of `framedReadingIso` is `framedReadingHom`. -/
theorem framedReadingIso_hom (T : Space.SchemesOver D.Y)
    (m : projectiveSite B n T.left ⟶ projectiveSite B n W)
    (hm : (spaceIsoY E T).hom ≫ framedProjection E φ T =
      Space.representedSpaceMap B integerBase B.contains_integerBase m) :
    (framedReadingIso E φ F₀ hF₀ κ T m hm).hom = framedReadingHom E φ F₀ hF₀ κ T m hm :=
  rfl

/-- The reading on `ℙⁿ_T`, with `h_{ℙⁿ_T}` spelled as a represented algebraic space. -/
abbrev readingY (T : Space.SchemesOver D.Y) :
    Space.Modules.{u, u} B integerBase B.contains_integerBase (D.space T).1 (D.space T).2 ⥤
      ((𝒯).obj (projectiveSite B n T.left)).Modules :=
  Space.modulePullback B integerBase B.contains_integerBase (spaceIsoY E T).hom ⋙
    (Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      (projectiveSite B n T.left)).inverse ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property

/-- `readingY` agrees with `reading`. -/
theorem readingY_eq (T : Space.SchemesOver D.Y) : readingY E T = reading E T :=
  rfl

/-- The reading of the projection onto a quasi-coherent quotient is an epimorphism. -/
theorem epi_readingY_map_cokernel_π (T : Space.SchemesOver D.Y)
    (K : Subobject (D.baseChangeModule T)) (hK : (D.quotientModule T K).IsQuasicoherentOnSite) :
    Epi ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
          (projectiveSite B n T.left)).inverse.map
        ((Space.modulePullback B integerBase B.contains_integerBase (spaceIsoY E T).hom).map
          (cokernel.π K.arrow)))) := by
  have h := epi_reading_map_cokernel_π E T K hK
  rw [← readingY_eq] at h
  exact h

/-! ### Pullback of quotients -/

/-- The square `h_{ℙⁿ_T ⟶ ℙⁿ_{T''}} ≫ (h_{ℙⁿ_{T''}} ≅ X_{T''}) = (h_{ℙⁿ_T} ≅ X_T) ≫ X_g`. -/
theorem representedSpaceMap_comp_spaceIsoY_hom {T T'' : Space.SchemesOver D.Y} (g : T ⟶ T'') :
    Space.representedSpaceMap B integerBase B.contains_integerBase
        (projectiveSiteMap B n g.left) ≫ (spaceIsoY E T'').hom =
      (spaceIsoY E T).hom ≫ D.relativeMap g :=
  (spaceIso_hom_relativeMap E g).symm

/-- `X_g` commutes with the projections to `h_{ℙⁿ_W}`. -/
theorem relativeMap_comp_framedProjection {T T'' : Space.SchemesOver D.Y} (g : T ⟶ T'') :
    D.relativeMap g ≫ framedProjection E φ T'' = framedProjection E φ T := by
  simp only [framedProjection, Space.baseChangeMap_comp_projection_assoc]

/-- The identifications `(X_T ⟶ h_{ℙⁿ_W})^* F₀ ≅ F_T` are compatible with pullback along
`X_g : X_T ⟶ X_{T''}`. -/
theorem framedModuleIso_hom_baseChangeComparison {T T'' : Space.SchemesOver D.Y} (g : T ⟶ T'') :
    (framedModuleIso E φ F₀ κ T).hom ≫ (D.baseChangeComparison g).hom.app D.F =
      (Space.modulePullbackTriangle B integerBase B.contains_integerBase
        (relativeMap_comp_framedProjection E φ g)).hom.app F₀ ≫
        (Space.modulePullback B integerBase B.contains_integerBase (D.relativeMap g)).map
          (framedModuleIso E φ F₀ κ T'').hom := by
  have coh := (Space.modulePushforwardCoherence B integerBase
      B.contains_integerBase).modulePullbackTriangle_comp
    (show D.relativeMap g ≫ D.sourceProjection T'' = D.sourceProjection T from
      Space.baseChangeMap_comp_projection D.f g)
    (rfl : D.sourceProjection T'' ≫ (baseSpaceIsoY E φ).inv = framedProjection E φ T'')
    (relativeMap_comp_framedProjection E φ g)
    (rfl : D.sourceProjection T ≫ (baseSpaceIsoY E φ).inv = framedProjection E φ T)
  kernel_have key := triangle_comp_app_mapIso coh F₀ κ
  refine Stacks.KernelApply.eq_of_heq_of_eq_of_heq ?_ key ?_ <;> kernel_congr

/-- The framed subobject of the pullback `D.quotientPullback g K` along `g : T ⟶ T''` is the
kernel of the inverse image along `ℙⁿ_T ⟶ ℙⁿ_{T''}` of the projection onto the quotient by the
framed subobject of `K`. -/
theorem framedSubobject_quotientPullback {T T'' : Space.SchemesOver D.Y} (g : T ⟶ T'')
    (pa : projectiveSite B n T''.left ⟶ projectiveSite B n W)
    (hT : (spaceIsoY E T'').hom ≫ framedProjection E φ T'' =
      Space.representedSpaceMap B integerBase B.contains_integerBase pa)
    (hTc : (spaceIsoY E T).hom ≫ framedProjection E φ T =
      Space.representedSpaceMap B integerBase B.contains_integerBase
        (projectiveSiteMap B n g.left ≫ pa))
    (K : Subobject (D.baseChangeModule T''))
    (hK : (D.quotientModule T'' K).IsQuasicoherentOnSite) :
    framedSubobject E φ F₀ hF₀ κ T _ hTc (D.quotientPullback g K) =
      kernelSubobject (inv ((Scheme.Modules.pullbackComp
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            (projectiveSiteMap B n g.left).left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            pa.left)).hom.app
            (framedBaseReading F₀)) ≫
        (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) (projectiveSiteMap B n g.left).left)).map
          (cokernel.π (framedSubobject E φ F₀ hF₀ κ T'' pa hT K).arrow)) := by
  have := epi_readingY_map_cokernel_π E T'' K hK
  have hA := D.quotientProjection_comp_quotientPullbackCokernelIso_hom g K
  have hB := framedModuleIso_hom_baseChangeComparison E φ F₀ κ g
  kernel_have key := absSub_pullback (projectiveSiteMap B n g.left) pa (spaceIsoY E T'')
    (spaceIsoY E T) (D.relativeMap g) ((spaceIsoY E T).hom ≫ D.relativeMap g)
    (representedSpaceMap_comp_spaceIsoY_hom E g)
    (rfl : (spaceIsoY E T).hom ≫ D.relativeMap g = _) (framedProjection E φ T'')
    (framedProjection E φ T) (relativeMap_comp_framedProjection E φ g) hT hTc F₀ hF₀
    (framedModuleIso E φ F₀ κ T'') (framedModuleIso E φ F₀ κ T)
    ((D.baseChangeComparison g).app D.F) hB K hK (D.quotientPullback g K)
    (D.quotientPullbackCokernelIso g K) hA
  kernel_have key' := kernelSubobject_eq_inv_comp_of_comp key
  unfold framedSubobject
  unfold absReadingHom at key'
  refine Stacks.KernelApply.eq_of_heq_of_eq_of_heq ?_ key' ?_ <;> kernel_congr

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
