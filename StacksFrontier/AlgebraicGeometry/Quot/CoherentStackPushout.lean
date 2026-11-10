module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackArtinAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentStackDiagonalEqualizer
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFinitePresentationStability
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactQuasiSeparatedPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Thickenings.SchemeChartLift
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningPushoutComparisonCriterion
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackStageSystem
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushforward

/-!
# `Coh_{X/B}` and pushouts along thickenings: the reduction of Stacks 08LQ

Let `f : X ⟶ B` be a finitely presented morphism of algebraic spaces over `S` (Situation 08KB)
and let

```
  Z ---i---> Z'
  |          |
  f          a
  v          v
  Y ---b---> Y'
```

be a pushout of schemes over `S` with `Z ⟶ Z'` a thickening and `Z ⟶ Y` affine (Stacks 07RT).
Stacks 08LQ: the functor `Coh_{X/B, Y'} ⟶ Coh_{X/B, Y} ×_{Coh_{X/B, Z}} Coh_{X/B, Z'}` is an
equivalence. The source's proof: the map `B(Y') ⟶ B(Y) ×_{B(Z)} B(Z')` is bijective
(Stacks 07SY), so one may fix the morphism `Y' ⟶ B`; then the statement is Stacks 08KV for the
base change `X ×_B Y' ⟶ Y'`.

This file carries the first step and the whole of the passage from `Coh_{X/B}` to modules: the
comparison functor is an equivalence as soon as modules glue along every square of test schemes
over the pushout square (`AlgebraicGeometry.Space.CoherentSituation.ModulesGlueOver`), which is
the content of Stacks 08KV for the base changes `X ×_B T ⟶ T`, together with the transfer of
properness of the support across the thickening.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.IsCoherentModule`: the conditions of Stacks 08KB on a
  module on a base change.
* `AlgebraicGeometry.Space.CoherentSituation.ModulesGlue` and
  `AlgebraicGeometry.Space.CoherentSituation.ModulesGlueOver`: modules glue along a square of
  test schemes, and along every square of test schemes over a square of schemes.

## Main results

* `AlgebraicGeometry.Space.existsUnique_desc_schemeSpace_of_isPushout`: **the first step**, the
  bijection `B(Y') ⟶ B(Y) ×_{B(Z)} B(Z')` for an arbitrary algebraic space `B`, read off
  Stacks 07SY.
* `AlgebraicGeometry.Space.CoherentSituation.objectsGlue` and
  `AlgebraicGeometry.Space.CoherentSituation.morphismsGlue`: objects and morphisms of `Coh_{X/B}`
  glue along the pushout once modules do.
* `Space.CoherentSituation.fiberSquareComparison_isEquivalence_of_modulesGlueOver`:
  **the reduction of Stacks 08LQ to the gluing of modules.**
* `CategoryTheory.Functor.comparison_square_comp` and
  `CategoryTheory.Functor.map_comp_overlap_of_squares`: the coherences of comparisons of composite
  functors the gluing of morphisms runs on, stated for arbitrary functors so that their instances
  at the inverse images of modules are checked by substitution alone.

## References

* [Stacks Project, Tag 08LQ](https://stacks.math.columbia.edu/tag/08LQ)
* [Stacks Project, Tag 07SY](https://stacks.math.columbia.edu/tag/07SY)
* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### Coherences of comparisons of composite functors -/

/-- **The associativity coherence of a family of comparisons, read at an object and inverted.**
For comparisons `τ₁ : Pαγ ≅ Pγ ⋙ Pα`, `τ₂ : L₁ ≅ Pμ ⋙ Pαγ`, `τ₃ : Pγμ ≅ Pμ ⋙ Pγ`,
`τ₄ : L₂ ≅ Pγμ ⋙ Pα` and `w : L₁ ≅ L₂` satisfying the associativity coherence, the inverse of `τ₃`
followed by the inverse of `τ₄` is the inverse of `τ₁` followed by the inverse of `τ₂` and `w`.

Stated for arbitrary functors, so that its instances at the inverse images of modules along
morphisms of test schemes are checked by substitution alone. -/
theorem CategoryTheory.Functor.map_inv_app_comp_inv_app_of_assoc {C₀ C₁ C₂ C₃ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
    {Pα : C₁ ⥤ C₀} {Pγ : C₂ ⥤ C₁} {Pμ : C₃ ⥤ C₂} {Pαγ : C₂ ⥤ C₀} {Pγμ : C₃ ⥤ C₁}
    {L₁ L₂ : C₃ ⥤ C₀} (τ₁ : Pαγ ≅ Pγ ⋙ Pα) (τ₂ : L₁ ≅ Pμ ⋙ Pαγ) (τ₃ : Pγμ ≅ Pμ ⋙ Pγ)
    (τ₄ : L₂ ≅ Pγμ ⋙ Pα) (w : L₁ ≅ L₂)
    (hfac : τ₂ ≪≫ Functor.isoWhiskerLeft Pμ τ₁ =
      w ≪≫ τ₄ ≪≫ Functor.isoWhiskerRight τ₃ Pα ≪≫ Functor.associator Pμ Pγ Pα) (K : C₃) :
    Pα.map (τ₃.inv.app K) ≫ τ₄.inv.app K = τ₁.inv.app (Pμ.obj K) ≫ τ₂.inv.app K ≫ w.hom.app K := by
  have hI := NatTrans.congr_app (congrArg Iso.inv hfac) K
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc] at hI
  rw [reassoc_of% hI]
  simp

/-- **The comparisons along a commutative square followed by a morphism agree.**  This is the
identity behind gluing morphisms of a fibred category whose fibres are categories of modules: for
a commutative square `α ≫ γ = β ≫ δ` followed by `μ`, the two composite comparisons of the
inverse images along `α ≫ γ ≫ μ = β ≫ δ ≫ μ`, one through `γ ≫ μ` and `δ ≫ μ` and one through `γ`,
`δ` and `μ`, agree. The comparisons are arbitrary isomorphisms subject to the two associativity
coherences `hA₁`, `hA₂`, the compatibility `hnat` of the identification `w` along the square with
the comparisons for `- ≫ μ`, and the compatibility `hcoh` of the identifications along the
square, along `- ≫ μ` and along associativity. -/
theorem CategoryTheory.Functor.comparison_square_comp {CX CY CX' CY' CY'' : Type*}
    [Category* CX] [Category* CY] [Category* CX'] [Category* CY'] [Category* CY'']
    {Pα : CY ⥤ CX} {Pβ : CX' ⥤ CX} {Pγ : CY' ⥤ CY} {Pδ : CY' ⥤ CX'} {Pμ : CY'' ⥤ CY'}
    {Pαγ Pβδ : CY' ⥤ CX} {Pγμ : CY'' ⥤ CY} {Pδμ : CY'' ⥤ CX'} {L₁ L₂ L₃ L₄ : CY'' ⥤ CX}
    (cαγ : Pαγ ≅ Pγ ⋙ Pα) (cβδ : Pβδ ≅ Pδ ⋙ Pβ) (cγμ : Pγμ ≅ Pμ ⋙ Pγ)
    (cδμ : Pδμ ≅ Pμ ⋙ Pδ) (cαγ_μ : L₁ ≅ Pμ ⋙ Pαγ) (cα_γμ : L₂ ≅ Pγμ ⋙ Pα)
    (cβδ_μ : L₃ ≅ Pμ ⋙ Pβδ) (cβ_δμ : L₄ ≅ Pδμ ⋙ Pβ) (w : Pαγ ≅ Pβδ) (w' : L₂ ≅ L₄)
    (a₁ : L₁ ≅ L₂) (a₂ : L₃ ≅ L₄) (wμ : L₁ ≅ L₃)
    (hA₁ : cαγ_μ ≪≫ Functor.isoWhiskerLeft Pμ cαγ =
      a₁ ≪≫ cα_γμ ≪≫ Functor.isoWhiskerRight cγμ Pα ≪≫ Functor.associator Pμ Pγ Pα)
    (hA₂ : cβδ_μ ≪≫ Functor.isoWhiskerLeft Pμ cβδ =
      a₂ ≪≫ cβ_δμ ≪≫ Functor.isoWhiskerRight cδμ Pβ ≪≫ Functor.associator Pμ Pδ Pβ) (K : CY'')
    (hnat : cαγ_μ.inv.app K ≫ wμ.hom.app K = w.hom.app (Pμ.obj K) ≫ cβδ_μ.inv.app K)
    (hcoh : a₁.hom.app K ≫ w'.hom.app K = wμ.hom.app K ≫ a₂.hom.app K) :
    Pα.map (cγμ.inv.app K) ≫ cα_γμ.inv.app K ≫ w'.hom.app K ≫ cβ_δμ.hom.app K =
      cαγ.inv.app (Pμ.obj K) ≫ w.hom.app (Pμ.obj K) ≫ cβδ.hom.app (Pμ.obj K) ≫
        Pβ.map (cδμ.inv.app K) := by
  have h₁ := Functor.map_inv_app_comp_inv_app_of_assoc cαγ cαγ_μ cγμ cα_γμ a₁ hA₁ K
  have h₂ := Functor.map_inv_app_comp_inv_app_of_assoc cβδ cβδ_μ cδμ cβ_δμ a₂ hA₂ K
  have h₂' : Pβ.map (cδμ.inv.app K) = cβδ.inv.app (Pμ.obj K) ≫ cβδ_μ.inv.app K ≫
      a₂.hom.app K ≫ cβ_δμ.hom.app K := by
    rw [← reassoc_of% h₂]; simp
  rw [reassoc_of% h₁, h₂', Iso.hom_inv_id_app_assoc, ← reassoc_of% hnat, reassoc_of% hcoh]


/-- **The compatibility condition for gluing morphisms of modules along a square, from two
commutative squares of morphisms of a fibred category of modules.**  Abstract form: `Fx`, `Fy`,
`Fz`, `Ft`, `Ft'` are the modules of five objects, `uY`, `uZ`, `r`, `s`, `mY`, `mZ` the module
comparisons of six morphisms forming two commutative squares (`hr`, `hm`), and the remaining data
are comparisons of inverse images subject to the coherence `hsq` of
`CategoryTheory.Functor.comparison_square_comp` and the transport identities `hY`, `hZ`, `hww`.
The two composites built from the module comparisons agree through the comparisons on the
overlap. -/
theorem CategoryTheory.Functor.map_comp_overlap_of_squares {CX CY CX' CY' CY'' : Type*}
    [Category* CX] [Category* CY] [Category* CX'] [Category* CY'] [Category* CY'']
    {Pα : CY ⥤ CX} {Pβ : CX' ⥤ CX} {Pγ : CY' ⥤ CY} {Pδ : CY' ⥤ CX'} {Pμ : CY'' ⥤ CY'}
    {Pαγ Pβδ : CY' ⥤ CX} {Pγμ PmY : CY'' ⥤ CY} {Pδμ PmZ : CY'' ⥤ CX'}
    {L₂ L₄ LmY LmZ : CY'' ⥤ CX}
    (cαγ : Pαγ ≅ Pγ ⋙ Pα) (cβδ : Pβδ ≅ Pδ ⋙ Pβ) (cγμ : Pγμ ≅ Pμ ⋙ Pγ)
    (cδμ : Pδμ ≅ Pμ ⋙ Pδ) (cα_γμ : L₂ ≅ Pγμ ⋙ Pα) (cβ_δμ : L₄ ≅ Pδμ ⋙ Pβ)
    (cαmY : LmY ≅ PmY ⋙ Pα) (cβmZ : LmZ ≅ PmZ ⋙ Pβ) (w : Pαγ ≅ Pβδ) (w' : L₂ ≅ L₄)
    (wm : LmY ≅ LmZ) (ρY : Pγμ ≅ PmY) (ρZ : Pδμ ≅ PmZ) (σY : L₂ ≅ LmY) (σZ : L₄ ≅ LmZ)
    {Fx : CX} {Fy : CY} {Fz : CX'} {Ft : CY'} {Ft' : CY''}
    (uY : Pα.obj Fy ⟶ Fx) (uZ : Pβ.obj Fz ⟶ Fx) [IsIso uZ] (r : Pγ.obj Ft ⟶ Fy) [IsIso r]
    (s : Pδ.obj Ft ⟶ Fz) [IsIso s] (mY : PmY.obj Ft' ⟶ Fy) (mZ : PmZ.obj Ft' ⟶ Fz)
    (hsq : Pα.map (cγμ.inv.app Ft') ≫ cα_γμ.inv.app Ft' ≫ w'.hom.app Ft' ≫ cβ_δμ.hom.app Ft' =
      cαγ.inv.app (Pμ.obj Ft') ≫ w.hom.app (Pμ.obj Ft') ≫ cβδ.hom.app (Pμ.obj Ft') ≫
        Pβ.map (cδμ.inv.app Ft'))
    (hY : Pα.map (ρY.hom.app Ft') ≫ cαmY.inv.app Ft' = cα_γμ.inv.app Ft' ≫ σY.hom.app Ft')
    (hZ : Pβ.map (ρZ.hom.app Ft') ≫ cβmZ.inv.app Ft' = cβ_δμ.inv.app Ft' ≫ σZ.hom.app Ft')
    (hww : σY.hom.app Ft' ≫ wm.hom.app Ft' = w'.hom.app Ft' ≫ σZ.hom.app Ft')
    (hr : cαγ.hom.app Ft ≫ Pα.map r ≫ uY = w.hom.app Ft ≫ cβδ.hom.app Ft ≫ Pβ.map s ≫ uZ)
    (hm : cαmY.hom.app Ft' ≫ Pα.map mY ≫ uY =
      wm.hom.app Ft' ≫ cβmZ.hom.app Ft' ≫ Pβ.map mZ ≫ uZ) :
    Pα.map (show Pγ.obj (Pμ.obj Ft') ⟶ Pγ.obj Ft from
        cγμ.inv.app Ft' ≫ ρY.hom.app Ft' ≫ mY ≫ CategoryTheory.inv r) ≫
        (cαγ.inv.app Ft ≫ w.hom.app Ft ≫ cβδ.hom.app Ft) =
      (cαγ.inv.app (Pμ.obj Ft') ≫ w.hom.app (Pμ.obj Ft') ≫ cβδ.hom.app (Pμ.obj Ft')) ≫
        Pβ.map (show Pδ.obj (Pμ.obj Ft') ⟶ Pδ.obj Ft from
          cδμ.inv.app Ft' ≫ ρZ.hom.app Ft' ≫ mZ ≫ CategoryTheory.inv s) := by
  have hr' : Pα.map (CategoryTheory.inv r) ≫ cαγ.inv.app Ft ≫ w.hom.app Ft ≫ cβδ.hom.app Ft =
      uY ≫ CategoryTheory.inv uZ ≫ Pβ.map (CategoryTheory.inv s) := by
    have : w.hom.app Ft ≫ cβδ.hom.app Ft =
        cαγ.hom.app Ft ≫ Pα.map r ≫ uY ≫ CategoryTheory.inv uZ ≫ Pβ.map (CategoryTheory.inv s) := by
      rw [reassoc_of% hr]; simp
    rw [this, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hm' : Pα.map mY ≫ uY =
      cαmY.inv.app Ft' ≫ wm.hom.app Ft' ≫ cβmZ.hom.app Ft' ≫ Pβ.map mZ ≫ uZ := by
    rw [← hm, Iso.inv_hom_id_app_assoc]
  have hZ' : σZ.hom.app Ft' ≫ cβmZ.hom.app Ft' = cβ_δμ.hom.app Ft' ≫ Pβ.map (ρZ.hom.app Ft') := by
    rw [← cancel_epi (cβ_δμ.inv.app Ft'), ← reassoc_of% hZ]; simp
  dsimp only
  simp only [Functor.map_comp, Category.assoc]
  rw [hr', reassoc_of% hm', reassoc_of% hY, reassoc_of% hww, reassoc_of% hZ']
  simp only [IsIso.hom_inv_id_assoc]
  rw [← reassoc_of% hsq]

/-- **Gluing of morphisms reflects isomorphisms.**  Abstract form: if morphisms `Pγ M ⟶ Pγ N` and
`Pδ M ⟶ Pδ N` compatible through the comparison `c₁⁻¹ ≫ c₂ ≫ c₃` of the two composites to the
overlap are the images of exactly one morphism `M ⟶ N` (for objects satisfying `Q`), then a
morphism between such objects whose two images are isomorphisms is an isomorphism. -/
theorem CategoryTheory.Functor.isIso_of_glue {C C₀ C₁ C₂ : Type*} [Category* C] [Category* C₀]
    [Category* C₁] [Category* C₂] {Pγ : C ⥤ C₁} {Pδ : C ⥤ C₂} {Pα : C₁ ⥤ C₀} {Pβ : C₂ ⥤ C₀}
    {Pαγ Pβδ : C ⥤ C₀} (c₁ : Pαγ ≅ Pγ ⋙ Pα) (c₂ : Pαγ ≅ Pβδ) (c₃ : Pβδ ≅ Pδ ⋙ Pβ)
    (Q : C → Prop)
    (hglue : ∀ M N : C, Q M → Q N → ∀ (φY : Pγ.obj M ⟶ Pγ.obj N) (φZ : Pδ.obj M ⟶ Pδ.obj N),
      Pα.map φY ≫ (c₁.inv.app N ≫ c₂.hom.app N ≫ c₃.hom.app N) =
        (c₁.inv.app M ≫ c₂.hom.app M ≫ c₃.hom.app M) ≫ Pβ.map φZ →
      ∃! φ : M ⟶ N, Pγ.map φ = φY ∧ Pδ.map φ = φZ)
    {M N : C} (hM : Q M) (hN : Q N) (φ : M ⟶ N) [IsIso (Pγ.map φ)] [IsIso (Pδ.map φ)] :
    IsIso φ := by
  have hnat : ∀ {K L : C} (g : K ⟶ L),
      Pα.map (Pγ.map g) ≫ (c₁.inv.app L ≫ c₂.hom.app L ≫ c₃.hom.app L) =
        (c₁.inv.app K ≫ c₂.hom.app K ≫ c₃.hom.app K) ≫ Pβ.map (Pδ.map g) := fun g => by
    have h₁ := c₁.inv.naturality g
    have h₂ := c₂.hom.naturality g
    have h₃ := c₃.hom.naturality g
    simp only [Functor.comp_map] at h₁ h₃
    rw [reassoc_of% h₁, reassoc_of% h₂, h₃]
    simp only [Category.assoc]
  obtain ⟨ψ, ⟨hψY, hψZ⟩, -⟩ := hglue N M hN hM (CategoryTheory.inv (Pγ.map φ))
    (CategoryTheory.inv (Pδ.map φ)) (by
      have h₁ := congrArg (Pα.map (CategoryTheory.inv (Pγ.map φ)) ≫ · ≫
        Pβ.map (CategoryTheory.inv (Pδ.map φ))) (hnat φ)
      simp only [← Functor.map_comp_assoc, IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
        Category.id_comp, Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id,
        Category.comp_id, Functor.comp_obj] at h₁
      simpa only [Category.assoc] using h₁.symm)
  obtain ⟨χM, -, hM'⟩ := hglue M M hM hM (𝟙 _) (𝟙 _) (by simp [Functor.comp_obj])
  obtain ⟨χN, -, hN'⟩ := hglue N N hN hN (𝟙 _) (𝟙 _) (by simp [Functor.comp_obj])
  refine ⟨ψ, ?_, ?_⟩
  · rw [hM' (φ ≫ ψ) ⟨by rw [Functor.map_comp, hψY, IsIso.hom_inv_id],
        by rw [Functor.map_comp, hψZ, IsIso.hom_inv_id]⟩,
      ← hM' (𝟙 M) ⟨CategoryTheory.Functor.map_id _ _, CategoryTheory.Functor.map_id _ _⟩]
  · rw [hN' (ψ ≫ φ) ⟨by rw [Functor.map_comp, hψY, IsIso.inv_hom_id],
        by rw [Functor.map_comp, hψZ, IsIso.inv_hom_id]⟩,
      ← hN' (𝟙 N) ⟨CategoryTheory.Functor.map_id _ _, CategoryTheory.Functor.map_id _ _⟩]


/-! ### Transporting the gluing of triples along equivalences -/

section TripleTransport

variable {𝒱' 𝒱 𝒰' 𝒰 𝒱c 𝒰'c 𝒰c : Type*} [Category* 𝒱'] [Category* 𝒱] [Category* 𝒰']
  [Category* 𝒰] [Category* 𝒱c] [Category* 𝒰'c] [Category* 𝒰c]
  {pV : 𝒱' ⥤ 𝒱} {pA : 𝒱' ⥤ 𝒰'} {pT : 𝒱 ⥤ 𝒰} {pC : 𝒰' ⥤ 𝒰} {Pαγ Pβδ : 𝒱' ⥤ 𝒰}
  (c₁ : Pαγ ≅ pV ⋙ pT) (c₂ : Pαγ ≅ Pβδ) (c₃ : Pβδ ≅ pA ⋙ pC)
  {qV : 𝒱' ⥤ 𝒱c} {qA : 𝒱' ⥤ 𝒰'c} {qT : 𝒱c ⥤ 𝒰c} {qC : 𝒰'c ⥤ 𝒰c} (c' : qV ⋙ qT ≅ qA ⋙ qC)
  {EV : 𝒱c ⥤ 𝒱} {EA : 𝒰'c ⥤ 𝒰'} {EU : 𝒰c ⥤ 𝒰}
  (θV : pV ≅ qV ⋙ EV) (θA : pA ≅ qA ⋙ EA) (θT : qT ⋙ EU ≅ EV ⋙ pT) (θC : qC ⋙ EU ≅ EA ⋙ pC)

/-- **The comparisons of two presentations of a gluing problem agree**: the hypothesis of
`CategoryTheory.Functor.hom_glue_of_transport` and `CategoryTheory.Functor.obj_glue_of_transport`,
that the comparison `c₁⁻¹ ≫ c₂ ≫ c₃` of one presentation is the comparison `c'` of the other,
read through the identifications `θ`. -/
def CategoryTheory.Functor.TransportCoherent : Prop :=
  ∀ K : 𝒱', c₁.inv.app K ≫ c₂.hom.app K ≫ c₃.hom.app K ≫ pC.map (θA.hom.app K) =
    pT.map (θV.hom.app K) ≫ θT.inv.app (qV.obj K) ≫ EU.map (c'.hom.app K) ≫
      θC.hom.app (qA.obj K)

variable {c₁ c₂ c₃ c' θV θA θT θC}

/-- The `EU`-image of the comparison `c'` is the comparison `c₁⁻¹ ≫ c₂ ≫ c₃` conjugated by `θ`. -/
private theorem map_comparison_eq_of_transportCoherent
    (hcoh : Functor.TransportCoherent c₁ c₂ c₃ c' θV θA θT θC) (K : 𝒱') :
    EU.map (c'.hom.app K) = θT.hom.app (qV.obj K) ≫ pT.map (θV.inv.app K) ≫
      (c₁.inv.app K ≫ c₂.hom.app K ≫ c₃.hom.app K) ≫ pC.map (θA.hom.app K) ≫
        θC.inv.app (qA.obj K) := by
  calc EU.map (c'.hom.app K) = θT.hom.app (qV.obj K) ≫ pT.map (θV.inv.app K) ≫
        (pT.map (θV.hom.app K) ≫ θT.inv.app (qV.obj K) ≫ EU.map (c'.hom.app K) ≫
          θC.hom.app (qA.obj K)) ≫ θC.inv.app (qA.obj K) := by
        simp [← Functor.map_comp_assoc]
    _ = _ := by rw [← hcoh K]; simp only [Category.assoc]

/-- **Gluing of morphisms transports along equivalences.**  If morphisms glue for the
presentation `(qV, qA, c')` and the two presentations are identified by `θ` through fully faithful
functors `EV`, `EA`, `EU`, morphisms glue for the presentation `(pV, pA, c₁⁻¹ ≫ c₂ ≫ c₃)`. -/
theorem CategoryTheory.Functor.hom_glue_of_transport
    (hcoh : TransportCoherent c₁ c₂ c₃ c' θV θA θT θC)
    (hEV : EV.FullyFaithful) (hEA : EA.FullyFaithful) (hEU : EU.FullyFaithful) {M N : 𝒱'}
    (hglue : ∀ (ψY : qV.obj M ⟶ qV.obj N) (ψZ : qA.obj M ⟶ qA.obj N),
      qT.map ψY ≫ c'.hom.app N = c'.hom.app M ≫ qC.map ψZ →
        ∃! φ : M ⟶ N, qV.map φ = ψY ∧ qA.map φ = ψZ)
    (φY : pV.obj M ⟶ pV.obj N) (φZ : pA.obj M ⟶ pA.obj N)
    (hm : pT.map φY ≫ (c₁.inv.app N ≫ c₂.hom.app N ≫ c₃.hom.app N) =
      (c₁.inv.app M ≫ c₂.hom.app M ≫ c₃.hom.app M) ≫ pC.map φZ) :
    ∃! φ : M ⟶ N, pV.map φ = φY ∧ pA.map φ = φZ := by
  have hcK := map_comparison_eq_of_transportCoherent hcoh
  have nT : ∀ {K L : 𝒱c} (ψ : K ⟶ L),
      EU.map (qT.map ψ) = θT.hom.app K ≫ pT.map (EV.map ψ) ≫ θT.inv.app L := fun ψ =>
    (NatIso.naturality_2 θT ψ).symm
  have nC : ∀ {K L : 𝒰'c} (ψ : K ⟶ L),
      EU.map (qC.map ψ) = θC.hom.app K ≫ pC.map (EA.map ψ) ≫ θC.inv.app L := fun ψ =>
    (NatIso.naturality_2 θC ψ).symm
  have nV : ∀ {K L : 𝒱'} (φ : K ⟶ L),
      pV.map φ = θV.hom.app K ≫ EV.map (qV.map φ) ≫ θV.inv.app L := fun φ =>
    (NatIso.naturality_2 θV φ).symm
  have nA : ∀ {K L : 𝒱'} (φ : K ⟶ L),
      pA.map φ = θA.hom.app K ≫ EA.map (qA.map φ) ≫ θA.inv.app L := fun φ =>
    (NatIso.naturality_2 θA φ).symm
  obtain ⟨ψY, hY⟩ : ∃ ψY : qV.obj M ⟶ qV.obj N, EV.map ψY = θV.inv.app M ≫ φY ≫ θV.hom.app N :=
    ⟨hEV.preimage _, hEV.map_preimage _⟩
  obtain ⟨ψZ, hZ⟩ : ∃ ψZ : qA.obj M ⟶ qA.obj N, EA.map ψZ = θA.inv.app M ≫ φZ ≫ θA.hom.app N :=
    ⟨hEA.preimage _, hEA.map_preimage _⟩
  have hcompat : qT.map ψY ≫ c'.hom.app N = c'.hom.app M ≫ qC.map ψZ := by
    apply hEU.map_injective
    rw [Functor.map_comp, Functor.map_comp, hcK, hcK, nT, nC, hY, hZ]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp,
      ← Functor.map_comp_assoc pT (θV.hom.app N), Iso.hom_inv_id_app, Functor.map_id,
      Category.id_comp]
    rw [reassoc_of% hm]
    simp only [← Functor.map_comp_assoc pC (θA.hom.app M), Iso.hom_inv_id_app, Functor.map_id,
      Category.id_comp]
  obtain ⟨φ, ⟨h₁, h₂⟩, hu⟩ := hglue ψY ψZ hcompat
  refine ⟨φ, ⟨?_, ?_⟩, fun φ' ⟨h₁', h₂'⟩ => hu φ' ⟨hEV.map_injective ?_, hEA.map_injective ?_⟩⟩
  · rw [nV, h₁, hY]; simp
  · rw [nA, h₂, hZ]; simp
  · rw [hY, ← h₁', nV]; simp
  · rw [hZ, ← h₂', nA]; simp

/-- **Gluing of objects transports along equivalences.**  An object glued for the presentation
`(qV, qA, c')` from objects identified through `EV`, `EA` with the given ones gives, through `θ`,
a gluing for the presentation `(pV, pA, c₁⁻¹ ≫ c₂ ≫ c₃)`. -/
theorem CategoryTheory.Functor.obj_glue_of_transport
    (hcoh : TransportCoherent c₁ c₂ c₃ c' θV θA θT θC)
    {MY : 𝒱} {MX' : 𝒰'} (θ : pT.obj MY ⟶ pC.obj MX') {KY : 𝒱c} {KA : 𝒰'c}
    (εY : EV.obj KY ≅ MY) (εA : EA.obj KA ≅ MX') (θ'' : qT.obj KY ⟶ qC.obj KA)
    (hθ'' : EU.map θ'' = θT.hom.app KY ≫ pT.map εY.hom ≫ θ ≫ pC.map εA.inv ≫ θC.inv.app KA)
    {G : 𝒱'} (ζY : qV.obj G ⟶ KY) (ζA : qA.obj G ⟶ KA)
    (hζ : qT.map ζY ≫ θ'' = c'.hom.app G ≫ qC.map ζA) :
    pT.map (θV.hom.app G ≫ EV.map ζY ≫ εY.hom) ≫ θ =
      (c₁.inv.app G ≫ c₂.hom.app G ≫ c₃.hom.app G) ≫
        pC.map (θA.hom.app G ≫ EA.map ζA ≫ εA.hom) := by
  have h := congrArg EU.map hζ
  rw [Functor.map_comp, Functor.map_comp, hθ''] at h
  have nT := θT.hom.naturality ζY
  have nC := θC.hom.naturality ζA
  simp only [Functor.comp_map] at nT nC
  have eT : EU.map (qT.map ζY) ≫ θT.hom.app KY = θT.hom.app (qV.obj G) ≫ pT.map (EV.map ζY) := nT
  have eC : EU.map (qC.map ζA) ≫ θC.hom.app KA = θC.hom.app (qA.obj G) ≫ pC.map (EA.map ζA) := nC
  rw [map_comparison_eq_of_transportCoherent hcoh G] at h
  have h' := congrArg (fun q => pT.map (θV.hom.app G) ≫ θT.inv.app (qV.obj G) ≫ q ≫
    θC.hom.app KA ≫ pC.map εA.hom) h
  simp only [Category.assoc] at h'
  rw [reassoc_of% eT, reassoc_of% eC] at h'
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc] at h' ⊢
  rw [← Functor.map_comp_assoc pT (θV.hom.app G) (θV.inv.app G), Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp, ← Functor.map_comp pC (εA.inv) (εA.hom),
    Iso.inv_hom_id, Functor.map_id, Category.comp_id] at h'
  exact h'

end TripleTransport

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The base maps: `B(Y') = B(Y) ×_{B(Z)} B(Z')` -/

section BaseMaps

variable {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')

/-- **The first step of the proof of Stacks 08LQ.** For a pushout of schemes over `S` along a
thickening `i` and an affine morphism `f`, and an algebraic space `Z` over `S`, a pair of
morphisms `Y ⟶ Z` and `X' ⟶ Z` agreeing on `X` comes from exactly one morphism `Y' ⟶ Z`: the map
`Z(Y') ⟶ Z(Y) ×_{Z(X)} Z(X')` is bijective. This is Stacks 07SY, that the square is a pushout in
the algebraic spaces over `S` too. -/
theorem existsUnique_desc_schemeSpace_of_isPushout
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hsq : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b))
    {Z : AlgebraicSpaces B S hS} (gY : (schemeSpaceFunctor B S hS).obj Y ⟶ Z)
    (gX' : (schemeSpaceFunctor B S hS).obj X' ⟶ Z)
    (h : (schemeSpaceFunctor B S hS).map f ≫ gY = (schemeSpaceFunctor B S hS).map i ≫ gX') :
    ∃! g' : (schemeSpaceFunctor B S hS).obj Y' ⟶ Z,
      (schemeSpaceFunctor B S hS).map b ≫ g' = gY ∧
        (schemeSpaceFunctor B S hS).map a ≫ g' = gX' := by
  have P := isPushout_algebraicSpaces_of_isThickening_of_isAffineHom' B S hS i f a b hi hsq
  refine ⟨P.desc gX' gY h.symm, ⟨P.inr_desc gX' gY h.symm, P.inl_desc gX' gY h.symm⟩, ?_⟩
  rintro g' ⟨hb, ha⟩
  refine P.hom_ext ?_ ?_
  · exact ha.trans (P.inl_desc gX' gY h.symm).symm
  · exact hb.trans (P.inr_desc gX' gY h.symm).symm

end BaseMaps


/-! ### Coherent modules on a base change, and squares of test schemes -/

attribute [local instance] pointTopology

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

variable {TX TY TX' TY' : SchemesOver D.Y} (α : TX ⟶ TY) (β : TX ⟶ TX') (γ : TY ⟶ TY')
  (δ : TX' ⟶ TY') (hw : α ≫ γ = β ≫ δ)

/-- **Modules glue along a square of test schemes.**  For a commutative square
`α ≫ γ = β ≫ δ` of test schemes, write `c_M : (X_α)^*(X_γ)^*M ⟶ (X_β)^*(X_δ)^*M` for the
comparison of the two inverse images of a module `M` on `X_{TY'}` to `X_{TX}` (the comparisons
of Stacks 03LU for the two factorizations of the diagonal, and the identification of the inverse
images along the two equal diagonals). Then, on modules satisfying the conditions of
Stacks 08KB,

* a pair of morphisms `(X_γ)^*M ⟶ (X_γ)^*N` and `(X_δ)^*M ⟶ (X_δ)^*N` compatible through `c`
  is the pair of inverse images of exactly one morphism `M ⟶ N`, and
* a module on `X_{TY}` and a module on `X_{TX'}` with an isomorphism of their inverse images to
  `X_{TX}` are the inverse images of one module on `X_{TY'}`, compatibly through `c`.

For the square of base changes of a thickening-and-affine pushout this is Stacks 08KV, with its
parts (a) and (b) and the transfer of properness of the support across the thickening: the
restriction of modules to triples is fully faithful and essentially surjective. -/
structure ModulesGlue : Prop where
  /-- Morphisms glue. -/
  hom_glue : ∀ (M N : Modules.{u, u} B S hS (D.space TY').1 (D.space TY').2),
      D.IsCoherentModule TY' M → D.IsCoherentModule TY' N →
      ∀ (φY : (modulePullback B S hS (D.relativeMap γ)).obj M ⟶
          (modulePullback B S hS (D.relativeMap γ)).obj N)
        (φZ : (modulePullback B S hS (D.relativeMap δ)).obj M ⟶
          (modulePullback B S hS (D.relativeMap δ)).obj N),
        (modulePullback B S hS (D.relativeMap α)).map φY ≫
            ((D.compComparison α γ).inv.app N ≫ (D.relativeMapComparison hw).hom.app N ≫
              (D.compComparison β δ).hom.app N) =
          ((D.compComparison α γ).inv.app M ≫ (D.relativeMapComparison hw).hom.app M ≫
              (D.compComparison β δ).hom.app M) ≫
            (modulePullback B S hS (D.relativeMap β)).map φZ →
        ∃! φ : M ⟶ N, (modulePullback B S hS (D.relativeMap γ)).map φ = φY ∧
          (modulePullback B S hS (D.relativeMap δ)).map φ = φZ
  /-- Objects glue. -/
  obj_glue : ∀ (MY : Modules.{u, u} B S hS (D.space TY).1 (D.space TY).2)
      (MX' : Modules.{u, u} B S hS (D.space TX').1 (D.space TX').2)
      (θY : (modulePullback B S hS (D.relativeMap α)).obj MY ⟶
        (modulePullback B S hS (D.relativeMap β)).obj MX'),
      IsIso θY → D.IsCoherentModule TY MY → D.IsCoherentModule TX' MX' →
      ∃ (G : Modules.{u, u} B S hS (D.space TY').1 (D.space TY').2)
        (eY : (modulePullback B S hS (D.relativeMap γ)).obj G ⟶ MY)
        (eX' : (modulePullback B S hS (D.relativeMap δ)).obj G ⟶ MX'),
        IsIso eY ∧ IsIso eX' ∧ D.IsCoherentModule TY' G ∧
          (modulePullback B S hS (D.relativeMap α)).map eY ≫ θY =
            ((D.compComparison α γ).inv.app G ≫ (D.relativeMapComparison hw).hom.app G ≫
              (D.compComparison β δ).hom.app G) ≫
              (modulePullback B S hS (D.relativeMap β)).map eX'

end CoherentSituation



/-! ### Coherences of the comparisons of inverse images along test schemes -/

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-- The comparison of Stacks 03LU for `k ≫ μ` transported along an equality `k = k'` of first
factors is the identification of the inverse images along `k` and `k'`, read after `μ`. -/
theorem compComparison_relativeMapComparison_comp {T T₁ T₂ : SchemesOver D.Y}
    {k k' : T ⟶ T₁} (e : k = k') (μ : T₁ ⟶ T₂)
    (K : Modules.{u, u} B S hS (D.space T₂).1 (D.space T₂).2) :
    (D.compComparison k μ).inv.app K ≫
        (D.relativeMapComparison (congrArg (· ≫ μ) e)).hom.app K =
      (D.relativeMapComparison e).hom.app ((modulePullback B S hS (D.relativeMap μ)).obj K) ≫
        (D.compComparison k' μ).inv.app K := by
  subst e
  simp only [relativeMapComparison_hom_app, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- **The comparisons along a commutative square of test schemes followed by a morphism.**  For
a commutative square `α ≫ γ = β ≫ δ` of test schemes and a morphism `μ`, the two composite
comparisons of the inverse images of a module `K` along `α ≫ (γ ≫ μ) = β ≫ (δ ≫ μ)`, one through
`γ ≫ μ` and `δ ≫ μ` and one through `γ`, `δ` and `μ`, agree. -/
theorem compComparison_square_comp {TX TY TX' TY' TY'' : SchemesOver D.Y} (α : TX ⟶ TY)
    (β : TX ⟶ TX') (γ : TY ⟶ TY') (δ : TX' ⟶ TY') (μ : TY' ⟶ TY'') (hw : α ≫ γ = β ≫ δ)
    (hw' : α ≫ γ ≫ μ = β ≫ δ ≫ μ)
    (K : Modules.{u, u} B S hS (D.space TY'').1 (D.space TY'').2) :
    (modulePullback B S hS (D.relativeMap α)).map ((D.compComparison γ μ).inv.app K) ≫
        (D.compComparison α (γ ≫ μ)).inv.app K ≫ (D.relativeMapComparison hw').hom.app K ≫
          (D.compComparison β (δ ≫ μ)).hom.app K =
      (D.compComparison α γ).inv.app ((modulePullback B S hS (D.relativeMap μ)).obj K) ≫
        (D.relativeMapComparison hw).hom.app ((modulePullback B S hS (D.relativeMap μ)).obj K) ≫
          (D.compComparison β δ).hom.app ((modulePullback B S hS (D.relativeMap μ)).obj K) ≫
            (modulePullback B S hS (D.relativeMap β)).map ((D.compComparison δ μ).inv.app K) :=
  Functor.comparison_square_comp (D.compComparison α γ) (D.compComparison β δ)
    (D.compComparison γ μ) (D.compComparison δ μ) (D.compComparison (α ≫ γ) μ)
    (D.compComparison α (γ ≫ μ)) (D.compComparison (β ≫ δ) μ) (D.compComparison β (δ ≫ μ))
    (D.relativeMapComparison hw) (D.relativeMapComparison hw')
    (D.relativeMapComparison (Category.assoc α γ μ))
    (D.relativeMapComparison (Category.assoc β δ μ))
    (D.relativeMapComparison (congrArg (· ≫ μ) hw))
    (compComparison_assoc (modulePushforwardCoherence B S hS) D α γ μ)
    (compComparison_assoc (modulePushforwardCoherence B S hS) D β δ μ) K
    (D.compComparison_relativeMapComparison_comp hw μ K)
    (by simp only [relativeMapComparison_hom_app, eqToHom_trans])

end CoherentSituation


/-! ### Properness of the support across a thickening of test schemes -/

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-- **The support of a module is proper over a test scheme as soon as that of its inverse image
to a thickening of the test scheme is.**  Let `γ : T ⟶ T'` be a morphism of test schemes whose
underlying morphism of schemes is a thickening, and let `G` be a quasi-coherent `𝒪_{X_{T'}}`-module
of finite type. If the support of `(X_γ)^*G` is a closed subset proper over `T`, the support of
`G` is a closed subset proper over `T'`: the morphism `X_γ` is a thickening, hence a homeomorphism
onto `X_{T'}` carrying the support of `(X_γ)^*G` onto that of `G` (Stacks 07TZ), and a closed
immersion, hence universally closed, so the image is proper over `T'` (Stacks 0CZG). -/
theorem properSupport_of_thickening {T T' : SchemesOver D.Y} (γ : T ⟶ T')
    (hγ : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map γ.left))
    (G : Modules.{u, u} B S hS (D.space T').1 (D.space T').2) (hqc : G.IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite G)
    (h : ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection T).hom)
      (hU : IsClosed (D.support T ((modulePullback B S hS (D.relativeMap γ)).obj G))),
      IsProperOver B S hS (D.space T).2 ((schemeSpaceFunctor B S hS).obj T.left).2
        (D.projection T).hom hp (D.support T ((modulePullback B S hS (D.relativeMap γ)).obj G))
          hU) :
    ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection T').hom)
      (hU : IsClosed (D.support T' G)),
      IsProperOver B S hS (D.space T').2 ((schemeSpaceFunctor B S hS).obj T'.left).2
        (D.projection T').hom hp (D.support T' G) hU := by
  obtain ⟨hp, hU, hproper⟩ := h
  have hp' : IsLocallyOfFiniteType B S hS (D.projection T').hom :=
    isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      (D.isFinitePresentation_projection T').1
  have hpb := isPullback_baseChangeMap D.f γ
  have hthb : IsThickeningHom B S hS ((schemeSpaceFunctor B S hS).map γ.left) :=
    FormalSpace.isThickeningHom_yonedaSpace_map B S hS γ.left hγ
  have hth : IsThickeningHom B S hS (D.relativeMap γ) :=
    C1573.isThickeningHom_fst_of_isPullback B S hS hpb hthb
  obtain ⟨hci, hsurj⟩ := (isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS _).1 hth
  have hucl : UniversallyClosed B S hS (D.relativeMap γ).hom :=
    universallyClosed_of_isClosedImmersion B S hS (D.space T).2 (D.space T').2 _ hci
  have hsupp : D.support T ((modulePullback B S hS (D.relativeMap γ)).obj G) =
      pointsMap B S hS (D.space T).1 (D.relativeMap γ).hom ⁻¹' D.support T' G :=
    supportOfSheaf_modulePullback_eq B S hS (D.relativeMap γ) G hqc hft
  have himage : pointsMap B S hS (D.space T).1 (D.relativeMap γ).hom ''
      D.support T ((modulePullback B S hS (D.relativeMap γ)).obj G) = D.support T' G := by
    rw [hsupp, Set.image_preimage_eq _ hsurj]
  have hcomm : (D.relativeMap γ).hom ≫ (D.projection T').hom =
      (D.projection T).hom ≫ ((schemeSpaceFunctor B S hS).map γ.left).hom :=
    congrArg (fun k => k.hom) (baseChangeMap_comp_inclusion D.f γ)
  have hγp : IsProper B S hS ((schemeSpaceFunctor B S hS).map γ.left).hom :=
    isProper_of_isClosedImmersion B S hS ((schemeSpaceFunctor B S hS).obj T.left).2
      ((schemeSpaceFunctor B S hS).obj T'.left).2 _
      ((isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS _).1 hthb).1
  have hft' : IsLocallyOfFiniteType B S hS ((D.relativeMap γ).hom ≫ (D.projection T').hom) := by
    rw [hcomm]
    exact isLocallyOfFiniteType_comp' B S hS _ _ ((schemeSpaceFunctor B S hS).obj T.left).2
      ((schemeSpaceFunctor B S hS).obj T'.left).2 hp hγp.2.1.1
  have hTp : IsProperOver B S hS (D.space T).2 ((schemeSpaceFunctor B S hS).obj T'.left).2
      ((D.relativeMap γ).hom ≫ (D.projection T').hom) hft'
      (D.support T ((modulePullback B S hS (D.relativeMap γ)).obj G)) hU := by
    change IsProper B S hS (_ ≫ _)
    rw [hcomm, ← Category.assoc]
    exact isProper_comp B S hS (isAlgebraicSpace_reducedClosedSubspace B S hS _ _ _ _)
      ((schemeSpaceFunctor B S hS).obj T.left).2 ((schemeSpaceFunctor B S hS).obj T'.left).2
      _ _ hproper hγp
  have := isProperOver_image_of_universallyClosed B S hS (D.space T).2 (D.space T').2
    ((schemeSpaceFunctor B S hS).obj T'.left).2 (D.relativeMap γ).hom (D.projection T').hom
    hucl hft' hp' _ hU hTp
  refine ⟨hp', himage ▸ isClosed_image_of_universallyClosed B S hS (D.space T).2
    (D.space T').2 _ hucl _ hU, ?_⟩
  convert this using 2
  exact himage.symm

end CoherentSituation

/-! ### Objects of `Coh_{X/Y}` glue along a pushout -/

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-- Two morphisms of `Coh_{X/Y}` given by their components are equal once their base maps are and
their module comparisons agree through the identification of the inverse images along the two
equal base maps. -/
theorem _root_.AlgebraicGeometry.Space.CoherentHom.mk_eq_mk {A A' : CoherentObject D}
    {b b' : A.T ⟶ A'.T} (hb : b = b')
    {f : (modulePullback B S hS (D.relativeMap b)).obj A'.F ⟶ A.F}
    {f' : (modulePullback B S hS (D.relativeMap b')).obj A'.F ⟶ A.F} [IsIso f] [IsIso f']
    (hf : f = (D.relativeMapComparison hb).hom.app A'.F ≫ f') :
    (⟨b, f, inferInstance⟩ : CoherentHom A A') = ⟨b', f', inferInstance⟩ := by
  subst hb
  have : f = f' := by
    rw [hf, relativeMapComparison_hom_app, eqToHom_refl, Category.id_comp]
  subst this
  rfl

/-- The composite of a morphism of `Coh_{X/Y}` with one given by its components, written through
its components. -/
theorem _root_.AlgebraicGeometry.Space.CoherentHom.comp_mk {x y t : CoherentObject D}
    (α : CoherentHom x y) (γ : y.T ⟶ t.T)
    (eY : (modulePullback B S hS (D.relativeMap γ)).obj t.F ⟶ y.F) [IsIso eY] :
    α.comp (⟨γ, eY, inferInstance⟩ : CoherentHom y t) = ⟨α.base ≫ γ,
      Functor.fibreComp (D.compComparison α.base γ) α.fibre eY,
      by dsimp only [Functor.fibreComp]; infer_instance⟩ :=
  rfl

/-- **Two composites in `Coh_{X/Y}` agree** once their base maps do and their module comparisons
agree through the comparison of the two inverse images along the two factorizations. -/
theorem _root_.AlgebraicGeometry.Space.CoherentHom.comp_mk_eq_comp_mk {x y z t : CoherentObject D}
    (α : CoherentHom x y) (β : CoherentHom x z) (γ : y.T ⟶ t.T) (δ : z.T ⟶ t.T)
    (eY : (modulePullback B S hS (D.relativeMap γ)).obj t.F ⟶ y.F) [IsIso eY]
    (eZ : (modulePullback B S hS (D.relativeMap δ)).obj t.F ⟶ z.F) [IsIso eZ]
    (hw : α.base ≫ γ = β.base ≫ δ)
    (h : (modulePullback B S hS (D.relativeMap α.base)).map eY ≫ α.fibre =
      (D.compComparison α.base γ).inv.app t.F ≫ (D.relativeMapComparison hw).hom.app t.F ≫
        (D.compComparison β.base δ).hom.app t.F ≫
          (modulePullback B S hS (D.relativeMap β.base)).map eZ ≫ β.fibre) :
    α.comp (⟨γ, eY, inferInstance⟩ : CoherentHom y t) =
      β.comp (⟨δ, eZ, inferInstance⟩ : CoherentHom z t) := by
  rw [CoherentHom.comp_mk, CoherentHom.comp_mk]
  have : IsIso (Functor.fibreComp (D.compComparison α.base γ) α.fibre eY) := by
    dsimp only [Functor.fibreComp]; infer_instance
  have : IsIso (Functor.fibreComp (D.compComparison β.base δ) β.fibre eZ) := by
    dsimp only [Functor.fibreComp]; infer_instance
  refine CoherentHom.mk_eq_mk D hw ?_
  rw [Functor.fibreComp, Functor.fibreComp, h, Iso.hom_inv_id_app_assoc]

/-- The composite of two morphisms of `Coh_{X/Y}`, written through its components. -/
theorem _root_.AlgebraicGeometry.Space.CoherentHom.comp_eq_mk {x y t : CoherentObject D}
    (α : CoherentHom x y) (γ : CoherentHom y t) :
    α.comp γ = ⟨α.base ≫ γ.base,
      Functor.fibreComp (D.compComparison α.base γ.base) α.fibre γ.fibre,
      by dsimp only [Functor.fibreComp]; infer_instance⟩ :=
  rfl

/-- Two morphisms of `Coh_{X/Y}` given by their components which are equal have module
comparisons agreeing through the identification of the inverse images along the base maps. -/
theorem _root_.AlgebraicGeometry.Space.CoherentHom.fibre_eq_of_mk_eq {A A' : CoherentObject D}
    {b b' : A.T ⟶ A'.T}
    {f : (modulePullback B S hS (D.relativeMap b)).obj A'.F ⟶ A.F}
    {f' : (modulePullback B S hS (D.relativeMap b')).obj A'.F ⟶ A.F} {i : IsIso f}
    {i' : IsIso f'} (h : (⟨b, f, i⟩ : CoherentHom A A') = ⟨b', f', i'⟩) (hb : b = b') :
    f = (D.relativeMapComparison hb).hom.app A'.F ≫ f' := by
  subst hb
  injection h with _ hf

/-- A morphism given by its components is equal to a given morphism of `Coh_{X/Y}` once their
base maps are and their module comparisons agree through the identification of inverse images. -/
theorem _root_.AlgebraicGeometry.Space.CoherentHom.mk_eq {A A' : CoherentObject D}
    {b : A.T ⟶ A'.T} {f : (modulePullback B S hS (D.relativeMap b)).obj A'.F ⟶ A.F} [IsIso f]
    (n : CoherentHom A A') (hb : b = n.base)
    (hf : f = (D.relativeMapComparison hb).hom.app A'.F ≫ n.fibre) :
    (⟨b, f, inferInstance⟩ : CoherentHom A A') = n := by
  obtain ⟨nb, nf, ni⟩ := n
  exact CoherentHom.mk_eq_mk D hb hf

/-- **The module comparisons of two equal composites agree.** -/
theorem _root_.AlgebraicGeometry.Space.CoherentHom.fibre_eq_of_comp_eq
    {x y z t : CoherentObject D} (α : CoherentHom x y) (β : CoherentHom x z)
    (γ : CoherentHom y t) (δ : CoherentHom z t) (hE : α.comp γ = β.comp δ)
    (hw : α.base ≫ γ.base = β.base ≫ δ.base) :
    (D.compComparison α.base γ.base).hom.app t.F ≫
        (modulePullback B S hS (D.relativeMap α.base)).map γ.fibre ≫ α.fibre =
      (D.relativeMapComparison hw).hom.app t.F ≫ (D.compComparison β.base δ.base).hom.app t.F ≫
        (modulePullback B S hS (D.relativeMap β.base)).map δ.fibre ≫ β.fibre := by
  rw [CoherentHom.comp_eq_mk, CoherentHom.comp_eq_mk] at hE
  have := CoherentHom.fibre_eq_of_mk_eq D hE hw
  simpa only [Functor.fibreComp, Category.assoc] using this

/-- The comparison of Stacks 03LU for `α ≫ k` transported along an equality `k = k'` of second
factors is the identification of the inverse images along `k` and `k'`, read through `α`. -/
theorem map_relativeMapComparison_comp_compComparison_inv {T T₁ T₂ : SchemesOver D.Y}
    (α : T ⟶ T₁) {k k' : T₁ ⟶ T₂} (e : k = k')
    (K : Modules.{u, u} B S hS (D.space T₂).1 (D.space T₂).2) :
    (modulePullback B S hS (D.relativeMap α)).map ((D.relativeMapComparison e).hom.app K) ≫
        (D.compComparison α k').inv.app K =
      (D.compComparison α k).inv.app K ≫
        (D.relativeMapComparison (congrArg (α ≫ ·) e)).hom.app K := by
  subst e
  simp only [relativeMapComparison_hom_app, eqToHom_refl, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

/-- **A morphism of modules is invertible as soon as its two restrictions are**, along a square
along which modules glue. -/
theorem ModulesGlue.isIso {TX TY TX' TY' : SchemesOver D.Y} {α : TX ⟶ TY} {β : TX ⟶ TX'}
    {γ : TY ⟶ TY'} {δ : TX' ⟶ TY'} {hw : α ≫ γ = β ≫ δ} (h : D.ModulesGlue α β γ δ hw)
    {M N : Modules.{u, u} B S hS (D.space TY').1 (D.space TY').2} (hM : D.IsCoherentModule TY' M)
    (hN : D.IsCoherentModule TY' N) (φ : M ⟶ N)
    [IsIso ((modulePullback B S hS (D.relativeMap γ)).map φ)]
    [IsIso ((modulePullback B S hS (D.relativeMap δ)).map φ)] : IsIso φ :=
  Functor.isIso_of_glue (D.compComparison α γ) (D.relativeMapComparison hw) (D.compComparison β δ)
    (D.IsCoherentModule TY') h.hom_glue hM hN φ

/-- A module on a base change satisfying the conditions of Stacks 08KB is the module of an object
of `Coh_{X/Y}` over that test scheme. Stated as an existence, so that the object can be handled as
a variable: its test scheme and module are then identified with the given ones by substitution
rather than by unfolding. -/
theorem exists_coherentObject_of_isCoherentModule {T : SchemesOver D.Y}
    (G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) (hG : D.IsCoherentModule T G) :
    ∃ (t : CoherentObject D) (_ : t.T = T), HEq t.F G :=
  ⟨⟨T, G, hG.1, hG.2, hG.3, hG.4⟩, rfl, HEq.rfl⟩



/-- The inverse image of the module of an object of `Coh_{X/Y}` along a morphism of test schemes
satisfies the conditions of Stacks 08KB. -/
theorem isCoherentModule_modulePullback (A : CoherentObject D) {V : SchemesOver D.Y}
    (h : V ⟶ A.T) : D.IsCoherentModule V ((modulePullback B S hS (D.relativeMap h)).obj A.F) := by
  have hst := modulePullbackStabilityOfFinitePresentation B S hS
  have hfp := hst.finitePresentation (D.relativeMap h) A.F A.finitePresentation
  refine ⟨inferInstance, hfp, hst.flat (isPullback_baseChangeMap D.f h) A.F
    A.finitePresentation A.flat, ?_⟩
  obtain ⟨hp, hU, hproper⟩ := A.properSupport
  have := A.finitePresentation
  obtain ⟨hU', hproper'⟩ := hst.properSupport (isPullback_baseChangeMap D.f h) hp A.F
    A.quasicoherent inferInstance hU hproper
  exact ⟨(isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
    (isPullback_baseChangeMap D.f h) hp, hU', hproper'⟩

/-- Composing with a morphism given by its components: the composite is a given morphism
exactly when the inverse image of the module comparison is the one forced by the two others. -/
theorem _root_.AlgebraicGeometry.Space.CoherentHom.comp_mk_eq_iff {y t t' : CoherentObject D}
    (r : CoherentHom y t) (e : t.T ⟶ t'.T) (mY : CoherentHom y t') (hrb : r.base ≫ e = mY.base)
    (f' : (modulePullback B S hS (D.relativeMap e)).obj t'.F ⟶ t.F) [IsIso f'] :
    r.comp ⟨e, f', inferInstance⟩ = mY ↔
      (modulePullback B S hS (D.relativeMap r.base)).map f' =
        (D.compComparison r.base e).inv.app t'.F ≫ (D.relativeMapComparison hrb).hom.app t'.F ≫
          mY.fibre ≫ inv r.fibre := by
  rw [CoherentHom.comp_mk]
  have : IsIso (Functor.fibreComp (D.compComparison r.base e) r.fibre f') := by
    dsimp only [Functor.fibreComp]; infer_instance
  refine ⟨fun h ↦ ?_, fun h ↦ CoherentHom.mk_eq D mY hrb ?_⟩
  · have := CoherentHom.fibre_eq_of_mk_eq D h hrb
    simp only [Functor.fibreComp] at this
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, IsIso.hom_inv_id, Category.comp_id]
      using congrArg (fun q => (D.compComparison r.base e).inv.app t'.F ≫ q ≫ inv r.fibre) this
  · simp only [Functor.fibreComp, h, Iso.hom_inv_id_app_assoc, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id]

/-- **Morphisms of `Coh_{X/Y}` glue along a square of test schemes along which modules glue.**
Let `uY ≫ r = uZ ≫ s` and `uY ≫ mY = uZ ≫ mZ` be two commutative squares of `Coh_{X/Y}` out of
one object `x`, with `r`, `s` into `t` and `mY`, `mZ` into `t'`, and let `e : t.T ⟶ t'.T` be a
morphism of test schemes with `r.base ≫ e = mY.base` and `s.base ≫ e = mZ.base`. If modules
glue along the square of the base maps of `uY`, `uZ`, `r`, `s`, there is exactly one morphism
`t ⟶ t'` over `e` whose composites with `r` and `s` are `mY` and `mZ`. -/
theorem existsUnique_coherentHom_of_modulesGlue {x y z t t' : CoherentObject D}
    (uY : CoherentHom x y) (uZ : CoherentHom x z) (r : CoherentHom y t) (s : CoherentHom z t)
    (mY : CoherentHom y t') (mZ : CoherentHom z t') (e : t.T ⟶ t'.T)
    (hrb : r.base ≫ e = mY.base) (hsb : s.base ≫ e = mZ.base) (huZ : uZ.comp s = uY.comp r)
    (hxy : uY.comp mY = uZ.comp mZ) (hw0 : uY.base ≫ r.base = uZ.base ≫ s.base)
    (hmod : D.ModulesGlue uY.base uZ.base r.base s.base hw0) :
    ∃! m : CoherentHom t t', m.base = e ∧ r.comp m = mY ∧ s.comp m = mZ := by
  have hM : D.IsCoherentModule t.T ((modulePullback B S hS (D.relativeMap e)).obj t'.F) :=
    D.isCoherentModule_modulePullback t' e
  have hw1 : uY.base ≫ mY.base = uZ.base ≫ mZ.base := congrArg CoherentHom.base hxy
  have hw' : uY.base ≫ r.base ≫ e = uZ.base ≫ s.base ≫ e := by
    rw [← Category.assoc, hw0, Category.assoc]
  have hcomp := Functor.map_comp_overlap_of_squares (D.compComparison uY.base r.base)
    (D.compComparison uZ.base s.base) (D.compComparison r.base e) (D.compComparison s.base e)
    (D.compComparison uY.base (r.base ≫ e)) (D.compComparison uZ.base (s.base ≫ e))
    (D.compComparison uY.base mY.base) (D.compComparison uZ.base mZ.base)
    (D.relativeMapComparison hw0) (D.relativeMapComparison hw') (D.relativeMapComparison hw1)
    (D.relativeMapComparison hrb) (D.relativeMapComparison hsb)
    (D.relativeMapComparison (congrArg (uY.base ≫ ·) hrb))
    (D.relativeMapComparison (congrArg (uZ.base ≫ ·) hsb))
    uY.fibre uZ.fibre r.fibre s.fibre mY.fibre mZ.fibre
    (D.compComparison_square_comp uY.base uZ.base r.base s.base e hw0 hw' t'.F)
    (D.map_relativeMapComparison_comp_compComparison_inv uY.base hrb t'.F)
    (D.map_relativeMapComparison_comp_compComparison_inv uZ.base hsb t'.F)
    (by simp only [relativeMapComparison_hom_app, eqToHom_trans])
    (CoherentHom.fibre_eq_of_comp_eq D uY uZ r s huZ.symm hw0)
    (CoherentHom.fibre_eq_of_comp_eq D uY uZ mY mZ hxy hw1)
  obtain ⟨φ, ⟨hφY, hφZ⟩, huniqφ⟩ := hmod.hom_glue _ _ hM t.isCoherentModule _ _ hcomp
  have : IsIso ((modulePullback B S hS (D.relativeMap r.base)).map φ) := by
    rw [hφY]; infer_instance
  have : IsIso ((modulePullback B S hS (D.relativeMap s.base)).map φ) := by
    rw [hφZ]; infer_instance
  have : IsIso φ := hmod.isIso D hM t.isCoherentModule φ
  refine ⟨⟨e, φ, inferInstance⟩, ⟨rfl, (CoherentHom.comp_mk_eq_iff D r e mY hrb φ).2 hφY,
    (CoherentHom.comp_mk_eq_iff D s e mZ hsb φ).2 hφZ⟩, ?_⟩
  rintro ⟨b', f', i'⟩ ⟨hb', h₁, h₂⟩
  change b' = e at hb'
  subst hb'
  have hf' : f' = φ := huniqφ f' ⟨(CoherentHom.comp_mk_eq_iff D r b' mY hrb f').1 h₁,
    (CoherentHom.comp_mk_eq_iff D s b' mZ hsb f').1 h₂⟩
  subst hf'
  rfl

section ObjectsGlue

variable {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')

/-- **Modules glue along every square of test schemes lying over a square of schemes.**  The
condition `AlgebraicGeometry.Space.CoherentSituation.ModulesGlue` for every commutative square of
test schemes over `Y` whose underlying square of schemes is `f ≫ b = i ≫ a`. For a pushout along
a thickening and an affine morphism this is what Stacks 08KV supplies. -/
def ModulesGlueOver : Prop :=
  ∀ {TX TY TX' TY' : SchemesOver D.Y} (α : TX ⟶ TY) (β : TX ⟶ TX') (γ : TY ⟶ TY')
    (δ : TX' ⟶ TY') (hw : α ≫ γ = β ≫ δ) (hX : TX.left = X) (hY : TY.left = Y)
    (hX' : TX'.left = X') (hY' : TY'.left = Y'),
    α.left = eqToHom hX ≫ f ≫ eqToHom hY.symm → β.left = eqToHom hX ≫ i ≫ eqToHom hX'.symm →
    γ.left = eqToHom hY ≫ b ≫ eqToHom hY'.symm → δ.left = eqToHom hX' ≫ a ≫ eqToHom hY'.symm →
    D.ModulesGlue α β γ δ hw

variable {i f a b}

/-- Transporting the point of an object of `Coh_{X/Y}` along an equality of its test scheme with
`U` recovers the structure morphism of the test scheme. -/
private theorem map_eqToHom_comp_coherentObjectPoint (A : CoherentObject D)
    {U : BigFppfOver B S hS} (hA : A.T.left = U) :
    (schemeSpaceFunctor B S hS).map (eqToHom hA) ≫ coherentObjectPoint A hA = A.T.hom := by
  rw [coherentObjectPoint, ← Category.assoc, ← Functor.map_comp, eqToHom_trans, eqToHom_refl,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **Objects glue along one square of test schemes.**  If modules glue along a commutative square
`α ≫ γ = β ≫ δ` of test schemes, a span `y ← x → z` of `Coh_{X/Y}` over `α` and `β` is completed
to a commutative square by an object over the fourth corner and morphisms over `γ` and `δ`. -/
theorem exists_coherentHom_comp_eq_of_modulesGlue {x y z : CoherentObject D} {TY' : SchemesOver D.Y}
    (α : CoherentHom x y) (β : CoherentHom x z) (γ : y.T ⟶ TY') (δ : z.T ⟶ TY')
    (hw : α.base ≫ γ = β.base ≫ δ) (hmod : D.ModulesGlue α.base β.base γ δ hw) :
    ∃ (t : CoherentObject D) (ht : t.T = TY') (γ' : CoherentHom y t) (δ' : CoherentHom z t),
      γ'.base = γ ≫ eqToHom ht.symm ∧ δ'.base = δ ≫ eqToHom ht.symm ∧
        α.comp γ' = β.comp δ' := by
  obtain ⟨G, eY, eZ, hiY, hiZ, hGc, hc⟩ := hmod.obj_glue y.F z.F (α.fibre ≫ inv β.fibre)
    inferInstance y.isCoherentModule z.isCoherentModule
  obtain ⟨t, ht, hF⟩ := D.exists_coherentObject_of_isCoherentModule G hGc
  subst ht
  obtain rfl := eq_of_heq hF
  have hc' : (modulePullback B S hS (D.relativeMap α.base)).map eY ≫ α.fibre =
      (D.compComparison α.base γ).inv.app t.F ≫ (D.relativeMapComparison hw).hom.app t.F ≫
        (D.compComparison β.base δ).hom.app t.F ≫
          (modulePullback B S hS (D.relativeMap β.base)).map eZ ≫ β.fibre := by
    have := congrArg (· ≫ β.fibre) hc
    simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using this
  exact ⟨t, rfl, ⟨γ, eY, hiY⟩, ⟨δ, eZ, hiZ⟩, by rw [eqToHom_refl, Category.comp_id],
    by rw [eqToHom_refl, Category.comp_id], CoherentHom.comp_mk_eq_comp_mk D α β γ δ eY eZ hw hc'⟩

/-- **Objects of `Coh_{X/Y}` glue along a pushout along a thickening and an affine morphism**,
granted that modules glue along the squares of test schemes over it: a span `y ← x → z` of
`Coh_{X/Y}` over `Y ← X → X'` is completed to a commutative square by an object over `Y'`.

The morphism `Y' ⟶ Y` of that object is the one Stacks 07SY glues from those of `y` and `z`
(`AlgebraicGeometry.Space.existsUnique_desc_schemeSpace_of_isPushout`), and its module is a
preimage of the triple formed by the modules of `y` and `z` and the comparison through `x`. -/
theorem objectsGlue (hmod : D.ModulesGlueOver i f a b) (w : f ≫ b = i ≫ a)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hsq : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    Stack.ThickeningPushout.ObjectsGlue (coherentSiteProjection D.categoryData) f i b a := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  intro x y z α β hα hβ
  have hxT : x.1.T.left = X := x.2
  have hyT : y.1.T.left = Y := y.2
  have hzT : z.1.T.left = X' := z.2
  obtain ⟨g', ⟨hgb, hga⟩, -⟩ := existsUnique_desc_schemeSpace_of_isPushout i f a b hi hsq
    (coherentFiberPoint D y) (coherentFiberPoint D z)
    ((coherentFiberPoint_naturality D x y f α hα).trans
      (coherentFiberPoint_naturality D x z i β hβ).symm)
  have hb : (schemeSpaceFunctor B S hS).map (eqToHom hyT ≫ b) ≫ g' = y.1.T.hom := by
    rw [Functor.map_comp, Category.assoc, hgb]
    exact map_eqToHom_comp_coherentObjectPoint D y.1 hyT
  have ha : (schemeSpaceFunctor B S hS).map (eqToHom hzT ≫ a) ≫ g' = z.1.T.hom := by
    rw [Functor.map_comp, Category.assoc, hga]
    exact map_eqToHom_comp_coherentObjectPoint D z.1 hzT
  obtain ⟨T', hT', mb, ma, hmb, hma⟩ : ∃ (T' : SchemesOver D.Y) (hT' : T'.left = Y')
      (mb : y.1.T ⟶ T') (ma : z.1.T ⟶ T'), mb.left = eqToHom hyT ≫ b ≫ eqToHom hT'.symm ∧
        ma.left = eqToHom hzT ≫ a ≫ eqToHom hT'.symm :=
    ⟨CostructuredArrow.mk g', rfl, CostructuredArrow.homMk (eqToHom hyT ≫ b) hb,
      CostructuredArrow.homMk (eqToHom hzT ≫ a) ha, by rw [eqToHom_refl, Category.comp_id]; rfl,
      by rw [eqToHom_refl, Category.comp_id]; rfl⟩
  have hαl : α.base.left = eqToHom hxT ≫ f ≫ eqToHom hyT.symm :=
    IsHomLift.fac' (coherentSiteProjection D.categoryData) f α
  have hβl : β.base.left = eqToHom hxT ≫ i ≫ eqToHom hzT.symm :=
    IsHomLift.fac' (coherentSiteProjection D.categoryData) i β
  have hw : α.base ≫ mb = β.base ≫ ma := by
    refine CostructuredArrow.hom_ext _ _ ?_
    rw [CostructuredArrow.comp_left, CostructuredArrow.comp_left, hmb, hma, hαl, hβl]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [reassoc_of% w]
  obtain ⟨t, ht, γ', δ', hγ', hδ', hcomp⟩ := D.exists_coherentHom_comp_eq_of_modulesGlue α β mb ma
    hw (hmod α.base β.base mb ma hw hxT hyT hzT hT' hαl hβl hmb hma)
  have htl : t.T.left = Y' := (congrArg CostructuredArrow.left ht).trans hT'
  refine ⟨⟨t, htl⟩, γ', δ', ?_, ?_, hcomp⟩
  · refine IsHomLift.of_fac' _ b γ' y.2 htl ?_
    change γ'.base.left = _
    rw [hγ', CostructuredArrow.comp_left, hmb, CostructuredArrow.eqToHom_left]
    simp only [Category.assoc, eqToHom_trans]
    rfl
  · refine IsHomLift.of_fac' _ a δ' z.2 htl ?_
    change δ'.base.left = _
    rw [hδ', CostructuredArrow.comp_left, hma, CostructuredArrow.eqToHom_left]
    simp only [Category.assoc, eqToHom_trans]
    rfl


/-- **Morphisms of `Coh_{X/Y}` glue along a pushout along a thickening and an affine morphism**,
granted that modules glue along the squares of test schemes over it: for objects `t`, `t'` over
`Y'`, morphisms from objects `y` over `Y` and `z` over `X'`, a pair of morphisms `y ⟶ t'`,
`z ⟶ t'` agreeing on every common lift of `X` factors through a given pair `y ⟶ t`, `z ⟶ t` by
exactly one morphism `t ⟶ t'` of the fibre over `Y'`.

The two morphisms `Y' ⟶ Y` of `t` and `t'` agree, by Stacks 07SY
(`AlgebraicGeometry.Space.existsUnique_desc_schemeSpace_of_isPushout`), and the module
comparison of the factorization is the unique morphism of modules whose two restrictions are
the given ones. -/
theorem morphismsGlue (hmod : D.ModulesGlueOver i f a b) (w : f ≫ b = i ≫ a)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hsq : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    Stack.ThickeningPushout.MorphismsGlue (coherentSiteProjection D.categoryData) f i b a := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  let : (coherentSiteProjection D.categoryData).IsFibered :=
    D.isFiberedInGroupoids_siteProjection.isFibered
  intro y z t t' r s mY mZ hr hs hmY hmZ hcompat
  have hyT : y.1.T.left = Y := y.2
  have hzT : z.1.T.left = X' := z.2
  have : IsIso r.fibre := CoherentHom.isIso_fibre (A := y.1) (A' := t.1) r
  have : IsIso s.fibre := CoherentHom.isIso_fibre (A := z.1) (A' := t.1) s
  have : IsIso mY.fibre := CoherentHom.isIso_fibre (A := y.1) (A' := t'.1) mY
  have : IsIso mZ.fibre := CoherentHom.isIso_fibre (A := z.1) (A' := t'.1) mZ
  have htT : t.1.T.left = Y' := t.2
  have ht'T : t'.1.T.left = Y' := t'.2
  -- the two morphisms to the base agree
  have hpr := coherentFiberPoint_naturality D y t b r hr
  have hpmY := coherentFiberPoint_naturality D y t' b mY hmY
  have hps := coherentFiberPoint_naturality D z t a s hs
  have hpmZ := coherentFiberPoint_naturality D z t' a mZ hmZ
  obtain ⟨g, -, huniq⟩ := existsUnique_desc_schemeSpace_of_isPushout i f a b hi hsq
    (coherentFiberPoint D y) (coherentFiberPoint D z) (by
      rw [← hpr, ← hps, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, w])
  have hpt : coherentFiberPoint D t = coherentFiberPoint D t' :=
    (huniq _ ⟨hpr, hps⟩).trans (huniq _ ⟨hpmY, hpmZ⟩).symm
  obtain ⟨e, he⟩ : ∃ e : t.1.T ⟶ t'.1.T, e.left = eqToHom (htT.trans ht'T.symm) :=
    ⟨CostructuredArrow.homMk (eqToHom (htT.trans ht'T.symm)) (by
      rw [← map_eqToHom_comp_coherentObjectPoint D t.1 htT,
        ← map_eqToHom_comp_coherentObjectPoint D t'.1 ht'T, ← Category.assoc, ← Functor.map_comp,
        eqToHom_trans]
      exact congrArg ((schemeSpaceFunctor B S hS).map (eqToHom htT) ≫ ·) hpt.symm), rfl⟩
  -- a common lift of `X`
  let c := (coherentSiteProjection D.categoryData).chosenPullbacks
  let x := c.obj f y
  let uY : CoherentHom x.1 y.1 := c.map f y
  have huY : (coherentSiteProjection D.categoryData).IsHomLift f (c.map f y) := inferInstance
  have hxT : x.1.T.left = X := x.2
  have huYl : uY.base.left = eqToHom hxT ≫ f ≫ eqToHom hyT.symm :=
    IsHomLift.fac' (coherentSiteProjection D.categoryData) f (c.map f y)
  have hrl : r.base.left = eqToHom hyT ≫ b ≫ eqToHom htT.symm :=
    IsHomLift.fac' (coherentSiteProjection D.categoryData) b r
  have hsl : s.base.left = eqToHom hzT ≫ a ≫ eqToHom htT.symm :=
    IsHomLift.fac' (coherentSiteProjection D.categoryData) a s
  have hmYl : mY.base.left = eqToHom hyT ≫ b ≫ eqToHom ht'T.symm :=
    IsHomLift.fac' (coherentSiteProjection D.categoryData) b mY
  have hmZl : mZ.base.left = eqToHom hzT ≫ a ≫ eqToHom ht'T.symm :=
    IsHomLift.fac' (coherentSiteProjection D.categoryData) a mZ
  obtain ⟨uZ, huZl, huZ⟩ := D.exists_fillIn (X := t.1) (Y := z.1) (Z := x.1) s (uY.comp r)
    (eqToHom hxT ≫ i ≫ eqToHom hzT.symm) (by
      change _ = (uY.base ≫ r.base).left
      rw [CostructuredArrow.comp_left, huYl, hrl, hsl]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [reassoc_of% w])
  have huZh : (coherentSiteProjection D.categoryData).IsHomLift i (show x.1 ⟶ z.1 from uZ) :=
    IsHomLift.of_fac' _ i _ hxT hzT huZl
  have hxy : uY.comp mY = uZ.comp mZ :=
    hcompat x (c.map f y) uZ huY huZh huZ.symm
  -- the square of test schemes and its modules
  have hw0 : uY.base ≫ r.base = uZ.base ≫ s.base := (congrArg CoherentHom.base huZ).symm
  have hrb : r.base ≫ e = mY.base := by
    refine CostructuredArrow.hom_ext _ _ ?_
    rw [CostructuredArrow.comp_left, hrl, he, hmYl]
    simp only [Category.assoc, eqToHom_trans]
  have hsb : s.base ≫ e = mZ.base := by
    refine CostructuredArrow.hom_ext _ _ ?_
    rw [CostructuredArrow.comp_left, hsl, he, hmZl]
    simp only [Category.assoc, eqToHom_trans]
  have hmod' := hmod uY.base uZ.base r.base s.base hw0 hxT hyT hzT htT huYl huZl hrl hsl
  obtain ⟨m, ⟨hmb, hm₁, hm₂⟩, hmu⟩ :=
    D.existsUnique_coherentHom_of_modulesGlue uY uZ r s mY mZ e hrb hsb huZ hxy hw0 hmod'
  have hml : (coherentSiteProjection D.categoryData).IsHomLift (𝟙 Y') (show t.1 ⟶ t'.1 from m) :=
    IsHomLift.of_fac' _ _ _ htT ht'T (by
      change m.base.left = _
      rw [hmb, he, Category.id_comp]
      exact (eqToHom_trans htT ht'T.symm).symm)
  refine ⟨⟨m, hml⟩, ⟨hm₁, hm₂⟩, ?_⟩
  rintro ⟨m', hm'⟩ ⟨h₁, h₂⟩
  have hb' : (show CoherentHom t.1 t'.1 from m').base = e := by
    refine CostructuredArrow.hom_ext _ _ ?_
    have := IsHomLift.fac' (coherentSiteProjection D.categoryData) (𝟙 Y') m'
    change (show CoherentHom t.1 t'.1 from m').base.left = _ at this
    rw [this, he, Category.id_comp]
    exact eqToHom_trans htT ht'T.symm
  exact Functor.Fiber.hom_ext (hmu m' ⟨hb', h₁, h₂⟩)

/-- **The reduction of Stacks 08LQ to the gluing of modules.**  For a pushout of schemes over `S`
along a thickening `i` and an affine morphism `f`, if modules glue along every square of test
schemes over it, the functor `Coh_{X/Y, Y'} ⟶ Coh_{X/Y, Y} ×_{Coh_{X/Y, X}} Coh_{X/Y, X'}` on
fibre categories is an equivalence. Objects and morphisms glue by
`AlgebraicGeometry.Space.CoherentSituation.objectsGlue` and
`AlgebraicGeometry.Space.CoherentSituation.morphismsGlue`, and
`AlgebraicGeometry.Stack.ThickeningPushout.fiberSquareComparison_isEquivalence_of_glue` turns
these into an equivalence. The hypothesis `hmod` is what Stacks 08KV supplies. -/
theorem fiberSquareComparison_isEquivalence_of_modulesGlueOver
    (hmod : D.ModulesGlueOver i f a b) (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hsq : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    letI : (coherentSiteProjection D.categoryData).IsFibered :=
      D.isFiberedInGroupoids_siteProjection.isFibered
    (Deformation.Artin.fiberSquareComparison (coherentSiteProjection D.categoryData)
      (coherentSiteProjection D.categoryData).chosenPullbacks f i b a w.symm).IsEquivalence :=
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  let : (coherentSiteProjection D.categoryData).IsFibered :=
    D.isFiberedInGroupoids_siteProjection.isFibered
  Stack.ThickeningPushout.fiberSquareComparison_isEquivalence_of_glue
    D.isFiberedInGroupoids_siteProjection w.symm (D.objectsGlue hmod w.symm hi hsq)
    (D.morphismsGlue hmod w.symm hi hsq)

end ObjectsGlue

end CoherentSituation

end AlgebraicGeometry.Space

end
