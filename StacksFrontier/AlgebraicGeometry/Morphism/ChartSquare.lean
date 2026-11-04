module

public import StacksFrontier.AlgebraicGeometry.Morphism.Composition
public import StacksFrontier.AlgebraicGeometry.ProjMapComposition.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Comparison

/-!
# The data of Tag 07ZG along a morphism of relative Proj given by `Proj.map` on charts

Let `ψ : A ⟶ B` be a homomorphism of quasi-coherent graded `𝒪_Y`-algebras and `ψ' : A' ⟶ B'` one
of quasi-coherent graded `𝒪_{Y'}`-algebras, and let `c_A : Proj_{Y'}(A') ⟶ Proj_Y(A)` and
`c_B : Proj_{Y'}(B') ⟶ Proj_Y(B)` be morphisms which, on the charts over the members of an open
cover of `Y'` by affine opens `W'`, are `Proj` of graded ring maps `σ_A : Γ(W, A) ⟶ Γ(W', A')` and
`σ_B : Γ(W, B) ⟶ Γ(W', B')` (for affine opens `W` of `Y`) followed by the charts over `W`, with
`σ_B ∘ ψ_W = ψ'_{W'} ∘ σ_A`. Then the open `U(ψ')` of Tag 07ZG is the inverse image of `U(ψ)`
under `c_B`, and `c_A ∘ r_{ψ'} = r_ψ ∘ c_B|_{U(ψ')}`.

Both the base-change morphism of Tag 01O3 and the isomorphism of relative Proj induced by an
isomorphism of graded algebras are of this kind, so this is the compatibility of Tag 07ZG with
both.

## Main definitions

* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.ChartSquare`: the chart-wise data over one affine open
  `W'` of `Y'`.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.preimage_relativeMapDomain_of_chartSquare`:
  `c_B⁻¹(U(ψ)) = U(ψ')`.
* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.relativeMapHom_comp_of_chartSquare`:
  `r_{ψ'} ≫ c_A = c_B|_{U(ψ')} ≫ r_ψ`.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwistGlue
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.RelativeProjMapComp

universe u

namespace Stacks.AlgebraicGeometry.Tag07ZGMorphism

/-! ### Two facts about `Proj.map` and about morphisms out of an open subscheme -/

/-- If `a ≫ b` fixes a monomorphism `ι` from the left, then `a ≫ b` can be inserted in front of
any morphism out of `X`. -/
private theorem eq_comp_comp_of_comp_comp_eq {C : Type*} [Category C] {X Y Z W : C} {ι : X ⟶ W}
    [Mono ι] {a : X ⟶ Y} {b : Y ⟶ X} (h : a ≫ b ≫ ι = ι) (f : X ⟶ Z) : f = a ≫ b ≫ f := by
  have : a ≫ b = 𝟙 X := by rw [← cancel_mono ι, Category.assoc, h, Category.id_comp]
  rw [← Category.assoc, this, Category.id_comp]

section Generalities

variable {A B C : Type u} {σ τ υ : Type u}
  [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike υ C] [AddSubgroupClass υ C]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → υ) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **The inverse image of a domain of definition under `Proj.map`** is the domain of definition
of the composite. -/
theorem proj_map_preimage_mapDomain (φ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒞)
    (hχ : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant ℬ).map χ) :
    AlgebraicGeometry.Proj.map χ hχ ⁻¹ᵁ mapDomain 𝒜 ℬ φ = mapDomain 𝒜 𝒞 (χ.comp φ) := by
  have hdom := mapDomain_eq_top_of_irrelevant_le_map ℬ 𝒞 χ hχ
  rw [← mapHomOfTop_eq_map ℬ 𝒞 χ hχ hdom, mapHomOfTop, Scheme.Hom.comp_preimage,
    Scheme.Hom.comp_preimage, mapHom_preimage_mapDomain 𝒜 ℬ 𝒞 φ χ,
    ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, Category.assoc,
    topIso_inv_isoOfEq_hom_ι ℬ 𝒞 χ hdom, Scheme.Hom.id_preimage]

/-- On a domain of definition that is everything, the morphism of Tag 01MY is `Proj.map`. -/
theorem mapHom_eq_ι_comp_proj_map (χ : 𝒜 →+*ᵍ ℬ)
    (hχ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map χ) :
    mapHom 𝒜 ℬ χ = (mapDomain 𝒜 ℬ χ).ι ≫ AlgebraicGeometry.Proj.map χ hχ := by
  have hdom := mapDomain_eq_top_of_irrelevant_le_map 𝒜 ℬ χ hχ
  rw [← mapHomOfTop_eq_map 𝒜 ℬ χ hχ hdom, mapHomOfTop]
  refine (eq_comp_comp_of_comp_comp_eq (a := (mapDomain 𝒜 ℬ χ).ι) (ι := (mapDomain 𝒜 ℬ χ).ι)
    (b := (Scheme.topIso _).inv ≫ ((AlgebraicGeometry.Proj ℬ).isoOfEq hdom.symm).hom)
    (by simp) _).trans ?_
  simp only [Category.assoc]

end Generalities

/-- **Morphisms out of an open subscheme agree once they agree on the members of a cover.** -/
theorem hom_ext_of_le_iSup {X Z : Scheme.{u}} (O : X.Opens) {ι : Type*} (V : ι → X.Opens)
    (hV : ∀ i, V i ≤ O) (hcov : O ≤ ⨆ i, V i) (f g : O.toScheme ⟶ Z)
    (H : ∀ i, X.homOfLE (hV i) ≫ f = X.homOfLE (hV i) ≫ g) : f = g := by
  refine Scheme.hom_ext_of_forall f g fun x => ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov x.2)
  refine ⟨O.ι ⁻¹ᵁ V i, hi, ?_⟩
  have hle : O.ι ⁻¹ᵁ V i ≤ O.ι ⁻¹ᵁ V i := le_rfl
  have hfac : (O.ι ⁻¹ᵁ V i).ι = O.ι.resLE (V i) (O.ι ⁻¹ᵁ V i) hle ≫ X.homOfLE (hV i) := by
    rw [← cancel_mono O.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι]
  rw [hfac, Category.assoc, Category.assoc, H i]

/-! ### Chart squares -/

variable {Y Y' : Scheme.{u}} {A B : SheafGradedAlgebra Y} {A' B' : SheafGradedAlgebra Y'}
  (ψ : SheafGradedAlgebraHom A B) (ψ' : SheafGradedAlgebraHom A' B')
  (cA : (relativeProj A').scheme ⟶ (relativeProj A).scheme)
  (cB : (relativeProj B').scheme ⟶ (relativeProj B).scheme)

/-- **A chart square over an affine open `W'` of `Y'`**: an affine open `W` of `Y` and graded ring
maps `σ_A : Γ(W, A) ⟶ Γ(W', A')`, `σ_B : Γ(W, B) ⟶ Γ(W', B')` such that `c_A` and `c_B` are
`Proj σ_A` and `Proj σ_B` on the charts over `W'`, the square `σ_B ∘ ψ_W = ψ'_{W'} ∘ σ_A`
commutes, and precomposing `ψ'_{W'}` with `σ_A` does not change its domain of definition. -/
structure ChartSquare (W' : Y'.Opens) (hW' : IsAffineOpen W') where
  /-- The affine open of `Y` below `W'`. -/
  W : Y.Opens
  /-- It is affine. -/
  hW : IsAffineOpen W
  /-- The graded ring map of sections of the sources. -/
  σA : A.grading W →+*ᵍ A'.grading W'
  /-- The graded ring map of sections of the targets. -/
  σB : B.grading W →+*ᵍ B'.grading W'
  /-- `Proj σ_A` is defined. -/
  hσA : HomogeneousIdeal.irrelevant (A'.grading W') ≤
    (HomogeneousIdeal.irrelevant (A.grading W)).map σA
  /-- `Proj σ_B` is defined. -/
  hσB : HomogeneousIdeal.irrelevant (B'.grading W') ≤
    (HomogeneousIdeal.irrelevant (B.grading W)).map σB
  /-- `c_A` on the chart over `W'`. -/
  chart_cA : (relativeProj A').chart W' hW' ≫ cA =
    AlgebraicGeometry.Proj.map σA hσA ≫ (relativeProj A).chart W hW
  /-- `c_B` on the chart over `W'`. -/
  chart_cB : (relativeProj B').chart W' hW' ≫ cB =
    AlgebraicGeometry.Proj.map σB hσB ≫ (relativeProj B).chart W hW
  /-- The square of graded ring maps commutes. -/
  comm : σB.comp (ψ.sectionHom W) = (ψ'.sectionHom W').comp σA
  /-- Precomposition with `σ_A` does not change the domain of definition of `ψ'_{W'}`. -/
  mapDomain_comp : mapDomain (A.grading W) (B'.grading W') ((ψ'.sectionHom W').comp σA) =
    mapDomain (A'.grading W') (B'.grading W') (ψ'.sectionHom W')

variable {ψ ψ' cA cB}

/-- On a chart square, the inverse image of `U(ψ)` under `c_B` read on the chart over `W'` is the
chart domain of `ψ'`. -/
theorem ChartSquare.chart_preimage {W' : Y'.Opens} {hW' : IsAffineOpen W'}
    (sq : ChartSquare ψ ψ' cA cB W' hW') :
    (relativeProj B').chart W' hW' ⁻¹ᵁ (cB ⁻¹ᵁ ψ.relativeMapDomain) =
      (relativeProj B').chart W' hW' ⁻¹ᵁ ψ'.relativeMapDomain := by
  rw [← Scheme.Hom.comp_preimage, sq.chart_cB, Scheme.Hom.comp_preimage,
    ψ.chart_preimage_relativeMapDomain sq.W sq.hW, ψ'.chart_preimage_relativeMapDomain W' hW',
    SheafGradedAlgebraHom.chartDomain, SheafGradedAlgebraHom.chartDomain,
    proj_map_preimage_mapDomain, sq.comm, sq.mapDomain_comp]

/-- A point of `Proj_{Y'}(B')` lying over an affine open `W'` of `Y'` is in the image of the chart
over `W'`. -/
theorem exists_chart_eq {W' : Y'.Opens} (hW' : IsAffineOpen W') (x : (relativeProj B').scheme)
    (hx : (relativeProj B').toBase x ∈ W') :
    ∃ z, (relativeProj B').chart W' hW' z = x := by
  have hx' : x ∈ (relativeProj B').toBase ⁻¹ᵁ W' := hx
  rw [← chart_image_top (relativeProj B') W' hW'] at hx'
  obtain ⟨z, -, hz⟩ := hx'
  exact ⟨z, hz⟩

variable (hsq : ∀ y : Y', ∃ (W' : Y'.Opens) (hW' : IsAffineOpen W'), y ∈ W' ∧
  Nonempty (ChartSquare ψ ψ' cA cB W' hW'))

include hsq

/-- **The open of Tag 07ZG along a chart square: `c_B⁻¹(U(ψ)) = U(ψ')`.** -/
theorem preimage_relativeMapDomain_of_chartSquare :
    cB ⁻¹ᵁ ψ.relativeMapDomain = ψ'.relativeMapDomain := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  obtain ⟨W', hW', hy, ⟨sq⟩⟩ := hsq ((relativeProj B').toBase x)
  obtain ⟨z, rfl⟩ := exists_chart_eq hW' x hy
  have h := congrArg (fun O : (AlgebraicGeometry.Proj (B'.grading W')).Opens => z ∈ O)
    sq.chart_preimage
  exact h.to_iff

/-- **The morphism of Tag 07ZG along a chart square: `r_{ψ'} ≫ c_A = c_B|_{U(ψ')} ≫ r_ψ`.** -/
theorem relativeMapHom_comp_of_chartSquare :
    relativeMapHom ψ' ≫ cA =
      cB.resLE ψ.relativeMapDomain ψ'.relativeMapDomain
          (preimage_relativeMapDomain_of_chartSquare hsq).ge ≫ relativeMapHom ψ := by
  set I := {p : AffineOpen Y' // Nonempty (ChartSquare ψ ψ' cA cB p.1 p.2)}
  have hpiece : ∀ i : I, chartImage ψ' i.1 ≤ ψ'.relativeMapDomain :=
    fun i => chartImage_le ψ' i.1
  refine hom_ext_of_le_iSup _ (fun i : I => chartImage ψ' i.1) hpiece ?_ _ _ ?_
  · intro x hx
    obtain ⟨W', hW', hy, hne⟩ := hsq ((relativeProj B').toBase x)
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W', hW'⟩, hne⟩, ?_⟩
    rw [chartImage_eq_inf ψ' ⟨W', hW'⟩]
    exact ⟨hx, hy⟩
  · rintro ⟨⟨W', hW'⟩, ⟨sq⟩⟩
    set D' := mapDomain (A'.grading W') (B'.grading W') (ψ'.sectionHom W')
    set D := mapDomain (A.grading sq.W) (B.grading sq.W) (ψ.sectionHom sq.W)
    rw [← cancel_epi (((relativeProj B').chart W' hW').isoImage D').hom]
    -- the composite with `σ_B ∘ ψ_W`, through the outer factor
    obtain ⟨q, hq, hq'⟩ := mapHom_comp_of_eq (A.grading sq.W) (B.grading sq.W)
      (B'.grading W') (ψ.sectionHom sq.W) sq.σB rfl
      (mapDomain_comp_le_of_eq _ _ _ (ψ.sectionHom sq.W) sq.σB rfl)
    -- the composite with `ψ'_{W'} ∘ σ_A`, through the inner factor
    obtain ⟨q₂, hq₂, hq₂'⟩ := mapHom_comp_of_eq (A.grading sq.W) (A'.grading W')
      (B'.grading W') sq.σA (ψ'.sectionHom W') sq.comm
      (mapDomain_comp_le_of_eq _ _ _ sq.σA (ψ'.sectionHom W') sq.comm)
    have hD : D' = mapDomain (A.grading sq.W) (B'.grading W') (sq.σB.comp (ψ.sectionHom sq.W)) :=
      by rw [sq.comm, sq.mapDomain_comp]
    set e := ((AlgebraicGeometry.Proj (B'.grading W')).isoOfEq hD).hom
    have he : e ≫ (AlgebraicGeometry.Proj (B'.grading W')).homOfLE
        (mapDomain_comp_le_of_eq _ _ _ sq.σA (ψ'.sectionHom W') sq.comm) ≫ D'.ι = D'.ι := by
      rw [Scheme.homOfLE_ι, Scheme.isoOfEq_hom_ι]
    have hmapσA := mapHom_eq_ι_comp_proj_map (A.grading sq.W) (A'.grading W') sq.σA sq.hσA
    have hmapσB := mapHom_eq_ι_comp_proj_map (B.grading sq.W) (B'.grading W') sq.σB sq.hσB
    -- the morphism `D' ⟶ U(ψ)` factors through the chart domain over `W`
    have hk : (((relativeProj B').chart W' hW').isoImage D').hom ≫
        (relativeProj B').scheme.homOfLE (hpiece ⟨⟨W', hW'⟩, ⟨sq⟩⟩) ≫
          cB.resLE ψ.relativeMapDomain ψ'.relativeMapDomain
            (preimage_relativeMapDomain_of_chartSquare hsq).ge =
        e ≫ q ≫ (((relativeProj B).chart sq.W sq.hW).isoImage D).hom ≫
          (relativeProj B).scheme.homOfLE (chartImage_le ψ ⟨sq.W, sq.hW⟩) := by
      rw [← cancel_mono ψ.relativeMapDomain.ι]
      simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc,
        Scheme.homOfLE_ι, Scheme.Hom.isoImage_hom_ι_assoc, Scheme.Hom.isoImage_hom_ι]
      rw [sq.chart_cB, reassoc_of% hq, hmapσB]
      simp only [Category.assoc, Scheme.homOfLE_ι_assoc, e, Scheme.isoOfEq_hom_ι_assoc]
    -- the two composites with `σ_B ∘ ψ_W`
    have hf : mapHom (A'.grading W') (B'.grading W') (ψ'.sectionHom W') ≫
        AlgebraicGeometry.Proj.map sq.σA sq.hσA =
        e ≫ q ≫ mapHom (A.grading sq.W) (B.grading sq.W) (ψ.sectionHom sq.W) := by
      refine (eq_comp_comp_of_comp_comp_eq he _).trans ?_
      rw [← reassoc_of% hq₂, ← hmapσA, ← hq₂', hq']
    calc (((relativeProj B').chart W' hW').isoImage D').hom ≫
          (relativeProj B').scheme.homOfLE (hpiece ⟨⟨W', hW'⟩, ⟨sq⟩⟩) ≫ relativeMapHom ψ' ≫ cA
        = (mapHom (A'.grading W') (B'.grading W') (ψ'.sectionHom W') ≫
            (relativeProj A').chart W' hW') ≫ cA := by
          rw [← chart_comp_relativeMapHom ψ' ⟨W', hW'⟩]
          simp only [Category.assoc]
          rfl
      _ = e ≫ q ≫ mapHom (A.grading sq.W) (B.grading sq.W) (ψ.sectionHom sq.W) ≫
            (relativeProj A).chart sq.W sq.hW := by
          rw [Category.assoc, sq.chart_cA, ← Category.assoc, hf]
          simp only [Category.assoc]
      _ = e ≫ q ≫ (((relativeProj B).chart sq.W sq.hW).isoImage D).hom ≫
            (relativeProj B).scheme.homOfLE (chartImage_le ψ ⟨sq.W, sq.hW⟩) ≫
              relativeMapHom ψ := by
          rw [chart_comp_relativeMapHom ψ ⟨sq.W, sq.hW⟩]
      _ = _ := by
          rw [← reassoc_of% hk]

end Stacks.AlgebraicGeometry.Tag07ZGMorphism

end
