module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyCompositionPresented
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SourceCoverImpliesEveryDiagram
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableSourceRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransferRefined

/-!
# The cancellation property of a local property of morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. Let `P` be a local property of morphisms of
`WAdmᶜᵒᵘⁿᵗ` with the cancellation property, and let `f : X ⟶ Y`, `g : Y ⟶ Z` be morphisms of
locally countably indexed formal algebraic spaces over `S`. If `g ∘ f` and `g` satisfy
`HasPropertyOnEveryAffineEtaleDiagram`, then `f` satisfies it, together with the equivalent
conditions `HasPropertyAfterTargetCover` and `HasPropertyAfterSourceCover`.

## Main results

* `AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_of_comp_of_spfPresentation`: the
  cancellation axiom read on a composable pair `U ⟶ V ⟶ W` of morphisms of affine formal
  algebraic spaces whose last object is presented by a ring of the class.
* `AlgebraicGeometry.FormalSpace.exists_presentedSourceCover_of_comp_of_atlas` and
  `AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_of_comp_of_atlas`:
  `HasPropertyAfterSourceCover` for the first factor, on an affine étale covering of its source.
* `FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_comp_of_isLocallyCountablyIndexed`:
  the cancellation property for locally countably indexed formal algebraic spaces.

## Implementation notes

A local property of `WAdmᶜᵒᵘⁿᵗ` is "a property of morphisms of `WAdm^{count}`, invariant under
isomorphism of source and target in this category" satisfying the three axioms. The three axioms
and the cancellation property are `TopologicalRing.PropertyIsLocalWithCancellation`; the
invariance under isomorphism is the hypothesis `hPiso`, as in
`hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocallyCountablyIndexed`.

## References

* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN1](https://stacks.math.columbia.edu/tag/0AN1)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 0GBL](https://stacks.math.columbia.edu/tag/0GBL)
* [Stacks Project, Tag 0GBM](https://stacks.math.columbia.edu/tag/0GBM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- The cancellation property, read on a composable pair `U ⟶ V ⟶ W` of morphisms of affine
formal algebraic spaces whose last object is presented by a ring of the class `C`: if
`s : V ⟶ W` and `t ≫ s` have `P`, so has `t`.

Given a presentation `g` of `t` by rings of `C`, `s` is presented by a continuous homomorphism
`gs` out of the ring presenting `W`, and `g ∘ gs` presents `t ≫ s`; the two hypotheses give
`P gs` and `P (g ∘ gs)`, and cancellation gives `P g`. -/
theorem hasPropertyOnAffineChartMap_of_comp_of_spfPresentation
    (hCwa : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C R → TopologicalRing.IsWeaklyAdmissible R)
    (hcancel : ∀ {A M R : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A] [CommRing M] [TopologicalSpace M] [IsTopologicalRing M]
      [IsLinearTopology M M] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C A → C M → C R → ∀ (φ : M →+* R) (ψ : A →+* M),
      Continuous φ → Continuous ψ → P ψ → P (φ.comp ψ) → P φ)
    {U V W : FppfSheaf B S hS} (t : U ⟶ V) (s : V ⟶ W)
    (hW : ∃ PW : SpfPresentation B S hS W, C PW.ring)
    (hs : HasPropertyOnAffineChartMap B S hS C P s)
    (hts : HasPropertyOnAffineChartMap B S hS C P (t ≫ s)) :
    HasPropertyOnAffineChartMap B S hS C P t := by
  intro A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV g hg
  obtain ⟨PW, hCW⟩ := hW
  obtain ⟨eW⟩ := PW.iso
  have hWwa := hCwa PW.ring hCW
  obtain ⟨gs, hgs, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hWwa hA
    (eV.inv ≫ s ≫ eW.hom)
  have hPs : P gs.toRingHom := hs PW.ring A hCW hCA hWwa PW.system D eV eW gs (by rw [hgs]; simp)
  have hPts : P (ContinuousHom.comp hA hWwa g gs).toRingHom := by
    refine hts PW.ring R hCW hCR hWwa PW.system E eU eW (ContinuousHom.comp hA hWwa g gs) ?_
    rw [← formalSpectrumMap_comp_eq hA hWwa g gs, hgs, hg]
    simp
  rw [ContinuousHom.comp_toRingHom] at hPts
  exact hcancel hCW hCA hCR g.toRingHom gs.toRingHom g.continuous gs.continuous hPs hPts

/-- If `P` has the cancellation property on arrows of the class `C` and `g ∘ f`, `g` satisfy
`HasPropertyOnEveryAffineEtaleDiagram`, then `f` satisfies `HasPropertyAfterSourceCover`, on a
covering whose members and the charts of `Y` they factor through are presented by rings of `C`.
The atlases of `X`, `Y` and `Z` are asked to consist of charts with a property `Q` which passes
along representable étale maps of affine formal algebraic spaces and makes them presented by
rings of `C`.

Each member `Uᵢ ⟶ X` of the covering factors as `Uᵢ ⟶ Vᵢ ⟶ Y`, and `Vᵢ ⟶ Y` as
`Vᵢ ⟶ Wᵢ ⟶ Z`; `P` holds on `Vᵢ ⟶ Wᵢ` by the hypothesis on `g` and on `Uᵢ ⟶ Wᵢ` by the
hypothesis on `g ∘ f`, so it holds on `Uᵢ ⟶ Vᵢ` by cancellation. -/
theorem exists_presentedSourceCover_of_comp_of_atlas
    (hCwa : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C R → TopologicalRing.IsWeaklyAdmissible R)
    (hcancel : ∀ {A M R : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A] [CommRing M] [TopologicalSpace M] [IsTopologicalRing M]
      [IsLinearTopology M M] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C A → C M → C R → ∀ (φ : M →+* R) (ψ : A →+* M),
      Continuous φ → Continuous ψ → P ψ → P (φ.comp ψ) → P φ)
    (Q : FppfSheaf B S hS → Prop)
    (hQ : ∀ {V' V : FppfSheaf B S hS} (e : V' ⟶ V), IsAffineFormalAlgebraicSpace B S hS V' →
      IsAffineFormalAlgebraicSpace B S hS V → IsRepresentableEtale B S hS e → Q V → Q V')
    (hQC : ∀ V : FppfSheaf B S hS, IsAffineFormalAlgebraicSpace B S hS V → Q V →
      ∃ PV : SpfPresentation B S hS V, C PV.ring)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hXQ : HasAffineEtaleAtlasWithProperty B S hS X Q)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hYQ : HasAffineEtaleAtlasWithProperty B S hS Y Q)
    (hZ : IsFormalAlgebraicSpace B S hS Z) (hZQ : HasAffineEtaleAtlasWithProperty B S hS Z Q)
    (hfg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P (f ≫ g))
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P g) :
    ∃ (I : Type (u + 1)) (U V : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X)
      (v : ∀ i, V i ⟶ Y) (t : ∀ i, U i ⟶ V i),
      IsAffineEtaleCover B S hS U u ∧ (∀ i, IsAffineFormalAlgebraicSpace B S hS (V i)) ∧
        (∀ i, IsRepresentableEtale B S hS (v i)) ∧ (∀ i, u i ≫ f = t i ≫ v i) ∧
        (∀ i, HasPropertyOnAffineChartMap B S hS C P (t i)) ∧
        (∀ i, ∃ PU : SpfPresentation B S hS (U i), C PU.ring) ∧
        ∀ i, ∃ PV : SpfPresentation B S hS (V i), C PV.ring := by
  obtain ⟨I, U, V, W, u, t, s, v, w, hUcover, hUQ, hVaffine, hVQ, hWaffine, hWQ, hv, hw, hsq₁,
    hsq₂, hs⟩ := exists_affineEtaleCover_chartFactorization_comp_of_atlas B S hS C P Q hQ f g
      hXQ hY hYQ hZ hZQ hg
  refine ⟨I, U, V, u, v, t, hUcover, hVaffine, hv, hsq₁, fun i ↦ ?_,
    fun i ↦ hQC (U i) (hUcover.1 i) (hUQ i), fun i ↦ hQC (V i) (hVaffine i) (hVQ i)⟩
  refine hasPropertyOnAffineChartMap_of_comp_of_spfPresentation B S hS C P hCwa hcancel (t i)
    (s i) (hQC (W i) (hWaffine i) (hWQ i)) (hs i)
    (hfg (U i) (W i) (u i) (w i) (t i ≫ s i) (hUcover.1 i) (hWaffine i) (hUcover.2.1 i) (hw i)
      ?_)
  rw [← Category.assoc, hsq₁ i, Category.assoc, hsq₂ i, Category.assoc]

/-- If `P` has the cancellation property on arrows of the class `C` and `g ∘ f`, `g` satisfy
`HasPropertyOnEveryAffineEtaleDiagram`, then `f` satisfies `HasPropertyAfterSourceCover`. The
atlases of `X`, `Y` and `Z` are asked to consist of charts with a property `Q` which passes along
representable étale maps of affine formal algebraic spaces and makes them presented by rings of
`C`. -/
theorem hasPropertyAfterSourceCover_of_comp_of_atlas
    (hCwa : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C R → TopologicalRing.IsWeaklyAdmissible R)
    (hcancel : ∀ {A M R : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A] [CommRing M] [TopologicalSpace M] [IsTopologicalRing M]
      [IsLinearTopology M M] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C A → C M → C R → ∀ (φ : M →+* R) (ψ : A →+* M),
      Continuous φ → Continuous ψ → P ψ → P (φ.comp ψ) → P φ)
    (Q : FppfSheaf B S hS → Prop)
    (hQ : ∀ {V' V : FppfSheaf B S hS} (e : V' ⟶ V), IsAffineFormalAlgebraicSpace B S hS V' →
      IsAffineFormalAlgebraicSpace B S hS V → IsRepresentableEtale B S hS e → Q V → Q V')
    (hQC : ∀ V : FppfSheaf B S hS, IsAffineFormalAlgebraicSpace B S hS V → Q V →
      ∃ PV : SpfPresentation B S hS V, C PV.ring)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hXQ : HasAffineEtaleAtlasWithProperty B S hS X Q)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hYQ : HasAffineEtaleAtlasWithProperty B S hS Y Q)
    (hZ : IsFormalAlgebraicSpace B S hS Z) (hZQ : HasAffineEtaleAtlasWithProperty B S hS Z Q)
    (hfg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P (f ≫ g))
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P g) :
    HasPropertyAfterSourceCover B S hS C P f := by
  obtain ⟨I, U, V, u, v, t, hUcover, hVaffine, hv, hsq, ht, -, -⟩ :=
    exists_presentedSourceCover_of_comp_of_atlas B S hS C P hCwa hcancel Q hQ hQC f g hXQ hY
      hYQ hZ hZQ hfg hg
  exact ⟨I, U, u, hUcover, fun i ↦ ⟨V i, v i, t i, hVaffine i, hv i, hsq i, ht i⟩⟩

/-- Let `P` be a local property of morphisms of `WAdmᶜᵒᵘⁿᵗ` which has the cancellation
property, and let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally countably indexed formal
algebraic spaces over `S`. If `g ∘ f` and `g` satisfy `HasPropertyOnEveryAffineEtaleDiagram`,
then `f` satisfies `HasPropertyOnEveryAffineEtaleDiagram`, `HasPropertyAfterTargetCover` and
`HasPropertyAfterSourceCover`.

Here `P` being local with the cancellation property is `hP` (the three axioms and the
cancellation property) together with `hPiso`, the clause that `P` is "invariant under isomorphism
of source and target in this category". -/
@[stacks 0GBM]
theorem hasPropertyOnEveryAffineEtaleDiagram_of_comp_of_isLocallyCountablyIndexed
    (hP : TopologicalRing.PropertyIsLocalWithCancellation P)
    (hPiso : ∀ {B A B' A' : Type u}
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [CommRing B'] [TopologicalSpace B'] [IsTopologicalRing B'] [IsLinearTopology B' B']
      [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
      (eB : B ≃+* B') (eA : A ≃+* A'), Continuous eB → Continuous eB.symm →
      Continuous eA → Continuous eA.symm → ∀ (f : B →+* A), Continuous f →
      TopologicalRing.IsCountablyWeaklyAdmissible B →
      TopologicalRing.IsCountablyWeaklyAdmissible A →
      TopologicalRing.IsCountablyWeaklyAdmissible B' →
      TopologicalRing.IsCountablyWeaklyAdmissible A' →
      (P f ↔ P ((eA.toRingHom.comp f).comp eB.symm.toRingHom)))
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hZ : IsLocallyCountablyIndexed B S hS Z)
    (hfg : HasPropertyOnEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible P (f ≫ g))
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible P g) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS
        TopologicalRing.IsCountablyWeaklyAdmissible P f ∧
      HasPropertyAfterTargetCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P f ∧
      HasPropertyAfterSourceCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P f := by
  have h3 : HasPropertyAfterSourceCover B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible P f :=
    hasPropertyAfterSourceCover_of_comp_of_atlas B S hS _ P (fun _ _ _ _ _ h ↦ h.1)
      (fun hA hM hR φ ψ hφ hψ hPψ hPφψ ↦ hP.cancellation φ ψ hR hM hA hφ hψ ⟨hPψ, hPφψ⟩)
      (IsCountablyIndexed B S hS)
      (fun e hV' hV he hVc ↦ isCountablyIndexed_of_isRepresentable' B S hS e hV' hV he.1 hVc)
      (fun V _ hV ↦ exists_spfPresentation_of_isCountablyIndexed B S hS V hV)
      f g hX.2 hY.1 hY.2 hZ.1 hZ.2 hfg hg
  have h1 : HasPropertyOnEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible P f :=
    hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocallyCountablyIndexed B S hS
      P hP.isLocal hPiso f hX hY h3
  exact ⟨h1, hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram_of_formal' B S hS _ P f
    hX.1 hY.1 h1, h3⟩

end AlgebraicGeometry.FormalSpace

end
