module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyCompositionPresented
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocallyOfFiniteTypeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SourceCoverImpliesEveryDiagram
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransferRefined
public import StacksFrontier.RingTheory.Rig.RigSmoothLocality
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianAdicDescentCompletionOver

/-!
# Stacks 0ANG, condition (3) implies condition (1), for locally Noetherian formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. Remark 0ANI says that for a local property
`P` of morphisms of `WAdmᴺᵒᵉᵗʰ` the same argument as for Stacks 0ANG gives the equivalence of its
three conditions for a morphism of locally Noetherian formal algebraic spaces. This file proves
the implication (3) ⟹ (1) of that variant, with nothing assumed beyond the source's hypotheses.

## Main results

* `AlgebraicGeometry.FormalSpace.isNoetherian_of_isRepresentableEtale_of_isLocallyNoetherian`:
  an affine formal algebraic space representable étale over a locally Noetherian formal
  algebraic space is Noetherian. This is the implication (2) ⟹ (1) of Stacks 0AKX at the
  property "Noetherian".
* `AlgebraicGeometry.FormalSpace.hasChartsPresentedByClass_of_isLocallyNoetherian`: the charts
  of a locally Noetherian formal algebraic space are presented by rings of `WAdmᴺᵒᵉᵗʰ`.
* `FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocallyNoetherian`:
  the variant of Stacks 0ANG of Remark 0ANI, condition (3) implies condition (1).

## Implementation notes

The chart `Z ⟶ X` is countably indexed (the implication (2) ⟹ (1) of Stacks 0AKX at countable
indexing, a Noetherian affine formal algebraic space being countably indexed), hence
`Z = Spf A` for a ring `A` of `WAdmᶜᵒᵘⁿᵗ` (Stacks 0AN1). The atlas of `X` refined against `Z` is
a family of Noetherian affine formal algebraic spaces representable étale over `Z` (Stacks 0AJ3
for the fibre products, clause (5) of Stacks 0AKQ along the étale maps to the Noetherian
members of the atlas), and quasi-compactness of `Z` cuts it down to a finite one. By Stacks 0AN8
and Stacks 0AN9 that finite covering of `Z` is the formal spectrum of the completion
`(R₁)^∧ ≅ ∏ᵢ Wᵢ` of a faithfully flat étale ring map `c : A → R₁`
(`AlgebraicGeometry.FormalSpace.isCompletedEtaleFiniteCoverOfChartMap_of_presentation`, applied
to the identity of `Z`). Each `Wᵢ` presents a Noetherian affine formal algebraic space, so it is
adic and Noetherian (Stacks 0AIC), hence so is the finite product, and
`TopologicalRing.CompletionOver.isNoetherianAdic_of_faithfullyFlat` descends this to `A`. That
is the argument of Stacks 0AKX with Stacks 0AKW, with the finite disjoint union of the source
read on rings.

Situation 0CBA calls `P` local when it is "a property of morphisms of `WAdm^{count}`,
invariant under isomorphism of source and target in this category" satisfying the three axioms,
and Remark 0ANI asks the same on `WAdm^{Noeth}`. The three axioms are
`TopologicalRing.PropertyIsLocalNoetherian`; the invariance under isomorphism is the
hypothesis `hPiso`, as in
`FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocallyCountablyIndexed`.

## References

* [Stacks Project, Tag 0AKQ](https://stacks.math.columbia.edu/tag/0AKQ)
* [Stacks Project, Tag 0AKW](https://stacks.math.columbia.edu/tag/0AKW)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AN9](https://stacks.math.columbia.edu/tag/0AN9)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The charts of a locally Noetherian formal algebraic space are Noetherian.** Let `X` be a
locally Noetherian formal algebraic space over `S` and let `g : Z ⟶ X` be representable by
algebraic spaces and étale, with `Z` an affine formal algebraic space. Then `Z` is Noetherian.
This is the implication (2) ⟹ (1) of **Stacks 0AKX** at the property "Noetherian".

`Z` is `Spf A` for a ring `A` of `WAdmᶜᵒᵘⁿᵗ`. The Noetherian atlas of `X` refined against `Z`
and cut down to a finite subfamily is, by Stacks 0AN8 and Stacks 0AN9, the formal spectrum of
the completion of a faithfully flat étale ring map `c : A → R₁`, and that completion is the
product of the rings presenting the members, which are adic and Noetherian. The descent
`TopologicalRing.CompletionOver.isNoetherianAdic_of_faithfullyFlat` concludes. -/
theorem isNoetherian_of_isRepresentableEtale_of_isLocallyNoetherian {X : FppfSheaf B S hS}
    (hX : IsLocallyNoetherian B S hS X) {Z : FppfSheaf B S hS} (g : Z ⟶ X)
    (hZ : IsAffineFormalAlgebraicSpace B S hS Z) (hg : IsRepresentableEtale B S hS g) :
    IsNoetherian B S hS Z := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have hZc : IsCountablyIndexed B S hS Z :=
    isCountablyIndexed_of_isRepresentableEtale_of_isLocallyCountablyIndexed B S hS X
      (isLocallyCountablyIndexed_of_isLocallyNoetherian' hX) Z g hZ hg
  obtain ⟨PZ, hwa, hcount⟩ :=
    hasCountableWeakPresentation_of_isCountablyIndexedAffine B S hS Z ⟨hZ, hZc⟩
  obtain ⟨eZ⟩ := PZ.iso
  -- the Noetherian atlas of `X` refined against `Z`, cut down to a finite subfamily
  obtain ⟨hXf, I, Xi, fi, hXiaff, hXiet, hXisurj, hXinoeth⟩ := hX
  obtain ⟨K, U, w, κ, v, hUaff, hUet, hvet, hcov⟩ :=
    exists_affineEtaleFamily_over_chart_of_atlas B S hS hXf Xi fi hXiaff hXiet hXisurj g hZ hg
  have hUnoeth : ∀ k, IsNoetherian B S hS (U k) := fun k ↦
    isNoetherian_of_isRepresentable' B S hS (v k) (hUaff k) (hXiaff (κ k)) (hvet k).1
      (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS (v k) (hvet k)) (hXinoeth (κ k))
  obtain ⟨σ, hσ, k, hsub⟩ :=
    exists_finite_subfamily_isAffineEtaleCover_of_isAffineFormalAlgebraicSpace B S hS hZ U w
      ⟨hUaff, hUet, hcov⟩
  -- the finite covering, presented by the completion of a faithfully flat étale ring map
  have hcover := isCompletedEtaleFiniteCoverOfChartMap_of_presentation B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible (fun _ _ _ _ _ hX ↦ hX)
    (fun φ _ _ hX ↦ TopologicalRing.isCountablyWeaklyAdmissible_completionOver φ hX)
    (fun e he he' hX ↦ TopologicalRing.isCountablyWeaklyAdmissible_of_ringEquiv e he he' hX)
    (τ := 𝟙 Z) hσ (fun s ↦ w (k s)) (fun s ↦ w (k s)) (fun _ ↦ 𝟙 Z) hsub (fun _ ↦ hZ)
    (fun _ ↦ isRepresentableEtale_of_isIso B S hS (𝟙 Z)) (fun _ ↦ by simp)
  obtain ⟨gid, hgid, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hwa hwa
    (eZ.inv ≫ 𝟙 Z ≫ eZ.hom)
  have hA : TopologicalRing.IsAdic PZ.ring ∧ IsNoetherianRing PZ.ring := by
    refine hcover PZ.ring PZ.ring ⟨hwa, hcount⟩ ⟨hwa, hcount⟩ hwa PZ.system PZ.system eZ eZ gid
      (by rw [hgid]; simp) _ ?_
    intro ι _ κ' Zr Wr Bz R₁ _ _ _ _ _ _ _ _ _ _ _ hCZ hCW hCWpi hZwa Dz Ew eW eZ' μ hμ bz hbz
      ez hezc hezcs c hc hcff ew hewc hewcs hewg
    -- each ring of the product presents a Noetherian affine formal algebraic space
    have hWnoeth : ∀ i, TopologicalRing.IsNoetherianAdic (Wr i) := by
      intro i
      obtain ⟨-, M, _, _, _, _, ⟨hMwa, ⟨Pr⟩⟩, hMnoeth, hMadic⟩ := hUnoeth (k (κ' i))
      obtain ⟨-, -, φ, -, -, -, -, hφ, hφ'⟩ :=
        exists_continuous_ringEquiv_of_formalSpectrum_iso hMwa (hCW i).1
          ((eW i).symm ≪≫ Pr.formalSpectrumIso)
      exact TopologicalRing.isNoetherianAdic_of_ringEquiv φ hφ hφ' ⟨hMadic, hMnoeth⟩
    have : ∀ i, IsNoetherianRing (Wr i) := fun i ↦ (hWnoeth i).2
    have hprod : TopologicalRing.IsNoetherianAdic (∀ i, Wr i) :=
      ⟨Rig.isAdic_pi Wr fun i ↦ (hWnoeth i).1, inferInstance⟩
    have hcompl : TopologicalRing.IsAdic (TopologicalRing.CompletionOver c) ∧
        IsNoetherianRing (TopologicalRing.CompletionOver c) :=
      TopologicalRing.isNoetherianAdic_of_ringEquiv ew.symm hewcs (by simpa using hewc) hprod
    exact TopologicalRing.CompletionOver.isNoetherianAdic_of_faithfullyFlat hwa c hcff hcompl
  exact ⟨(isPresentingRing_of_isCountablyIndexed B S hS hZ hZc).1, PZ.ring, inferInstance,
    inferInstance, inferInstance, inferInstance,
    ⟨hwa, ⟨PZ.system.weakIdealColimitPresentation.ofIso eZ⟩⟩, hA.2, hA.1⟩

/-- **The charts of a locally Noetherian formal algebraic space are presented by rings of
`WAdmᴺᵒᵉᵗʰ`.** They are Noetherian by
`AlgebraicGeometry.FormalSpace.isNoetherian_of_isRepresentableEtale_of_isLocallyNoetherian`, and
the presenting ring of a Noetherian affine formal algebraic space is adic and Noetherian. -/
theorem hasChartsPresentedByClass_of_isLocallyNoetherian {X : FppfSheaf B S hS}
    (hX : IsLocallyNoetherian B S hS X) :
    HasChartsPresentedByClass B S hS TopologicalRing.IsNoetherianAdic X := fun U a hU ha ↦
  exists_spfPresentation_of_isNoetherian B S hS U
    (isNoetherian_of_isRepresentableEtale_of_isLocallyNoetherian B S hS hX a hU ha)

/-- **The variant of Stacks 0ANG for locally Noetherian formal algebraic spaces (Remark 0ANI),
condition (3) implies condition (1).** Let `f : X ⟶ Y` be a morphism of locally Noetherian
formal algebraic spaces over `S` and let `P` be a local property of morphisms of `WAdmᴺᵒᵉᵗʰ`
(Remark 0ANI: `hP` for the three axioms of Situation 0CBA on `WAdmᴺᵒᵉᵗʰ` and `hPiso` for
"invariant under isomorphism of source and target in this category"). If there are an affine
étale covering `{Uᵢ ⟶ X}` as in Definition 0AIM and factorizations `Uᵢ ⟶ Vᵢ ⟶ Y` through
affine formal algebraic spaces representable étale over `Y` with `P` on each `Uᵢ ⟶ Vᵢ`, then
for every commutative square with affine formal algebraic spaces `U`, `V` and representable
étale maps `U ⟶ X`, `V ⟶ Y`, the morphism `U ⟶ V` has `P`.

This is
`FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_hasChartsPresentedByClass`
at the class `WAdmᴺᵒᵉᵗʰ`: its rings are weakly admissible with a countable fundamental system
of open ideals, being adic; the class is closed under completion along an étale ring map by
clause (5) of Stacks 0ANB, an étale algebra over a Noetherian ring being Noetherian; and it is
closed under isomorphism of topological rings. The charts of `X` and `Y` are presented by rings
of the class by
`AlgebraicGeometry.FormalSpace.hasChartsPresentedByClass_of_isLocallyNoetherian`. -/
@[stacks 0ANI "the variant of Lemma 0ANG for morphisms of locally Noetherian formal algebraic \
spaces, condition (3) implies condition (1); hP and hPiso together are the local property of \
WAdm^Noeth"]
theorem hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocallyNoetherian
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.PropertyIsLocalNoetherian P)
    (hPiso : ∀ {B A B' A' : Type u}
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [CommRing B'] [TopologicalSpace B'] [IsTopologicalRing B'] [IsLinearTopology B' B']
      [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
      (eB : B ≃+* B') (eA : A ≃+* A'), Continuous eB → Continuous eB.symm →
      Continuous eA → Continuous eA.symm → ∀ (f : B →+* A), Continuous f →
      TopologicalRing.IsNoetherianAdic B → TopologicalRing.IsNoetherianAdic A →
      TopologicalRing.IsNoetherianAdic B' → TopologicalRing.IsNoetherianAdic A' →
      (P f ↔ P ((eA.toRingHom.comp f).comp eB.symm.toRingHom)))
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hf : HasPropertyAfterSourceCover B S hS TopologicalRing.IsNoetherianAdic P f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic P f :=
  hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_hasChartsPresentedByClass B S hS
    TopologicalRing.IsNoetherianAdic P hP hPiso
    (fun _ _ _ _ _ hR ↦ ⟨hR.1.isWeaklyAdmissible, Rig.countablyGenerated_nhds_of_isAdicRing hR.1⟩)
    (fun {X Y} _ _ _ _ _ φ _ hφ hR ↦ by
      let : Algebra X Y := φ.toAlgebra
      have : Algebra.Etale X Y := hφ
      have : IsNoetherianRing X := hR.2
      exact TopologicalRing.completionOver_isNoetherianAdic φ hR
        (Algebra.FiniteType.isNoetherianRing X Y))
    (fun e he he' hR ↦ TopologicalRing.isNoetherianAdic_of_ringEquiv e he he' hR) f
    (hasChartsPresentedByClass_of_isLocallyNoetherian B S hS hX)
    (hasChartsPresentedByClass_of_isLocallyNoetherian B S hS hY) hf

end AlgebraicGeometry.FormalSpace

end
