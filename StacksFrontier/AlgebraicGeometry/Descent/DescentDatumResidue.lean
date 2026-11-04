module

public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumStepThreeToFive

/-!
# The residue of Stacks 0APK over an affine base, machine-checked

Let `f : X ⟶ S` be a surjective flat quasi-compact morphism of affine schemes and let `D` be a
descent datum relative to `f` whose scheme `V` over `X` is ind-quasi-affine. This is the case to
which the proof of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) reduces by Stacks
02W3, and it is the case that the two consumers of that tag in this library ask for — see the
implementation notes of `StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentSizeBound`, which
record that Stacks 02W3 lies off the route from here to Stacks 0APL.

Of the five steps of the source's proof of that case, **step 3 is proved unconditionally** as
`AlgebraicGeometry.exists_mem_isTransitionInvariant_isTransitionInvariantSet_descentDatum` and
**steps 4 and 5 are proved** as
`AlgebraicGeometry.DescentDatum.exists_subalgebra_isPushout_and_existsUnique_opens_of_invariant`,
whose only remaining hypothesis is coassociativity of the unit of `ψ`. This file records, as one
compiled statement, exactly what is left: the single theorem below derives effectivity of `D` from
four named hypotheses and nothing else, so each of the four is an obligation and together they are
sufficient.

**This is not Stacks 0APK and carries no tag.** It is a reduction: a statement with four
hypotheses which no declaration of this repository discharges. Its value is that the four are
*exhaustive* — that is what the proof checks — so they may be discharged one at a time with nothing
else required.

## Main results

* `AlgebraicGeometry.DescentDatum.isEffective_of_unitCoassoc_of_preimage_of_restrictOpen`:
  **the four obligations that remain for Stacks 0APK over an affine base.**

## Implementation notes

*The four hypotheses, and where each comes from in the source.*

1. `hkey` is the cocycle condition for the gluing isomorphism `φ` transported to the isomorphism
   `ψ` of Stacks 0APJ, in the coassociative form that
   `AlgebraicGeometry.ModuleCat.isPushout_descentInvariants_of_isPushout` consumes. The source
   writes "The cocycle condition for `φ` translates into the cocycle condition for `ψ` as in
   Descent, Definition 023G (details omitted)".
2. `hpreimage` is the compatibility of the two preimages of `j(W)` in
   `Spec Γ(E, 𝒪_V|_E) ×_{Spec C₀} Spec Γ(E, 𝒪_V|_E)`, which the source reads off the commutative
   diagram relating `j` to the embeddings `j'` and `j''` of `E ×_S X` and `X ×_S E`. The
   naturality of `j` that this needs is proved, as
   `AlgebraicGeometry.toΓSpec_base_sectionsRingOnSubsetMap`; what is not proved is the comparison
   of the images of `j` and `j'`, i.e. that the intersection `E'` of Stacks 0API is compatible
   with the flat base change `Spec Γ(X, ⊤) ⟶ Spec Γ(S, ⊤)`.
3. `hrestrict` is the step the source performs as "Contemplating the diagram above we see that the
   descent datum `(W, φ|_{W ×_S X})` is effective": the open `W₀` of `Spec C₀` whose base change
   is `j(W)` trivializes the restriction of `D` to `W`. It needs the isomorphism half of Stacks
   0API, proved as `AlgebraicGeometry.exists_iInter_iso_iInter_in_specΓ`, together with the
   identification of the restricted gluing isomorphism with the canonical one.
4. `hglueing` is [Stacks, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4), the final appeal.
   It is stated here with the *equality* `AlgebraicGeometry.DescentDatum.IsTransitionInvariant`
   where the source writes the inclusion `φ(W ×_S X) ⊆ X ×_S W`; since
   `AlgebraicGeometry.DescentDatum.isTransitionInvariant_of_le` turns the inclusion into the
   equality, the two are interchangeable, and
   `AlgebraicGeometry.DescentDatum.exists_openImmersionHom_isEffective_iff` makes this shape
   interchangeable with the one the Lean statement of that tag uses. Steps 3 and 4 of its own proof
   are proved in `StacksFrontier.AlgebraicGeometry.Descent.Scheme.CanonicalInvariantOpen`; the
   glueing itself is not.

*Why `hkey` is quantified over the algebra structures.* `Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)` holds only
through `f.appTop` and so cannot be an instance, and the subset `E` that `hkey` speaks about is
produced inside the proof by step 3. The hypothesis therefore quantifies over the subset, over the
three algebra structures and over the three equations identifying each `algebraMap` with its
geometric morphism — which is the same shape in which
`StacksFrontier.AlgebraicGeometry.Descent.DescentDatumStepFourFive` states them, so an eventual proof
of `hkey` slots in without transport. The same applies to `hpreimage` and `hrestrict`.

*No tag is placed*, for the reason given above.

## References

* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
* [Stacks Project, Tag 0API](https://stacks.math.columbia.edu/tag/0API)
* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
* [Stacks Project, Tag 023G](https://stacks.math.columbia.edu/tag/023G)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace AlgebraicGeometry.DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f)

/-- **The four obligations that remain for [Stacks, Tag
0APK](https://stacks.math.columbia.edu/tag/0APK) over an affine base.**  Let `f : X ⟶ S` be a
surjective flat quasi-compact morphism of affine schemes and let `D` be a descent datum relative
to `f` whose scheme over `X` is ind-quasi-affine.  Then `D` is effective as soon as

1. the unit of the transition isomorphism `ψ` of Stacks 0APJ is coassociative, for every
   intersection `E` of a nonempty family of quasi-compact opens of `V` which is invariant under
   the gluing isomorphism set-theoretically — this is the cocycle condition for `φ` transported to
   `ψ`, which the source performs with "details omitted";
2. the two preimages of the image `j(W)` of an invariant open `W ⊆ E` agree in
   `Spec Γ(E, 𝒪_V|_E) ×_{Spec C₀} Spec Γ(E, 𝒪_V|_E)`, for every `Γ(S, ⊤)`-subalgebra `C₀` of
   `Γ(E, 𝒪_V|_E)` whose base change to `Γ(X, ⊤)` is `Γ(E, 𝒪_V|_E)`;
3. an open `W₀` of `Spec C₀` whose preimage in `Spec Γ(E, 𝒪_V|_E)` is `j(W)` makes the restriction
   of `D` to `W` effective;
4. Stacks 0AP4 holds for `D`: effectivity of the restrictions of `D` to a family of invariant
   opens covering `V` implies effectivity of `D`.

Everything else the source's proof uses is proved: step 3 by
`AlgebraicGeometry.exists_mem_isTransitionInvariant_isTransitionInvariantSet_descentDatum`, the
packaging of `j(W)` by `AlgebraicGeometry.DescentDatum.exists_opens_coe_eq_subsetΓSpecImage`, and
steps 4 and 5 by
`AlgebraicGeometry.DescentDatum.exists_subalgebra_isPushout_and_existsUnique_opens_of_invariant`,
whose faithful-flatness and quasi-separatedness hypotheses are discharged here from `[Flat f]`,
`[Surjective f]` and `[IsIndQuasiAffineHom D.over.hom]`.

This statement is **not** Stacks 0APK: it carries four hypotheses that no declaration of this
repository discharges.  What it establishes is that those four are *exhaustive*. -/
theorem isEffective_of_unitCoassoc_of_preimage_of_restrictOpen
    [IsAffine S] [IsAffine X] [Flat f] [Surjective f] [QuasiCompact f]
    [IsIndQuasiAffineHom D.over.hom]
    (hkey : ∀ (E : Set D.over.left)
      [Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)] [Algebra ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      [Algebra ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      [IsScalarTower ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      (hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop)
      (hRC : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
        (D.over.hom ≫ f).appTop ≫ D.over.left.topToSubset E)
      (hAC : CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
        D.over.hom.appTop ≫ D.over.left.topToSubset E)
      [QuasiSeparatedSpace D.over.left] {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
      (hU : ∀ i, IsCompact (U i : Set D.over.left)) (hE : E = ⋂ i, (U i : Set D.over.left))
      (h₁ : (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
        ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
      (h₂ : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
        ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E))
      (c : ↥(D.over.left.sectionsRingOnSubset E)),
      LinearMap.lTensor ↥Γ(X, ⊤)
          (ModuleCat.algebraUnitTransition ↥Γ(S, ⊤) ↥Γ(X, ⊤) _
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂))
          (ModuleCat.algebraUnitTransition ↥Γ(S, ⊤) ↥Γ(X, ⊤) _
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂) c) =
        LinearMap.lTensor ↥Γ(X, ⊤)
          (TensorProduct.mk ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E) 1)
          (ModuleCat.algebraUnitTransition ↥Γ(S, ⊤) ↥Γ(X, ⊤) _
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂) c))
    (hpreimage : ∀ (E : Set D.over.left)
      [Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)] [Algebra ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      [Algebra ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      [IsScalarTower ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
      (_hU : ∀ i, IsCompact (U i : Set D.over.left)) (_hE : E = ⋂ i, (U i : Set D.over.left))
      (W : D.over.left.Opens) (_hWinv : D.IsTransitionInvariant W)
      (_hWE : (W : Set D.over.left) ⊆ E)
      (C₀ : Subalgebra ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E))
      (_hpush : Algebra.IsPushout ↥Γ(S, ⊤) ↥Γ(X, ⊤) C₀ ↥(D.over.left.sectionsRingOnSubset E)),
      (pullback.fst (Spec.map (CommRingCat.ofHom
              (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E))))
            (Spec.map (CommRingCat.ofHom
              (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E))))).base ⁻¹'
          subsetΓSpecImage D.over.left E (W : Set D.over.left) =
        (pullback.snd (Spec.map (CommRingCat.ofHom
              (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E))))
            (Spec.map (CommRingCat.ofHom
              (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E))))).base ⁻¹'
          subsetΓSpecImage D.over.left E (W : Set D.over.left))
    (hrestrict : ∀ (E : Set D.over.left)
      [Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)] [Algebra ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      [Algebra ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      [IsScalarTower ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
      (_hU : ∀ i, IsCompact (U i : Set D.over.left)) (_hE : E = ⋂ i, (U i : Set D.over.left))
      (W : D.over.left.Opens) (hWinv : D.IsTransitionInvariant W)
      (_hWE : (W : Set D.over.left) ⊆ E)
      (C₀ : Subalgebra ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E))
      (_hpush : Algebra.IsPushout ↥Γ(S, ⊤) ↥Γ(X, ⊤) C₀ ↥(D.over.left.sectionsRingOnSubset E))
      (W₀ : (Spec (CommRingCat.of C₀)).Opens)
      (_hW₀ : ((Spec.map (CommRingCat.ofHom
          (algebraMap C₀ ↥(D.over.left.sectionsRingOnSubset E))) ⁻¹ᵁ W₀ :
            (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E))).Opens) :
          Set (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E)))) =
        subsetΓSpecImage D.over.left E (W : Set D.over.left)),
      DescentData.IsEffective (D.restrictOpen W hWinv))
    (hglueing : (∀ v : D.over.left, ∃ (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W),
        v ∈ W ∧ DescentData.IsEffective (D.restrictOpen W hW)) →
      DescentData.IsEffective D) :
    DescentData.IsEffective D := by
  refine hglueing fun v => ?_
  obtain ⟨W, E, I, hI, U, hWinv, hU, hEeq, hEinv, hv, hWE, -⟩ :=
    D.exists_mem_isTransitionInvariant_subsetΓSpecOpens v
  have _ := hI
  refine ⟨W, hWinv, hv, ?_⟩
  let _instRA : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let _instAC : Algebra ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E) :=
    (D.over.hom.appTop ≫ D.over.left.topToSubset E).hom.toAlgebra
  let _instRC : Algebra ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E) :=
    ((D.over.hom ≫ f).appTop ≫ D.over.left.topToSubset E).hom.toAlgebra
  have hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop := by
    rfl
  have hAC : CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
      D.over.hom.appTop ≫ D.over.left.topToSubset E := by
    rfl
  have hRC : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
      (D.over.hom ≫ f).appTop ≫ D.over.left.topToSubset E := by
    rfl
  have hst : IsScalarTower ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have h : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
        CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) ≫
          CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤)
            ↥(D.over.left.sectionsRingOnSubset E)) := by
      rw [hRA, hAC, hRC, Scheme.Hom.comp_appTop, Category.assoc]
    exact congrArg CommRingCat.Hom.hom h
  have hiqa : IsIndQuasiAffine D.over.left := isIndQuasiAffine_of_isIndQuasiAffineHom_hom D.over
  have hqs : QuasiSeparatedSpace D.over.left :=
    quasiSeparatedSpace_of_isIndQuasiAffineHom_hom D.over
  obtain ⟨C₀, hpush, hdesc⟩ :=
    D.exists_subalgebra_isPushout_and_existsUnique_opens_of_invariant E hRA hRC hAC U hU hEeq
      hEinv (fun c => hkey E hRA hRC hAC U hU hEeq _ _ c)
  obtain ⟨W₀, hW₀, -⟩ := hdesc
    (subsetΓSpecOpens D.over.left U hU E (W : Set D.over.left) hEeq hWE W.isOpen)
    (hpreimage E U hU hEeq W hWinv hWE C₀ hpush)
  exact hrestrict E U hU hEeq W hWinv hWE C₀ hpush W₀ (by rw [hW₀]; rfl)

end AlgebraicGeometry.DescentDatum

end

end
