module

public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumResidue
public import StacksFrontier.AlgebraicGeometry.Descent.DescentInvariantsProjections
public import StacksFrontier.AlgebraicGeometry.Descent.OpenSubsetFaithfullyFlatBaseChange

/-!
# The residue of Stacks 0APK over an affine base, with the descended ring named

`AlgebraicGeometry.DescentDatum.isEffective_of_unitCoassoc_of_preimage_of_restrictOpen` reduces
effectivity of a descent datum over an affine base to four obligations. Two of those four —
`hpreimage` and `hrestrict` — are quantified over **an arbitrary** `Γ(S, ⊤)`-subalgebra `C₀` of
`Γ(E, 𝒪_V|_E)` with `Algebra.IsPushout Γ(S, ⊤) Γ(X, ⊤) C₀ Γ(E, 𝒪_V|_E)`, because the subalgebra
reaches that proof through the existential of
`AlgebraicGeometry.DescentDatum.exists_subalgebra_isPushout_and_existsUnique_opens_of_invariant`.
That is stronger than the source's step 5, which speaks only about the subalgebra of
`ψ`-invariants: for a different `C₀` with the same base-change property, the condition on the two
preimages is the condition for a *different* descent structure on `Γ(E, 𝒪_V|_E)` over `Γ(S, ⊤)`,
and the invariance of `W` under the gluing isomorphism says nothing about it. The implementation
notes of `StacksFrontier.AlgebraicGeometry.Descent.DescentInvariantsProjections` record the same
observation from the other side: once the existential is destructed, a consumer can no longer see
that `C₀` *is* `ModuleCat.descentInvariants`, so no statement about the two comparison legs of
Stacks 0APJ applies to it.

This file is the same reduction with the subalgebra named. It uses
`AlgebraicGeometry.DescentDatum.isPushout_descentInvariants_of_invariantSet`, which already
delivers the pushout property at `ModuleCat.descentInvariants`, together with
`ModuleCat.preimage_pullback_eq_of_preimage_specMap_eq` and
`AlgebraicGeometry.existsUnique_opens_preimage_eq_of_isPushout`, exactly as the notes of that
file prescribe. Two things change:

* the obligation about preimages becomes a condition on the two comparison legs of Stacks 0APJ,
  `iC ≫ Φ` and `kC`, which mentions **no subalgebra at all**;
* the obligation about the restricted datum is asked for only at the subalgebra of invariants and
  at an open of its spectrum, so a single `W₀` has to be handled rather than one for every `C₀`.

The other two obligations, the coassociativity `hkey` and Stacks 0AP4 as `hglueing`, are
unchanged, character for character, from the statement they have in
`StacksFrontier.AlgebraicGeometry.Descent.DescentDatumResidue`.

## Main results

* `ModuleCat.existsUnique_opens_preimage_eq_descentInvariants` : **step 5 of the proof of Stacks
  0APK at the named subalgebra.** An open of `Spec C` whose preimages under the two comparison
  legs of Stacks 0APJ agree descends uniquely to `Spec C₀` for `C₀` the invariants.
* `AlgebraicGeometry.DescentDatum.isEffective_of_unitCoassoc_of_legs_of_restrictOpen` : **the
  three obligations that remain for Stacks 0APK over an affine base, besides Stacks 0AP4.**

## Implementation notes

*What this is not.* It is not a proof of Stacks 0APK and carries no tag; it is a reduction, like
the statement it replaces. Nor does it claim that the four obligations of the earlier statement
are false — no counterexample is offered. What is established here is that the three obligations
below suffice, and they are the ones the source's own argument addresses.

*Why the legs condition is the right shape.* By
`ModuleCat.isPullback_specMap_descentInvariants` the ring `Q = Γ(X ×_S E, 𝒪)` of the second
pushout square of Stacks 0APJ *is* `C ⊗_{C₀} C`, with the two coprojections given by `iC ≫ Φ` and
`kC`. So `Spec Q` is the fibre product `Spec C ×_{Spec C₀} Spec C` that Stacks 03N0 asks about,
and the condition on the two projections is the condition on the two legs — which are the maps
the commutative diagram of step 4 of the source relates to the embeddings `j'` and `j''` of
`E ×_S X` and `X ×_S E`. The legs are the canonical restriction maps
`AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap` of the two projections of the fibre products,
composed on one side with the isomorphism `Φ` the gluing isomorphism induces, so the condition is
stated entirely in terms of the datum.

*Where the stage-level case of the legs condition is.* With `E = ⋂ᵢ Uᵢ` the legs condition at
`j(W)` is the comparison of the image of `j` with the base change of that image; its single-open
case, for a quasi-compact open in place of the intersection `E`, is proved as
`AlgebraicGeometry.preimage_specMap_appLE_image_toSpecΓ`. The implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.StageEmbeddingBaseChange` say exactly what passing from
that case to the intersection still needs.

## References

* [Stacks Project, Tag 0API](https://stacks.math.columbia.edu/tag/0API)
* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry

universe u

namespace ModuleCat

variable {R A C : Type u} [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra A C]
    [Algebra R C] [IsScalarTower R A C] {P Q : CommRingCat.{u}}
    {iC : CommRingCat.of C ⟶ P} {iA : CommRingCat.of A ⟶ P}
    {kA : CommRingCat.of A ⟶ Q} {kC : CommRingCat.of C ⟶ Q}

variable (hP : IsPushout (CommRingCat.ofHom (algebraMap R C))
      (CommRingCat.ofHom (algebraMap R A)) iC iA)
    (hQ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R C)) kA kC)
    (Φ : P ≅ Q)
    (h1 : CommRingCat.ofHom (algebraMap A C) ≫ iC ≫ Φ.hom = kA)
    (h2 : iA ≫ Φ.hom = CommRingCat.ofHom (algebraMap A C) ≫ kC)

include h1 h2 in
/-- **Step 5 of the proof of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) at the
named subalgebra.**  In the situation of
`ModuleCat.isPushout_descentInvariants_of_isPushout`, let `C₀` be the subalgebra of
`ψ`-invariants and suppose `C` is the base change of `A` along `R → C₀`.  Then an open subscheme
of `Spec C` whose preimages under the two comparison legs `iC ≫ Φ` and `kC` of Stacks 0APJ agree
is the preimage of a unique open subscheme of `Spec C₀`.

This is `AlgebraicGeometry.existsUnique_opens_preimage_eq_of_isPushout` with its hypothesis
supplied by `ModuleCat.preimage_pullback_eq_of_preimage_specMap_eq`, which is the route the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.DescentInvariantsProjections` prescribe:  the existential
form `ModuleCat.exists_subalgebra_isPushout_and_existsUnique_opens_preimage_eq` hides the
subalgebra, and a consumer that destructs it can no longer see that it is
`ModuleCat.descentInvariants`, so no statement about the two legs applies. -/
theorem existsUnique_opens_preimage_eq_descentInvariants [Module.FaithfullyFlat R A]
    (hpo : Algebra.IsPushout R A
      (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)) C)
    (W' : (Spec (CommRingCat.of C)).Opens)
    (hlegs : (Spec.map (iC ≫ Φ.hom)).base ⁻¹' (W' : Set (Spec (CommRingCat.of C))) =
      (Spec.map kC).base ⁻¹' (W' : Set (Spec (CommRingCat.of C)))) :
    ∃! W₀ : (Spec (CommRingCat.of
        (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)))).Opens,
      Spec.map (CommRingCat.ofHom (algebraMap
          (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)) C)) ⁻¹ᵁ W₀ = W' :=
  have := hpo
  existsUnique_opens_preimage_eq_of_isPushout R A _ C W'
    (preimage_pullback_eq_of_preimage_specMap_eq hP hQ Φ h1 h2 hpo
      (W' : Set (Spec (CommRingCat.of C))) hlegs)

end ModuleCat

namespace AlgebraicGeometry.DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f)

/-- **The three obligations that remain for [Stacks, Tag
0APK](https://stacks.math.columbia.edu/tag/0APK) over an affine base, besides Stacks 0AP4.**  Let
`f : X ⟶ S` be a surjective flat quasi-compact morphism of affine schemes and let `D` be a descent
datum relative to `f` whose scheme over `X` is ind-quasi-affine.  Then `D` is effective as soon as

1. `hkey`: the unit of the transition isomorphism `ψ` of Stacks 0APJ is coassociative — the
   cocycle condition for the gluing isomorphism transported to `ψ`, which the source performs
   with "details omitted".  This hypothesis is character for character the `hkey` of
   `AlgebraicGeometry.DescentDatum.isEffective_of_unitCoassoc_of_preimage_of_restrictOpen`;
2. `hlegs`: for an intersection `E` of a nonempty family of quasi-compact opens which is
   set-theoretically invariant, and an invariant open `W ⊆ E`, the two preimages of the image
   `j(W)` under the two comparison legs `iC ≫ Φ` and `kC` of Stacks 0APJ agree.  **This mentions
   no subalgebra**, unlike the `hpreimage` it replaces.  All of invariance of `W`, invariance of
   `E` and `W ⊆ E` are asked for: without them the condition is a statement about an open that
   the gluing isomorphism moves, and the source asserts nothing of the kind;
3. `hrestrict`: an open `W₀` of the spectrum of the subalgebra of `ψ`-invariants whose preimage
   in `Spec Γ(E, 𝒪_V|_E)` is `j(W)` makes the restriction of `D` to `W` effective.  The
   subalgebra is **named** here, where the `hrestrict` it replaces quantifies over every
   subalgebra whose base change to `Γ(X, ⊤)` is `Γ(E, 𝒪_V|_E)`;
4. `hglueing`: Stacks 0AP4 for `D`.  Unchanged from the earlier statement.

The passage from `hlegs` to the condition on the two projections of
`Spec Γ(E, 𝒪_V|_E) ×_{Spec C₀} Spec Γ(E, 𝒪_V|_E)` that Stacks 03N0 consumes is
`ModuleCat.preimage_pullback_eq_of_preimage_specMap_eq`, and it is performed inside
`ModuleCat.existsUnique_opens_preimage_eq_descentInvariants`.

**This is not Stacks 0APK and carries no tag.**  It is a reduction: a statement with four
hypotheses which no declaration of this repository discharges.  Its value over
`AlgebraicGeometry.DescentDatum.isEffective_of_unitCoassoc_of_preimage_of_restrictOpen` is that
its second and third obligations are stated about the subalgebra the source's proof actually
produces, so that the library's statements about the two legs of Stacks 0APJ apply to them. -/
theorem isEffective_of_unitCoassoc_of_legs_of_restrictOpen
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
    (hlegs : ∀ (E : Set D.over.left) {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
      (_hU : ∀ i, IsCompact (U i : Set D.over.left))
      (_hE : E = ⋂ i, (U i : Set D.over.left)) (hEinv : D.IsTransitionInvariantSet E)
      (W : D.over.left.Opens) (_hWinv : D.IsTransitionInvariant W)
      (_hWE : (W : Set D.over.left) ⊆ E),
      (Spec.map (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
            (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
          (D.transitionSectionsIso E
            (D.subset_preimage_transitionPullbackIso_hom_of_invariantSet E hEinv)
            (D.subset_preimage_transitionPullbackIso_inv_of_invariantSet E hEinv)).hom)).base ⁻¹'
          subsetΓSpecImage D.over.left E (W : Set D.over.left) =
        (Spec.map (Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
            (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _))).base ⁻¹'
          subsetΓSpecImage D.over.left E (W : Set D.over.left))
    (hrestrict : ∀ (E : Set D.over.left)
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
      (W : D.over.left.Opens) (hWinv : D.IsTransitionInvariant W)
      (_hWE : (W : Set D.over.left) ⊆ E)
      (W₀ : (Spec (CommRingCat.of ↥(ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤)
          ↥(D.over.left.sectionsRingOnSubset E)
          (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂)))).Opens)
      (_hW₀ : ((Spec.map (CommRingCat.ofHom (algebraMap
            (ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤)
              ↥(D.over.left.sectionsRingOnSubset E)
              (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂))
            ↥(D.over.left.sectionsRingOnSubset E))) ⁻¹ᵁ W₀ :
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
  have hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop := rfl
  have hAC : CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
      D.over.hom.appTop ≫ D.over.left.topToSubset E := rfl
  have hRC : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
      (D.over.hom ≫ f).appTop ≫ D.over.left.topToSubset E := rfl
  have hst : IsScalarTower ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have h : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
        CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) ≫
          CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤)
            ↥(D.over.left.sectionsRingOnSubset E)) := by
      rw [hRA, hAC, hRC, Scheme.Hom.comp_appTop, Category.assoc]
    exact congrArg CommRingCat.Hom.hom h
  clear_value _instRA _instAC _instRC
  have hiqa : IsIndQuasiAffine D.over.left := isIndQuasiAffine_of_isIndQuasiAffineHom_hom D.over
  have hqs : QuasiSeparatedSpace D.over.left :=
    quasiSeparatedSpace_of_isIndQuasiAffineHom_hom D.over
  have hff : Module.FaithfullyFlat ↥Γ(S, ⊤) ↥Γ(X, ⊤) :=
    faithfullyFlat_of_algebraMap_eq_appTop f hRA
  have hpush := D.isPushout_descentInvariants_of_invariantSet E hRA hRC hAC U hU hEeq hEinv
    (fun c => hkey E hRA hRC hAC U hU hEeq _ _ c)
  have hdesc := ModuleCat.existsUnique_opens_preimage_eq_descentInvariants
    (D.isPushout_algebraMap_transitionSource E hRA hRC U hU hEeq)
    (D.isPushout_algebraMap_transitionTarget E hRA hRC U hU hEeq)
    (D.transitionSectionsIso E
      (D.subset_preimage_transitionPullbackIso_hom_of_invariantSet E hEinv)
      (D.subset_preimage_transitionPullbackIso_inv_of_invariantSet E hEinv))
    (D.algebraMap_comp_transitionSectionsIso_hom E hAC _ _)
    (D.transitionSectionsIso_hom_eq_algebraMap_comp E hAC _ _)
    hpush (subsetΓSpecOpens D.over.left U hU E (W : Set D.over.left) hEeq hWE W.isOpen)
    (hlegs E U hU hEeq hEinv W hWinv hWE)
  obtain ⟨W₀, hW₀, -⟩ := hdesc
  exact hrestrict E hRA hRC hAC U hU hEeq _ _ W hWinv hWE W₀
    (TopologicalSpace.Opens.ext_iff.mp hW₀)

end AlgebraicGeometry.DescentDatum

end

end
