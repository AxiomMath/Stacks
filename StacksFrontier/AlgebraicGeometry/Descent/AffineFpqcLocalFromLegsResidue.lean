module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcLocalFromDescentData
public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumCocycleDiagram

/-!
# Affineness is fpqc local on the base, from the three remaining obligations of Stacks 0APK

`AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc_of_isEffective_affine_indQuasiAffine`
of `StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcLocalFromDescentData` derives the conclusion
of Stacks 041Z — affineness of morphisms of algebraic spaces over `S` is fpqc local on the base
— from Stacks 0APK over an affine base, and
`AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen` of
`StacksFrontier.AlgebraicGeometry.Descent.DescentDatumCocycleDiagram` reduces that instance of
Stacks 0APK to three obligations, the coassociativity obligation of the earlier four-obligation
reduction having been discharged.

**This file joins those two**, so that the conclusion of Stacks 041Z is available from the three
obligations alone. Its content is the universal quantification: the reduction of Stacks 0APK is
stated for one descent datum with its hypotheses in scope as instances, whereas the statement it
has to feed quantifies over every surjective flat quasi-compact morphism of affine schemes and
every ind-quasi-affine descent datum relative to it, with those hypotheses as explicit
arguments. That the three obligations transport across that change of quantification with no
coercion is what is recorded here, and it is not visible to any search over names.

## Main definitions

There are no new definitions, structures, classes or instances, and no new named hypothesis is
coined. The three hypotheses are the three arguments of
`AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen`, quoted character for
character and wrapped in the quantifier that statement's consumer needs; the proof is a bare
application of it, so the elaborator checks the quotation.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc_of_legs_of_restrictOpen`: the
  conclusion of Stacks 041Z from `hlegs`, `hrestrict` and `hglueing`. The last of the three is
  Stacks 0AP4.

## Implementation notes

*What this measures, and why Stacks 0245 is not among the hypotheses.* Stacks 041Z cites Stacks
0245, 02L5, 041Y and 041J in its proof, and none of them appears here, because all four are
discharged upstream: the affine case of Stacks 0245 is
`AlgebraicGeometry.Space.exists_affineCandidate_of_isPullback`, which is what the descent step
of `StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcChartDescent` consumes, and that file's
implementation notes record why the general form of Stacks 0245 and the other three tags are not
needed. So the hypotheses below are the whole residue of Stacks 041Z in this development, and a
census of Stacks 0245 — which has no tag site in this repository in any of the four attribute
forms — measures neither its availability for this route nor anything 041Z still owes.

*Why the hypotheses are not vacuous.* The family they quantify over is inhabited, by
`AlgebraicGeometry.exists_isAffine_descentDatum_isIndQuasiAffineHom`, which exhibits an affine
base, an affine source, the identity as a surjective flat quasi-compact morphism between them
and a descent datum relative to it whose scheme over the source is ind-quasi-affine. Were that
family empty the three hypotheses would hold trivially and this statement would prove the
conclusion of Stacks 041Z outright.

*Why the obligations are asked at the named transition algebra.* `hrestrict` takes the open
`W₀` of the spectrum of `AlgebraicGeometry.ModuleCat.descentInvariants` at
`AlgebraicGeometry.DescentDatum.descentAlgebraTransition` rather than at an arbitrary
subalgebra. That is deliberate and is inherited unchanged: a hypothesis quantified over an
arbitrary subalgebra carrying a pushout square cannot be discharged, because every route to it
needs the subalgebra to be syntactically the invariants, and the implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.DescentInvariantsProjections` say so.

*Nothing is tagged.* Each of the three hypotheses is a statement this repository does not prove,
the last of them being Stacks 0AP4, so this is not Stacks 041Z and not Stacks 0APK, and
`@[stacks 041Z]` is **not** placed here. The tag belongs on the unconditional instance that
Stacks 041Z states, once the three obligations are proved; at that point this statement
is one application away from it.

## References

* [Stacks Project, Tag 041Z](https://stacks.math.columbia.edu/tag/041Z)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

/-- **The conclusion of Stacks 041Z from the three remaining obligations of Stacks 0APK.**
Suppose that for every surjective flat quasi-compact morphism `g : T' ⟶ T` of affine schemes and
every descent datum `D` relative to `g` whose scheme over `T'` is ind-quasi-affine, the three
obligations `hlegs`, `hrestrict` and `hglueing` of
`AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen` hold. Then affineness of
morphisms of algebraic spaces over `S` is fpqc local on the base.

The three hypotheses are that statement's three arguments, quantified over the data it keeps in
scope; `hglueing` is [Stacks, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4). The family
quantified over is inhabited, by
`AlgebraicGeometry.exists_isAffine_descentDatum_isIndQuasiAffineHom`, so none of the three is
vacuously satisfied.

**This is not Stacks 041Z and carries no tag**, since all three hypotheses are open. -/
theorem isAffineHom_isLocalAtTarget_fpqc_of_legs_of_restrictOpen
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hlegs : ∀ {T T' : Scheme.{u}} {g : T' ⟶ T} (D : DescentDatum g) [IsAffine T]
      [IsAffine T'] [Flat g] [Surjective g] [QuasiCompact g]
      [IsIndQuasiAffineHom D.over.hom]
      (E : Set D.over.left) {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
      (_hU : ∀ i, IsCompact (U i : Set D.over.left))
      (_hE : E = ⋂ i, (U i : Set D.over.left)) (hEinv : D.IsTransitionInvariantSet E)
      (W : D.over.left.Opens) (_hWinv : D.IsTransitionInvariant W)
      (_hWE : (W : Set D.over.left) ⊆ E),
      (Spec.map (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ g) g) E
            (⇑(pullback.fst (D.over.hom ≫ g) g) ⁻¹' E) (Set.Subset.refl _) ≫
          (D.transitionSectionsIso E
            (D.subset_preimage_transitionPullbackIso_hom_of_invariantSet E hEinv)
            (D.subset_preimage_transitionPullbackIso_inv_of_invariantSet E hEinv)).hom)).base ⁻¹'
          subsetΓSpecImage D.over.left E (W : Set D.over.left) =
        (Spec.map (Scheme.sectionsRingOnSubsetMap (pullback.snd g (D.over.hom ≫ g)) E
            (⇑(pullback.snd g (D.over.hom ≫ g)) ⁻¹' E) (Set.Subset.refl _))).base ⁻¹'
          subsetΓSpecImage D.over.left E (W : Set D.over.left))
    (hrestrict : ∀ {T T' : Scheme.{u}} {g : T' ⟶ T} (D : DescentDatum g) [IsAffine T]
      [IsAffine T'] [Flat g] [Surjective g] [QuasiCompact g]
      [IsIndQuasiAffineHom D.over.hom]
      (E : Set D.over.left)
      [Algebra ↥Γ(T, ⊤) ↥Γ(T', ⊤)] [Algebra ↥Γ(T, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      [Algebra ↥Γ(T', ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      [IsScalarTower ↥Γ(T, ⊤) ↥Γ(T', ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      (hRA : CommRingCat.ofHom (algebraMap ↥Γ(T, ⊤) ↥Γ(T', ⊤)) = g.appTop)
      (hRC : CommRingCat.ofHom (algebraMap ↥Γ(T, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
        (D.over.hom ≫ g).appTop ≫ D.over.left.topToSubset E)
      (hAC : CommRingCat.ofHom (algebraMap ↥Γ(T', ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
        D.over.hom.appTop ≫ D.over.left.topToSubset E)
      [QuasiSeparatedSpace D.over.left] {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
      (hU : ∀ i, IsCompact (U i : Set D.over.left)) (hE : E = ⋂ i, (U i : Set D.over.left))
      (h₁ : (⇑(pullback.fst (D.over.hom ≫ g) g) ⁻¹' E) ⊆
        ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd g (D.over.hom ≫ g)) ⁻¹' E))
      (h₂ : (⇑(pullback.snd g (D.over.hom ≫ g)) ⁻¹' E) ⊆
        ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ g) g) ⁻¹' E))
      (W : D.over.left.Opens) (hWinv : D.IsTransitionInvariant W)
      (_hWE : (W : Set D.over.left) ⊆ E)
      (W₀ : (Spec (CommRingCat.of ↥(ModuleCat.descentInvariants ↥Γ(T, ⊤) ↥Γ(T', ⊤)
          ↥(D.over.left.sectionsRingOnSubset E)
          (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂)))).Opens)
      (_hW₀ : ((Spec.map (CommRingCat.ofHom (algebraMap
            (ModuleCat.descentInvariants ↥Γ(T, ⊤) ↥Γ(T', ⊤)
              ↥(D.over.left.sectionsRingOnSubset E)
              (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂))
            ↥(D.over.left.sectionsRingOnSubset E))) ⁻¹ᵁ W₀ :
            (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E))).Opens) :
          Set (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E)))) =
        subsetΓSpecImage D.over.left E (W : Set D.over.left)),
      DescentData.IsEffective (D.restrictOpen W hWinv))
    (hglueing : ∀ {T T' : Scheme.{u}} {g : T' ⟶ T} (D : DescentDatum g) [IsAffine T]
      [IsAffine T'] [Flat g] [Surjective g] [QuasiCompact g]
      [IsIndQuasiAffineHom D.over.hom],
      (∀ v : D.over.left, ∃ (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W),
        v ∈ W ∧ DescentData.IsEffective (D.restrictOpen W hW)) →
      DescentData.IsEffective D) :
    MorphismProperty.IsLocalAtTarget
      (fun {X Y} (f : X ⟶ Y) => IsAffineHom B S hS f.hom :
        MorphismProperty (AlgebraicSpaces B S hS))
      (Topology.fpqc.precoverage.{u, v} B S hS) :=
  isAffineHom_isLocalAtTarget_fpqc_of_isEffective_affine_indQuasiAffine B S hS
    fun _g _hT _hT' _hs _hfl _hqc D _hiqa =>
      D.isEffective_of_legs_of_restrictOpen (hlegs D) (hrestrict D) (hglueing D)

end AlgebraicGeometry.Space

end
