module

public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumCocycleDiagram
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcDescentReduction
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescendedScheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.IndQuasiAffine.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.IndQuasiAffine.Coproducts

/-!
# Effective fpqc descent for ind-quasi-affine morphisms over an affine base

Let `S` be an affine scheme, let `{X i ⟶ S}` be an fpqc covering family and let `D` be a descent
datum relative to that family, in the sense of Stacks 023W, each of whose component morphisms
`V i ⟶ X i` is ind-quasi-affine.  This file assembles, from material already in the library, the
statement that `D` is effective relative to the family in the sense of Stacks 02VU — the assertion
of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) over an affine base — **from the
two obligations `hlegs` and `hrestrict` of
`AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen` and nothing else.**

Three things are contributed. Stacks 0AP4, the third obligation of that statement, is discharged
outright by `AlgebraicGeometry.DescentDatum.isEffective_of_forall_exists_restrictOpen`. The
reduction of Stacks 02W3 over an affine base,
`AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffine`, is instantiated at
`AlgebraicGeometry.IsIndQuasiAffineHom`: its two hypotheses on the property are stability under
base change, which is Stacks 0AP7, and closure under finite disjoint unions, which is
`AlgebraicGeometry.isIndQuasiAffineHom_sigmaMap`. And the single-chart conclusion is put in the
exact shape that reduction consumes, so that the passage from one surjective flat morphism of
affine schemes to an arbitrary fpqc covering family of an affine base costs nothing further.

## Main results

* `AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen_of_isAffine`: the
  single-chart case, with Stacks 0AP4 discharged — effectivity of every descent datum with
  ind-quasi-affine component relative to a surjective flat morphism of affine schemes, from
  `hlegs` and `hrestrict` alone.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_isIndQuasiAffineHom_of_isAffine`: **the
  assertion of Stacks 0APK over an affine base, from `hlegs` and `hrestrict`.**

## Implementation notes

*No tag is carried.* The two hypotheses are open: no declaration of this repository discharges
either, and the implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.DescentDatumResidueInvariants` and
`StacksFrontier.AlgebraicGeometry.Descent.StageEmbeddingBaseChange` say what each still needs.  So
the conclusion below is a reduction and not Stacks 0APK, exactly as the statements it is built
from are. What it adds to them is that nothing beyond those two obligations separates the
single-chart case from the covering-family statement of the tag over an affine base.

*The hypotheses are quoted character for character* from
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_legs_of_restrictOpen`, so one supplier
discharges that statement, the conclusion of Stacks 041Z, and this one together, with no
transport.

*Why the base is affine here.* The reduction instantiated in this file,
`AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffine`, is the fpqc case of Stacks 02W3
over an affine base only. The affineness is not forced by the argument: the general-base fpqc
case of Stacks 02W3,
`AlgebraicGeometry.DescentData.isFamilyEffective_fpqc_of_affineSingleton_of_anyIndex` of
`StacksFrontier.AlgebraicGeometry.Descent.DescendingTypesOfMorphismsGeneralBase`, glues the schemes
descended over the affine opens along Stacks 01LH and takes the same two hypotheses on the
property, and it is what
`StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcEffective` consumes to state Stacks 0APK
over an arbitrary base. What is affine-base-only is this conditional form, which keeps the two
open obligations visible.

*Quasi-compactness is not a hypothesis.* The residue statement asks for `[QuasiCompact g]`, which
for a morphism between affine schemes is an instance, through
`AlgebraicGeometry.isAffineHom_of_isAffine`.

## References

* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
* [Stacks Project, Tag 0AP7](https://stacks.math.columbia.edu/tag/0AP7)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace DescentDatum

/-- **The affine-chart case of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) from
the two obligations `hlegs` and `hrestrict`.**  Suppose that for every surjective flat
quasi-compact morphism `g : T' ⟶ T` of affine schemes and every descent datum `D` relative to `g`
whose scheme over `T'` is ind-quasi-affine, the obligations `hlegs` and `hrestrict` of
`AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen` hold.  Then every such
descent datum is effective.

The third obligation of that statement, locality of effectivity on the scheme carrying the datum,
is [Stacks, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4), and it is supplied here by
`AlgebraicGeometry.DescentDatum.isEffective_of_forall_exists_restrictOpen`.

The conclusion is in the shape `AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffine`
consumes, which is what makes the covering-family statement below immediate. -/
theorem isEffective_of_legs_of_restrictOpen_of_isAffine
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
    {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] (g : T' ⟶ T)
    (hsurj : Surjective g) (hflat : Flat g) (D : DescentDatum g)
    (hiqa : IsIndQuasiAffineHom (D.obj ()).hom) :
    DescentData.IsEffective D := by
  have := hsurj
  have := hflat
  have : IsIndQuasiAffineHom D.over.hom := hiqa
  exact D.isEffective_of_legs_of_restrictOpen (hlegs D) (hrestrict D)
    (isEffective_of_forall_exists_restrictOpen D)

end DescentDatum

namespace DescentData

/-- **The assertion of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) over an
affine base, from the two obligations `hlegs` and `hrestrict`.**  Suppose that for every
surjective flat quasi-compact morphism `g : T' ⟶ T` of affine schemes and every descent datum `D`
relative to `g` whose scheme over `T'` is ind-quasi-affine, the obligations `hlegs` and
`hrestrict` of `AlgebraicGeometry.DescentDatum.isEffective_of_legs_of_restrictOpen` hold.  Let `S`
be an affine scheme, let `{X i ⟶ S}` be an fpqc covering family and let `D` be a descent datum
relative to it each of whose component morphisms is ind-quasi-affine.  Then `D` is effective: it
is isomorphic to the canonical descent datum of a scheme over `S`.

The passage from the single morphism to the covering family is the fpqc case of
[Stacks, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3) over an affine base,
`AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffine`, whose two hypotheses on the
property of morphisms are stability under base change — Stacks 0AP7, as
`AlgebraicGeometry.isIndQuasiAffineHom_isStableUnderBaseChange` — and closure under finite
disjoint unions, as `AlgebraicGeometry.isIndQuasiAffineHom_sigmaMap`. -/
theorem isFamilyEffective_of_isIndQuasiAffineHom_of_isAffine
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
    {ι : Type u} {S : Scheme.{u}} [IsAffine S] {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage S)
    (D : DescentData f) (hP : ∀ i, IsIndQuasiAffineHom (D.obj i).hom) :
    D.IsFamilyEffective :=
  isFamilyEffective_of_isAffine (P := @IsIndQuasiAffineHom)
    (fun a ha ↦ isIndQuasiAffineHom_sigmaMap a ha)
    (fun a hsurj hflat E hPE ↦
      DescentDatum.isEffective_of_legs_of_restrictOpen_of_isAffine hlegs hrestrict a hsurj hflat
        E hPE)
    f hf D hP

end DescentData

end AlgebraicGeometry

end

end
