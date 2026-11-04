module

public import StacksFrontier.AlgebraicGeometry.Stacks.DenseTestValuative.AffineCase
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationTrivialImplications
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionProperness
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothObject
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SiteObjectBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact

/-!
# From a proper surjective algebraic-space cover to a proper surjective scheme cover

Let `V = Spec A` be an affine scheme of the big fppf site of `S`, `f : 𝒳 ⟶ V` a separated
1-morphism of finite type of algebraic stacks, and `a : X ⟶ 𝒳` a proper surjective 1-morphism
from an algebraic space. Then there is a scheme `X'` with a surjective, universally closed
1-morphism `X' ⟶ 𝒳` satisfying the existence part of the valuative criterion, whose composite
to `V` is induced by a separated quasi-compact morphism of schemes locally of finite type.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_iff_representingMap`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiCompactMorphism_iff_representingMap`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_iff_representingMap`: a 1-morphism
  between algebraic stacks represented by algebraic spaces is locally of finite type,
  quasi-compact, or separated if and only if the morphism of representing presheaves is.
* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_of_representingMap`: such a
  1-morphism is universally closed if the morphism of representing presheaves is.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_schemeCover_of_algebraicSpaceCover`: the
  statement above.

## References

* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
* [Stacks Project, Tag 04YS](https://stacks.math.columbia.edu/tag/04YS)
* [Stacks Project, Tag 0512](https://stacks.math.columbia.edu/tag/0512)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

section Represented

variable {𝒜 𝒞 : AlgebraicStacks.{u, w} B S hS} (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
  (eF : StacksRepresentableCFG.EquivalenceOver
    𝒜.val.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver
    𝒞.val.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
  (k : 𝒜 ⟶ 𝒞)

include hF hG eF eG in
/-- A 1-morphism between algebraic stacks represented by algebraic spaces is representable by
algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_of_represented :
    IsRepresentableByAlgebraicSpaces B S hS k.hom.hom :=
  isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS k.hom
    ⟨F, hF, ⟨eF⟩⟩ ⟨G, hG, ⟨eG⟩⟩

include hF hG in
/-- A 1-morphism between algebraic stacks represented by algebraic spaces is locally of finite
type if and only if the morphism of representing presheaves is. -/
theorem isLocallyOfFiniteType_iff_representingMap :
    IsLocallyOfFiniteType B S hS k ↔
      Space.IsLocallyOfFiniteType B S hS (representingMap B S hS 𝒜.val 𝒞.val F G eF eG k.hom) :=
  (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
    (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    𝒜.property 𝒞.property k.hom).trans
  (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
    (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    𝒜.property 𝒞.property F G hF hG eF eG k.hom)

include hF hG in
/-- A 1-morphism between algebraic stacks represented by algebraic spaces is quasi-compact if
and only if the morphism of representing presheaves is. -/
theorem isQuasiCompactMorphism_iff_representingMap :
    IsQuasiCompactMorphism.{u, w} B S hS k ↔
      Space.IsQuasiCompact B S hS (representingMap B S hS 𝒜.val 𝒞.val F G eF eG k.hom) := by
  have _ : (Space.quasiCompactProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isQuasiCompact_isLocalAtTarget_fppf B S hS
  have hrep := isRepresentableByAlgebraicSpaces_of_represented B S hS F G hF hG eF eG k
  exact (isQuasiCompact_iff_baseChange_quasiCompact B S hS k hrep).symm.trans
    (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.quasiCompactProperty B S hS) k.hom hrep F G hF hG eF eG)

include hF hG in
/-- A 1-morphism between algebraic stacks represented by algebraic spaces is separated if and
only if the morphism of representing presheaves is. -/
theorem isSeparated_iff_representingMap :
    IsSeparated B S hS k ↔
      Space.IsSeparated B S hS (representingMap B S hS 𝒜.val 𝒞.val F G eF eG k.hom) := by
  have _ : (Space.separatedProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have hrep := isRepresentableByAlgebraicSpaces_of_represented B S hS F G hF hG eF eG k
  have htfae := isSeparated_relativeDiagonal_tfae B S hS k hrep
  exact (htfae.out 3 1).trans
    (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.separatedProperty B S hS) k.hom hrep F G hF hG eF eG)

include hF hG in
/-- A 1-morphism between algebraic stacks represented by algebraic spaces is universally closed
if the morphism of representing presheaves is. -/
theorem universallyClosed_of_representingMap
    (h : Space.UniversallyClosed B S hS (representingMap B S hS 𝒜.val 𝒞.val F G eF eG k.hom)) :
    UniversallyClosed B S hS k := by
  have _ : (Space.universallyClosedProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have hrep := isRepresentableByAlgebraicSpaces_of_represented B S hS F G hF hG eF eG k
  exact (representable_universallyClosed_iff_closedMap_baseChange B S hS k hrep).1
    ((hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.universallyClosedProperty B S hS) k.hom hrep F G hF hG eF eG).2 h)

end Represented

/-- Let `f : 𝒳 ⟶ Spec A` be a separated 1-morphism of finite type and `a : X ⟶ 𝒳` a proper
surjective 1-morphism from an algebraic space. Then there are a scheme `X'` of the site, a
surjective, universally closed 1-morphism `p : X' ⟶ 𝒳` satisfying the existence part of the
valuative criterion, and a separated quasi-compact morphism `φ : X' ⟶ Spec A` locally of finite
type with `p ≫ f` 2-isomorphic to the 1-morphism induced by `φ`. -/
theorem exists_schemeCover_of_algebraicSpaceCover
    (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) (a₀ : Spec A ⟶ S)
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ schemeStack.{u, w} B S hS (siteObject B S hS hA a₀))
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (a : algebraicSpaceStack.{u, w} B S hS X hX ⟶ 𝒳) (ha : IsProper B S hS a)
    (has : Stack.IsSurjective B S hS a) :
    ∃ (X' : BigFppfOver B S hS) (p : schemeStack.{u, w} B S hS X' ⟶ 𝒳)
      (φ : X' ⟶ siteObject B S hS hA a₀),
      UniversallyClosed B S hS p ∧ ValuativeCriterion.Existence B S hS p ∧
      Stack.IsSurjective B S hS p ∧
      _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map φ) ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map φ) ∧
      QuasiCompact ((BigFppfOver.toScheme B S hS).map φ) ∧
      Nonempty (p ≫ f ≅ schemeStackMap.{u, w} B S hS φ) := by
  let V := siteObject B S hS hA a₀
  let k := a ≫ f
  let eX : StacksRepresentableCFG.EquivalenceOver
      (algebraicSpaceStack.{u, w} B S hS X hX).val.val.p
      (presheafOfCategories (X ⋙ typeToCat)).p := StacksRepresentableCFG.EquivalenceOver.refl _
  let eV := PresheafOfCategories.sliceElementsEquivalenceOver V
  have hyV := isAlgebraicSpace_yoneda B S hS V
  have hksep : IsSeparated B S hS k := isSeparated_comp B S hS a f ha.1 hsep
  have hkft : IsFiniteType B S hS k := isFiniteType_comp B S hS a f ha.2.1 hft
  let gX := representingMap B S hS (algebraicSpaceStack.{u, w} B S hS X hX).val
    (schemeStack.{u, w} B S hS V).val X (yoneda.obj V) eX eV k.hom
  have hgsep := (isSeparated_iff_representingMap B S hS X (yoneda.obj V) hX hyV eX eV k).1 hksep
  have hglft :=
    (isLocallyOfFiniteType_iff_representingMap B S hS X (yoneda.obj V) hX hyV eX eV k).1 hkft.1
  have hgqc :=
    (isQuasiCompactMorphism_iff_representingMap B S hS X (yoneda.obj V) hX hyV eX eV k).1 hkft.2
  obtain ⟨X', ψ, p₀, hp₀, hp₀s, hp₀g, hψ⟩ :=
    Space.exists_chowSchemeCover_over_spec B S hS A hA a₀ hX gX hgsep ⟨hglft, hgqc⟩
  let eX' := PresheafOfCategories.sliceElementsEquivalenceOver X'
  have hyX' := isAlgebraicSpace_yoneda B S hS X'
  obtain ⟨c, hc⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := schemeStack.{u, w} B S hS X') (𝒴 := algebraicSpaceStack.{u, w} B S hS X hX)
    (yoneda.obj X') X eX' eX p₀
  have hcUC : UniversallyClosed B S hS c :=
    universallyClosed_of_representingMap B S hS (yoneda.obj X') X hyX' hX eX' eX c
      (hc ▸ hp₀.2.2)
  have hcsep : IsSeparated B S hS c :=
    (isSeparated_iff_representingMap B S hS (yoneda.obj X') X hyX' hX eX' eX c).2 (hc ▸ hp₀.1)
  have hcex : ValuativeCriterion.Existence B S hS c :=
    valuativeCriterionExistence_of_universallyClosed B S hS
      (isQuasiSeparated_of_isSeparated B S hS hcsep) hcUC
  have haex : ValuativeCriterion.Existence B S hS a :=
    (valuativeCriterion_of_isProper B S hS a (isQuasiSeparated_of_isSeparated B S hS ha.1) ha).2
  have hcsurj : Stack.IsSurjective B S hS c :=
    isSurjective_of_isSurjective_representingMap B S hS (yoneda.obj X') X hyX' hX eX' eX c
      (hc ▸ hp₀s)
  refine ⟨X', c ≫ a, ψ, universallyClosed_comp B S hS c a hcUC ha.2.2,
    valuativeCriterionExistence_comp B S hS c a hcex haex, ?_, hψ.isSeparated,
    hψ.locallyOfFiniteType, IsHQuasiProjective.quasiCompact hψ, ?_⟩
  · intro x
    obtain ⟨y, hy⟩ := has x
    obtain ⟨z, hz⟩ := hcsurj y
    exact ⟨z, by rw [pointsMap_comp, Function.comp_apply, hz, hy]⟩
  · have h1 : representingMap B S hS (schemeStack.{u, w} B S hS X').val
        (schemeStack.{u, w} B S hS V).val (yoneda.obj X') (yoneda.obj V) eX' eV
        (c.hom ≫ k.hom) = yoneda.map ψ := by
      rw [representingMap_comp B S hS (yoneda.obj X') X (yoneda.obj V) eX' eX eV c.hom k.hom, hc]
      exact hp₀g
    have h3 : siteMap B S hS (c ≫ k) = ψ := Functor.map_injective yoneda
      ((representingMap_eq_yoneda_map_baseMap B S hS ((c ≫ k).hom.hom)).symm.trans h1)
    exact ⟨α_ c a f ≪≫ schemeStackMapIso B S hS (c ≫ k) ≪≫
      eqToIso (congrArg (schemeStackMap.{u, w} B S hS) h3)⟩

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
