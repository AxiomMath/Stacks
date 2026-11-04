module

public import StacksFrontier.AlgebraicGeometry.Stacks.DenseTestValuative.Reduction
public import StacksFrontier.AlgebraicGeometry.Stacks.DenseTestValuative.SpaceCover
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyFppfCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic

/-!
# Stacks 0CQM for a 1-morphism representable by algebraic spaces

When `f : 𝒳 ⟶ 𝒴` is representable by algebraic spaces, the base change of `f` to a smooth chart
`Spec A ⟶ 𝒴` is represented by an algebraic space (**Stacks 0300**), so the proof of
**Stacks 0CQM** needs Chow's lemma only for algebraic spaces (**Stacks 089J**), not for
algebraic stacks: the algebraic space representing the base change is its own proper surjective
cover.

## Main results

In namespace `AlgebraicGeometry.Stack.AlgebraicStacks`:

* `isProper_of_denseTestExistence_of_isRepresentableByAlgebraicSpaces`: Stacks 0CQM for a
  1-morphism representable by algebraic spaces.

## References

* [Stacks Project, Tag 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

/-- **An algebraic stack represented by an algebraic space has a proper surjective cover by it.**
If the underlying category fibred in groupoids of `𝒳` is represented by an algebraic space `F`,
the 1-morphism from the algebraic stack of `F` to `𝒳` whose representing morphism is the
identity of `F` is proper and surjective. -/
theorem exists_isProper_isSurjective_of_isRepresentableByAlgebraicSpace
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳.val) :
    ∃ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
      (a : algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒳),
      IsProper B S hS a ∧ Stack.IsSurjective B S hS a := by
  obtain ⟨F, hF, ⟨e⟩⟩ := h𝒳
  let eF : StacksRepresentableCFG.EquivalenceOver
      (algebraicSpaceStack.{u, w} B S hS F hF).val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p := StacksRepresentableCFG.EquivalenceOver.refl _
  obtain ⟨a, ha⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := algebraicSpaceStack.{u, w} B S hS F hF) (𝒴 := 𝒳) F F eF e (𝟙 F)
  have hid : Space.IsProper B S hS (𝟙 F) := Space.isProper_of_isIso B S hS (𝟙 F)
  have hsep := (isSeparated_iff_representingMap B S hS F F hF hF eF e a).2 (ha ▸ hid.1)
  have hlft := (isLocallyOfFiniteType_iff_representingMap B S hS F F hF hF eF e a).2
    (ha ▸ hid.2.1.1)
  have hqc := (isQuasiCompactMorphism_iff_representingMap B S hS F F hF hF eF e a).2
    (ha ▸ hid.2.1.2)
  have huc := universallyClosed_of_representingMap B S hS F F hF hF eF e a (ha ▸ hid.2.2)
  have hsurj := isSurjective_of_isSurjective_representingMap B S hS F F hF hF eF e a
    (ha ▸ Space.isSurjective_id B S hS F)
  exact ⟨F, hF, a, ⟨hsep, ⟨hlft, hqc⟩, huc⟩, hsurj⟩

/-- **Stacks 0CQM for a 1-morphism representable by algebraic spaces.** Let `f : 𝒳 ⟶ 𝒴` and
`h : 𝒰 ⟶ 𝒳` be 1-morphisms of algebraic stacks over `S`, with `𝒴` locally Noetherian, `f` and
`h` of finite type, `f` separated and representable by algebraic spaces, and the image of
`|h| : |𝒰| → |𝒳|` dense in `|𝒳|`. If every 2-commutative diagram
`Spec K ⟶ 𝒰 ⟶ 𝒳 ⟶ 𝒴`, `Spec A ⟶ 𝒴` with `A` a discrete valuation ring with fraction field
`K` admits a dotted arrow after an extension of `K` and passage to a dominating valuation ring,
then `f` is proper. -/
theorem isProper_of_denseTestExistence_of_isRepresentableByAlgebraicSpaces
    {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (h : 𝒰 ⟶ 𝒳)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hf : IsFiniteType B S hS f) (hh : IsFiniteType B S hS h) (hsep : IsSeparated B S hS f)
    (hdense : letI := Stack.pointTopology B S hS 𝒳.val
      Dense (Set.range (Stack.pointsMap B S hS 𝒰.val.val 𝒰.val.property 𝒳.val.property
        h.hom.hom)))
    (hlift : ValuativeCriterion.DenseTestExistence B S hS h f)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    IsProper B S hS f := by
  refine isProper_of_denseTestExistence_of_forall_affine B S hS f h h𝒴 hf hh hsep hdense hlift
    fun A hA a₀ _ g _ P hP => ?_
  have hf' : IsFiniteType B S hS P.fst := isFiniteType_baseChange B S hS f g P hP hf
  have hsep' : IsSeparated B S hS P.fst :=
    isSeparated_baseChange_of_isTwoFibreProduct B S hS f g P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hsep
  have hrepP : IsRepresentableByAlgebraicSpaces B S hS P.fst.hom.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒳.val 𝒴.val _
      f.hom g.hom (AlgebraicStacks.toCatFiberedInGroupoids B S hS P)
      (AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids B S hS P hP) hrep
  have hPsp : IsRepresentableByAlgebraicSpace B S hS P.pt.val :=
    isRepresentableByAlgebraicSpace_of_representable B S hS P.pt.val
      (schemeStack.{u, w} B S hS (siteObject B S hS hA a₀)).val P.fst.hom hrepP
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS (siteObject B S hS hA a₀))
  obtain ⟨F, hF, a, ha, has⟩ :=
    exists_isProper_isSurjective_of_isRepresentableByAlgebraicSpace B S hS hPsp
  exact exists_schemeCover_of_algebraicSpaceCover B S hS A hA a₀ P.fst hsep' hf' hF a ha has

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
