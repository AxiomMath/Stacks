module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.MonomorphismFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.FullyFaithfulMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionFppfCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableBySpacesOfFppfCover
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal
public import StacksFrontier.CategoryTheory.Sites.Stack.FullyFaithfulDescent

/-!
# The four equivalent conditions for a monomorphism of algebraic stacks (Stacks 04ZZ)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. **Stacks 04ZZ** says that the
following are equivalent:

1. `f` is a monomorphism (Stacks 04ZW),
2. `f` is fully faithful,
3. the diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is an equivalence, and
4. there exist an algebraic space `W` and a surjective, flat morphism `W ⟶ 𝒴` locally of finite
   presentation such that `V = 𝒳 ×_𝒴 W` is an algebraic space and `V ⟶ W` is a monomorphism of
   algebraic spaces.

## The implications

* (1) ⟹ (2) is
  `AlgebraicGeometry.Stack.AlgebraicStacks.full_and_faithful_homFunctor_of_isMonomorphism`
  (Stacks 05UK with Stacks 003Z).
* (2) ⟺ (3) is Stacks 04Z7,
  `CategoryTheory.TwoFibreProductOver.full_and_faithful_iff_isEquivalence_diagonal`; the diagonal
  of `f` in the 2-category of algebraic stacks,
  `AlgebraicGeometry.Stack.relativeDiagonalAlgebraicStacks`, has that diagonal as its underlying
  functor.
* (2) ⟹ (1) is `AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_of_full_and_faithful`.
  Clause (1) contains the assertion that `f` is representable by algebraic spaces, which the
  source obtains from Stacks 04Y5, the implication (2) ⟹ (3) — a faithful 1-morphism of
  algebraic stacks is representable by algebraic spaces —
  `AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful`.
* (1) ⟹ (4) is
  `AlgebraicGeometry.Stack.AlgebraicStacks.hasMonomorphicFppfSpaceBaseChange_of_isMonomorphism`:
  `W` is the smooth scheme atlas of `𝒴`, `V` comes from Stacks 0300, and `V ⟶ W` is a
  monomorphism by Stacks 04XC.
* (4) ⟹ (2) is `AlgebraicStacks.full_and_faithful_homFunctor_of_hasMonomorphicFppfSpaceBaseChange`:
  `V ⟶ W` is fully faithful by Stacks 05UK, and full faithfulness descends along the locally
  essentially surjective `W ⟶ 𝒴`
  (`CategoryTheory.Functor.full_and_faithful_of_full_and_faithful_fst`, the fullness companion of
  Stacks 06DV).

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasMonomorphicFppfSpaceBaseChange`: clause (4).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.hasMonomorphicFppfSpaceBaseChange_of_isMonomorphism`:
  (1) ⟹ (4).
* `AlgebraicStacks.full_and_faithful_homFunctor_of_hasMonomorphicFppfSpaceBaseChange`: (4) ⟹ (2).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_tfae_of_bootstrap`: **Stacks 04ZZ**, the
  four conditions are equivalent.

## Implementation notes

Clause (4) is read as it is written, in the conventions of
`StacksFrontier.AlgebraicGeometry.Stacks.ImmersionFppfCoverCriterion` (Stacks 0503): an existential
over a category `𝒲` represented by an algebraic space `W`, a 1-morphism `g : 𝒲 ⟶ 𝒴` satisfying
`AlgebraicGeometry.Stack.IsSurjectiveFlatLocallyOfFinitePresentation`, a 2-fibre product square
`Q` over the cospan `(g, f)` and an algebraic space `V` representing its apex, asserting that the
induced morphism `V ⟶ W` of representing presheaves (`AlgebraicGeometry.Stack.representingMap`)
is a monomorphism in the category of algebraic spaces over `S`. Clause (3) reads "equivalence" as
`CategoryTheory.Functor.IsEquivalence` of the underlying functor, as in Stacks 0AHJ.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04Z7](https://stacks.math.columbia.edu/tag/04Z7)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 05UK](https://stacks.math.columbia.edu/tag/05UK)
* [Stacks Project, Tag 06DV](https://stacks.math.columbia.edu/tag/06DV)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

namespace AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Clause (4) of Stacks 04ZZ.** There are an algebraic space `W`, represented by `𝒲`, and a
surjective, flat 1-morphism `g : 𝒲 ⟶ 𝒴` locally of finite presentation, such that the apex
`V = 𝒳 ×_𝒴 W` of a 2-fibre product square `Q` over the cospan `(g, f)` is an algebraic space and
the induced morphism `V ⟶ W` is a monomorphism of algebraic spaces over `S`. -/
abbrev HasMonomorphicFppfSpaceBaseChange (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ (𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B S hS W)
    (eW : StacksRepresentableCFG.EquivalenceOver
      𝒲.val.p (presheafOfCategories (W ⋙ typeToCat)).p)
    (g : 𝒲 ⟶ 𝒴.val), IsSurjectiveFlatLocallyOfFinitePresentation B S hS g ∧
    ∃ (Q : Bicategory.TwoCommSq g f.hom) (_ : Bicategory.IsTwoFibreProduct Q)
      (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
      (eV : StacksRepresentableCFG.EquivalenceOver
        Q.pt.val.p (presheafOfCategories (V ⋙ typeToCat)).p),
      Mono (ObjectProperty.homMk (representingMap B S hS Q.pt 𝒲 V W eV eW Q.fst) :
        (⟨V, hV⟩ : AlgebraicSpaces B S hS) ⟶ (⟨W, hW⟩ : AlgebraicSpaces B S hS))

/-- **Stacks 04ZZ, the implication (1) ⟹ (4).** A monomorphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks
has a monomorphic base change to an fppf cover of `𝒴` by an algebraic space.

The cover is the smooth scheme atlas `U ⟶ 𝒴` of Stacks 026O: smooth morphisms of algebraic spaces
are flat (Stacks 04TA) and locally of finite presentation (Stacks 04AJ). The apex of the 2-fibre
product square is an algebraic space by Stacks 0300, `f` being representable by algebraic spaces,
and the induced morphism to `U` is a monomorphism by Stacks 04XC applied to the relative
monomorphy of `f`. -/
theorem hasMonomorphicFppfSpaceBaseChange_of_isMonomorphism (f : 𝒳 ⟶ 𝒴)
    (hf : IsMonomorphism B S hS f) :
    HasMonomorphicFppfSpaceBaseChange B S hS f := by
  obtain ⟨_, _, _, U, a, -, haprop⟩ := 𝒴.property
  let g : schemeFibredCategory B S hS U ⟶ 𝒴.val := Bicategory.InducedBicategory.mkHom a
  obtain ⟨W, hW, ⟨eW⟩⟩ := isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U
  have hg : IsSurjectiveFlatLocallyOfFinitePresentation B S hS g := fun V yv hyv F hF he =>
    have h := haprop V yv hyv F hF he
    ⟨h.1, Space.isFlat_of_isSmooth B S hS _ h.2,
      Space.isLocallyOfFinitePresentation_of_isSmooth B S hS h.2⟩
  let Q : Bicategory.TwoCommSq g f.hom :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u} g f.hom
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u} g f.hom
  obtain ⟨V, hV, ⟨eV⟩⟩ := exists_isAlgebraicSpace_pt B S hS 𝒳.val 𝒴.val
    (schemeFibredCategory B S hS U) f.hom g hf.1 Q hQ W hW eW
  exact ⟨schemeFibredCategory B S hS U, W, hW, eW, g, hg, Q, hQ, V, hV, eV,
    prop_representingMap_of_hasRelativeProperty.{u, u} B S hS
      (MorphismProperty.monomorphisms (AlgebraicSpaces B S hS)) f.hom hf.1 hf.2
      (schemeFibredCategory B S hS U) g Q hQ V W hV hW eV eW⟩

/-- **Stacks 04ZZ, the implication (4) ⟹ (2).** If a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks
has a monomorphic base change `V ⟶ W` to a surjective, flat, locally finitely presented cover of
`𝒴` by an algebraic space `W`, then `f` is fully faithful.

The projection `𝒳 ×_𝒴 W ⟶ W` is a 1-morphism between categories represented by algebraic spaces,
so it is representable by algebraic spaces (Stacks 02ZZ); its relative monomorphy is monomorphy
of `V ⟶ W` (Stacks 04XB for represented source and target), so it is fully faithful by
Stacks 05UK. Full faithfulness is carried over to the first projection of the canonical 2-fibre
product, which is equivalent to the given square, and descends along the locally essentially
surjective `W ⟶ 𝒴` by `CategoryTheory.Functor.full_and_faithful_of_full_and_faithful_fst`.
Representability of `f` is not needed. -/
theorem full_and_faithful_homFunctor_of_hasMonomorphicFppfSpaceBaseChange (f : 𝒳 ⟶ 𝒴)
    (hf : HasMonomorphicFppfSpaceBaseChange B S hS f) :
    (CatFiberedInGroupoids.homFunctor f.hom).Full ∧
      (CatFiberedInGroupoids.homFunctor f.hom).Faithful := by
  obtain ⟨𝒲, W, hW, eW, g, hg, Q, hQ, V, hV, eV, hmono⟩ := hf
  -- the projection `Q.fst : V ⟶ W` is fully faithful, by Stacks 05UK
  have hrep : IsRepresentableByAlgebraicSpaces B S hS Q.fst.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS Q.fst
      ⟨V, hV, ⟨eV⟩⟩ ⟨W, hW, ⟨eW⟩⟩
  have hrel := (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
    (MorphismProperty.monomorphisms (AlgebraicSpaces B S hS)) Q.fst hrep V W hV hW eV eW).2 hmono
  obtain ⟨hQfull, hQfaith⟩ := full_and_faithful_homFunctor_of_mono_representingMaps B S hS Q.fst
    hrep fun U y hy F hF he => (Space.mono_hom_iff_mono B S hS _).2 (hrel U y hy F hF he)
  -- so is the first projection of the canonical 2-fibre product
  let C : Bicategory.TwoCommSq g f.hom :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u} g f.hom
  have hC : Bicategory.IsTwoFibreProduct C :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u} g f.hom
  let a : Bicategory.TwoCommSq.PreHom Q C := Quotient.out (hC.from Q)
  let b : Bicategory.TwoCommSq.PreHom C Q := Quotient.out (hQ.from C)
  obtain ⟨e₂, -, -⟩ := Quotient.exact (hC.hom_ext (Quotient.mk _ (b.comp a)) (𝟙 C))
  obtain ⟨e₁, -, -⟩ := Quotient.exact (hQ.hom_ext (Quotient.mk _ (a.comp b)) (𝟙 Q))
  have hb : b.hom.hom.toFunctor.IsEquivalence :=
    (CategoryTheory.Equivalence.mk b.hom.hom.toFunctor a.hom.hom.toFunctor
      (CatFiberedInGroupoids.underlyingIso e₂).symm
      (CatFiberedInGroupoids.underlyingIso e₁)).isEquivalence_functor
  have e := (CatFiberedInGroupoids.underlyingIso b.isoFst).symm
  -- full faithfulness descends along `g`
  exact Functor.full_and_faithful_of_full_and_faithful_fst
    (CatFiberedInGroupoids.homFunctor_comp_p g) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids 𝒴.property.choose_spec.1.1
    𝒳.property.choose_spec.1.1
    (locallyEssSurjOnFibers_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS 𝒲
      ⟨W, hW, ⟨eW⟩⟩ g hg)
    (Functor.Full.of_iso (F := b.hom.hom.toFunctor ⋙ Q.fst.hom.toFunctor) e)
    (Functor.Faithful.of_iso (F := b.hom.hom.toFunctor ⋙ Q.fst.hom.toFunctor) e)

/-- **Stacks 04ZZ.** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` the following
are equivalent:

1. `f` is a monomorphism (Stacks 04ZW);
2. `f` is fully faithful;
3. the diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is an equivalence;
4. there are an algebraic space `W` and a surjective, flat, locally finitely presented
   `W ⟶ 𝒴` such that `V = 𝒳 ×_𝒴 W` is an algebraic space and `V ⟶ W` is a monomorphism.

(1) ⟹ (2) is Stacks 05UK, (2) ⟺ (3) is Stacks 04Z7, (2) ⟹ (1) is
`AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_of_full_and_faithful` (through
Stacks 04Y5), (1) ⟹ (4) is
`AlgebraicGeometry.Stack.AlgebraicStacks.hasMonomorphicFppfSpaceBaseChange_of_isMonomorphism` and
(4) ⟹ (2) is `full_and_faithful_homFunctor_of_hasMonomorphicFppfSpaceBaseChange`. -/
@[stacks 04ZZ]
theorem isMonomorphism_tfae_of_bootstrap (f : 𝒳 ⟶ 𝒴) :
    List.TFAE
      [IsMonomorphism B S hS f,
        (CatFiberedInGroupoids.homFunctor f.hom).Full ∧
          (CatFiberedInGroupoids.homFunctor f.hom).Faithful,
        (CatFiberedInGroupoids.homFunctor
          (relativeDiagonalAlgebraicStacks B S hS f).hom).IsEquivalence,
        HasMonomorphicFppfSpaceBaseChange B S hS f] := by
  tfae_have 1 → 2 := full_and_faithful_homFunctor_of_isMonomorphism B S hS f
  tfae_have 2 ↔ 3 := TwoFibreProductOver.full_and_faithful_iff_isEquivalence_diagonal
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
  tfae_have 2 → 1 := fun h => isMonomorphism_of_full_and_faithful B S hS f h.1 h.2
  tfae_have 1 → 4 := hasMonomorphicFppfSpaceBaseChange_of_isMonomorphism B S hS f
  tfae_have 4 → 2 := full_and_faithful_homFunctor_of_hasMonomorphicFppfSpaceBaseChange B S hS f
  tfae_finish

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
