module

public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentableUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableStackInSetoids
public import StacksFrontier.CategoryTheory.Sites.Stack.FaithfulDescent
public import StacksFrontier.CategoryTheory.Sites.Stack.LocallyEssSurjOnFibersComp
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids

/-!
# Representability by algebraic spaces from an fppf cover (Stacks 04ZP)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `W` be an algebraic space and
let `W ⟶ 𝒴` be surjective, flat and locally of finite presentation. **Stacks 04ZP** says that `f`
is representable by algebraic spaces if and only if `W ×_𝒴 𝒳` is an algebraic space. The
implication (1) ⟹ (2) is Stacks 0300,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct`. This file proves
the converse (2) ⟹ (1) and assembles the equivalence.

## Main results

* `AlgebraicGeometry.Stack.locallyEssSurjOnFibers_of_localEssSurj`: local lifts along the members
  of covering sieves make a 1-morphism locally essentially surjective on fibres.
* `AlgebraicGeometry.Stack.faithful_homFunctor_of_isTwoFibreProduct_of_locallyEssSurjOnFibers`:
  Stacks 06DV for a 2-fibre product square of categories fibred in groupoids at any universes.
* `AlgebraicStacks.locallyEssSurjOnFibers_of_isSurjective_isFlat_isLocallyOfFinitePresentation`:
  a surjective, flat, locally finitely presented 1-morphism from an algebraic space to an
  algebraic stack is locally essentially surjective on fibres, the hypothesis of Stacks 06DV.
* `AlgebraicGeometry.Stack.AlgebraicStacks.faithful_homFunctor_of_isTwoFibreProduct`: in the
  situation of Stacks 04ZP (2), `f` is faithful. This is the source's argument: the projection
  `W ×_𝒴 𝒳 ⟶ W` is faithful because the fibres of an algebraic space are thin, and Stacks 06DV
  (`CategoryTheory.Functor.faithful_of_faithful_fst`) descends faithfulness along the locally
  essentially surjective `W ⟶ 𝒴`.
* `AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_isTwoFibreProduct_of_bootstrap`:
  the implication (2) ⟹ (1) of Stacks 04ZP.
* `AlgebraicStacks.isRepresentableByAlgebraicSpaces_iff_isRepresentableByAlgebraicSpace_pt`:
  **Stacks 04ZP**.

## Implementation notes

The source's proof of (2) ⟹ (1) is: by Stacks 04Y5 it suffices that `f` be faithful, and that
follows from Stacks 06DV. The first step is the implication (2) ⟹ (3) of Stacks 04Y5,
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful`.

The surjectivity, flatness and local finite presentation of `W ⟶ 𝒴` are written out as the
relative-property condition of Stacks 03YK, exactly as
`AlgebraicGeometry.Stack.IsSurjectiveFlatLocallyOfFinitePresentation` does; it is not used by
name so that this file does not import
`StacksFrontier.AlgebraicGeometry.Stacks.ImmersionFppfCoverCriterion`, whose Stacks 0503 statements
consume this one. Representability of `W ⟶ 𝒴` by algebraic spaces is not assumed: it follows
from Stacks 045G, the diagonal of `𝒴` being representable.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 06DV](https://stacks.math.columbia.edu/tag/06DV)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Local essential surjectivity on fibres from local lifts.** If every object `y` of a fibre of
`𝒴` has, over the members `k` of a covering sieve, a morphism `g(z) ⟶ y` lying over `k`, then `g`
is locally essentially surjective on fibres in the sense of Stacks 06DV: the morphism is
cartesian, `𝒴` being fibred in groupoids, so it identifies `g(z)` with the pullback of `y`. -/
theorem locallyEssSurjOnFibers_of_localEssSurj
    {𝒲 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (g : 𝒲 ⟶ 𝒴)
    (hess : ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ (z : 𝒲.val.obj) (φ : (CatFiberedInGroupoids.homFunctor g).obj z ⟶ y.1),
            𝒴.val.p.IsHomLift k φ) :
    Functor.LocallyEssSurjOnFibers 𝒴.isFiberedInGroupoids.isFibered
      (CatFiberedInGroupoids.homFunctor_comp_p g) (BigFppfOver.topology B S hS) := by
  have : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  intro U y
  obtain ⟨R, hR, hRl⟩ := hess U y
  refine ⟨R, hR, fun V k hk => ?_⟩
  obtain ⟨z, φ, hφ⟩ := hRl hk
  have hz : 𝒲.val.p.obj z = V :=
    (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p g) z).symm.trans
      (IsHomLift.domain_eq 𝒴.val.p k φ)
  exact ⟨Functor.Fiber.mk hz, ⟨Functor.fiberIsoPullbackFiber 𝒴.val.p y k _ φ
    (𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift k φ)⟩⟩

/-- **Faithfulness descends along a locally essentially surjective 1-morphism (Stacks 06DV).** Let
`f : 𝒳 ⟶ 𝒴` and `g : 𝒲 ⟶ 𝒴` be 1-morphisms of categories fibred in groupoids over the big fppf
site of `S`, with `𝒳` a stack and `g` locally essentially surjective on fibres. If the first
projection of some 2-fibre product square over the cospan `(g, f)` is faithful, then `f` is
faithful.

The faithfulness is carried from the given square to the canonical 2-fibre product, to which it
is equivalent, and descends along `g` by `CategoryTheory.Functor.faithful_of_faithful_fst`. The
universes are those at which the 2-category is closed under the canonical 2-fibre product. -/
theorem faithful_homFunctor_of_isTwoFibreProduct_of_locallyEssSurjOnFibers
    {𝒳 𝒴 𝒲 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒴) (h𝒳 : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (hloc : Functor.LocallyEssSurjOnFibers 𝒴.isFiberedInGroupoids.isFibered
      (CatFiberedInGroupoids.homFunctor_comp_p g) (BigFppfOver.topology B S hS))
    (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hQfst : (CatFiberedInGroupoids.homFunctor Q.fst).Faithful) :
    (CatFiberedInGroupoids.homFunctor f).Faithful := by
  classical
  let C : Bicategory.TwoCommSq g f :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, v, u + 1, w} g f
  have hC : Bicategory.IsTwoFibreProduct C :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, v, u + 1, w} g f
  let a : Bicategory.TwoCommSq.PreHom Q C := Quotient.out (hC.from Q)
  let b : Bicategory.TwoCommSq.PreHom C Q := Quotient.out (hQ.from C)
  obtain ⟨e₂, -, -⟩ :=
    Quotient.exact (hC.hom_ext (Quotient.mk _ (b.comp a)) (𝟙 C))
  have hb : b.hom.hom.toFunctor.Faithful := by
    have : (Bicategory.TwoCommSq.PreHom.id C).hom.hom.toFunctor.Faithful :=
      inferInstanceAs (𝟭 _).Faithful
    exact Functor.Faithful.of_comp_iso (G := a.hom.hom.toFunctor)
      (CatFiberedInGroupoids.underlyingIso e₂)
  have hCfst : (TwoFibreProductOver.fst 𝒲.val.p 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor g) (CatFiberedInGroupoids.homFunctor f)).Faithful :=
    have : (b.hom ≫ Q.fst).hom.toFunctor.Faithful :=
      @Functor.Faithful.comp _ _ _ _ _ _ _ _ hb hQfst
    Functor.Faithful.of_iso (F := (b.hom ≫ Q.fst).hom.toFunctor)
      (CatFiberedInGroupoids.underlyingIso b.isoFst).symm
  -- Stacks 06DV
  exact Functor.faithful_of_faithful_fst_univ (CatFiberedInGroupoids.homFunctor_comp_p g)
    (CatFiberedInGroupoids.homFunctor_comp_p f) 𝒴.isFiberedInGroupoids
    𝒳.isFiberedInGroupoids h𝒳 hloc hCfst

namespace AlgebraicStacks

/-- **An fppf cover of an algebraic stack by an algebraic space is locally essentially surjective
on fibres.** Let `𝒲` be represented by an algebraic space and let `g : 𝒲 ⟶ 𝒴` be a 1-morphism to
an algebraic stack which is surjective, flat and locally of finite presentation. Then every object
of a fibre of `𝒴` becomes, after restriction to the members of a covering sieve, isomorphic in
the fibre to the image of an object of `𝒲`: this is the hypothesis of Stacks 06DV.

`g` is representable by algebraic spaces by Stacks 045G, the diagonal of `𝒴` being
representable, and
`AlgebraicGeometry.Stack.localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation`
gives the local lifts, which are strongly cartesian because `𝒴` is fibred in groupoids. -/
theorem locallyEssSurjOnFibers_of_isSurjective_isFlat_isLocallyOfFinitePresentation
    {𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒲 : IsRepresentableByAlgebraicSpace B S hS 𝒲) (g : 𝒲 ⟶ 𝒴.val)
    (hg : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.val.obj)
      (_hyv : yv ⋙ 𝒴.val.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒲.val.p 𝒴.val.val.p yv
          (CatFiberedInGroupoids.homFunctor g))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsFlat B S hS h ∧
         Space.IsLocallyOfFinitePresentation B S hS h))
    :
    Functor.LocallyEssSurjOnFibers 𝒴.val.isFiberedInGroupoids.isFibered
      (CatFiberedInGroupoids.homFunctor_comp_p g) (BigFppfOver.topology B S hS) := by
  -- `g` is representable by algebraic spaces, by Stacks 045G
  have hdiag : HasRepresentableDiagonal B S hS 𝒴.val := 𝒴.property.choose_spec.2.1
  have hgr : IsRepresentableByAlgebraicSpaces B S hS g.hom :=
    isRepresentableFromAlgebraicSpaces_of_hasRepresentableDiagonal.{u, u, u + 1, u, u + 1}
      B S hS 𝒴.val hdiag 𝒲 h𝒲 g.hom
  -- `g` is locally essentially surjective on fibres
  exact locallyEssSurjOnFibers_of_localEssSurj B S hS g
    (localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS g hgr hg)

/-- **Faithfulness from an fppf cover by an algebraic space.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism
of algebraic stacks over `S`, let `𝒲` be represented by an algebraic space and let
`g : 𝒲 ⟶ 𝒴` be surjective, flat and locally of finite presentation. If the apex of a 2-fibre
product square over the cospan `(g, f)` is represented by an algebraic space, then `f` is
faithful.

This is the second half of the source's proof of Stacks 04ZP: the projection
`W ×_𝒴 𝒳 ⟶ W` is faithful since the fibres of an algebraic space are thin, and Stacks 06DV
descends faithfulness along `g`, which is locally essentially surjective. -/
theorem faithful_homFunctor_of_isTwoFibreProduct
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒲 : IsRepresentableByAlgebraicSpace B S hS 𝒲)
    (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒴.val)
    (hg : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.val.obj)
      (_hyv : yv ⋙ 𝒴.val.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒲.val.p 𝒴.val.val.p yv
          (CatFiberedInGroupoids.homFunctor g))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsFlat B S hS h ∧
         Space.IsLocallyOfFinitePresentation B S hS h))
    (Q : Bicategory.TwoCommSq g f.hom) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hQpt : IsRepresentableByAlgebraicSpace B S hS Q.pt) :
    (CatFiberedInGroupoids.homFunctor f.hom).Faithful := by
  -- the projection of the given square to `𝒲` is faithful: its source has thin fibres
  have hthin := (isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS Q.pt
    hQpt).fiber_isThin
  have hQfst : (CatFiberedInGroupoids.homFunctor Q.fst).Faithful := by
    have : 𝒲.val.p.IsFibered := 𝒲.isFiberedInGroupoids.isFibered
    rw [Functor.IsFiberedInGroupoids.faithful_iff_forall_fiber Q.pt.val.p 𝒲.val.p
      Q.pt.isFiberedInGroupoids 𝒲.isFiberedInGroupoids _
      (CatFiberedInGroupoids.homFunctor_comp_p Q.fst)]
    intro U
    exact ⟨fun {a b} α β _ => @Subsingleton.elim _ (hthin U a b) α β⟩
  exact faithful_homFunctor_of_isTwoFibreProduct_of_locallyEssSurjOnFibers.{u, u, u + 1} B S hS
    f.hom g 𝒳.property.choose_spec.1.1
    (locallyEssSurjOnFibers_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS 𝒲 h𝒲 g hg)
    Q hQ hQfst

/-- **The implication (2) ⟹ (1) of Stacks 04ZP.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic
stacks over `S`, let `𝒲` be represented by an algebraic space `W` and let `g : 𝒲 ⟶ 𝒴` be
surjective, flat and locally of finite presentation. If the apex `W ×_𝒴 𝒳` of a 2-fibre product
square over the cospan `(g, f)` is represented by an algebraic space then `f` is representable by
algebraic spaces.

This is the source's proof: `f` is faithful by
`AlgebraicGeometry.Stack.AlgebraicStacks.faithful_homFunctor_of_isTwoFibreProduct` (Stacks 06DV),
and faithfulness gives representability by the implication (2) ⟹ (3) of Stacks 04Y5,
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful`. -/
theorem isRepresentableByAlgebraicSpaces_of_isTwoFibreProduct_of_bootstrap
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒲 : IsRepresentableByAlgebraicSpace B S hS 𝒲)
    (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒴.val)
    (hg : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.val.obj)
      (_hyv : yv ⋙ 𝒴.val.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒲.val.p 𝒴.val.val.p yv
          (CatFiberedInGroupoids.homFunctor g))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsFlat B S hS h ∧
         Space.IsLocallyOfFinitePresentation B S hS h))
    (Q : Bicategory.TwoCommSq g f.hom) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hQpt : IsRepresentableByAlgebraicSpace B S hS Q.pt) :
    IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
  isRepresentableByAlgebraicSpaces_of_faithful B S hS f
    (faithful_homFunctor_of_isTwoFibreProduct B S hS 𝒲 h𝒲 f g hg Q hQ hQpt)

/-- **Stacks 04ZP.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `𝒲` be
represented by an algebraic space `W` and let `g : 𝒲 ⟶ 𝒴` be surjective, flat and locally of
finite presentation. Then `f` is representable by algebraic spaces if and only if the apex
`W ×_𝒴 𝒳` of a 2-fibre product square over the cospan `(g, f)` is represented by an algebraic
space.

The implication (1) ⟹ (2) is Stacks 0300,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct`, which needs none
of the hypotheses on `g`; the converse is
`isRepresentableByAlgebraicSpaces_of_isTwoFibreProduct_of_bootstrap`. -/
@[stacks 04ZP]
theorem isRepresentableByAlgebraicSpaces_iff_isRepresentableByAlgebraicSpace_pt
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒲 : IsRepresentableByAlgebraicSpace B S hS 𝒲)
    (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒴.val)
    (hg : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.val.obj)
      (_hyv : yv ⋙ 𝒴.val.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒲.val.p 𝒴.val.val.p yv
          (CatFiberedInGroupoids.homFunctor g))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsFlat B S hS h ∧
         Space.IsLocallyOfFinitePresentation B S hS h))
    (Q : Bicategory.TwoCommSq g f.hom) (hQ : Bicategory.IsTwoFibreProduct Q) :
    IsRepresentableByAlgebraicSpaces B S hS f.hom.hom ↔
      IsRepresentableByAlgebraicSpace B S hS Q.pt :=
  ⟨fun hf => Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      𝒳.val 𝒴.val 𝒲 f.hom g Q hQ hf h𝒲,
    isRepresentableByAlgebraicSpaces_of_isTwoFibreProduct_of_bootstrap B S hS 𝒲 h𝒲 f g hg Q hQ⟩

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
