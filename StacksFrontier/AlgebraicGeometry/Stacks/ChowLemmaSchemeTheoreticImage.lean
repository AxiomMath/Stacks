module

public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedCriterion
public import StacksFrontier.CategoryTheory.Sites.Gerbe.BaseEquivalence
public import StacksFrontier.CategoryTheory.Sites.Gerbe.NatIso
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# The scheme theoretic image step of Chow's lemma for algebraic stacks

In the proof of Chow's lemma for algebraic stacks (Stacks 0CQ8) a gerbe `𝒱 ⟶ V` over an open
`V ⊆ Y'` is embedded in an algebraic stack `𝒵` over `Y'`, and the scheme theoretic image `𝒳'` of
`𝒱 ⟶ 𝒵` is shown to satisfy `V ×_{Y'} 𝒳' = 𝒱`. The argument is: the immersion `𝒱 ⟶ 𝒵_V` is
universally closed (Stacks 0CPT, `𝒱 ⟶ V` being a universal homeomorphism), hence a closed
immersion, so it is its own scheme theoretic image, and formation of scheme theoretic images
commutes with the flat base change `𝒵_V ⟶ 𝒵` (Stacks 0CMK).

This file proves the general steps of that argument which do not depend on the particular
situation of Stacks 0CQ8.

## Main results

* `AlgebraicGeometry.Space.isClosedImmersion_of_isImmersion_of_universallyClosed`: a universally
  closed immersion of algebraic spaces is a closed immersion.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isClosedImmersion_of_isImmersion_of_universallyClosed`:
  the same for 1-morphisms of algebraic stacks.
* `Stack.AlgebraicStacks.eq_essImage_of_isSchemeTheoreticImage_of_isClosedImmersion`:
  the scheme theoretic image of a closed immersion is its essential image.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_of_isEquivalence_comp`: if `u ≫ p` is a
  gerbe and `u` is an equivalence, then `p` is a gerbe.

## References

* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
* [Stacks Project, Tag 0CMK](https://stacks.math.columbia.edu/tag/0CMK)
* [Stacks Project, Tag 0CPT](https://stacks.math.columbia.edu/tag/0CPT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A universally closed immersion of algebraic spaces is a closed immersion.** Every
represented base change is an immersion of schemes which is universally closed, hence has closed
image, hence is a closed immersion. -/
theorem isClosedImmersion_of_isImmersion_of_universallyClosed
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y} (hf : IsImmersion B S hS f)
    (huc : UniversallyClosed B S hS f) : IsClosedImmersion B S hS f := by
  have huc' := (presheaf_universallyClosed_iff B S hS hX hY hf.rep).2 huc
  refine ⟨hf.rep, fun a b g fst snd hpb => ?_⟩
  have h1 : _root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map snd) :=
    hf.property g fst snd hpb
  have h2 : _root_.AlgebraicGeometry.UniversallyClosed ((BigFppfOver.toScheme B S hS).map snd) :=
    huc'.property g fst snd hpb
  change _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map snd)
  exact _root_.AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion _ (by
    simpa only [Set.image_univ] using
      ((BigFppfOver.toScheme B S hS).map snd).isClosedMap _ isClosed_univ)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A universally closed immersion of algebraic stacks is a closed immersion.** Both are
conditions on the algebraic spaces representing the base changes along scheme-valued points
(Stacks 04XB, with Stacks 0512 for universal closedness), where it is
`AlgebraicGeometry.Space.isClosedImmersion_of_isImmersion_of_universallyClosed`. -/
theorem isClosedImmersion_of_isImmersion_of_universallyClosed {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hf : IsImmersion B S hS f) (huc : UniversallyClosed B S hS f) :
    IsClosedImmersion B S hS f := by
  have huc' := (Stack.representable_universallyClosed_iff_closedMap_baseChange B S hS f hf.1).2 huc
  refine ⟨hf.1, fun U y hy F hF e => ?_⟩
  exact Space.isClosedImmersion_of_isImmersion_of_universallyClosed B S hS
    ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).property
    (isAlgebraicSpace_yoneda B S hS (Over.mk U.hom))
    (hf.2 U y hy F hF e) (huc' U y hy F hF e)

/-- **The scheme theoretic image of a closed immersion is its essential image** (Stacks 0CMI,
with Stacks 0506): the essential image is a closed substack through which the closed immersion
factors, and it lies in every substack, closed under isomorphism, through which it factors. -/
theorem eq_essImage_of_isSchemeTheoreticImage_of_isClosedImmersion
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsClosedImmersion B S hS f)
    {P : ObjectProperty 𝒴.val.val.obj} (hP : IsSchemeTheoreticImage f P) :
    P = (CatFiberedInGroupoids.homFunctor f.hom).essImage := by
  refine le_antisymm (hP.2.2 _ (isClosedSubstack_essImage f hf)
    ((factorsThroughSubstack_iff_forall f).2 fun x => ⟨x, ⟨Iso.refl _⟩⟩)) ?_
  have : P.IsClosedUnderIsomorphisms := hP.1.1
  rintro y ⟨x, ⟨i⟩⟩
  exact P.prop_of_iso i ((factorsThroughSubstack_iff_forall f).1 hP.2.1 x)

/-- **Gerbes descend along equivalences of the source.** If `u : 𝒲 ⟶ 𝒬` is an equivalence of
the underlying categories and `u ≫ p` is 2-isomorphic to a gerbe `g`, then `p` is a gerbe
(Stacks 06P0). -/
theorem isGerbeOver_of_isEquivalence_comp {𝒲 𝒬 𝒱 : AlgebraicStacks.{u, w} B S hS}
    (u : 𝒲 ⟶ 𝒬) (p : 𝒬 ⟶ 𝒱) (g : 𝒲 ⟶ 𝒱)
    (hu : (CatFiberedInGroupoids.homFunctor u.hom).IsEquivalence) (η : u ≫ p ≅ g)
    (hg : IsGerbeOver B S hS g) : IsGerbeOver B S hS p := by
  set q := 𝒱.val.val.p
  set a := CatFiberedInGroupoids.homFunctor u.hom
  set F' := CatFiberedInGroupoids.homFunctor p.hom
  have hup : CatFiberedInGroupoids.homFunctor (u ≫ p).hom ⋙ q = 𝒲.val.val.p :=
    CatFiberedInGroupoids.homFunctor_comp_p (u ≫ p).hom
  have hgp : CatFiberedInGroupoids.homFunctor g.hom ⋙ q = 𝒲.val.val.p :=
    CatFiberedInGroupoids.homFunctor_comp_p g.hom
  have hcomp : CategoryTheory.IsGerbeOver (BigFppfOver.topology B S hS) q (a ⋙ F') := by
    have h := hg.of_verticalNatIso (hgp.trans hup.symm) (underlyingIso B S hS η).symm
      (Functor.IsVerticalNatTrans.inv q (underlyingIso B S hS η)
        (isVerticalNatTrans_underlyingIso B S hS η))
    exact h
  have hpP : F' ⋙ q = 𝒬.val.val.p := CatFiberedInGroupoids.homFunctor_comp_p p.hom
  have hpa : (a ⋙ F') ⋙ q = 𝒲.val.val.p := by
    rw [Functor.assoc, hpP]
    exact CatFiberedInGroupoids.homFunctor_comp_p u.hom
  obtain ⟨e⟩ := StacksRepresentableCFG.nonempty_isEquivalenceOver_of_isEquivalence
    𝒲.val.isFiberedInGroupoids 𝒬.val.isFiberedInGroupoids a
    (CatFiberedInGroupoids.homFunctor_comp_p u.hom) hu
  have e' : Functor.IsEquivalenceOver ((a ⋙ F') ⋙ q) (F' ⋙ q) a := by
    rw [hpa, hpP]
    exact e
  exact CategoryTheory.IsGerbeOver.of_isEquivalenceOver_base rfl e' hcomp

end AlgebraicGeometry.Stack.AlgebraicStacks

end
