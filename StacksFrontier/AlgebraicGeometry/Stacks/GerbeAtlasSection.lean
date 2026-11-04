module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatLocalSection
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace

/-!
# A gerbe acquires a section over an algebraic space atlas of its source

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` making `𝒳` a gerbe over `𝒴`. This
file produces an **algebraic space** `U` over `S` and a surjective, flat, locally finitely
presented 1-morphism `g : 𝒰 ⟶ 𝒴` out of the algebraic stack of `U` after which `f` acquires a
section: every 2-fibre product of the cospan `(f, g)` has a section of its projection to `𝒰`.

This is the reduction step of **Stacks 06QH**, the implication (1) `⟹` (2), in the form clause (2)
needs it: that clause asks for an algebraic space `U` and an identification of `𝒳 ×_𝒴 U` with a
classifying stack over `U`, so the covering 1-morphism has to come out of the algebraic stack of
an *algebraic space*, not out of the algebraic stack of an object of the site.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_space_section_snd_of_isGerbeOver`: the statement
  above.

## Implementation notes

The covering 1-morphism is **not** built by the source's argument, which replaces the target first
by a scheme smoothly covering it and then by a member of an fppf covering of that scheme over
which the fibre category of `𝒳` is nonempty. It is built instead out of a *smooth atlas of the
source*: if `a : 𝒰 ⟶ 𝒳` is smooth and surjective then `g = a ≫ f` is surjective, flat and locally
of finite presentation — `a` is, because a smooth 1-morphism is flat (**Stacks 04TA**) and locally
of finite presentation (**Stacks 0DNP**), and `f` is, by **Stacks 06QI** — and the square with legs
`a` and `𝟙 𝒰` over the cospan `(f, g)`, filled by the left unitor, is 2-commutative *by
construction*. Its mediating 1-morphism into a 2-fibre product (**Stacks 003Q**) is the section.

So no instance of Stacks 06P1 and no fppf covering enters, and the section comes for free with the
atlas. The atlas is obtained as an algebraic space rather than as a scheme by composing a smooth
surjective scheme atlas (`AlgebraicGeometry.Stack.exists_smooth_surjective_schemeStack`) with the
smooth surjective comparison
`AlgebraicGeometry.Stack.exists_smooth_surjective_algebraicSpaceStack_hom` of the algebraic stack
of the presheaf represented by a scheme of the site with the algebraic stack of that scheme; the
composite is not asserted to be smooth, only flat, locally of finite presentation and surjective,
which is all that is used.

The companion
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_section_snd_of_isGerbeOver` of
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeCharacterization` produces a section over the algebraic
stack of an *object of the site*, which is what
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatLocalSection` consumes; neither statement implies
the other without a comparison of the two kinds of base, and the one proved here is the one
clause (2) of Stacks 06QH asks for.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04TA](https://stacks.math.columbia.edu/tag/04TA)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 06QH](https://stacks.math.columbia.edu/tag/06QH)
* [Stacks Project, Tag 06QI](https://stacks.math.columbia.edu/tag/06QI)
* [Stacks Project, Tag 0DNP](https://stacks.math.columbia.edu/tag/0DNP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

/-- **Every algebraic stack over `S` is covered by an algebraic space through a surjective, flat,
locally finitely presented 1-morphism.** A smooth surjective scheme atlas
(`AlgebraicGeometry.Stack.exists_smooth_surjective_schemeStack`) is composed with the smooth
surjective comparison of the algebraic stack of the presheaf a scheme of the site represents with
the algebraic stack of that scheme
(`AlgebraicGeometry.Stack.exists_smooth_surjective_algebraicSpaceStack_hom`); both legs are flat
(**Stacks 04TA**) and locally of finite presentation (**Stacks 0DNP**) because they are smooth. -/
theorem exists_isSurjective_isFlat_isLfp_spaceAtlas
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    ∃ (U : AlgebraicSpaces B S hS) (a : ofAlgebraicSpace.{u, w} B S hS U ⟶ 𝒳),
      Stack.IsSurjective B S hS a ∧ IsFlat B S hS a ∧
        IsLocallyOfFinitePresentation B S hS a := by
  obtain ⟨V, a, hasm, hasurj⟩ := Stack.exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  obtain ⟨e, hesm, hesurj⟩ :=
    Stack.exists_smooth_surjective_algebraicSpaceStack_hom.{u, w} B S hS V
  refine ⟨⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩, e ≫ a,
    Stack.isSurjective_comp B S hS e a hesurj hasurj,
    isFlat_comp B S hS e a (isFlat_of_isSmooth B S hS e hesm)
      (isFlat_of_isSmooth B S hS a hasm),
    isLocallyOfFinitePresentation_comp B S hS e a
      (isLocallyOfFinitePresentation_of_isSmooth B S hS e hesm)
      (isLocallyOfFinitePresentation_of_isSmooth B S hS a hasm)⟩

/-- **A gerbe acquires a section after a surjective, flat, locally finitely presented 1-morphism
onto its target out of the algebraic stack of an algebraic space.** Let `f : 𝒳 ⟶ 𝒴` make `𝒳` a
gerbe over `𝒴`. Then there are an algebraic space `U` over `S` and a surjective, flat, locally
finitely presented `g : 𝒰 ⟶ 𝒴` out of the algebraic stack of `U` such that *every* 2-fibre product
of the cospan `(f, g)` has a section of its projection to `𝒰`.

This is the reduction step of **Stacks 06QH** (1) `⟹` (2) at the kind of base clause (2) names.
The covering 1-morphism is `g = a ≫ f` for `a : 𝒰 ⟶ 𝒳` a flat, locally finitely presented,
surjective atlas of the *source*: it is surjective, flat and locally of finite presentation
because `f` is, by **Stacks 06QI**, and the square with legs `a` and `𝟙 𝒰` over the cospan
`(f, g)` filled by the left unitor is 2-commutative by construction, so the mediating 1-morphism
into a 2-fibre product (**Stacks 003Q**) carries `𝟙 𝒰` to a 2-isomorphism `σ ≫ P.snd ≅ 𝟙 𝒰`. -/
theorem exists_space_section_snd_of_isGerbeOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsGerbeOver B S hS f) :
    ∃ (U : AlgebraicSpaces B S hS) (g : ofAlgebraicSpace.{u, w} B S hS U ⟶ 𝒴),
      Stack.IsSurjective B S hS g ∧ IsFlat B S hS g ∧
        IsLocallyOfFinitePresentation B S hS g ∧
        ∀ P : Bicategory.TwoCommSq f g, Bicategory.IsTwoFibreProduct P →
          ∃ σ : ofAlgebraicSpace.{u, w} B S hS U ⟶ P.pt,
            Nonempty (σ ≫ P.snd ≅ 𝟙 (ofAlgebraicSpace.{u, w} B S hS U)) := by
  obtain ⟨U, a, hasurj, haflat, halfp⟩ :=
    exists_isSurjective_isFlat_isLfp_spaceAtlas.{u, w} B S hS 𝒳
  refine ⟨U, a ≫ f,
    Stack.isSurjective_comp B S hS a f hasurj (Stack.isSurjective_of_isGerbeOver B S hS f hf),
    isFlat_comp B S hS a f haflat
      (isFlat_of_isGerbeOver B S hS f hf (exists_flatLfpSection_of_isGerbeOver B S hS f hf)),
    isLocallyOfFinitePresentation_comp B S hS a f halfp
      (isLocallyOfFinitePresentation_of_isGerbeOver B S hS f hf
        (exists_flatLfpSection_of_isGerbeOver B S hS f hf)),
    fun P hP => ?_⟩
  let Q : Bicategory.TwoCommSq f (a ≫ f) :=
    { pt := ofAlgebraicSpace.{u, w} B S hS U
      fst := a
      snd := 𝟙 _
      iso := (Bicategory.leftUnitor (a ≫ f)).symm }
  exact ⟨(Bicategory.twoFibreProductPreHom hP Q).hom,
    ⟨(Bicategory.twoFibreProductPreHom hP Q).isoSnd.symm⟩⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
