module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.Locality
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.SmoothPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalCompleteIntersectionFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalCompleteIntersectionMorphismCancellation

/-!
# Cancelling a smooth 1-morphism from a local complete intersection morphism (Stacks 0CJ6)

**Stacks 0CJ6**: in a 2-commutative triangle `𝒳 ⟶ 𝒴 ⟶ 𝒵` of algebraic stacks over `S`, if
`𝒴 ⟶ 𝒵` is smooth and `𝒳 ⟶ 𝒵` is a local complete intersection morphism, then `𝒳 ⟶ 𝒴` is a
local complete intersection morphism. Here `𝒵` is an arbitrary algebraic stack.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_comp_of_flatBaseChange`: the
  cancellation of the existential smooth-diagram criterion of Stacks 06FM, for a property `P`
  which is only stable under *flat* base change.
* **Stacks 0CJ6**, in the namespace `AlgebraicGeometry.Stack`:
  `AlgebraicStacks.isLocalCompleteIntersection_of_isLocalCompleteIntersection_comp_of_isSmooth`.

## Implementation notes

The generic cancellation `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_comp` first
makes the final target representable, by base changing both hypotheses along a smooth
presentation `t : 𝒯 ⟶ 𝒵` by an algebraic space (Stacks 06FQ), and for that asks that the
restriction of the property to algebraic spaces be stable under *arbitrary* base change. The only
base change it performs is along `t`, which is smooth and so flat, so for `P` the flat form of
Stacks 06FQ,
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_baseChange_of_isFlat`, suffices. That is
the one change made here; the rest of the argument is the generic one. The Koszul property of
morphisms of algebraic spaces is stable under flat base change by Stacks 06C7
(`AlgebraicGeometry.Space.isLocalCompleteIntersection_pullback_snd`), and smoothness is stable
under arbitrary base change by Stacks 03ZE
(`AlgebraicGeometry.Space.isSmooth_isStableUnderBaseChange`).

The space-level inputs are all proved: the cancellation for morphisms of algebraic spaces is
Stacks 0CHL (`AlgebraicGeometry.Space.isLocalCompleteIntersection_of_comp_of_isSmooth`), and
smooth locality on the source-and-target of the Koszul property, which crosses the equivalence of
the two conditions of Stacks 06FM, is
`AlgebraicGeometry.Space.isLocalCompleteIntersection_isSmoothLocalOnSourceAndTarget` (Stacks 0CHM
and 0CHN through Stacks 06FB). The triangle is taken with an arbitrary third edge `h : 𝒳 ⟶ 𝒵`
and a 2-isomorphism `f ≫ g ≅ h`, which is what a 2-commutative triangle of algebraic stacks is.

## References

* [Stacks Project, Tag 0CHL](https://stacks.math.columbia.edu/tag/0CHL)
* [Stacks Project, Tag 0CJ3](https://stacks.math.columbia.edu/tag/0CJ3)
* [Stacks Project, Tag 0CJ6](https://stacks.math.columbia.edu/tag/0CJ6)
* [Stacks Project, Tag 06C7](https://stacks.math.columbia.edu/tag/06C7)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FQ](https://stacks.math.columbia.edu/tag/06FQ)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Cancellation of the existential smooth-diagram criterion of Stacks 06FM, for a property
stable under flat base change.** Let `P` and `Q` be properties of morphisms of algebraic spaces
over `S`, both smooth local on the source-and-target, with `P` invariant under isomorphism and
stable under flat base change and with the restriction of `Q` to algebraic spaces stable under
base change, and let `P` cancel against `Q` for morphisms of algebraic spaces. Then for
1-morphisms `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` of algebraic stacks, if `f ≫ g` has `P` and `g` has
`Q`, then `f` has `P`.

The proof is that of `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_comp`, with the
base change of `f ≫ g` along the smooth presentation `t : 𝒯 ⟶ 𝒵` performed by the flat form of
Stacks 06FQ, `t` being flat as a smooth 1-morphism. -/
theorem hasPropertyOnSomeSmoothDiagram_of_comp_of_flatBaseChange
    (P Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    (hQ : Space.IsSmoothLocalOnSourceAndTarget B S hS Q)
    (hPiso : MorphismProperty.RespectsIso P)
    (hPbc : ∀ {X₀ Y₀ Y₀' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (_hX : IsAlgebraicSpace B S hS X₀) (_hY : IsAlgebraicSpace B S hS Y₀)
      (_hY' : IsAlgebraicSpace B S hS Y₀') (m : X₀ ⟶ Y₀) (n : Y₀' ⟶ Y₀),
      Space.IsFlat B S hS n → P m → P (Limits.pullback.snd m n))
    [(spaceProperty B S hS Q).IsStableUnderBaseChange]
    (hcancel : ∀ {U V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u},
      IsAlgebraicSpace B S hS U → IsAlgebraicSpace B S hS V → IsAlgebraicSpace B S hS W →
      ∀ (p : U ⟶ V) (q : V ⟶ W), P (p ≫ q) → Q q → P p)
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : HasPropertyOnSomeSmoothDiagram B S hS P (f ≫ g).hom)
    (hg : HasPropertyOnSomeSmoothDiagram B S hS Q g.hom) :
    HasPropertyOnSomeSmoothDiagram B S hS P f.hom := by
  obtain ⟨V₀, hV₀, t₀, ht₀sm, ht₀su⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS 𝒵.property
  set 𝒯 : AlgebraicStacks.{u, w} B S hS := algebraicSpaceStack.{u, w} B S hS V₀ hV₀ with h𝒯
  set t : 𝒯 ⟶ 𝒵 := Bicategory.InducedBicategory.mkHom t₀ with ht
  have htflat : AlgebraicStacks.IsFlat B S hS t :=
    (AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS t).2
      (hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS
        (fun _ _ k => Space.IsFlat B S hS k) t₀ V₀ hV₀
        (StacksRepresentableCFG.EquivalenceOver.refl _) ht₀sm (Space.isFlat_id B S hS hV₀))
  -- the base change of the presentation along `g`
  set A := twoFibreProductSquareAlgebraicStacks B S hS g t with hAdef
  have hA : Bicategory.IsTwoFibreProduct A :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g t
  have hAu : Bicategory.IsTwoFibreProduct A.underlying :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom t₀
  have hpsm : IsRelativelySmooth.{u, u, u + 1} B S hS A.fst.hom :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS (fibredCategory B S hS V₀) 𝒵.val 𝒴.val
      t₀ g.hom A.underlying hAu ht₀sm
  have hpsu : IsSurjectiveOnObjects B S hS A.pt.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor A.fst.hom) :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS A.fst.hom
      hpsm.1).2
      (hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
        (Space.surjectiveMorphismProperty B S hS) (fibredCategory B S hS V₀) 𝒵.val 𝒴.val
        t₀ g.hom A.underlying hAu ht₀sm.1
        ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS t₀
          ht₀sm.1).1 ht₀su))
  -- the base change of `f` along that, and the pasted rectangle over `(t, f ≫ g)`
  set C := twoFibreProductSquareAlgebraicStacks B S hS A.fst f with hCdef
  have hC : Bicategory.IsTwoFibreProduct C :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS A.fst f
  have hAsw : Bicategory.IsTwoFibreProduct A.swap := Bicategory.isTwoFibreProduct_swap hA
  have hRout : Bicategory.IsTwoFibreProduct (A.swap.paste C) :=
    Bicategory.isTwoFibreProduct_paste hAsw hC
  -- base change both hypotheses to the representable `𝒯`; for `P` along the flat `t`
  have h1 : HasPropertyOnSomeSmoothDiagram B S hS P (C.fst ≫ A.swap.fst).hom :=
    hasPropertyOnSomeSmoothDiagram_baseChange_of_isFlat.{u, w} B S hS P hPiso hPbc (f ≫ g) t
      htflat (A.swap.paste C) hRout hfg
  have h2 : HasPropertyOnSomeSmoothDiagram B S hS Q A.swap.fst.hom :=
    hasPropertyOnSomeSmoothDiagram_baseChange.{u, w} B S hS Q hQ g t A.swap hAsw hg
  -- cancel there, and descend along the atlas `A.fst`
  have h3 : HasPropertyOnSomeSmoothDiagram B S hS P C.fst.hom :=
    hasPropertyOnSomeSmoothDiagram_of_comp_of_representableTarget B S hS P Q hcancel
      C.pt.property A.pt.property V₀ hV₀ C.fst.hom A.swap.fst.hom
      ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS P hP C.pt.property
        𝒯.property (C.fst ≫ A.swap.fst).hom).2 h1)
      ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS Q hQ A.pt.property
        𝒯.property A.swap.fst.hom).2 h2)
  exact hasPropertyOnSomeSmoothDiagram_of_baseChange_along_atlas B S hS P f.hom A.fst.hom
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} A.fst.hom f.hom).swap
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        A.fst.hom f.hom))
    hpsm hpsu h3

namespace AlgebraicStacks

/-- **Stacks 0CJ6.** Let `f : 𝒳 ⟶ 𝒴`, `g : 𝒴 ⟶ 𝒵` and `h : 𝒳 ⟶ 𝒵` be 1-morphisms of algebraic
stacks over `S` forming a 2-commutative triangle, `f ≫ g ≅ h`. If `g` is smooth and `h` is a
local complete intersection morphism, then `f` is a local complete intersection morphism.

Both the hypothesis on `h` and the conclusion are the universal smooth-diagram criterion of
Stacks 06FM (Definition Stacks 0CJ3), and they are moved to the existential one by smooth
locality on the source-and-target of the Koszul property of morphisms of algebraic spaces,
`AlgebraicGeometry.Space.isLocalCompleteIntersection_isSmoothLocalOnSourceAndTarget`. The
cancellation is `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_comp_of_flatBaseChange`
at the pair (Koszul, smooth), whose space-level input is Stacks 0CHL,
`AlgebraicGeometry.Space.isLocalCompleteIntersection_of_comp_of_isSmooth`, and which uses flat
base change of the Koszul property (Stacks 06C7) and base change of smoothness (Stacks 03ZE). -/
@[stacks 0CJ6]
theorem isLocalCompleteIntersection_of_isLocalCompleteIntersection_comp_of_isSmooth
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) (h : 𝒳 ⟶ 𝒵) (e : f ≫ g ≅ h)
    (hg : IsSmooth B S hS g) (hh : IsLocalCompleteIntersection B S hS h) :
    IsLocalCompleteIntersection B S hS f := by
  have hlci := Space.isLocalCompleteIntersection_isSmoothLocalOnSourceAndTarget B S hS
  have hiso : MorphismProperty.RespectsIso
      (fun ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (k : F ⟶ G) =>
        Space.IsLocalCompleteIntersection B S hS k) :=
    Space.holdsOnEveryEtaleChart_respectsIso_presheaf B S hS _
  have hbc : ∀ {X₀ Y₀ Y₀' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (_hX : IsAlgebraicSpace B S hS X₀) (_hY : IsAlgebraicSpace B S hS Y₀)
      (_hY' : IsAlgebraicSpace B S hS Y₀') (m : X₀ ⟶ Y₀) (n : Y₀' ⟶ Y₀),
      Space.IsFlat B S hS n → Space.IsLocalCompleteIntersection B S hS m →
      Space.IsLocalCompleteIntersection B S hS (Limits.pullback.snd m n) := by
    intro X₀ Y₀ Y₀' hX₀ hY₀ hY₀' m n hn hm
    exact Space.isLocalCompleteIntersection_pullback_snd B S hS
      (ObjectProperty.homMk m : (⟨X₀, hX₀⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y₀, hY₀⟩)
      (ObjectProperty.homMk n : (⟨Y₀', hY₀'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y₀, hY₀⟩) hn hm
  have : (Stack.spaceProperty B S hS
      (fun _ _ k => Space.IsSmooth B S hS k)).IsStableUnderBaseChange :=
    Space.isSmooth_isStableUnderBaseChange B S hS
  have hhsome := (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
    (fun _ _ k => Space.IsLocalCompleteIntersection B S hS k) hlci
    𝒳.property 𝒵.property h.hom).1 hh
  have hfgsome : Stack.HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ k => Space.IsLocalCompleteIntersection B S hS k) (f ≫ g).hom :=
    Stack.hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS _
      (Bicategory.InducedBicategory.isoHom e.symm) hhsome
  exact (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ k => Space.IsLocalCompleteIntersection B S hS k) hlci
      𝒳.property 𝒴.property f.hom).2
    (Stack.hasPropertyOnSomeSmoothDiagram_of_comp_of_flatBaseChange.{u, w} B S hS
      (fun _ _ k => Space.IsLocalCompleteIntersection B S hS k)
      (fun _ _ k => Space.IsSmooth B S hS k) hlci
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) hiso hbc
      (fun hU hV hW p q hpq hq =>
        Space.isLocalCompleteIntersection_of_comp_of_isSmooth B S hS hU hV hW p q hq hpq)
      f g hfgsome hg)

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
