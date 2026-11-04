module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# Fppf descent of the étale-smooth diagram test of Stacks 0CIF

Let `P` be a property of morphisms of algebraic spaces over `S` which is local on the target for
the fppf topology. The universal étale-smooth diagram test of condition (1) of **Stacks 0CIF**
(`AlgebraicGeometry.Stack.HasPropertyOnEveryEtaleSmoothDiagram`) descends along a surjective,
flat, locally finitely presented 1-morphism `g : 𝒵 ⟶ 𝒴`: if the base change
`𝒳 ×_𝒴 𝒵 ⟶ 𝒵` of `f : 𝒳 ⟶ 𝒴` passes the test, so does `f`. This is the étale-smooth reading
of **Stacks 0DN6**, and it is the step "it suffices to prove `U ×_𝒴 W ⟶ V ×_𝒴 W` is étale by
Descent on Spaces, Lemma 042B" of the proof of **Stacks 0CIQ**.

## Main results

* `AlgebraicGeometry.Stack.prop_of_etaleChart`: the top horizontal morphism of a diagram whose
  source is an étale chart of a 2-fibre product has `P`, given the universal étale-smooth test.
* `AlgebraicGeometry.Stack.prop_representingMap_fst_of_hasPropertyOnEveryEtaleSmoothDiagram`: the
  base change of the top horizontal morphism of an étale-smooth diagram over `f` along a smooth
  leg over `𝒵` has `P`.
* `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_of_baseChange`: fppf descent of
  the universal étale-smooth diagram test.

## Implementation notes

The argument is the one of `AlgebraicGeometry.Stack.hasProperty_of_baseChange` (Stacks 0DN6),
with the smooth comparisons of Stacks 06FM replaced by the étale comparisons of Stacks 0CIF. Given
an étale-smooth diagram `(U, V, a, b, h)` over `f`, the covering of `V` is a smooth surjective
presentation `V' ⟶ 𝒵 ×_𝒴 V` by an algebraic space; the induced `V' ⟶ V` is surjective, flat and
locally of finite presentation, the base change of `h` along it is the morphism of representing
spaces of the first projection of `V' ×_V U`, and fppf locality on the target recovers `P h`. The
chain of 2-fibre products identifying `V' ×_V U` with a 2-fibre product of the new diagram's
cospan is the one of Stacks 0DN6, and each of its steps is an equivalence or a base change of the
given étale comparison, so the new comparison is étale by **Stacks 045C** and **045B** at
étaleness (`AlgebraicGeometry.Stack.isRelativelyEtale_baseChange`,
`AlgebraicGeometry.Stack.isRelativelyEtale_comp`). The right-hand vertical 1-morphism of the new
diagram is smooth as the composite of the presentation with a base change of the smooth `b`.

No étale-smooth locality of `P` is used: only fppf locality on the target.

## References

* [Stacks Project, Tag 042B](https://stacks.math.columbia.edu/tag/042B)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIQ](https://stacks.math.columbia.edu/tag/0CIQ)
* [Stacks Project, Tag 0DN6](https://stacks.math.columbia.edu/tag/0DN6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
open CategoryTheory.CatFiberedInGroupoids

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The top horizontal morphism of a diagram whose source is an étale chart of a 2-fibre
product.** Let `q` pass the universal étale-smooth diagram test for `P`, let `b` be smooth out of
the algebraic stack of an algebraic space `V`, let `Q` be a 2-fibre product of `(b, q)` and let
`cc` be an étale 1-morphism from the category fibred in groupoids of an algebraic space `U` into
its apex. Then every morphism `h : U ⟶ V` inducing `cc` followed by the projection to `V` has
`P`: the diagram that `cc` defines has étale comparisons by
`AlgebraicGeometry.Stack.isRelativelyEtale_preHom_diagramCone_of_chart`. -/
theorem prop_of_etaleChart
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳₀ 𝒴₀ : AlgebraicStacks.{u, w} B S hS} (q : 𝒳₀ ⟶ 𝒴₀)
    (hevery : HasPropertyOnEveryEtaleSmoothDiagram B S hS P q)
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V)
    (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴₀)
    (hb : IsRelativelySmooth B S hS b.hom)
    (Q : Bicategory.TwoCommSq b.hom q.hom) (hQ : Bicategory.IsTwoFibreProduct Q)
    (cc : fibredCategory B S hS U ⟶ Q.pt) (hcc : IsRelativelyEtale B S hS cc)
    (h : U ⟶ V) (e : (associatedMap B S hS h).1 ≅ cc ≫ Q.fst) :
    P (ObjectProperty.homMk h : (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩) :=
  hevery U V hU hV
    (Bicategory.InducedBicategory.mkHom (cc ≫ Q.snd) : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳₀)
    b h (Bicategory.whiskerRightIso e b.hom ≪≫ Bicategory.whiskerLeftIso cc Q.iso) hb
    (fun Q' hQ' k => isRelativelyEtale_preHom_diagramCone_of_chart B S hS q.hom b.hom Q hQ cc hcc
      h e Q' hQ' k)

/-- `AlgebraicGeometry.Stack.prop_of_etaleChart` for the morphism of representing presheaves
that the composite of the chart with the projection induces. -/
theorem prop_representingMap_of_etaleChart
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳₀ 𝒴₀ : AlgebraicStacks.{u, w} B S hS} (q : 𝒳₀ ⟶ 𝒴₀)
    (hevery : HasPropertyOnEveryEtaleSmoothDiagram B S hS P q)
    (Vv Ww : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hVv : IsAlgebraicSpace B S hS Vv) (hWw : IsAlgebraicSpace B S hS Ww)
    (bb : algebraicSpaceStack.{u, w} B S hS Vv hVv ⟶ 𝒴₀)
    (hbb : IsRelativelySmooth B S hS bb.hom)
    (Q : Bicategory.TwoCommSq bb.hom q.hom) (hQ : Bicategory.IsTwoFibreProduct Q)
    (cc : fibredCategory B S hS Ww ⟶ Q.pt)
    (hcc : IsRelativelyEtale B S hS cc) :
    P (ObjectProperty.homMk (representingMap B S hS (fibredCategory B S hS Ww)
        (fibredCategory B S hS Vv) Ww Vv
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) (cc ≫ Q.fst)) :
      (⟨Ww, hWw⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Vv, hVv⟩) := by
  set hTop := representingMap B S hS (fibredCategory B S hS Ww) (fibredCategory B S hS Vv) Ww Vv
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (cc ≫ Q.fst) with hTopDef
  have hleft : representingMap B S hS (fibredCategory B S hS Ww) (fibredCategory B S hS Vv)
      Ww Vv (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (associatedMap B S hS hTop).1 = hTop :=
    representingMap_associatedMap B S hS Ww Vv hTop
  obtain ⟨e, hee, -⟩ := existsUnique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS Ww) (fibredCategory B S hS Vv) Ww Vv
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) hleft
  exact prop_of_etaleChart B S hS P q hevery hWw hVv bb hbb Q hQ cc hcc hTop
    (Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e hee))

/-- **The base change of an étale-smooth diagram along a smooth leg over `𝒵`.** Let the
canonical base change `𝒳 ×_𝒴 𝒵 ⟶ 𝒵` of `f` pass the universal étale-smooth diagram test for
`P`, let `(U, V, a, b, h, η)` be a diagram over `f` with étale comparisons, and let
`pm : V' ⟶ V` be a 1-morphism out of an algebraic space with a smooth leg `bV' : V' ⟶ 𝒵` and a
2-cell `pm ≫ b ≅ bV' ≫ g`. Then the morphism of representing spaces of the first projection of
`V' ×_V U`, which is the base change of `h` along `pm`, has `P`.

This is the étale-smooth reading of
`AlgebraicGeometry.Stack.prop_representingMap_fst_of_hasPropertyOnEverySmoothDiagram`. -/
theorem prop_representingMap_fst_of_hasPropertyOnEveryEtaleSmoothDiagram
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hevery : HasPropertyOnEveryEtaleSmoothDiagram B S hS P
      (twoFibreProductSquareAlgebraicStacks B S hS f g).snd)
    (U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (a : fibredCategory B S hS U ⟶ 𝒳.val) (b : fibredCategory B S hS V ⟶ 𝒴.val)
    (h : U ⟶ V)
    (η : (associatedMap B S hS h).1 ≫ b ≅ a ≫ f.hom)
    (hcomp : ∀ (Q : Bicategory.TwoCommSq b f.hom) (_hQ : Bicategory.IsTwoFibreProduct Q)
      (k : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f.hom a b h η) Q),
        IsRelativelyEtale B S hS k.hom)
    (V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV' : IsAlgebraicSpace B S hS V')
    (bV' : fibredCategory B S hS V' ⟶ 𝒵.val)
    (hbV' : IsRelativelySmooth B S hS bV')
    (pm : fibredCategory B S hS V' ⟶ fibredCategory B S hS V)
    (θ₂ : pm ≫ b ≅ bV' ≫ g.hom)
    (W₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW₀ : IsAlgebraicSpace B S hS W₀)
    (eW₀ : StacksRepresentableCFG.EquivalenceOver (twoFibreProductSquare.{u, u, u + 1, u + 1} pm
        (associatedMap B S hS h).1).pt.val.p
      (presheafOfCategories (W₀ ⋙ typeToCat)).p) :
    P (ObjectProperty.homMk (representingMap B S hS
        (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS h).1).pt
        (fibredCategory B S hS V') W₀ V' eW₀
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS h).1).fst) :
      (⟨W₀, hW₀⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V', hV'⟩) := by
  -- (1) the comparison the diagram's own hypothesis makes étale
  have hTBsw : Bicategory.IsTwoFibreProduct (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom
      b).swap :=
    Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        f.hom b)
  have k₀ : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f.hom a b h η)
      (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b).swap :=
    Quotient.out (hTBsw.from (diagramCone B S hS f.hom a b h η))
  have hk₀ : IsRelativelyEtale B S hS k₀.hom :=
    hcomp (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b).swap hTBsw k₀
  -- (2) the base change of that comparison along `pm`
  have hpbk : IsRelativelyEtale B S hS (twoFibreProductSquare.{u, u, u + 1, u + 1}
      (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom
      b).snd).snd k₀.hom).fst :=
    isRelativelyEtale_baseChange B S hS (fibredCategory B S hS U)
        (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b).pt
      (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom
          b).snd).pt k₀.hom (twoFibreProductSquare.{u, u, u + 1, u + 1} pm
          (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b).snd).snd
          (twoFibreProductSquare.{u, u, u + 1, u + 1} (twoFibreProductSquare.{u, u, u + 1, u + 1} pm
          (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b).snd).snd k₀.hom)
          (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom b).snd).snd k₀.hom) hk₀
  -- (3) the two 2-fibre products of the cospan `(pm, associatedMap h)`
  have hLL : Bicategory.IsTwoFibreProduct (cancelSndSquare.{u, u, u + 1, u + 1} pm
      (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b).snd k₀.hom (associatedMap B S hS h).1
      k₀.isoFst.symm) :=
    isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} pm
        (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b).snd k₀.hom (associatedMap B S hS h).1
        k₀.isoFst.symm
  have c1 : Bicategory.TwoCommSq.PreHom (twoFibreProductSquare.{u, u, u + 1, u + 1} pm
      (associatedMap B S hS h).1) (cancelSndSquare.{u, u, u + 1, u + 1} pm
      (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b).snd k₀.hom (associatedMap B S hS h).1
      k₀.isoFst.symm) := Quotient.out (hLL.from (twoFibreProductSquare.{u, u, u + 1, u + 1} pm
      (associatedMap B S hS h).1))
  have hc1 : (CatFiberedInGroupoids.homFunctor c1.hom).IsEquivalence :=
    Bicategory.isEquivalence_of_isTwoFibreProduct
        (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS h).1)
        hLL c1
  -- (4) the swap comparison
  have c2 : Bicategory.TwoCommSq.PreHom (twoFibreProductSquare.{u, u, u + 1, u + 1} pm
      (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b).snd).swap
      (twoFibreProductSquare.{u, u, u + 1, u + 1} (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom
      b).snd pm) :=
    Quotient.out ((isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b).snd pm).from
        (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (twoFibreProductSquare.{u, u, u + 1, u + 1}
            f.hom
        b).snd).swap)
  have hc2 : (CatFiberedInGroupoids.homFunctor c2.hom).IsEquivalence :=
    Bicategory.isEquivalence_of_isTwoFibreProduct
      (Bicategory.isTwoFibreProduct_swap
          (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} pm
          (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b).snd))
          (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b).snd pm) c2
  -- (5) the two 2-fibre products of the outer cospan `(f, bV' ≫ g)`
  have hC2 : Bicategory.IsTwoFibreProduct (cancelSndSquare.{u, u, u + 1, u + 1} f.hom b pm (bV' ≫
      g.hom) θ₂)
      := isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} f.hom b pm (bV' ≫ g.hom) θ₂
  have hC1 : Bicategory.IsTwoFibreProduct (cancelSndSquare.{u, u, u + 1, u + 1} f.hom g.hom bV'
      (bV' ≫ g.hom)
      (Iso.refl _)) := isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} f.hom g.hom bV' (bV'
          ≫ g.hom)
      (Iso.refl _)
  have e12 : Bicategory.TwoCommSq.PreHom (cancelSndSquare.{u, u, u + 1, u + 1} f.hom b pm (bV' ≫
      g.hom) θ₂)
      (cancelSndSquare.{u, u, u + 1, u + 1} f.hom g.hom bV' (bV' ≫ g.hom) (Iso.refl _)) :=
          Quotient.out
      (hC1.from (cancelSndSquare.{u, u, u + 1, u + 1} f.hom b pm (bV' ≫ g.hom) θ₂))
  have he12 : (CatFiberedInGroupoids.homFunctor e12.hom).IsEquivalence :=
    Bicategory.isEquivalence_of_isTwoFibreProduct hC2 hC1 e12
  -- (6) the chosen 2-fibre product of the new diagram's cospan, and its smooth projection
  have hQ1 : Bicategory.IsTwoFibreProduct (twoFibreProductSquare.{u, u, u + 1, u + 1}
      (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom).snd bV').swap :=
    Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom).snd bV')
  -- (7) the equivalence onto the apex, and the composite comparison
  have hiW : IsRelativelyEtale B S hS (equivalenceOverInvMap B S hS (𝒳 :=
      (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS h).1).pt) W₀ eW₀) :=
    isRelativelyEtale_equivalenceOverInvMap B S hS (𝒳 :=
        (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS h).1).pt) W₀ hW₀ eW₀
  have hcU : IsRelativelyEtale B S hS (((((equivalenceOverInvMap B S hS (𝒳 :=
      (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS h).1).pt) W₀ eW₀) ≫
      c1.hom) ≫ (twoFibreProductSquare.{u, u, u + 1, u + 1}
      (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom
      b).snd).snd k₀.hom).fst) ≫ c2.hom) ≫ e12.hom) :=
    isRelativelyEtale_comp_of_isEquivalence B S hS _ e12.hom he12
      (isRelativelyEtale_comp_of_isEquivalence B S hS _ c2.hom hc2
        (isRelativelyEtale_comp B S hS _ (twoFibreProductSquare.{u, u, u + 1, u + 1}
            (twoFibreProductSquare.{u, u, u + 1, u + 1} pm
            (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b).snd).snd k₀.hom).fst
          (isRelativelyEtale_comp_of_isEquivalence B S hS _ c1.hom hc1 hiW) hpbk))
  -- (8) the comparison 2-cell onto the `V'`-leg
  have κ : ((((((equivalenceOverInvMap B S hS (𝒳 := (twoFibreProductSquare.{u, u, u + 1, u + 1} pm
      (associatedMap B S hS h).1).pt) W₀ eW₀) ≫ c1.hom) ≫
      (twoFibreProductSquare.{u, u, u + 1, u + 1} (twoFibreProductSquare.{u, u, u + 1, u + 1} pm
      (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b).snd).snd k₀.hom).fst) ≫ c2.hom) ≫
          e12.hom) ≫
      (twoFibreProductSquare.{u, u, u + 1, u + 1} (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom
      g.hom).snd bV').snd) ≅ (equivalenceOverInvMap B S hS (𝒳 :=
      (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS h).1).pt) W₀ eW₀) ≫
      (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS h).1).fst :=
    Bicategory.associator _ e12.hom (twoFibreProductSquare.{u, u, u + 1, u + 1}
        (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom).snd bV').snd ≪≫
      Bicategory.whiskerLeftIso _ e12.isoSnd.symm ≪≫
      Bicategory.associator _ c2.hom (twoFibreProductSquare.{u, u, u + 1, u + 1}
          (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b).snd pm).snd ≪≫
      Bicategory.whiskerLeftIso _ c2.isoSnd.symm ≪≫
      Bicategory.associator _ (twoFibreProductSquare.{u, u, u + 1, u + 1}
          (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom b).snd).snd k₀.hom).fst (twoFibreProductSquare.{u, u, u + 1, u + 1} pm
          (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b).snd).fst ≪≫
      Bicategory.associator (equivalenceOverInvMap B S hS (𝒳 :=
          (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS h).1).pt) W₀ eW₀)
          c1.hom (cancelSndSquare.{u, u, u + 1, u + 1} pm
          (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b).snd k₀.hom (associatedMap B S hS h).1
          k₀.isoFst.symm).fst ≪≫
      Bicategory.whiskerLeftIso _ c1.isoFst.symm
  -- (9) the two top horizontal morphisms agree
  have hfin : representingMap B S hS (fibredCategory B S hS W₀) (fibredCategory B S hS V')
      W₀ V' (StacksRepresentableCFG.EquivalenceOver.refl _)
          (StacksRepresentableCFG.EquivalenceOver.refl _) ((((((equivalenceOverInvMap B S hS (𝒳 :=
          (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS h).1).pt) W₀ eW₀) ≫
          c1.hom) ≫ (twoFibreProductSquare.{u, u, u + 1, u + 1}
          (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom b).snd).snd k₀.hom).fst) ≫ c2.hom) ≫ e12.hom) ≫
          (twoFibreProductSquare.{u, u, u + 1, u + 1} (twoFibreProductSquare.{u, u, u + 1, u + 1}
              f.hom
          g.hom).snd bV').snd)
      = representingMap B S hS (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS
          h).1).pt (fibredCategory B S hS V') W₀ V' eW₀ (StacksRepresentableCFG.EquivalenceOver.refl
          _) (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS h).1).fst := by
    rw [representingMap_congr_twoIso B S hS W₀ V' (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) κ,
      representingMap_comp (𝒜 := fibredCategory B S hS W₀) (ℬ :=
          (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS h).1).pt)
        (𝒞 := fibredCategory B S hS V') B S hS W₀ W₀ V' (StacksRepresentableCFG.EquivalenceOver.refl
            _) eW₀ (StacksRepresentableCFG.EquivalenceOver.refl _),
      representingMap_equivalenceOverInvMap (𝒳 := (twoFibreProductSquare.{u, u, u + 1, u + 1} pm
          (associatedMap B S hS h).1).pt) B S hS W₀ eW₀, Category.id_comp]
  rw [← hfin]
  exact prop_representingMap_of_etaleChart B S hS P
      (twoFibreProductSquareAlgebraicStacks B S hS f g).snd hevery V' W₀ hV' hW₀
      (Bicategory.InducedBicategory.mkHom bV') hbV'
      (twoFibreProductSquare.{u, u, u + 1, u + 1} (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom
      g.hom).snd bV').swap hQ1 (((((equivalenceOverInvMap B S hS (𝒳 :=
      (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS h).1).pt) W₀ eW₀) ≫
      c1.hom) ≫ (twoFibreProductSquare.{u, u, u + 1, u + 1}
      (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom
      b).snd).snd k₀.hom).fst) ≫ c2.hom) ≫ e12.hom) hcU

/-- **Fppf descent of the universal étale-smooth diagram test of Stacks 0CIF.** Let `P` be a
property of morphisms of algebraic spaces over `S` which is local on the target for the fppf
topology, and let `g : 𝒵 ⟶ 𝒴` be surjective, flat and locally of finite presentation. If the base
change `𝒳 ×_𝒴 𝒵 ⟶ 𝒵` of `f : 𝒳 ⟶ 𝒴` along `g` passes the universal étale-smooth diagram test for
`P`, then so does `f`. -/
theorem hasPropertyOnEveryEtaleSmoothDiagram_of_baseChange
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [hlocal : P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hgsurj : IsSurjective B S hS g)
    (hgflat : AlgebraicStacks.IsFlat B S hS g)
    (hglfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    (hbase : HasPropertyOnEveryEtaleSmoothDiagram B S hS P
      (twoFibreProductSquareAlgebraicStacks B S hS f g).snd) :
    HasPropertyOnEveryEtaleSmoothDiagram B S hS P f := by
  intro U V hU hV a b h η hb hcomp
  -- a smooth surjective presentation of the base change of `g` along `b`
  obtain ⟨V', hV', b₁, hb₁sm, hb₁su⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS g b).pt.property
  -- the covering `V' ⟶ V` is surjective, flat and locally of finite presentation
  have hmsurj : Space.IsSurjective B S hS (representingMap B S hS (fibredCategory B S hS V')
      (fibredCategory B S hS V) V' V (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫
      (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd)) := by
    refine isSurjective_representingMap_of_isSurjectiveOnObjects B S hS (b₁ ≫
        (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd) V' V
      (StacksRepresentableCFG.EquivalenceOver.refl _) (StacksRepresentableCFG.EquivalenceOver.refl
          _) ?_
    exact isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS V').val.p
        (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).pt.val.p
      (fibredCategory B S hS V).val.p (homFunctor b₁) (homFunctor
          (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd)
      (homFunctor_comp_p (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd) hb₁su
      (isSurjectiveOnObjects_twoFibreProductSnd.{u, u, u + 1} B S hS 𝒵.val 𝒴.val
        (fibredCategory B S hS V) g.hom b.hom
        (isSurjectiveOnObjects_of_pointsMap_surjective B S hS g hgsurj))
  have hmflat : Space.IsFlat B S hS (representingMap B S hS (fibredCategory B S hS V')
      (fibredCategory B S hS V) V' V (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫
      (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd)) :=
    isFlat_representingMap_comp_of_isRelativelySmooth.{u, w} B S hS g hgflat hV
        b
        (twoFibreProductSquareAlgebraicStacks B S hS g b)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g
          b) hV'
      (Bicategory.InducedBicategory.mkHom b₁) hb₁sm
  have hmlfp : Space.IsLocallyOfFinitePresentation B S hS (representingMap B S hS (fibredCategory B
      S hS V') (fibredCategory B S hS V) V' V (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫
      (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd)) :=
    isLocallyOfFinitePresentation_representingMap_comp_of_isRelativelySmooth.{u, w} B S hS g
      hglfp hV b
          (twoFibreProductSquareAlgebraicStacks B S hS g b)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g
          b) hV'
      (Bicategory.InducedBicategory.mkHom b₁) hb₁sm
  -- the fppf descent square
  have hqhrep : IsRepresentableByAlgebraicSpaces B S hS (associatedMap B S hS h).1.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS (associatedMap B S hS
        h).1
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV)
  obtain ⟨W₀, hW₀, ⟨eW₀⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
    (fibredCategory B S hS V) (fibredCategory B S hS V') (fibredCategory B S hS U)
    ((associatedMap B S hS (representingMap B S hS (fibredCategory B S hS V') (fibredCategory B S hS
        V) V' V (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫
        (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd))).1).hom (associatedMap B S hS
        h).1.hom hqhrep
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS V' hV')
  have hFib : (twoFibreProductStructureFunctor B S hS (fibredCategory B S hS V')
      (fibredCategory B S hS U) (fibredCategory B S hS V) ((associatedMap B S hS (representingMap B
          S hS (fibredCategory B S hS V') (fibredCategory B S hS V) V' V
          (StacksRepresentableCFG.EquivalenceOver.refl _)
          (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫
          (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd))).1) (associatedMap B S hS
          h).1).IsFibered :=
    (twoFibreProductSquare.{u, u, u + 1, u + 1} ((associatedMap B S hS (representingMap B S hS
        (fibredCategory B S hS V') (fibredCategory B S hS V) V' V
        (StacksRepresentableCFG.EquivalenceOver.refl _) (StacksRepresentableCFG.EquivalenceOver.refl
        _) (b₁ ≫ (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd))).1) (associatedMap
            B S
        hS h).1).pt.isFiberedInGroupoids.isFibered
  have hsq := isPullback_representingMap_twoFibreProduct B S hS
    (fibredCategory B S hS V') (fibredCategory B S hS U) (fibredCategory B S hS V)
    V' U V (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) (StacksRepresentableCFG.EquivalenceOver.refl
        _) ((associatedMap B S hS (representingMap B S hS (fibredCategory B S hS V') (fibredCategory
        B S hS V) V' V (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫
        (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd))).1) (associatedMap B S hS
            h).1 W₀
        eW₀
  rw [representingMap_associatedMap B S hS U V h,
    representingMap_associatedMap B S hS V' V (representingMap B S hS (fibredCategory B S hS V')
        (fibredCategory B S hS V) V' V (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫
        (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd))] at hsq
  have hsqA : IsPullback
      (ObjectProperty.homMk (representingMap B S hS (twoFibreProductSquare.{u, u, u + 1, u + 1}
          ((associatedMap B S hS (representingMap B S hS (fibredCategory B S hS V') (fibredCategory
          B S hS V) V' V (StacksRepresentableCFG.EquivalenceOver.refl _)
          (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫
          (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd))).1) (associatedMap B S hS
          h).1).pt (fibredCategory B S hS U) W₀ U eW₀
        (StacksRepresentableCFG.EquivalenceOver.refl _) (twoFibreProductSquare.{u, u, u + 1, u + 1}
            ((associatedMap B S hS (representingMap B S hS (fibredCategory B S hS V')
            (fibredCategory B S hS V) V' V (StacksRepresentableCFG.EquivalenceOver.refl _)
            (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫
            (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd))).1) (associatedMap B S hS
            h).1).snd) : (⟨W₀, hW₀⟩ : AlgebraicSpaces B S hS) ⟶ ⟨U, hU⟩)
      (ObjectProperty.homMk (representingMap B S hS (twoFibreProductSquare.{u, u, u + 1, u + 1}
          ((associatedMap B S hS (representingMap B S hS (fibredCategory B S hS V') (fibredCategory
          B S hS V) V' V (StacksRepresentableCFG.EquivalenceOver.refl _)
          (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫
          (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd))).1) (associatedMap B S hS
          h).1).pt (fibredCategory B S hS V') W₀ V' eW₀
        (StacksRepresentableCFG.EquivalenceOver.refl _) (twoFibreProductSquare.{u, u, u + 1, u + 1}
            ((associatedMap B S hS (representingMap B S hS (fibredCategory B S hS V')
            (fibredCategory B S hS V) V' V (StacksRepresentableCFG.EquivalenceOver.refl _)
            (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫
            (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd))).1) (associatedMap B S hS
            h).1).fst) : (⟨W₀, hW₀⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V', hV'⟩)
      (ObjectProperty.homMk h : (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩)
      (ObjectProperty.homMk (representingMap B S hS (fibredCategory B S hS V') (fibredCategory B S
          hS V) V' V (StacksRepresentableCFG.EquivalenceOver.refl _)
          (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫
          (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd)) : (⟨V', hV'⟩ :
              AlgebraicSpaces
          B S hS) ⟶ ⟨V, hV⟩) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) hsq
  -- the 2-cell relating the covering to the smooth leg over `𝒵`
  have hmleft : representingMap B S hS (fibredCategory B S hS V') (fibredCategory B S hS V)
      V' V (StacksRepresentableCFG.EquivalenceOver.refl _)
          (StacksRepresentableCFG.EquivalenceOver.refl _) ((associatedMap B S hS (representingMap B
          S hS (fibredCategory B S hS V') (fibredCategory B S hS V) V' V
          (StacksRepresentableCFG.EquivalenceOver.refl _)
          (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫
          (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd))).1)
      = representingMap B S hS (fibredCategory B S hS V') (fibredCategory B S hS V) V' V
        (StacksRepresentableCFG.EquivalenceOver.refl _) (StacksRepresentableCFG.EquivalenceOver.refl
            _) (b₁ ≫ (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd) :=
    representingMap_associatedMap B S hS V' V (representingMap B S hS (fibredCategory B S hS V')
        (fibredCategory B S hS V) V' V (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫
        (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd))
  obtain ⟨em, hem, -⟩ := existsUnique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS V') (fibredCategory B S hS V) V' V
        (StacksRepresentableCFG.EquivalenceOver.refl _) (StacksRepresentableCFG.EquivalenceOver.refl
        _) hmleft
  exact Space.prop_of_isPullback_of_fppf.{u, v} B S hS P hsqA
    hmsurj hmflat hmlfp
    (prop_representingMap_fst_of_hasPropertyOnEveryEtaleSmoothDiagram B S hS P f g hbase
      U V a.hom b.hom h η hcomp V' hV' (b₁ ≫ (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom
          b.hom).fst)
      (isRelativelySmooth_comp B S hS b₁ (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom
          b.hom).fst
          hb₁sm
        (isRelativelySmooth_baseChange.{u, u, u + 1} B S hS (fibredCategory B S hS V) 𝒴.val
          𝒵.val b.hom g.hom (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom)
              (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom) hb))
      ((associatedMap B S hS (representingMap B S hS (fibredCategory B S hS V') (fibredCategory B S
          hS V) V' V (StacksRepresentableCFG.EquivalenceOver.refl _)
          (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫
          (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd))).1)
      (Bicategory.whiskerRightIso
          (Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso em hem)) b.hom ≪≫
        Bicategory.associator b₁ (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).snd b.hom
            ≪≫
        Bicategory.whiskerLeftIso b₁ (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom
            b.hom).iso.symm
            ≪≫
        (Bicategory.associator b₁ (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b.hom).fst
            g.hom).symm)
      W₀ hW₀ eW₀)

end AlgebraicGeometry.Stack

end
