module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfSingletonCovering
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients

/-!
# Fppf descent of a property of 1-morphisms of algebraic stacks (Stacks 0DN6)

Let `P` be a property of morphisms of algebraic spaces over `S` which is smooth local on the
source-and-target (**Stacks 06F8**) and whose restriction to algebraic spaces is local on the
target for the fppf topology. **Stacks 0DN6** asserts that the induced property of 1-morphisms
of algebraic stacks — the smooth-diagram condition of **Stacks 06FM**, which is Definition
**06FN** — descends along a surjective, flat, locally finitely presented 1-morphism: if the base
change `𝒵 ×_𝒴 𝒳 ⟶ 𝒵` of `f : 𝒳 ⟶ 𝒴` along such a `g : 𝒵 ⟶ 𝒴` has `P`, then so does `f`.

The source's proof first replaces `𝒵` by an algebraic space covering it; the argument here does
not, because the *universal* form of Stacks 06FM accepts a smooth diagram over the base change
whose target leg factors through such a covering, and that is all the replacement is used for.
Given an arbitrary smooth diagram `(U, V, a, b, h)` over `f`, the covering of `V` is a smooth
surjective presentation `V' ⟶ 𝒵 ×_𝒴 V` by an algebraic space; the induced `V' ⟶ V` is
surjective, flat and locally of finite presentation, the base change of `h` along it is the
morphism of representing spaces of the first projection of `V' ×_V U`, and fppf locality on the
target recovers `P h` from `P` of that base change.

## Main results

* `AlgebraicGeometry.Stack.prop_representingMap_fst_of_smooth_comparison`: if the comparison of
  a cone of algebraic spaces with a 2-fibre product is smooth, then the morphism of representing
  spaces induced by the cone's first leg has `P`, as soon as `P` satisfies the *universal*
  smooth-diagram condition of **Stacks 06FM** for the cospan's second leg. No hypothesis on `P`
  is used.
* `AlgebraicGeometry.Stack.prop_representingMap_fst_of_hasPropertyOnEverySmoothDiagram`: the
  base change of a smooth diagram's top horizontal morphism along a smooth leg over `𝒵` has `P`.
  This is the 2-fibre product calculus of the proof of **Stacks 0DN6**.
* `AlgebraicGeometry.Stack.hasProperty_of_baseChange`: a 1-morphism of algebraic stacks has `P`
  if its base change along a surjective, flat, locally finitely presented 1-morphism does
  (**Stacks 0DN6**).

## Implementation notes

`prop_representingMap_fst_of_smooth_comparison` is stated for an *abstract* 2-fibre product
square rather than the canonical one, and that is load-bearing rather than cosmetic: the
compatibility square of **Stacks 003O** for the comparison is closed by `simp` only while the
square's filler is opaque, and with the canonical square's `swap` in its place the normal form
of the whiskered associators no longer matches.

The chain identifying `V' ×_V U` with the 2-fibre product of the new diagram's cospan is five
comparisons long and every step is either an equivalence or a base change of a smooth
1-morphism, so no step needs a hypothesis on `P`:

* `V' ×_V U` and `(V' ×_V (𝒳 ×_𝒴 V)) ×_{𝒳 ×_𝒴 V} U` are both 2-fibre products of the cospan
  `(V' ⟶ V, U ⟶ V)`, the second by **Stacks 02XD** in the form
  `CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare` with the comparison
  `U ⟶ 𝒳 ×_𝒴 V` supplied by the given diagram as its reindexing 2-isomorphism;
* the projection of the second onto `V' ×_V (𝒳 ×_𝒴 V)` is the base change of that comparison,
  which the universal condition's own smoothness hypothesis makes smooth;
* `V' ×_V (𝒳 ×_𝒴 V)` and `(𝒳 ×_𝒴 V) ×_V V'` differ by
  `CategoryTheory.Bicategory.TwoCommSq.swap`;
* `(𝒳 ×_𝒴 V) ×_V V'` and `(𝒳 ×_𝒴 𝒵) ×_𝒵 V'` are both 2-fibre products of the outer cospan
  `(f, V' ⟶ 𝒵 ⟶ 𝒴)`, again by `isTwoFibreProduct_cancelSndSquare`, the first reindexed by the
  filler of the covering square and the second by an identity.

The two legs of the hypothesis are read on `(𝒳 ×_𝒴 𝒵) ⟶ 𝒵` rather than on `(𝒵 ×_𝒴 𝒳) ⟶ 𝒵`,
transported by `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct`,
because that is the orientation in which the iterated product above is a 2-fibre product of the
new diagram's cospan.

The precoverage index universe of the fppf locality hypothesis is left free, which is strictly
more general than pinning it to the site's universe.

## References

* [Stacks Project, Tag 06F8](https://stacks.math.columbia.edu/tag/06F8)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FN](https://stacks.math.columbia.edu/tag/06FN)
* [Stacks Project, Tag 0DN6](https://stacks.math.columbia.edu/tag/0DN6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
open CategoryTheory.CatFiberedInGroupoids

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two 2-fibre products of the same cospan are related by a comparison that is an equivalence. -/
private theorem exists_preHom_isEquivalence
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵} {P Q : Bicategory.TwoCommSq f g}
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q) :
    ∃ c : Bicategory.TwoCommSq.PreHom P Q, (CatFiberedInGroupoids.homFunctor c.hom).IsEquivalence :=
  ⟨Quotient.out (hQ.from P), Bicategory.isEquivalence_of_isTwoFibreProduct hP hQ _⟩

/-- Let `q : 𝒳₀ ⟶ 𝒴₀` satisfy the universal smooth-diagram condition for `P`, let `Q` be a
2-fibre product of a smooth `bb : Vv ⟶ 𝒴₀` from an algebraic space with `q`, and let
`cc : Ww ⟶ Q.pt` be smooth from an algebraic space. Then the morphism `Ww ⟶ Vv` of algebraic
spaces representing `cc ≫ Q.fst` has `P`. -/
theorem prop_representingMap_fst_of_smooth_comparison
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {𝒳₀ 𝒴₀ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (q : 𝒳₀ ⟶ 𝒴₀)
    (hevery : HasPropertyOnEverySmoothDiagram B S hS P q)
    (Vv Ww : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hVv : IsAlgebraicSpace B S hS Vv) (hWw : IsAlgebraicSpace B S hS Ww)
    (bb : fibredCategory B S hS Vv ⟶ 𝒴₀)
    (hbb : IsRelativelySmooth.{u, u, u + 1} B S hS bb)
    (Q : Bicategory.TwoCommSq bb q) (hQ : Bicategory.IsTwoFibreProduct Q)
    (cc : fibredCategory B S hS Ww ⟶ Q.pt)
    (hcc : IsRelativelySmooth.{u, u, u + 1} B S hS cc) :
    P (representingMap B S hS (fibredCategory B S hS Ww) (fibredCategory B S hS Vv) Ww Vv
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) (cc ≫ Q.fst)) := by
  set hTop := representingMap B S hS (fibredCategory B S hS Ww) (fibredCategory B S hS Vv) Ww Vv
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (cc ≫ Q.fst)
  have hQsnd : IsRelativelySmooth.{u, u, u + 1} B S hS Q.snd :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS (fibredCategory B S hS Vv) 𝒴₀ 𝒳₀ bb q
      Q.swap (Bicategory.isTwoFibreProduct_swap hQ) hbb
  obtain ⟨e, hee, -⟩ := existsUnique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS Ww) (fibredCategory B S hS Vv) Ww Vv
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (representingMap_associatedMap B S hS Ww Vv hTop)
  let eIso : (associatedMap B S hS hTop).1 ≅ cc ≫ Q.fst :=
    Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e hee)
  let η : (associatedMap B S hS hTop).1 ≫ bb ≅ (cc ≫ Q.snd) ≫ q :=
    Bicategory.whiskerRightIso eIso bb ≪≫ Bicategory.associator cc Q.fst bb ≪≫
      Bicategory.whiskerLeftIso cc Q.iso ≪≫ (Bicategory.associator cc Q.snd q).symm
  let k₁ : Bicategory.TwoCommSq.PreHom
      (diagramCone B S hS q (cc ≫ Q.snd) bb hTop η) Q :=
    { hom := cc
      isoFst := eIso
      isoSnd := Iso.refl _
      compat := by
        have hid : Bicategory.whiskerRight (𝟙 (cc ≫ Q.snd)) q = 𝟙 ((cc ≫ Q.snd) ≫ q) :=
          Bicategory.id_whiskerRight _ _
        simp [η, hid] }
  exact hevery Ww Vv hWw hVv (cc ≫ Q.snd) bb hTop η
    (isRelativelySmooth_comp B S hS cc Q.snd hcc hQsnd) hbb
    (fun Q' hQ' k => isRelativelySmooth_preHom_of_isTwoFibreProduct B S hS hQ hQ' k₁ k hcc)

/-- Let the second projection `𝒳 ×_𝒴 𝒵 ⟶ 𝒵` of the cospan `(f, g)` satisfy the universal
smooth-diagram condition for `P`, and let `(U, V, a, b, h, η)` be a smooth diagram over `f`. If
`bV' : V' ⟶ 𝒵` is smooth from an algebraic space, `pm : V' ⟶ V` and `θ₂ : pm ≫ b ≅ bV' ≫ g`, and
`W₀` is an algebraic space equivalent to the 2-fibre product of `pm` and `h`, then the morphism
`W₀ ⟶ V'` representing the first projection of that 2-fibre product has `P`. -/
theorem prop_representingMap_fst_of_hasPropertyOnEverySmoothDiagram
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hevery : HasPropertyOnEverySmoothDiagram B S hS P (twoFibreProductSquare.{u, u, u + 1, u + 1} f
        g).snd)
    (U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (a : fibredCategory B S hS U ⟶ 𝒳) (b : fibredCategory B S hS V ⟶ 𝒴)
    (h : U ⟶ V)
    (η : (associatedMap B S hS h).1 ≫ b ≅ a ≫ f)
    (hcomp : ∀ (Q : Bicategory.TwoCommSq b f) (_hQ : Bicategory.IsTwoFibreProduct Q)
      (k : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f a b h η) Q),
        IsRelativelySmooth.{u, u, u + 1} B S hS k.hom)
    (V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV' : IsAlgebraicSpace B S hS V')
    (bV' : fibredCategory B S hS V' ⟶ 𝒵)
    (hbV' : IsRelativelySmooth.{u, u, u + 1} B S hS bV')
    (pm : fibredCategory B S hS V' ⟶ fibredCategory B S hS V)
    (θ₂ : pm ≫ b ≅ bV' ≫ g)
    (W₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW₀ : IsAlgebraicSpace B S hS W₀)
    (eW₀ : StacksRepresentableCFG.EquivalenceOver (twoFibreProductSquare.{u, u, u + 1, u + 1} pm
        (associatedMap B S hS h).1).pt.val.p
      (presheafOfCategories (W₀ ⋙ typeToCat)).p) :
    P (representingMap B S hS (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS
        h).1).pt (fibredCategory B S hS V') W₀ V' eW₀
        (StacksRepresentableCFG.EquivalenceOver.refl _) (twoFibreProductSquare.{u, u, u + 1, u + 1}
            pm (associatedMap B S hS h).1).fst) := by
  set T := twoFibreProductSquare.{u, u, u + 1, u + 1} f b
  set T' := twoFibreProductSquare.{u, u, u + 1, u + 1} pm T.snd
  let X := twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS h).1
  set G := twoFibreProductSquare.{u, u, u + 1, u + 1}
    (twoFibreProductSquare.{u, u, u + 1, u + 1} f g).snd bV'
  have hTBsw : Bicategory.IsTwoFibreProduct T.swap :=
    Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      f b)
  have k₀ : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f a b h η) T.swap :=
    Quotient.out (hTBsw.from (diagramCone B S hS f a b h η))
  set R := twoFibreProductSquare.{u, u, u + 1, u + 1} T'.snd k₀.hom
  set L := cancelSndSquare.{u, u, u + 1, u + 1} pm T.snd k₀.hom (associatedMap B S hS h).1
    k₀.isoFst.symm
  have hpbk : IsRelativelySmooth.{u, u, u + 1} B S hS R.fst :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS (fibredCategory B S hS U) T.pt T'.pt
      k₀.hom T'.snd R (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} T'.snd k₀.hom)
      (hcomp T.swap hTBsw k₀)
  have hLL : Bicategory.IsTwoFibreProduct L :=
    isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} pm T.snd k₀.hom
      (associatedMap B S hS h).1 k₀.isoFst.symm
  obtain ⟨c1, hc1⟩ := exists_preHom_isEquivalence B S hS
    (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS h).1)
    hLL
  obtain ⟨c2, hc2⟩ := exists_preHom_isEquivalence B S hS
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} pm T.snd))
    (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} T.snd pm)
  have hC1 : Bicategory.IsTwoFibreProduct
      (cancelSndSquare.{u, u, u + 1, u + 1} f g bV' (bV' ≫ g) (Iso.refl _)) :=
    isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} f g bV' (bV' ≫ g) (Iso.refl _)
  obtain ⟨e12, he12⟩ := exists_preHom_isEquivalence B S hS
    (isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} f b pm (bV' ≫ g) θ₂) hC1
  set cU := (((equivalenceOverInvMap B S hS (𝒳 := X.pt) W₀ eW₀ ≫ c1.hom) ≫ R.fst) ≫ c2.hom) ≫
    e12.hom
  have hcU : IsRelativelySmooth.{u, u, u + 1} B S hS cU :=
    isRelativelySmooth_comp_of_isEquivalence B S hS _ e12.hom he12
      (isRelativelySmooth_comp_of_isEquivalence B S hS _ c2.hom hc2
        (isRelativelySmooth_comp B S hS _ R.fst
          (isRelativelySmooth_comp_of_isEquivalence B S hS _ c1.hom hc1
            (isRelativelySmooth_equivalenceOverInvMap B S hS (𝒳 := X.pt) W₀ hW₀ eW₀)) hpbk))
  have κ : cU ≫ G.snd ≅ equivalenceOverInvMap B S hS (𝒳 := X.pt) W₀ eW₀ ≫ X.fst :=
    Bicategory.associator _ e12.hom G.snd ≪≫ Bicategory.whiskerLeftIso _ e12.isoSnd.symm ≪≫
      Bicategory.associator _ c2.hom (twoFibreProductSquare.{u, u, u + 1, u + 1} T.snd pm).snd ≪≫
      Bicategory.whiskerLeftIso _ c2.isoSnd.symm ≪≫ Bicategory.associator _ R.fst T'.fst ≪≫
      Bicategory.associator (equivalenceOverInvMap B S hS (𝒳 := X.pt) W₀ eW₀) c1.hom L.fst ≪≫
      Bicategory.whiskerLeftIso _ c1.isoFst.symm
  have hfin : representingMap B S hS (fibredCategory B S hS W₀) (fibredCategory B S hS V') W₀ V'
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (cU ≫ G.snd) =
      representingMap B S hS
        (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS h).1).pt
        (fibredCategory B S hS V') W₀ V' eW₀ (StacksRepresentableCFG.EquivalenceOver.refl _)
        (twoFibreProductSquare.{u, u, u + 1, u + 1} pm (associatedMap B S hS h).1).fst := by
    rw [representingMap_congr_twoIso B S hS W₀ V' (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) κ,
      representingMap_comp (𝒜 := fibredCategory B S hS W₀) (ℬ := X.pt)
        (𝒞 := fibredCategory B S hS V') B S hS W₀ W₀ V'
        (StacksRepresentableCFG.EquivalenceOver.refl _) eW₀
        (StacksRepresentableCFG.EquivalenceOver.refl _),
      representingMap_equivalenceOverInvMap (𝒳 := X.pt) B S hS W₀ eW₀, Category.id_comp]
  rw [← hfin]
  exact prop_representingMap_fst_of_smooth_comparison B S hS P
    (twoFibreProductSquare.{u, u, u + 1, u + 1} f g).snd hevery V' W₀ hV' hW₀ bV' hbV' G.swap
    (Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (twoFibreProductSquare.{u, u, u + 1, u + 1} f g).snd bV')) cU hcU

/-- Let `P` be smooth local on the source-and-target, with fppf local restriction to algebraic
spaces, and let `g : 𝒵 ⟶ 𝒴` be surjective, flat and locally of finite presentation. If the base
change `𝒵 ×_𝒴 𝒳 ⟶ 𝒵` of `f : 𝒳 ⟶ 𝒴` along `g` has `P`, then `f` has `P`. -/
@[stacks 0DN6]
theorem hasProperty_of_baseChange
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    [hlocal : (spaceProperty B S hS P).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hgsurj : IsSurjective B S hS g)
    (hgflat : AlgebraicStacks.IsFlat B S hS g)
    (hglfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    (hbase : HasPropertyOnSomeSmoothDiagram B S hS P
      (twoFibreProductSquareAlgebraicStacks B S hS g f).fst.hom) :
    HasPropertyOnSomeSmoothDiagram B S hS P f.hom := by
  have hevery : HasPropertyOnEverySmoothDiagram B S hS P (twoFibreProductSquare.{u, u, u + 1, u + 1}
      f.hom g.hom).snd :=
    (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS P hP
      (isAlgebraicStack_twoFibreProductSquare B S hS f g) 𝒵.property
          (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom).snd).2
      (hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct B S hS P
        (twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom f.hom)
            (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom).swap
            (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom f.hom)
        (Bicategory.isTwoFibreProduct_swap
            (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom)) hbase)
  refine (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS P hP 𝒳.property 𝒴.property
    f.hom).1 ?_
  intro U V hU hV a b h η ha hb hcomp
  obtain ⟨V', hV', b₁, hb₁sm, hb₁su⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS g (Bicategory.InducedBicategory.mkHom b :
          algebraicSpaceStack B S hS V hV ⟶ 𝒴)).pt.property
  set T := twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b
  set m := representingMap B S hS (fibredCategory B S hS V') (fibredCategory B S hS V) V' V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫ T.snd)
  have hmsurj : Space.IsSurjective B S hS m :=
    isSurjective_representingMap_of_isSurjectiveOnObjects B S hS (b₁ ≫ T.snd) V' V
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS V').val.p T.pt.val.p
        (fibredCategory B S hS V).val.p (homFunctor b₁) (homFunctor T.snd)
        (homFunctor_comp_p T.snd) hb₁su
        (isSurjectiveOnObjects_twoFibreProductSnd.{u, u, u + 1} B S hS 𝒵.val 𝒴.val
          (fibredCategory B S hS V) g.hom b
          (isSurjectiveOnObjects_of_pointsMap_surjective B S hS g hgsurj)))
  have hmflat : Space.IsFlat B S hS m :=
    isFlat_representingMap_comp_of_isRelativelySmooth.{u, w} B S hS g hgflat hV
      (Bicategory.InducedBicategory.mkHom b : algebraicSpaceStack B S hS V hV ⟶ 𝒴)
      (twoFibreProductSquareAlgebraicStacks B S hS g (Bicategory.InducedBicategory.mkHom b :
        algebraicSpaceStack B S hS V hV ⟶ 𝒴))
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g
        (Bicategory.InducedBicategory.mkHom b : algebraicSpaceStack B S hS V hV ⟶ 𝒴)) hV'
      (Bicategory.InducedBicategory.mkHom b₁) hb₁sm
  have hmlfp : Space.IsLocallyOfFinitePresentation B S hS m :=
    isLocallyOfFinitePresentation_representingMap_comp_of_isRelativelySmooth.{u, w} B S hS g
      hglfp hV (Bicategory.InducedBicategory.mkHom b : algebraicSpaceStack B S hS V hV ⟶ 𝒴)
      (twoFibreProductSquareAlgebraicStacks B S hS g (Bicategory.InducedBicategory.mkHom b :
        algebraicSpaceStack B S hS V hV ⟶ 𝒴))
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g
        (Bicategory.InducedBicategory.mkHom b : algebraicSpaceStack B S hS V hV ⟶ 𝒴)) hV'
      (Bicategory.InducedBicategory.mkHom b₁) hb₁sm
  obtain ⟨W₀, hW₀, ⟨eW₀⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
    (fibredCategory B S hS V) (fibredCategory B S hS V') (fibredCategory B S hS U)
    (associatedMap B S hS m).1.hom (associatedMap B S hS h).1.hom
    (isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
      (associatedMap B S hS h).1 (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV))
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS V' hV')
  set Y := twoFibreProductSquare.{u, u, u + 1, u + 1} (associatedMap B S hS m).1
    (associatedMap B S hS h).1
  have hFib : (twoFibreProductStructureFunctor B S hS (fibredCategory B S hS V')
      (fibredCategory B S hS U) (fibredCategory B S hS V) (associatedMap B S hS m).1
      (associatedMap B S hS h).1).IsFibered :=
    Y.pt.isFiberedInGroupoids.isFibered
  have hmleft : representingMap B S hS (fibredCategory B S hS V') (fibredCategory B S hS V) V' V
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (associatedMap B S hS m).1 = m :=
    representingMap_associatedMap B S hS V' V m
  have hsq := isPullback_representingMap_twoFibreProduct B S hS
    (fibredCategory B S hS V') (fibredCategory B S hS U) (fibredCategory B S hS V)
    V' U V (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (associatedMap B S hS m).1 (associatedMap B S hS h).1 W₀ eW₀
  rw [representingMap_associatedMap B S hS U V h, hmleft] at hsq
  have hsqA : IsPullback
      (ObjectProperty.homMk (representingMap B S hS Y.pt (fibredCategory B S hS U) W₀ U eW₀
        (StacksRepresentableCFG.EquivalenceOver.refl _) Y.snd) :
        (⟨W₀, hW₀⟩ : AlgebraicSpaces B S hS) ⟶ ⟨U, hU⟩)
      (ObjectProperty.homMk (representingMap B S hS Y.pt (fibredCategory B S hS V') W₀ V' eW₀
        (StacksRepresentableCFG.EquivalenceOver.refl _) Y.fst) :
        (⟨W₀, hW₀⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V', hV'⟩)
      (ObjectProperty.homMk h : (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩)
      (ObjectProperty.homMk m : (⟨V', hV'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) hsq
  obtain ⟨em, hem, -⟩ := existsUnique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS V') (fibredCategory B S hS V) V' V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) hmleft
  exact Space.prop_of_isPullback_of_fppf.{u, v} B S hS (spaceProperty B S hS P) hsqA
    hmsurj hmflat hmlfp
    (prop_representingMap_fst_of_hasPropertyOnEverySmoothDiagram B S hS P f.hom g.hom hevery
      U V a b h η hcomp V' hV' (b₁ ≫ T.fst)
      (isRelativelySmooth_comp B S hS b₁ T.fst hb₁sm
        (isRelativelySmooth_baseChange.{u, u, u + 1} B S hS (fibredCategory B S hS V) 𝒴.val
          𝒵.val b g.hom T (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom b)
          hb))
      (associatedMap B S hS m).1
      (Bicategory.whiskerRightIso
          (Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso em hem)) b ≪≫
        Bicategory.associator b₁ T.snd b ≪≫ Bicategory.whiskerLeftIso b₁ T.iso.symm ≪≫
        (Bicategory.associator b₁ T.fst g.hom).symm)
      W₀ hW₀ eW₀)

end AlgebraicGeometry.Stack

end
