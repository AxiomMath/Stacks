module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfSourceLocalityFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentProperty
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Descent of local finite type across a surjective flat 1-morphism of finite presentation

Let `𝒳 ⟶ 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over `S`. If the composite `𝒳 ⟶ 𝒵` is
locally of finite type and `𝒳 ⟶ 𝒴` is representable by algebraic spaces, surjective, flat and
locally of finite presentation, then `𝒴 ⟶ 𝒵` is locally of finite type.

The property descends across the *first* factor of a composite, which is the fppf-descent
direction on the **source**. It is not the base-change descent of **Stacks 0DN6**, where a
surjective flat 1-morphism `𝒵 ⟶ 𝒴` is pulled back and the conclusion is about the morphism being
pulled back (`AlgebraicGeometry.Stack.hasProperty_of_baseChange` and
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_baseChange`). Nor is it
**Stacks 06U9**, which cancels in the other direction.

## Main results

* `AlgebraicGeometry.Space.prop_of_comp_of_fppf`: a property of morphisms of algebraic spaces
  local on the source for the fppf topology may be descended across one surjective flat morphism
  locally of finite presentation.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_comp_of_fppf`: that descent at local finite
  type, using that local finite type is fppf local on the source (**Stacks 06EW**).
* `AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_of_comp_of_fppf`: the same descent for
  the *universal* smooth-diagram condition of **Stacks 06FM**, for any property whose
  restriction to algebraic spaces descends across such a morphism.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_comp_of_fppf`: local finite
  type descends across a representable surjective flat 1-morphism locally of finite presentation.

## Implementation notes

`AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFiniteType` is **Stacks 06FS** part (1),
the universal form of the smooth-diagram condition, so the proof starts from an arbitrary smooth
diagram `(V, W, b, c, h)` over `𝒴 ⟶ 𝒵` instead of choosing smooth presentations:

* `U` is the algebraic space representing `V ×_{W ×_𝒵 𝒴} ((W ×_𝒵 𝒴) ×_𝒴 𝒳)`, which is also a
  base change of `𝒳 ⟶ 𝒴` along `V ⟶ W ×_𝒵 𝒴 ⟶ 𝒴` by **Stacks 003Q**
  (`CategoryTheory.Bicategory.isTwoFibreProduct_pasteFst`), hence representable by an algebraic
  space by **Stacks 0300**;
* `U ⟶ V` is the morphism of representing spaces of that base change, so it inherits
  surjectivity, flatness and local finite presentation from `𝒳 ⟶ 𝒴` by **Stacks 03YK**
  (`AlgebraicGeometry.Stack.prop_representingMap_of_hasRelativeProperty`);
* `U ⟶ W` carries the property because `U ⟶ (W ×_𝒵 𝒴) ×_𝒴 𝒳` is smooth — it is the base change
  along `𝒳 ⟶ 𝒴` of the comparison `V ⟶ W ×_𝒵 𝒴` that the given diagram's own universal clause
  makes smooth — and `(W ×_𝒵 𝒴) ×_𝒴 𝒳` is a 2-fibre product of the cospan `(c, f ≫ g)` by
  **Stacks 003Q** (`CategoryTheory.Bicategory.isTwoFibreProduct_paste`). So
  `AlgebraicGeometry.Stack.prop_representingMap_fst_of_smooth_comparison` applies; it asks for one
  smooth 1-morphism into one chosen 2-fibre product, rather than for smoothness of every
  comparison 1-morphism into every 2-fibre product of `(c, f ≫ g)`.

`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_of_comp_of_fppf` takes the covering
hypothesis on `f` in the form `hfcov`, as the three properties of the morphism of representing
spaces induced by an arbitrary base change of `f` along a 1-morphism out of an algebraic space,
rather than as `AlgebraicGeometry.Stack.HasRelativeProperty` at flatness and local finite
presentation. Those two relative properties carry instance hypotheses — stability under base
change and fppf locality on the target — which are available but are not *instances*, so writing
them into a statement would force the caller to supply them there. In `hfcov` they stay inside the
proof of `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_comp_of_fppf`.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 06EW](https://stacks.math.columbia.edu/tag/06EW)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06U8](https://stacks.math.columbia.edu/tag/06U8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory
open CategoryTheory.CatFiberedInGroupoids

universe u v w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Fppf descent on the source across one morphism.** Let `P` be a property of morphisms of
algebraic spaces over `S` which is local on the source for the fppf topology. If `p : X ⟶ Y` is
surjective, flat and locally of finite presentation and `p ≫ q` has `P`, then `q` has `P`.

The one-member presieve of such a `p` is an fppf covering family of `Y` by **Stacks 03Y8**
(`AlgebraicGeometry.Space.ofArrows_singleton_mem_fppf_precoverage`), and
`CategoryTheory.MorphismProperty.IsLocalAtSource.of_forall_comp` at that family has exactly one
member to check. -/
theorem prop_of_comp_of_fppf
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtSource (Topology.fppf.precoverage.{u, v} B S hS)]
    {X Y Z : AlgebraicSpaces B S hS} (p : X ⟶ Y) (q : Y ⟶ Z)
    (hsurj : IsSurjective B S hS p.hom) (hflat : IsFlat B S hS p.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS p.hom)
    (hpq : P (p ≫ q)) : P q :=
  MorphismProperty.IsLocalAtSource.of_forall_comp
    (ofArrows_singleton_mem_fppf_precoverage.{u, v} B S hS p hsurj hflat hlfp)
    (fun {_} {_} hg => by cases hg; exact hpq)

/-- If `p : X ⟶ Y` is a surjective flat
morphism of algebraic spaces over `S` locally of finite presentation and `p ≫ q` is locally of
finite type, then `q` is locally of finite type.

Local finite type is local on the source for the fppf topology, which is Stacks 06EW
(`AlgebraicGeometry.Space.isLocallyOfFiniteType_isLocalAtSource_fppf`). The smooth statement
would not do: a smooth covering is an fppf covering and not conversely, and the covering produced
here is only flat and locally of finite presentation. -/
theorem isLocallyOfFiniteType_of_comp_of_fppf
    {X Y Z : AlgebraicSpaces B S hS} (p : X ⟶ Y) (q : Y ⟶ Z)
    (hsurj : IsSurjective B S hS p.hom) (hflat : IsFlat B S hS p.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS p.hom)
    (hpq : IsLocallyOfFiniteType B S hS (p.hom ≫ q.hom)) :
    IsLocallyOfFiniteType B S hS q.hom :=
  prop_of_comp_of_fppf.{u, u} B S hS
    (fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) => IsLocallyOfFiniteType B S hS k.hom)
    p q hsurj hflat hlfp hpq

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent of the universal smooth-diagram condition across the first factor of a
composite.** Let `P` be a property of morphisms of presheaves on the big fppf site of `S`
which descends across a surjective flat morphism of algebraic spaces locally of finite
presentation (`hdescent`), let `f : 𝒳 ⟶ 𝒴` be representable by algebraic spaces and such that
every base change of it along a 1-morphism out of an algebraic space induces a surjective flat
morphism of representing spaces locally of finite presentation (`hfcov`). If `f ≫ g` satisfies
the universal condition for `P`, then so does `g`.

Applied to an arbitrary smooth diagram `(V, W, b, c, h)` over `g`: the comparison
`k₀ : 𝒮_V ⟶ W ×_𝒵 𝒴` that the diagram's own clause makes smooth is base-changed along `f`, and
`hfcov` reads off the covering `U ⟶ V`. See the module's implementation notes. -/
theorem hasPropertyOnEverySmoothDiagram_of_comp_of_fppf
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hdescent : ∀ ⦃X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄,
      IsAlgebraicSpace B S hS X → IsAlgebraicSpace B S hS Y → IsAlgebraicSpace B S hS Z →
      ∀ (p : X ⟶ Y) (q : Y ⟶ Z),
        Space.IsSurjective B S hS p → Space.IsFlat B S hS p →
        Space.IsLocallyOfFinitePresentation B S hS p → P (p ≫ q) → P q)
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hfcov : ∀ (V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hV' : IsAlgebraicSpace B S hS V')
      (k : fibredCategory B S hS V' ⟶ 𝒴)
      (N : Bicategory.TwoCommSq k f) (_hN : Bicategory.IsTwoFibreProduct N)
      (U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hU' : IsAlgebraicSpace B S hS U')
      (eU' : StacksRepresentableCFG.EquivalenceOver N.pt.val.p
        (presheafOfCategories (U' ⋙ typeToCat)).p),
      Space.IsSurjective B S hS (representingMap B S hS N.pt (fibredCategory B S hS V') U' V'
          eU' (StacksRepresentableCFG.EquivalenceOver.refl _) N.fst) ∧
      Space.IsFlat B S hS (representingMap B S hS N.pt (fibredCategory B S hS V') U' V'
          eU' (StacksRepresentableCFG.EquivalenceOver.refl _) N.fst) ∧
      Space.IsLocallyOfFinitePresentation B S hS
        (representingMap B S hS N.pt (fibredCategory B S hS V') U' V'
          eU' (StacksRepresentableCFG.EquivalenceOver.refl _) N.fst))
    (hfg : HasPropertyOnEverySmoothDiagram B S hS P (f ≫ g)) :
    HasPropertyOnEverySmoothDiagram B S hS P g := by
  intro V W hV hW b c h η hb hc hcomp
  -- `S₀` is the 2-fibre product `W ×_𝒵 𝒴`
  have hS₀ : Bicategory.IsTwoFibreProduct
      (twoFibreProductSquare.{u, u, u + 1, u + 1} c g) :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} c g
  set S₀ := twoFibreProductSquare.{u, u, u + 1, u + 1} c g with hS₀def
  -- `T₀` is the 2-fibre product `(W ×_𝒵 𝒴) ×_𝒴 𝒳`
  have hT₀ : Bicategory.IsTwoFibreProduct
      (twoFibreProductSquare.{u, u, u + 1, u + 1} S₀.snd f) :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} S₀.snd f
  set T₀ := twoFibreProductSquare.{u, u, u + 1, u + 1} S₀.snd f with hT₀def
  -- the pasted rectangle is a 2-fibre product of the cospan `(c, f ≫ g)`
  have hOut : Bicategory.IsTwoFibreProduct (S₀.paste T₀) :=
    Bicategory.isTwoFibreProduct_paste hS₀ hT₀
  -- the comparison the diagram's own hypothesis makes smooth
  have k₀ : Bicategory.TwoCommSq.PreHom (diagramCone B S hS g b c h η) S₀ :=
    Quotient.out (hS₀.from (diagramCone B S hS g b c h η))
  have hk₀ : IsRelativelySmooth.{u, u, u + 1} B S hS k₀.hom := hcomp S₀ hS₀ k₀
  -- `M` is the 2-fibre product `V ×_{W ×_𝒵 𝒴} ((W ×_𝒵 𝒴) ×_𝒴 𝒳)`
  have hM : Bicategory.IsTwoFibreProduct
      (twoFibreProductSquare.{u, u, u + 1, u + 1} k₀.hom T₀.fst) :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} k₀.hom T₀.fst
  set M := twoFibreProductSquare.{u, u, u + 1, u + 1} k₀.hom T₀.fst with hMdef
  -- and is at the same time a base change of `f` along `k₀.hom ≫ S₀.snd`
  have hN : Bicategory.IsTwoFibreProduct (T₀.pasteFst M) :=
    Bicategory.isTwoFibreProduct_pasteFst T₀ hT₀ M hM
  have hT₀rep : IsRepresentableByAlgebraicSpaces B S hS T₀.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒳 𝒴 S₀.pt f S₀.snd T₀ hT₀ hf
  obtain ⟨Uu, hUu, ⟨eUu⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
    S₀.pt (fibredCategory B S hS V) T₀.pt k₀.hom.hom T₀.fst.hom hT₀rep
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV)
  have eU : StacksRepresentableCFG.EquivalenceOver M.pt.val.p
      (presheafOfCategories (Uu ⋙ typeToCat)).p := eUu
  obtain ⟨hrsurj, hrflat, hrlfp⟩ :=
    hfcov V hV (k₀.hom ≫ S₀.snd) (T₀.pasteFst M) hN Uu hUu eU
  -- the comparison of the new diagram with the pasted 2-fibre product is smooth
  have hMsnd : IsRelativelySmooth.{u, u, u + 1} B S hS M.snd :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS (fibredCategory B S hS V) S₀.pt T₀.pt
      k₀.hom T₀.fst M.swap (Bicategory.isTwoFibreProduct_swap hM) hk₀
  have hcc₀ : IsRelativelySmooth.{u, u, u + 1} B S hS
      (equivalenceOverInvMap B S hS (𝒳 := M.pt) Uu eU) :=
    isRelativelySmooth_equivalenceOverInvMap B S hS (𝒳 := M.pt) Uu hUu eU
  have hcc : IsRelativelySmooth.{u, u, u + 1} B S hS
      (equivalenceOverInvMap B S hS (𝒳 := M.pt) Uu eU ≫ M.snd) :=
    isRelativelySmooth_comp B S hS _ _ hcc₀ hMsnd
  have key := prop_representingMap_fst_of_smooth_comparison B S hS P (f ≫ g) hfg W Uu hW hUu
    c hc (S₀.paste T₀) hOut (equivalenceOverInvMap B S hS (𝒳 := M.pt) Uu eU ≫ M.snd) hcc
  -- the two legs of `M` make the new diagram's top morphism `rU ≫ h`
  have twoiso : (equivalenceOverInvMap B S hS (𝒳 := M.pt) Uu eU ≫ M.snd) ≫ (S₀.paste T₀).fst ≅
      equivalenceOverInvMap B S hS (𝒳 := M.pt) Uu eU ≫
        (M.fst ≫ (associatedMap B S hS h).1) := by
    refine Bicategory.associator _ _ _ ≪≫ Bicategory.whiskerLeftIso _ ?_
    exact (Bicategory.associator _ _ _).symm ≪≫
      Bicategory.whiskerRightIso M.iso.symm S₀.fst ≪≫ Bicategory.associator _ _ _ ≪≫
      Bicategory.whiskerLeftIso M.fst k₀.isoFst.symm
  have e0 : representingMap B S hS (fibredCategory B S hS Uu) (fibredCategory B S hS W) Uu W
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        ((equivalenceOverInvMap B S hS (𝒳 := M.pt) Uu eU ≫ M.snd) ≫ (S₀.paste T₀).fst)
      = representingMap B S hS M.pt (fibredCategory B S hS V) Uu V eU
          (StacksRepresentableCFG.EquivalenceOver.refl _) M.fst ≫ h := by
    rw [representingMap_congr_twoIso B S hS Uu W
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) twoiso,
      representingMap_comp (𝒜 := fibredCategory B S hS Uu) (ℬ := M.pt)
        (𝒞 := fibredCategory B S hS W) B S hS Uu Uu W
        (StacksRepresentableCFG.EquivalenceOver.refl _) eU
        (StacksRepresentableCFG.EquivalenceOver.refl _),
      representingMap_equivalenceOverInvMap B S hS Uu eU, Category.id_comp,
      representingMap_comp (𝒜 := M.pt) (ℬ := fibredCategory B S hS V)
        (𝒞 := fibredCategory B S hS W) B S hS Uu V W eU
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _),
      representingMap_associatedMap B S hS V W h]
  rw [e0] at key
  exact hdescent hUu hV hW _ h hrsurj hrflat hrlfp key

namespace AlgebraicStacks

/-- Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over
`S`. If `f ≫ g` is locally of finite type and `f` is representable by algebraic spaces,
surjective, flat and locally of finite presentation, then `g` is locally of finite type. -/
@[stacks 06U8]
theorem isLocallyOfFiniteType_of_comp_of_fppf
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : IsLocallyOfFiniteType B S hS (f ≫ g))
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hfsurj : IsSurjective B S hS f)
    (hfflat : IsFlat B S hS f)
    (hflfp : IsLocallyOfFinitePresentation B S hS f) :
    IsLocallyOfFiniteType B S hS g := by
  let iflat1 : (spaceProperty B S hS
      (fun _ _ k => Space.IsFlat B S hS k)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  let iflat2 : (spaceProperty B S hS
      (fun _ _ k => Space.IsFlat B S hS k)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  let ilfp1 : (spaceProperty B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  let ilfp2 : (spaceProperty B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have hsurjRel : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) f.hom hf :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS f.hom hf).1
      (isSurjectiveOnObjects_of_pointsMap_surjective B S hS f hfsurj)
  have hflatRel : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (spaceProperty B S hS (fun _ _ k => Space.IsFlat B S hS k)) f.hom hf :=
    hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) f.hom hf hfflat
  have hlfpRel : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (spaceProperty B S hS
        (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)) f.hom hf :=
    hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) f.hom hf
      ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
        (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
        𝒳.property 𝒴.property f.hom).1 hflfp)
  refine hasPropertyOnEverySmoothDiagram_of_comp_of_fppf B S hS _ ?_ f.hom g.hom hf ?_ hfg
  · intro X Y Z hX hY hZ p q hps hpf hpl hpq
    exact Space.isLocallyOfFiniteType_of_comp_of_fppf B S hS
      (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩) (Z := ⟨Z, hZ⟩)
      (ObjectProperty.homMk p) (ObjectProperty.homMk q) hps hpf hpl hpq
  · intro V' hV' k N hN U' hU' eU'
    exact ⟨prop_representingMap_of_hasRelativeProperty B S hS
        (Space.surjectiveMorphismProperty B S hS) f.hom hf hsurjRel
        (fibredCategory B S hS V') k N hN U' V' hU' hV' eU'
        (StacksRepresentableCFG.EquivalenceOver.refl _),
      prop_representingMap_of_hasRelativeProperty B S hS _ f.hom hf hflatRel
        (fibredCategory B S hS V') k N hN U' V' hU' hV' eU'
        (StacksRepresentableCFG.EquivalenceOver.refl _),
      prop_representingMap_of_hasRelativeProperty B S hS _ f.hom hf hlfpRel
        (fibredCategory B S hS V') k N hN U' V' hU' hV' eU'
        (StacksRepresentableCFG.EquivalenceOver.refl _)⟩

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
