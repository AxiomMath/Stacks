module

public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleRestrictionAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.OpenPresentationQuotientStack
public import StacksFrontier.CategoryTheory.Sites.Stack.EssImageRestriction

/-!
# The isomorphism sheaves of the quotient stack presenting `FA_d` are algebraic spaces

Let `S` be a scheme of a big fppf site, let `d` be a positive integer, and let `G` be a groupoid
in algebraic spaces over an algebraic space `B` over `S` whose pointwise groupoid presheaf is
isomorphic to the presheaf `FA_d` of free rank-`d` algebra structures — for the conjugation action
of the unit-fixing subgroup of `GL_d` on the scheme of structure constants this is the `[X/G]` of
Stacks 05YQ. Then the sheaf `Isom(x, y)` of isomorphisms between two objects of a fibre of
`[U/R]` is an algebraic space over the scheme the test object lies over.

This is the conclusion of **Stacks 04TB** for this quotient stack, and unlike the general
statement it is **unconditional**: Stacks 04TB descends algebraicity along a surjective, flat,
locally finitely presented morphism and so consumes the bootstrap theorem Stacks 04S6, whereas
here the two objects are presented over a surjective **étale** morphism and Stacks 0BGR
closes the descent.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.exists_surjective_etale_presented_pair`: two objects of a
  fibre both come from points of the object space over a single object of the site whose structure
  morphism to the test object is surjective and étale.
* `AlgebraicGeometry.FiniteFreeAlgebra.quotientStackIsomSheavesAlgebraic_of_ffaIso`: **the
  conclusion of Stacks 04TB for this quotient stack, with nothing assumed.**
* `AlgebraicGeometry.FiniteFreeAlgebra.isAlgebraicStack_quotientStack_of_ffaIso`: **Stacks 04TK
  for this quotient stack with both of its carried hypotheses discharged** — a smooth groupoid in
  algebraic spaces presenting `FA_d` has an algebraic quotient stack, unconditionally.

## Implementation notes

The single object is the coproduct, inside the site, of the opens of the test object produced by
`AlgebraicGeometry.FiniteFreeAlgebra.exists_opens_essImage_toQuotientStack` for the two objects
and intersected pointwise — the intersection still contains the point it is indexed by, and the
essential image survives the restriction by
`CategoryTheory.Functor.IsFibredOneMorphism.essImage_pullbackFiber_comp`.

That coproduct exists in the site because the family is indexed by the points of the test object
and each member is an open of it: the number of points is below the size cutoff since the cutoff
is closed under powersets (`AlgebraicGeometry.Scheme.max_two_pow_mk_size_lt_of_isStrongPrelimit`),
and an open immersion does not raise the size
(`AlgebraicGeometry.Scheme.size_le_of_isOpenImmersion`). Its structure morphism is surjective
because every point of the test object lies in its own open, and étale because being étale is
Zariski-local at the source and the summands are open immersions of the test object. The two
objects are presented over the coproduct rather than only over its summands because the summands
are monomorphisms with empty pairwise intersections, so sections of a sheaf over them glue with no
compatibility condition — that is
`AlgebraicGeometry.Stack.presented_pullback_of_disjoint_cover`.

The last step is `AlgebraicGeometry.Stack.exists_shrunk_isomPresheaf`, the part of Stacks 04TB
that is independent of how algebraicity descends, followed by
`AlgebraicGeometry.Space.isAlgebraicSpace_of_surjective_etale_restriction`.

## References

* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 04TB](https://stacks.math.columbia.edu/tag/04TB)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S} {d : ℕ} [NeZero d]
  {B : AlgebraicSpaces 𝒞 S hS} (G : GroupoidInAlgebraicSpaces 𝒞 S hS B)
  (η : ffaSitePresheaf 𝒞 S hS d ≅
    AlgebraicGeometry.Stack.evaluationGroupoidFunctor G.toGroupoidInFunctors)

include η in
/-- **Two objects of a fibre of the quotient stack come from points of the object space over a
common family of opens of the test object.** The family is the pointwise intersection of the two
families of
`AlgebraicGeometry.FiniteFreeAlgebra.exists_opens_essImage_toQuotientStack`; it still contains the
point it is indexed by, and each essential image survives the restriction to the smaller open. -/
theorem exists_opens_essImage_toQuotientStack_pair
    (T : BigFppfOver 𝒞 S hS) (x y : (AlgebraicGeometry.Stack.quotientStack G).p.Fiber T) :
    ∃ O : ↥T.left.obj → T.left.obj.Opens, (∀ t, t ∈ O t) ∧
      (∀ t, (Functor.fiberFunctorOfCompEq
          (AlgebraicGeometry.Stack.isFibredOneMorphism_toQuotientStack G).comp_eq
          (BigFppfOver.openSubObj 𝒞 S hS T (O t))).essImage
        (Functor.pullbackFiber (AlgebraicGeometry.Stack.quotientStack G).p x
          (BigFppfOver.openSubHom 𝒞 S hS T (O t)))) ∧
      (∀ t, (Functor.fiberFunctorOfCompEq
          (AlgebraicGeometry.Stack.isFibredOneMorphism_toQuotientStack G).comp_eq
          (BigFppfOver.openSubObj 𝒞 S hS T (O t))).essImage
        (Functor.pullbackFiber (AlgebraicGeometry.Stack.quotientStack G).p y
          (BigFppfOver.openSubHom 𝒞 S hS T (O t)))) := by
  obtain ⟨O₁, hm₁, h₁⟩ := exists_opens_essImage_toQuotientStack G η T x
  obtain ⟨O₂, hm₂, h₂⟩ := exists_opens_essImage_toQuotientStack G η T y
  refine ⟨fun t => O₁ t ⊓ O₂ t, fun t => ⟨hm₁ t, hm₂ t⟩, fun t => ?_, fun t => ?_⟩
  · exact Functor.IsFibredOneMorphism.essImage_pullbackFiber_comp
      (AlgebraicGeometry.Stack.isFibredOneMorphism_toQuotientStack G)
      (BigFppfOver.openSubHomOfLE_comp_openSubHom 𝒞 S hS T (inf_le_left : O₁ t ⊓ O₂ t ≤ O₁ t))
      x (h₁ t)
  · exact Functor.IsFibredOneMorphism.essImage_pullbackFiber_comp
      (AlgebraicGeometry.Stack.isFibredOneMorphism_toQuotientStack G)
      (BigFppfOver.openSubHomOfLE_comp_openSubHom 𝒞 S hS T (inf_le_right : O₁ t ⊓ O₂ t ≤ O₂ t))
      y (h₂ t)

include η in
/-- **Two objects of a fibre of the quotient stack both come from points of the object space over
a single object of the site, surjective and étale over the test object.** The object is the
coproduct inside the site of the common family of opens of
`AlgebraicGeometry.FiniteFreeAlgebra.exists_opens_essImage_toQuotientStack_pair`.

This is the étale counterpart of
`AlgebraicGeometry.Stack.exists_single_cover_presented_pair`, which produces a surjective, flat,
locally finitely presented member of an fppf covering and whose consumer therefore needs the
bootstrap theorem Stacks 04S6. -/
theorem exists_surjective_etale_presented_pair
    (T : BigFppfOver 𝒞 S hS) (x y : (AlgebraicGeometry.Stack.quotientStack G).p.Fiber T) :
    ∃ (V : BigFppfOver 𝒞 S hS) (f : V ⟶ T),
      Surjective ((BigFppfOver.toScheme 𝒞 S hS).map f) ∧
      Etale ((BigFppfOver.toScheme 𝒞 S hS).map f) ∧
      ∃ a b : G.objects.obj.obj (op V),
        Nonempty ((AlgebraicGeometry.Stack.pointwiseToQuotientStackFiber G V).obj a ≅
          Functor.pullbackFiber (AlgebraicGeometry.Stack.quotientStack G).p x f) ∧
        Nonempty ((AlgebraicGeometry.Stack.pointwiseToQuotientStackFiber G V).obj b ≅
          Functor.pullbackFiber (AlgebraicGeometry.Stack.quotientStack G).p y f) := by
  classical
  obtain ⟨O, hmem, hx, hy⟩ := exists_opens_essImage_toQuotientStack_pair G η T x y
  set R : ↥T.left.obj → BigFppfOver 𝒞 S hS := fun t => BigFppfOver.openSubObj 𝒞 S hS T (O t)
    with hRdef
  set fi : ∀ t, R t ⟶ T := fun t => BigFppfOver.openSubHom 𝒞 S hS T (O t) with hfidef
  have hopen : ∀ t, IsOpenImmersion ((BigFppfOver.toScheme 𝒞 S hS).map (fi t)) := fun t =>
    inferInstanceAs (IsOpenImmersion (O t).ι)
  -- the coproduct of the family exists inside the site
  set μ : Cardinal.{u} := max (2 ^ Cardinal.mk ↥T.left.obj) T.left.obj.size with hμdef
  have hμ : μ < 𝒞.cutoff :=
    Scheme.max_two_pow_mk_size_lt_of_isStrongPrelimit 𝒞.cutoff_isStrongPrelimit T.left.property
  have hℵ : Cardinal.aleph0 ≤ μ := T.left.obj.aleph0_le_size.trans (le_max_right _ _)
  have hK : Cardinal.mk ↥T.left.obj ≤ μ := (Cardinal.cantor _).le.trans (le_max_left _ _)
  have hsize : ∀ t, ((BigFppfOver.toScheme 𝒞 S hS).obj (R t)).size ≤ μ := fun t =>
    (Scheme.size_le_of_isOpenImmersion ((BigFppfOver.toScheme 𝒞 S hS).map (fi t))).trans
      (le_max_right _ _)
  have hsum : 𝒞.Contains (∐ fun t => (BigFppfOver.toScheme 𝒞 S hS).obj (R t)) :=
    (schemeSize_coproduct_le _ μ hℵ hK hsize).trans_lt hμ
  obtain ⟨V, j, ⟨hV⟩, e, he⟩ := AlgebraicGeometry.Stack.exists_coproduct_of_contains 𝒞 S hS R hsum
  obtain ⟨hm, hj, hd⟩ := AlgebraicGeometry.Stack.coproduct_cover 𝒞 S hS R V j e he
  set f : V ⟶ T := Cofan.IsColimit.desc hV fi with hfdef
  have hfac : ∀ t, j t ≫ f = fi t := Cofan.IsColimit.fac hV fi
  have hfacmap : ∀ t, (BigFppfOver.toScheme 𝒞 S hS).map (j t) ≫
      (BigFppfOver.toScheme 𝒞 S hS).map f = (BigFppfOver.toScheme 𝒞 S hS).map (fi t) := fun t => by
    rw [← Functor.map_comp, hfac t]
  -- the structure morphism is surjective: every point lies in its own open
  have hfSurj : Surjective ((BigFppfOver.toScheme 𝒞 S hS).map f) := by
    constructor
    intro t
    obtain ⟨w, hw⟩ : ∃ w, (BigFppfOver.toScheme 𝒞 S hS).map (fi t) w = t := ⟨⟨t, hmem t⟩, rfl⟩
    refine ⟨(BigFppfOver.toScheme 𝒞 S hS).map (j t) w, ?_⟩
    rw [← Scheme.Hom.comp_apply, hfacmap t]
    exact hw
  -- and étale, being étale being Zariski-local at the source
  have hfEtale : Etale ((BigFppfOver.toScheme 𝒞 S hS).map f) := by
    have _ : IsZariskiLocalAtSource (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := RingHom.Etale)
    have hoi : ∀ t, IsOpenImmersion ((BigFppfOver.toScheme 𝒞 S hS).map (j t)) := fun t =>
      isOpenImmersion_toScheme_map_cofan hV t
    have hcovV : ∀ z : (BigFppfOver.toScheme 𝒞 S hS).obj V,
        ∃ t w, (BigFppfOver.toScheme 𝒞 S hS).map (j t) w = z := by
      intro z
      obtain ⟨t, ht⟩ : ∃ t, z ∈ Set.range ((BigFppfOver.toScheme 𝒞 S hS).map (j t)) :=
        Set.mem_iUnion.1 ((iUnion_range_toScheme_map_cofan hV).symm ▸ Set.mem_univ _)
      obtain ⟨w, hw⟩ := ht
      exact ⟨t, w, hw⟩
    have hetfi : ∀ t, Etale ((BigFppfOver.toScheme 𝒞 S hS).map (fi t)) := by
      intro t
      have := hopen t
      infer_instance
    exact IsZariskiLocalAtSource.of_openCover (P := @Etale.{u})
      (Scheme.Cover.mkOfCovers (↥T.left.obj)
        (fun t => (BigFppfOver.toScheme 𝒞 S hS).obj (R t))
        (fun t => (BigFppfOver.toScheme 𝒞 S hS).map (j t)) hcovV fun t => hoi t) fun t =>
      hfacmap t ▸ hetfi t
  -- the two objects are presented over the coproduct
  have pres := AlgebraicGeometry.Stack.presented_pullback_of_disjoint_cover 𝒞 S hS G R V T j
    hm hj hd f fi hfac
  obtain ⟨a, ha⟩ := pres x fun t =>
    AlgebraicGeometry.Stack.presented_of_essImage_toQuotientStack 𝒞 S hS G (hx t)
  obtain ⟨b, hb⟩ := pres y fun t =>
    AlgebraicGeometry.Stack.presented_of_essImage_toQuotientStack 𝒞 S hS G (hy t)
  exact ⟨V, f, hfSurj, hfEtale, a, b, ha, hb⟩

include η in
/-- **The conclusion of Stacks 04TB for the quotient stack presenting `FA_d`, with nothing
assumed.** Every isomorphism sheaf of a fibre of `[U/R]` is an algebraic space over the scheme the
fibre sits over.

The general statement, `AlgebraicGeometry.Stack.isAlgebraicSpace_isomPresheaf`, descends
algebraicity along a surjective, flat, locally finitely presented morphism and so consumes part
(3) of the bootstrap theorem Stacks 04S6, which this library does not prove. Here the two objects
are presented over a surjective **étale** morphism
(`AlgebraicGeometry.FiniteFreeAlgebra.exists_surjective_etale_presented_pair`), and along an étale
morphism Stacks 0BGR closes the descent
(`AlgebraicGeometry.Space.isAlgebraicSpace_of_surjective_etale_restriction`). Everything else is
`AlgebraicGeometry.Stack.exists_shrunk_isomPresheaf`, the part of Stacks 04TB that does not depend
on how algebraicity descends. -/
theorem quotientStackIsomSheavesAlgebraic_of_ffaIso :
    AlgebraicGeometry.Stack.QuotientStackIsomSheavesAlgebraic 𝒞 S hS G := by
  intro T x y
  obtain ⟨F, hFsheaf, ⟨e, he⟩, hres⟩ :=
    AlgebraicGeometry.Stack.exists_shrunk_isomPresheaf 𝒞 S hS B G T x y
  refine ⟨F, ?_, e, he⟩
  obtain ⟨V, f, hfSurj, hfEtale, a, b, ⟨ex⟩, ⟨ey⟩⟩ :=
    exists_surjective_etale_presented_pair G η T x y
  have hprod : IsAlgebraicSpace 𝒞 T.left.obj T.left.property
      (yoneda.obj (Over.mk f.left) ⨯ F) := hres V f a b ex ey
  have hfrom : Over.mkIdTerminal.from (Over.mk f.left) =
      (Over.homMk f.left : Over.mk f.left ⟶ Over.mk (𝟙 T.left)) :=
    Over.mkIdTerminal.hom_ext _ _
  refine Space.isAlgebraicSpace_of_surjective_etale_restriction 𝒞 T.left.obj T.left.property
    hFsheaf (Over.mk f.left) (by rwa [hfrom]) (by rwa [hfrom]) hprod

include η in
/-- **The quotient stack of a smooth groupoid in algebraic spaces presenting `FA_d` is an
algebraic stack over `S`, with nothing assumed.** This is Stacks 04TK with both of its carried
hypotheses discharged.

Stacks 04TK asks for Stacks 04M9 in the form of a presentation of the quotient stack and for the
conclusion of Stacks 04TB. The latter is
`AlgebraicGeometry.FiniteFreeAlgebra.quotientStackIsomSheavesAlgebraic_of_ffaIso`, proved here
without the bootstrap theorem; and the former follows from it, the one field Stacks 04M9 does not
supply being representability of the projection, which
`AlgebraicGeometry.Stack.representable_quotientStackProjectionHom_of_isomPresheafAlgebraic`
derives from Stacks 04TB alone. So the only remaining input is smoothness of the groupoid. -/
theorem isAlgebraicStack_quotientStack_of_ffaIso
    (hGsm : AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsSmooth 𝒞 S hS G) :
    AlgebraicGeometry.Stack.IsAlgebraicStack.{u, w} 𝒞 S hS
      (AlgebraicGeometry.Stack.quotientStack G) :=
  AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_hasSmoothPresentation G
    (quotientStackIsomSheavesAlgebraic_of_ffaIso G η)
    (AlgebraicGeometry.Stack.hasSmoothPresentation_quotientStack_of_isSmooth
      (AlgebraicGeometry.Stack.QuotientAtlas.presentation G
        (AlgebraicGeometry.Stack.representable_quotientStackProjectionHom_of_isomPresheafAlgebraic G
          (quotientStackIsomSheavesAlgebraic_of_ffaIso G η)))
      hGsm)

end AlgebraicGeometry.FiniteFreeAlgebra

end
