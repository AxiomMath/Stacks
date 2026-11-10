module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.CoproductOneMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionQuotientPresentation

/-!
# A section of a gerbe hits every object over a single fppf cover

Let `π : 𝒳 ⟶ 𝒰` be a 1-morphism of categories fibred in groupoids over the big fppf site of `S`
which makes `𝒳` a gerbe over `𝒰` in the sense of Stacks 06P2, let `𝒰` be the category represented
by an object `U` of the site, and let `x : 𝒰 ⟶ 𝒳` be a *section* of `π`. The gerbe condition says
that every object `ξ` of a fibre of `𝒳` becomes isomorphic to an `x`-image along the members of
*some covering sieve* of its base; that is
`AlgebraicGeometry.Stack.locallyEssSurjOnFibers_of_section_of_isGerbeOver`. This file replaces
that covering sieve by a **single** surjective, flat, locally finitely presented morphism
`b : V ⟶ T` of the site carrying one object of `𝒰` over `V` whose `x`-image is the restriction of
`ξ` along `b`.

## Why this is wanted

The surjectivity of a section of a gerbe is Stacks 06QG part (3)
(`AlgebraicGeometry.Stack.isSurjective_of_section_of_isGerbeOver`); its flatness and local finite
presentation are not proved in the library, and neither is part (2). The route to them that does
not pass through the converse half of **Stacks 06PL** — hence not through **Stacks 06PK**, whose
biconditional the library carries under a hypothesis standing in for **Stacks 06FI** — argues at a
smooth scheme atlas `a : 𝒲 ⟶ 𝒳`: the atlas object comes, fppf-locally on the atlas, from the
section, which produces a 1-morphism `q : 𝒱 ⟶ 𝒳` that is surjective, flat and locally of finite
presentation and factors as `g ≫ x`; then `𝒱 ×_𝒳 𝒱 ⟶ 𝒱` is flat and locally of finite
presentation by base change, `𝒱 ×_𝒳 𝒱 ⟶ 𝒰 ×_𝒳 𝒱` is the base change of `g` and so a surjection of
fppf sheaves, **Stacks 06NR** gives `𝒰 ×_𝒳 𝒱 ⟶ 𝒱` flat and locally of finite presentation, and
**Stacks 06PZ** and **Stacks 06Q8** descend that along `q` to `x` itself.

Producing that `q` has two halves: gathering the gerbe's covering sieve into one covering morphism
of the site, and reading the resulting object through the 2-Yoneda lemma. **The first half is what
this file proves**, together with the elementary input of the local surjectivity of `g`: a section
of any 1-morphism separates the objects of a fibre of its source, since `π ∘ x ≅ 𝟙`. The second
half is `StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionTwoYoneda`; the descent that follows
it — the Stacks 06NR step and the descent along `q` — is
`StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeFactorisationFppfDescent`, and it is
unconditional. Its surjectivity input, that `𝒱 ×_𝒳 𝒱 ⟶ 𝒰 ×_𝒳 𝒱` induces a surjection of fppf
sheaves, is proved there from `nonempty_iso_fiber_of_iso_section_image` below, reduced to a
statement about objects of fibres by
`AlgebraicGeometry.Stack.isLocallySurjective_representingMap_of_isoClassMap`. Only that lemma is
needed: the comparison isomorphism of an object of `𝒱 ×_𝒳 𝒱` is free data, so an isomorphism of
objects of a fibre of `𝒰` suffices and the upgrade to an equality of arrows of the site by
`fiberArrow_eq_of_iso` is not used.

## Main definitions

* `AlgebraicGeometry.Stack.fiberArrow`: the arrow `T ⟶ U` of the site named by an object of the
  fibre over `T` of the category represented by `U`.

## Main results

* `AlgebraicGeometry.Stack.exists_fiber_glue_schemeFibredCategory`: objects of the fibres of a
  represented category fibred in groupoids glue along a coproduct decomposition of the base — the
  universal property of the coproduct, with no descent condition.
* `AlgebraicGeometry.Stack.exists_single_cover_fiber_image_of_locallyEssSurjOnFibers`: the
  gathering step. Local essential surjectivity on fibres of a 1-morphism between stacks is
  witnessed over a single surjective, flat, locally finitely presented morphism of the site.
* `AlgebraicGeometry.Stack.exists_single_cover_section_image_of_isGerbeOver`: the same for the
  section of a gerbe, which is the form the route above consumes.
* `AlgebraicGeometry.Stack.nonempty_iso_fiber_of_iso_section_image` and
  `AlgebraicGeometry.Stack.fiberArrow_eq_of_iso`: a section separates objects of a fibre — two
  objects of a fibre of `𝒰` with isomorphic `x`-images are isomorphic, and over a represented
  `𝒰` they therefore name the same arrow of the site.

## Implementation notes

The gathering is the argument of **Stacks 04TB** used for the isomorphism sheaf, and the four
general ingredients it needs are already in the library, in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheafAlgebraic`:
the covering sieve is refined to a family indexed by a set of size at most that of the base
(`AlgebraicGeometry.Stack.exists_small_fppf_refinement_in_sieve`, **Stacks 000X**), that family is
gathered into one object of the site (`AlgebraicGeometry.Stack.exists_coproduct_of_contains`), its
summands are monomorphisms with empty pairwise intersections
(`AlgebraicGeometry.Stack.coproduct_cover`), and over such a cover the isomorphisms of two objects
of a stack glue with no compatibility condition
(`AlgebraicGeometry.Stack.exists_iso_of_disjoint_cover`). The flatness, local finite presentation
and surjectivity of the gathered morphism are read on the underlying coproduct of schemes, exactly
as in `AlgebraicGeometry.Stack.exists_single_cover_presented_pair`.

What is *not* shared with that precedent is the gluing of the lifts themselves. There they are
points of the object space of a groupoid, so they glue because that space is a sheaf; here they
are objects of a fibre of `𝒰`, and gluing them in an arbitrary stack is the descent of an object
along `{Vᵢ ⟶ ∐ Vᵢ}`. That gluing is available, and with no descent datum to assemble:
`CategoryTheory.Functor.exists_fiber_glue_of_disjointCover_of_isStack`, in
`StacksFrontier.AlgebraicGeometry.Stacks.CoproductOneMorphism`, glues objects of the fibres of any
stack along a covering family of monomorphisms with empty pairwise overlaps, which
`{Vᵢ ⟶ ∐ Vᵢ}` is, and that is what the gathering step below uses — so its source may be any
stack, in particular the algebraic stack of an algebraic space, which is the generality
**Stacks 06QG** part (3) is stated at. When `𝒰` is *represented* the gluing is cheaper still and
needs no stack condition at all: an object of the fibre over `Vᵢ` is an arrow `Vᵢ ⟶ U`, and the
arrows glue by the universal property of the coproduct; that is
`exists_fiber_glue_schemeFibredCategory`, kept because it is a strictly weaker hypothesis.

The comparison of the glued object's `x`-image with the restriction of `ξ` uses
`CategoryTheory.Functor.mapPullbackFiberIso'`, which carries the chosen pullback through the
functor on fibres, and `CategoryTheory.Functor.pullbackFiberCompIso'`, which contracts an
iterated chosen pullback.

## References

* [Stacks Project, Tag 000X](https://stacks.math.columbia.edu/tag/000X)
* [Stacks Project, Tag 04TB](https://stacks.math.columbia.edu/tag/04TB)
* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
* [Stacks Project, Tag 06P2](https://stacks.math.columbia.edu/tag/06P2)
* [Stacks Project, Tag 06PZ](https://stacks.math.columbia.edu/tag/06PZ)
* [Stacks Project, Tag 06Q8](https://stacks.math.columbia.edu/tag/06Q8)
* [Stacks Project, Tag 06QG](https://stacks.math.columbia.edu/tag/06QG)
* [Stacks Project, Tag 06QI](https://stacks.math.columbia.edu/tag/06QI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The category represented by `U` is fibred over the site, being fibred in groupoids. -/
local instance instIsFibered_schemeFibredCategory (U : BigFppfOver B S hS) :
    (schemeFibredCategory B S hS U).val.p.IsFibered :=
  (schemeFibredCategory B S hS U).isFiberedInGroupoids.isFibered

/-- **Objects of the fibres of a represented category fibred in groupoids glue along a coproduct
decomposition of the base.** An object of the fibre of the category represented by `U` over `X i`
is an arrow `X i ⟶ U` of the site, so a family of them over the summands of a coproduct `V` is
amalgamated by the universal property of the coproduct, and the chosen pullback of the
amalgamation along a summand inclusion is isomorphic in the fibre to the given object, both being
cartesian lifts of that inclusion. No descent condition enters. -/
theorem exists_fiber_glue_schemeFibredCategory
    {U : BigFppfOver B S hS} {I : Type u} {X : I → BigFppfOver B S hS}
    {V : BigFppfOver B S hS} {j : ∀ i, X i ⟶ V}
    (hV : Limits.IsColimit (Limits.Cofan.mk V j))
    (z : ∀ i, (schemeFibredCategory B S hS U).val.p.Fiber (X i)) :
    ∃ zz : (schemeFibredCategory B S hS U).val.p.Fiber V,
      ∀ i, Nonempty (pullbackFiber (schemeFibredCategory B S hS U).val.p zz (j i) ≅ z i) := by
  classical
  have h₂ : ∀ i, ((z i).1.left : BigFppfOver B S hS) = X i := fun i => (z i).2
  obtain ⟨d, hd⟩ : ∃ d : V ⟶ U, ∀ i, j i ≫ d = eqToHom (h₂ i).symm ≫ (z i).1.hom :=
    ⟨Limits.Cofan.IsColimit.desc hV (fun i => eqToHom (h₂ i).symm ≫ (z i).1.hom),
      fun i => Limits.Cofan.IsColimit.fac hV _ i⟩
  refine ⟨Functor.Fiber.mk
    (p := (schemeFibredCategory B S hS U).val.p) (a := Over.mk d) rfl, fun i => ?_⟩
  have hw : (eqToHom (h₂ i) ≫ j i) ≫ d = (z i).1.hom := by
    rw [Category.assoc, hd i, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  let φ : (z i).1 ⟶ (Over.mk d : Over U) := Over.homMk (eqToHom (h₂ i) ≫ j i) hw
  have hφ : (schemeFibredCategory B S hS U).val.p.IsHomLift (j i) φ := by
    refine IsHomLift.of_fac' _ (j i) φ (z i).2 rfl ?_
    change eqToHom (h₂ i) ≫ j i = eqToHom (h₂ i) ≫ j i ≫ eqToHom rfl
    simp
  have : (schemeFibredCategory B S hS U).val.p.IsStronglyCartesian (j i) φ :=
    (schemeFibredCategory B S hS U).isFiberedInGroupoids.isStronglyCartesian_homLift (j i) φ
  exact ⟨fiberIsoOfCartesian (j i)
    (IsPreFibered.pullbackMap (Functor.Fiber.mk
      (p := (schemeFibredCategory B S hS U).val.p) (a := Over.mk d) rfl).2 (j i)) φ
    (IsPreFibered.pullbackMap.IsCartesian _ _)
    (Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ (j i) φ)⟩

/-- A morphism which, precomposed with an isomorphism out of the coproduct of an fppf covering,
is the induced map out of that coproduct is flat, locally of finite presentation and surjective. -/
theorem flat_locallyOfFinitePresentation_surjective_of_iso_comp_eq_sigmaDesc
    {X Y : Scheme.{u}} (W : FppfCovering.{u} X) (e : ∐ W.X ≅ Y) {g : Y ⟶ X}
    (h : e.hom ≫ g = Limits.Sigma.desc W.f) :
    Flat g ∧ LocallyOfFinitePresentation g ∧ Surjective g := by
  have : ∀ i, Flat (W.f i) := W.flat
  have : ∀ i, LocallyOfFinitePresentation (W.f i) := W.lfp
  have : MorphismProperty.RespectsIso (@Flat.{u}) := Flat.isStableUnderBaseChange.respectsIso
  have : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  have : MorphismProperty.RespectsIso (@LocallyOfFinitePresentation.{u}) :=
    locallyOfFinitePresentation_isStableUnderBaseChange.respectsIso
  refine ⟨(MorphismProperty.cancel_left_of_respectsIso (@Flat.{u}) e.hom _).mp ?_,
    (MorphismProperty.cancel_left_of_respectsIso (@LocallyOfFinitePresentation.{u}) e.hom _).mp ?_,
    ⟨fun t => ?_⟩⟩
  · rw [h]
    infer_instance
  · rw [h]
    exact IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation.{u}) W.lfp
  · obtain ⟨i, a, ha⟩ := W.jointly_surjective t
    refine ⟨e.hom ((Limits.Sigma.ι W.X i) a), ?_⟩
    exact (congrArg (fun q : W.X i ⟶ X => q a)
      (show Limits.Sigma.ι W.X i ≫ e.hom ≫ g = W.f i by rw [h, Limits.Sigma.ι_comp_desc])).trans ha

/-- **The gathering step.** Let `x : 𝒰 ⟶ 𝒳` be a 1-morphism of categories fibred in groupoids
over the big fppf site of `S` whose source satisfies descent and whose target has `Mor`-sheaves,
and suppose `x` is locally essentially surjective on fibres. Then for every object `ξ` of a fibre
of `𝒳` there are a *single* surjective, flat, locally finitely presented morphism `b : V ⟶ T` of
the site and an object `z` of the fibre of `𝒰` over `V` whose `x`-image is isomorphic to the
restriction of `ξ` along `b`.

The covering sieve the hypothesis produces is refined to a size-bounded family, that family is
gathered into one object of the site, the objects of `𝒰` it carries are amalgamated over the
resulting disjoint cover by `CategoryTheory.Functor.exists_fiber_glue_of_disjointCover_of_isStack`
— which needs no compatibility datum, the pairwise overlaps of a disjoint cover being covered by
the empty sieve — and the isomorphisms glue over the same cover because `𝒳` has `Mor`-sheaves. -/
theorem exists_single_cover_fiber_image_of_locallyEssSurjOnFibers
    {𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    [𝒳.val.p.IsFibered]
    (x : 𝒰 ⟶ 𝒳)
    (h𝒰 : 𝒰.val.p.IsStack (BigFppfOver.topology B S hS))
    (hmor : ∀ (T : BigFppfOver B S hS) (a b : 𝒳.val.p.Fiber T),
      𝒳.val.p.IsMorSheaf (BigFppfOver.topology B S hS) T a b)
    (hloc : Functor.LocallyEssSurjOnFibers 𝒳.isFiberedInGroupoids.isFibered
      (CatFiberedInGroupoids.homFunctor_comp_p x) (BigFppfOver.topology B S hS))
    (T : BigFppfOver B S hS) (ξ : 𝒳.val.p.Fiber T) :
    ∃ (V : BigFppfOver B S hS) (b : V ⟶ T),
      Flat (B.inclusion.map b.left) ∧
      LocallyOfFinitePresentation (B.inclusion.map b.left) ∧
      Surjective (B.inclusion.map b.left) ∧
      ∃ z : 𝒰.val.p.Fiber V,
        Nonempty ((Fiber.mapOfComp 𝒰.val.p 𝒳.val.p
            (CatFiberedInGroupoids.homFunctor x)
            (CatFiberedInGroupoids.homFunctor_comp_p x) V).obj z ≅
          pullbackFiber 𝒳.val.p ξ b) := by
  classical
  have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have : 𝒰.val.p.IsFibered := 𝒰.isFiberedInGroupoids.isFibered
  obtain ⟨R, hR, hl⟩ := hloc T ξ
  obtain ⟨W, hcard, hsize, hmem⟩ := exists_small_fppf_refinement_in_sieve B S hS hR
  have hW i : B.Contains (W.X i) := (hsize i).trans_lt T.left.property
  let wi i : B.obj (hW i) ⟶ T.left := B.inclusion.preimage (W.f i)
  let Wi i : BigFppfOver B S hS := Over.mk (wi i ≫ T.hom)
  let fi i : Wi i ⟶ T := Over.homMk (wi i)
  have hfi i : R (fi i) := by
    have hi := hmem i (hW i)
    rwa [Sieve.overEquiv_iff] at hi
  have hsum : B.Contains (∐ (fun i => (BigFppfOver.toScheme B S hS).obj (Wi i))) :=
    (schemeSize_coproduct_le W.X T.left.obj.size T.left.obj.aleph0_le_size hcard
      hsize).trans_lt T.left.property
  obtain ⟨V, j, ⟨hV⟩, e, he⟩ := exists_coproduct_of_contains B S hS Wi hsum
  obtain ⟨hm, hj, hd⟩ := coproduct_cover B S hS Wi V j e he
  let f : V ⟶ T := Limits.Cofan.IsColimit.desc hV fi
  have hfac i : j i ≫ f = fi i := Limits.Cofan.IsColimit.fac hV fi i
  have hmap : e.hom ≫ B.inclusion.map f.left = Limits.Sigma.desc W.f := by
    refine Limits.Sigma.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, he i]
    change B.inclusion.map (j i).left ≫ B.inclusion.map f.left = _
    rw [← B.inclusion.map_comp]
    change B.inclusion.map (j i ≫ f).left = _
    rw [hfac, Limits.Sigma.ι_comp_desc]
    exact B.inclusion.map_preimage (X := B.obj (hW i)) (Y := T.left) (W.f i)
  obtain ⟨hfFlat, hfLfp, hfSurj⟩ :=
    flat_locallyOfFinitePresentation_surjective_of_iso_comp_eq_sigmaDesc W e hmap
  -- the local lifts, glued
  choose zi ezi using fun i => hl (fi i) (hfi i)
  obtain ⟨zz, hzz⟩ :=
    CategoryTheory.Functor.exists_fiber_glue_of_disjointCover_of_isStack h𝒰 hm hj
      (fun {_ _} hik => hd hik) zi
  refine ⟨V, f, hfFlat, hfLfp, hfSurj, zz, ?_⟩
  refine exists_iso_of_disjoint_cover (BigFppfOver.topology B S hS) 𝒳.val.p hmor
    𝒳.isFiberedInGroupoids Wi V j hm hj hd _ _ (fun i => ?_)
  exact ⟨Functor.mapPullbackFiberIso' (𝒳.isFiberedInGroupoids.isFibredOneMorphism
      (CatFiberedInGroupoids.homFunctor_comp_p x)) zz (j i) ≪≫
    (Fiber.mapOfComp _ _ _ (CatFiberedInGroupoids.homFunctor_comp_p x) (Wi i)).mapIso
      (hzz i).some ≪≫
    (ezi i).some ≪≫ (Functor.pullbackFiberCompIso' ξ f (j i) (fi i) (hfac i)).symm⟩

/-- The arrow of the site named by an object of a fibre of the category represented by `U`. -/
def fiberArrow {U T : BigFppfOver B S hS}
    (z : (schemeFibredCategory B S hS U).val.p.Fiber T) : T ⟶ U :=
  eqToHom (show ((z.1.left : BigFppfOver B S hS)) = T from z.2).symm ≫ z.1.hom

/-- Isomorphic objects of a fibre of the category represented by `U` name the same arrow. -/
theorem fiberArrow_eq_of_iso {U T : BigFppfOver B S hS}
    {z z' : (schemeFibredCategory B S hS U).val.p.Fiber T} (e : z ≅ z') :
    fiberArrow z = fiberArrow z' := by
  have h : ((z.1.left : BigFppfOver B S hS)) = T := z.2
  have h' : ((z'.1.left : BigFppfOver B S hS)) = T := z'.2
  have : (schemeFibredCategory B S hS U).val.p.IsHomLift (𝟙 T) e.hom.1 := e.hom.2
  have hlift : e.hom.1.left = eqToHom h ≫ 𝟙 T ≫ eqToHom h'.symm :=
    IsHomLift.fac' (schemeFibredCategory B S hS U).val.p (𝟙 T) e.hom.1
  have hw : e.hom.1.left ≫ z'.1.hom = z.1.hom := Over.w e.hom.1
  change eqToHom h.symm ≫ z.1.hom = eqToHom h'.symm ≫ z'.1.hom
  rw [← hw, hlift]
  simp

/-- **A section separates the objects of a fibre.** If `x : 𝒴 ⟶ 𝒳` is a section of `π : 𝒳 ⟶ 𝒴`,
then two objects of a fibre of `𝒴` whose `x`-images are isomorphic in the fibre of `𝒳` are
themselves isomorphic: applying `π` to the isomorphism and conjugating by the components of the
2-isomorphism `x ≫ π ≅ 𝟙 𝒴` gives a vertical morphism between them, and the fibres of `𝒴` are
groupoids.

With `fiberArrow_eq_of_iso` this is the local surjectivity input of the route described in the
module documentation: a point of `V` whose image under `q ≅ g ≫ x` agrees with the `x`-image of a
point of `U` has the *same* image in `U` under `g`. -/
theorem nonempty_iso_fiber_of_iso_section_image
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (π : 𝒳 ⟶ 𝒴) (x : 𝒴 ⟶ 𝒳) (hx : x ≫ π ≅ 𝟙 𝒴)
    {T : BigFppfOver B S hS} (z z' : 𝒴.val.p.Fiber T)
    (e : (Fiber.mapOfComp 𝒴.val.p 𝒳.val.p (CatFiberedInGroupoids.homFunctor x)
          (CatFiberedInGroupoids.homFunctor_comp_p x) T).obj z ≅
        (Fiber.mapOfComp 𝒴.val.p 𝒳.val.p (CatFiberedInGroupoids.homFunctor x)
          (CatFiberedInGroupoids.homFunctor_comp_p x) T).obj z') :
    Nonempty (z ≅ z') := by
  have hlift : ∀ {F G : 𝒴 ⟶ 𝒴} (t : F ⟶ G) (w : 𝒴.val.p.Fiber T),
      𝒴.val.p.IsHomLift (𝟙 T) (t.hom.toNatTrans.app w.1) := fun t w => by
    have hi := CatFiberedInGroupoids.isHomLift_app t w.1
    rwa [w.2] at hi
  have he : 𝒳.val.p.IsHomLift (𝟙 T) e.hom.1 := e.hom.2
  have h2 : 𝒴.val.p.IsHomLift (𝟙 T) (π.hom.toFunctor.map e.hom.1) :=
    (Functor.isHomLift_comp_iff (CatFiberedInGroupoids.homFunctor π) 𝒴.val.p (𝟙 T)
      e.hom.1).1 (by rwa [CatFiberedInGroupoids.homFunctor_comp_p π])
  have hobj : ∀ w : 𝒴.val.p.Fiber T,
      𝒴.val.p.obj (π.hom.toFunctor.obj (x.hom.toFunctor.obj w.1)) = T := fun w =>
    (BasedFunctor.w_obj π.hom _).trans ((BasedFunctor.w_obj x.hom w.1).trans w.2)
  let n1 : z ⟶ (Functor.Fiber.mk (hobj z) : 𝒴.val.p.Fiber T) :=
    ⟨hx.inv.hom.toNatTrans.app z.1, hlift hx.inv z⟩
  let n2 : (Functor.Fiber.mk (hobj z) : 𝒴.val.p.Fiber T) ⟶ Functor.Fiber.mk (hobj z') :=
    ⟨π.hom.toFunctor.map e.hom.1, h2⟩
  let n3 : (Functor.Fiber.mk (hobj z') : 𝒴.val.p.Fiber T) ⟶ z' :=
    ⟨hx.hom.hom.toNatTrans.app z'.1, hlift hx.hom z'⟩
  have : IsGroupoid (𝒴.val.p.Fiber T) := 𝒴.isFiberedInGroupoids.fiber_isGroupoid T
  exact ⟨asIso (n1 ≫ n2 ≫ n3)⟩

/-- **A section of a gerbe hits every object over a single fppf cover.** Let `π : 𝒳 ⟶ 𝒰` make
the algebraic stack `𝒳` a gerbe over a category `𝒰` fibred in groupoids which satisfies descent,
and let `x : 𝒰 ⟶ 𝒳` be a section of `π`. Then every object `ξ` of a fibre of `𝒳` is, after one
surjective, flat, locally finitely presented morphism `b : V ⟶ T` of the site, the `x`-image of
an object of `𝒰` over `V`.

This is `exists_single_cover_fiber_image_of_locallyEssSurjOnFibers` fed with
`AlgebraicGeometry.Stack.locallyEssSurjOnFibers_of_section_of_isGerbeOver`, which is where the
gerbe hypothesis is used, and with the `Mor`-sheaf condition supplied by the algebraicity of `𝒳`.
It is the half of the construction of the surjective, flat, locally finitely presented
1-morphism `q : 𝒱 ⟶ 𝒳` factoring through `x` that this file proves; the other half — the passage
from the object `z` to the 1-morphism `g : 𝒱 ⟶ 𝒰` it names by the 2-Yoneda lemma, together with
the 2-isomorphism `q ≅ g ≫ x` — is
`AlgebraicGeometry.Stack.exists_single_cover_section_factorisation_of_isGerbeOver`. -/
theorem exists_single_cover_section_image_of_isGerbeOver
    {𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    [𝒳.val.p.IsFibered]
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒰 : 𝒰.val.p.IsStack (BigFppfOver.topology B S hS))
    (π : 𝒳 ⟶ 𝒰) (x : 𝒰 ⟶ 𝒳) (hx : x ≫ π ≅ 𝟙 𝒰)
    (hπ : CategoryTheory.IsGerbeOver (BigFppfOver.topology B S hS)
      𝒰.val.p (CatFiberedInGroupoids.homFunctor π))
    (T : BigFppfOver B S hS) (ξ : 𝒳.val.p.Fiber T) :
    ∃ (V : BigFppfOver B S hS) (b : V ⟶ T),
      Flat (B.inclusion.map b.left) ∧
      LocallyOfFinitePresentation (B.inclusion.map b.left) ∧
      Surjective (B.inclusion.map b.left) ∧
      ∃ z : 𝒰.val.p.Fiber V,
        Nonempty ((Fiber.mapOfComp 𝒰.val.p 𝒳.val.p
            (CatFiberedInGroupoids.homFunctor x)
            (CatFiberedInGroupoids.homFunctor_comp_p x) V).obj z ≅
          pullbackFiber 𝒳.val.p ξ b) := by
  obtain ⟨-, h𝒳stack, -, -⟩ := id h𝒳
  exact exists_single_cover_fiber_image_of_locallyEssSurjOnFibers x h𝒰
    (fun W a b => h𝒳stack.1.isMorSheaf W a b)
    (locallyEssSurjOnFibers_of_section_of_isGerbeOver π x hx hπ) T ξ

end AlgebraicGeometry.Stack

end
