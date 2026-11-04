module

public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeCharacterization
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionTwoYoneda
public import StacksFrontier.AlgebraicGeometry.Stacks.JointlySurjectiveFlatFppfLocalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.CategoryTheory.Sites.Stack.LocallyEssSurjOnFibersComp
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Clause (2) of Stacks 06QH, and the reduction steps of (1) ⟹ (2)

Stacks 06QH characterises gerbes: a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks makes `𝒳` a
gerbe over `𝒴` (1) if and only if (2) there are an algebraic space `U`, a surjective, flat,
locally finitely presented `U ⟶ 𝒴` and a flat, locally finitely presented group algebraic space
`G` over `U` with `𝒳 ×_𝒴 U ≅ [U/G]` over `U`, for the trivial action of `G` on `U`.
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeCharacterization` proves the implication (2) ⟹ (1).
This file bundles clause (2) as a property of the 1-morphism and proves the two reduction steps
of the proof of the converse. The converse is completed, and the two implications are assembled
into the equivalence
`AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_iff_hasClassifyingFppfCover`, in
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeClassifyingFppfCover`.

**(1) ⟹ (2).** The source argues in three steps: pick a scheme `V` with a surjective smooth
`V ⟶ 𝒴`, which reduces the claim to a gerbe over a scheme; replace `V` by the member `U` of an
fppf covering of `V` over which the fibre category of `𝒳` is nonempty, so that the gerbe acquires
a section; and apply **Stacks 06QG** to a gerbe over a scheme with a section. The first two steps
are proved here; the third is in
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeClassifyingFppfCover`.

The first is `exists_isSurjective_isFlat_isLocallyOfFinitePresentation_schemeStack` together with
`hasClassifyingFppfCover_of_baseChange`, the statement that clause (2) descends along a
surjective, flat, locally finitely presented base change, which is what both of the source's
replacements amount to.

The second is `exists_isSurjective_isFlat_isLfp_section_of_isGerbeOver`, and in the form a
consumer uses it `exists_section_snd_of_isGerbeOver`: a gerbe acquires a section after a single
surjective, flat, locally finitely presented 1-morphism onto its target out of the algebraic
stack of an object of the site. Neither a coproduct of algebraic stacks nor the descent of an
object of `𝒳` along `{Vᵢ ⟶ ∐ Vᵢ}` is needed for it, although the source's phrasing suggests
otherwise: the gathering of the gerbe's covering sieve into *one* covering morphism of the site
can be carried out inside a smooth scheme atlas `a : 𝒲 ⟶ 𝒳` of `𝒳`, where an object of a fibre is
an arrow of the site and the arrows glue by the universal property of the coproduct with no
descent datum. The gathering is
`AlgebraicGeometry.Stack.exists_single_cover_fiber_image_of_locallyEssSurjOnFibers`, applied to
`a ≫ f`, which is locally essentially surjective on fibres because `a` and `f` separately are
(`locallyEssSurjOnFibers_of_isSurjective_isFlat_isLfp`,
`locallyEssSurjOnFibers_of_isGerbeOver`, and **Stacks 06DV**
`CategoryTheory.Functor.locallyEssSurjOnFibers_comp_iff`).

The third step is Stacks 06QG applied to the section the second step produces, read with its
equivalence over the base rather than over the site; it is
`exists_grpObj_nonempty_equivalenceOver_quotientStackToBase_of_section_of_isGerbeOver`
of `StacksFrontier.AlgebraicGeometry.Stacks.GerbeClassifyingFppfCover`. The covering 1-morphism the
implication is actually assembled from is not the one produced here but the one of
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_space_section_snd_of_isGerbeOver`, whose base is
an *algebraic space* rather than an object of the site, which is the kind of base clause (2)
names.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasClassifyingFppfCover`: clause (2) of Stacks 06QH,
  as a property of the 1-morphism.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_of_hasClassifyingFppfCover`: **Stacks
  06QH**, the implication (2) ⟹ (1) with clause (2) bundled, which is the form a consumer uses.
* `AlgebraicGeometry.Stack.AlgebraicStacks.hasClassifyingFppfCover_of_baseChange`: clause (2)
  descends along a surjective, flat, locally finitely presented base change.
* `exists_isSurjective_isFlat_isLocallyOfFinitePresentation_schemeStack`:
  every algebraic stack is covered by a scheme through a surjective, flat, locally finitely
  presented 1-morphism.
* `AlgebraicGeometry.Stack.AlgebraicStacks.locallyEssSurjOnFibers_of_isGerbeOver` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.locallyEssSurjOnFibers_of_isSurjective_isFlat_isLfp`:
  a gerbe 1-morphism, and a surjective flat locally finitely presented 1-morphism, are locally
  essentially surjective on fibres.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_isSurjective_isFlat_isLfp_section_of_isGerbeOver`
  and `AlgebraicGeometry.Stack.AlgebraicStacks.exists_section_snd_of_isGerbeOver`: the second
  step of the source's proof of (1) ⟹ (2) — a gerbe acquires a section after one surjective,
  flat, locally finitely presented 1-morphism onto its target out of the algebraic stack of an
  object of the site.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 041T](https://stacks.math.columbia.edu/tag/041T)
* [Stacks Project, Tag 041W](https://stacks.math.columbia.edu/tag/041W)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04TA](https://stacks.math.columbia.edu/tag/04TA)
* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
* [Stacks Project, Tag 04ZT](https://stacks.math.columbia.edu/tag/04ZT)
* [Stacks Project, Tag 06DV](https://stacks.math.columbia.edu/tag/06DV)
* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
* [Stacks Project, Tag 06P0](https://stacks.math.columbia.edu/tag/06P0)
* [Stacks Project, Tag 06P1](https://stacks.math.columbia.edu/tag/06P1)
* [Stacks Project, Tag 06PF](https://stacks.math.columbia.edu/tag/06PF)
* [Stacks Project, Tag 06PJ](https://stacks.math.columbia.edu/tag/06PJ)
* [Stacks Project, Tag 06PK](https://stacks.math.columbia.edu/tag/06PK)
* [Stacks Project, Tag 06PL](https://stacks.math.columbia.edu/tag/06PL)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
* [Stacks Project, Tag 06PX](https://stacks.math.columbia.edu/tag/06PX)
* [Stacks Project, Tag 06Q3](https://stacks.math.columbia.edu/tag/06Q3)
* [Stacks Project, Tag 06QF](https://stacks.math.columbia.edu/tag/06QF)
* [Stacks Project, Tag 06QG](https://stacks.math.columbia.edu/tag/06QG)
* [Stacks Project, Tag 06QH](https://stacks.math.columbia.edu/tag/06QH)
* [Stacks Project, Tag 07AN](https://stacks.math.columbia.edu/tag/07AN)
* [Stacks Project, Tag 0DNP](https://stacks.math.columbia.edu/tag/0DNP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

/-! ### Clause (2) as a property of a 1-morphism -/

/-- **Clause (2) of Stacks 06QH**, as a property of a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks
over `S`: there are an algebraic space `U` over `S`, a surjective, flat, locally finitely
presented 1-morphism `g : U ⟶ 𝒴`, and a group algebraic space `G` over `U` which is flat and
locally of finite presentation over `U`, such that the base change `𝒳 ×_𝒴 U ⟶ U` of `f` along
`g` is isomorphic, as an object over `U`, to the classifying stack `[U/G]` of the trivial action
of `G` on `U`.

The base change is read at an arbitrary 2-fibre-product square over the cospan `(f, g)`, as in
Stacks 06QE and 06QF, so that the property does not depend on a choice of model; the condition at
one such square implies it at every other, since the two apexes are equivalent over `U`. -/
abbrev HasClassifyingFppfCover (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ (U : AlgebraicSpaces B S hS) (g : ofAlgebraicSpace.{u, w} B S hS U ⟶ 𝒴),
    Stack.IsSurjective B S hS g ∧ IsFlat B S hS g ∧ IsLocallyOfFinitePresentation B S hS g ∧
      ∃ (G : Over U.obj) (_ : GrpObj G) (hG : IsAlgebraicSpace B S hS G.left),
        Space.IsFlat B S hS G.hom ∧ Space.IsLocallyOfFinitePresentation B S hS G.hom ∧
          ∃ (A : Space.ActionGroupoidConstruction U G (𝟙_ (Over U.obj)) hG U.property)
            (P : Bicategory.TwoCommSq f g) (_ : Bicategory.IsTwoFibreProduct P),
            Nonempty (StacksRepresentableCFG.EquivalenceOver
              (CatFiberedInGroupoids.homFunctor P.snd.hom)
              (quotientStackToBase A.groupoid).toFunctor)

/-- **Stacks 06QH, the implication (2) ⟹ (1), packaged.** A 1-morphism of algebraic stacks over
`S` which fppf-locally on its target is the classifying stack of a flat, locally finitely
presented group algebraic space makes its source a gerbe over its target.

This is `AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_of_equivalenceOver_quotientStack`
with the data of clause (2) bundled into `HasClassifyingFppfCover`, which is the form a consumer
that has clause (2) as a hypothesis — or has just produced it — can use. -/
@[stacks 06QH "(2) implies (1), with clause (2) bundled"]
theorem isGerbeOver_of_hasClassifyingFppfCover
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h : HasClassifyingFppfCover.{u, w} B S hS f) :
    IsGerbeOver B S hS f := by
  obtain ⟨U, g, hgsurj, hgflat, hglfp, G, instG, hG, hGflat, hGlfp, A, P, hP, ⟨e⟩⟩ := h
  exact isGerbeOver_of_equivalenceOver_quotientStack B S hS f U g hgsurj hgflat hglfp G hG
    hGflat hGlfp A P hP e

/-- **The reduction step of Stacks 06QH, (1) ⟹ (2): clause (2) descends along a surjective, flat,
locally finitely presented base change.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks
over `S` and let `h : 𝒴' ⟶ 𝒴` be surjective, flat and locally of finite presentation. If the base
change of `f` along `h` satisfies clause (2) of Stacks 06QH, then so does `f`.

This is the step by which the source's proof of (1) ⟹ (2) replaces `𝒴` first by a scheme
smoothly covering it and then by the member of an fppf covering of that scheme: the covering
1-morphism `g : U ⟶ 𝒴'` produced for the base change is composed with `h`, which keeps it
surjective (**Stacks 04ZT**), flat (**Stacks 06PX**) and locally of finite presentation
(**Stacks 06Q3**), and the two 2-fibre-product squares are pasted (**Stacks 003Q**), the pasted
rectangle having the *same* apex and second leg as the inner square — so the identification of
that apex with `[U/G]` over `U` is carried over unchanged. -/
@[stacks 06QH "(1) implies (2): the reduction along a surjective, flat, locally finitely \
presented base change"]
theorem hasClassifyingFppfCover_of_baseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (h : 𝒴' ⟶ 𝒴)
    (hhsurj : Stack.IsSurjective B S hS h) (hhflat : IsFlat B S hS h)
    (hhlfp : IsLocallyOfFinitePresentation B S hS h)
    (Q : Bicategory.TwoCommSq f h) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hbc : HasClassifyingFppfCover.{u, w} B S hS Q.snd) :
    HasClassifyingFppfCover.{u, w} B S hS f := by
  obtain ⟨U, g, hgsurj, hgflat, hglfp, G, instG, hG, hGflat, hGlfp, A, P, hP, e⟩ := hbc
  exact ⟨U, g ≫ h, Stack.isSurjective_comp B S hS g h hgsurj hhsurj,
    isFlat_comp B S hS g h hgflat hhflat,
    isLocallyOfFinitePresentation_comp B S hS g h hglfp hhlfp,
    G, instG, hG, hGflat, hGlfp, A, Q.paste P,
    Bicategory.isTwoFibreProduct_paste hQ hP, e⟩

/-- **Every algebraic stack over `S` is covered by a scheme through a surjective, flat, locally
finitely presented 1-morphism.** This is the first step of the source's proof of
Stacks 06QH (1) ⟹ (2), which picks a scheme `V` with a surjective smooth 1-morphism `V ⟶ 𝒴` in
order to reduce to a gerbe over a scheme: a smooth surjective scheme presentation exists because
`𝒴` is an algebraic stack, and a smooth 1-morphism is flat (**Stacks 04TA**) and locally of
finite presentation (**Stacks 0DNP**).

Together with `hasClassifyingFppfCover_of_baseChange` it reduces clause (2) of Stacks 06QH for
an arbitrary target to clause (2) for a target which is a scheme. -/
theorem exists_isSurjective_isFlat_isLocallyOfFinitePresentation_schemeStack
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒴 : Stack.AlgebraicStacks.{u, w} B S hS) :
    ∃ (V : BigFppfOver B S hS) (h : Stack.schemeStack.{u, w} B S hS V ⟶ 𝒴),
      Stack.IsSurjective B S hS h ∧ IsFlat B S hS h ∧
        IsLocallyOfFinitePresentation B S hS h := by
  obtain ⟨V, a, hasm, hasurj⟩ := Stack.exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒴
  exact ⟨V, a, hasurj, isFlat_of_isSmooth B S hS a hasm,
    isLocallyOfFinitePresentation_of_isSmooth B S hS a hasm⟩

/-! ### The fppf-local section of a gerbe -/

/-- The projection of an algebraic stack over `S` to the big fppf site is a fibred functor. -/
local instance instIsFibered_algebraicStack (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) :
    𝒵.val.val.p.IsFibered :=
  𝒵.val.isFiberedInGroupoids.isFibered

/-- A morphism lifting `k` into an object of a fibre of the target of a 1-morphism of categories
fibred in groupoids exhibits a fibre object of the source isomorphic to the chosen restriction. -/
private theorem exists_fiber_mapOfComp_iso_pullbackFiber
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (π : 𝒳 ⟶ 𝒴)
    [𝒴.val.p.IsFibered] {U V : BigFppfOver B S hS} (y : 𝒴.val.p.Fiber U) (k : V ⟶ U) (x : 𝒳.val.1)
    (ψ : (CatFiberedInGroupoids.homFunctor π).obj x ⟶ y.1) (hψ : 𝒴.val.p.IsHomLift k ψ) :
    ∃ z : 𝒳.val.p.Fiber V, Nonempty ((Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor π) (CatFiberedInGroupoids.homFunctor_comp_p π) V).obj z ≅
        Functor.pullbackFiber 𝒴.val.p y k) := by
  have hx : 𝒳.val.p.obj x = V := by
    rw [← CatFiberedInGroupoids.homFunctor_comp_p π]
    exact IsHomLift.domain_eq 𝒴.val.p k ψ
  exact ⟨⟨x, hx⟩, ⟨Functor.fiberIsoPullbackFiber 𝒴.val.p y k _ ψ
    (𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift k ψ)⟩⟩

/-- **A gerbe 1-morphism is locally essentially surjective on fibres.** Clause (2)(a) of
**Stacks 06P1** — the field `locally_essSurj` of `CategoryTheory.IsGerbeOver` — gives an object of
a fibre of the target, along the members of a covering sieve of its base, a *morphism* from the
image of an object of the source. In a category fibred in groupoids every such morphism is
strongly cartesian, so its domain is the chosen restriction
(`CategoryTheory.Functor.fiberIsoPullbackFiber`), which is the form
`CategoryTheory.Functor.LocallyEssSurjOnFibers` asks for. -/
theorem locallyEssSurjOnFibers_of_isGerbeOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (π : 𝒳 ⟶ 𝒴)
    (hπ : CategoryTheory.IsGerbeOver (BigFppfOver.topology B S hS) 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor π)) :
    Functor.LocallyEssSurjOnFibers 𝒴.isFiberedInGroupoids.isFibered
      (CatFiberedInGroupoids.homFunctor_comp_p π) (BigFppfOver.topology B S hS) := by
  have : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  intro U y
  obtain ⟨R, hR, hcov⟩ := hπ.locally_essSurj y.1 y.2
  refine ⟨R, hR, fun V g hg => ?_⟩
  obtain ⟨x, ψ, hψ⟩ := hcov g hg
  exact exists_fiber_mapOfComp_iso_pullbackFiber B S hS π y g x ψ hψ

/-- **A surjective, flat, locally finitely presented 1-morphism of algebraic stacks over `S` is
locally essentially surjective on fibres.** This is **Stacks 07AN**
(`AlgebraicGeometry.Stack.exists_fppfCovering_fibre_lift_of_family`) at a one-member family: an
object of a fibre of the target acquires, along the members of a covering sieve of its base, a
morphism from the image of an object of the source, and that morphism is strongly cartesian
because the target is fibred in groupoids. -/
theorem locallyEssSurjOnFibers_of_isSurjective_isFlat_isLfp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒲 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (q : 𝒲 ⟶ 𝒵)
    (hqsurj : Stack.IsSurjective B S hS q) (hqflat : IsFlat B S hS q)
    (hqlfp : IsLocallyOfFinitePresentation B S hS q) :
    Functor.LocallyEssSurjOnFibers 𝒵.val.isFiberedInGroupoids.isFibered
      (CatFiberedInGroupoids.homFunctor_comp_p q.hom) (BigFppfOver.topology B S hS) := by
  have hjs : (Set.univ : Set (points B S hS 𝒵)) =
      ⋃ _ : Unit, Set.range (pointsMap B S hS q) := by
    rw [Set.iUnion_const, hqsurj.range_eq]
  intro U x
  obtain ⟨R, hR, hRlift⟩ := Stack.exists_fppfCovering_fibre_lift_of_family B S hS
    (𝒳 := fun _ : Unit => 𝒲) (𝒴 := 𝒵) (fun _ => q) (fun _ => hqflat) (fun _ => hqlfp) hjs U x
  refine ⟨R, hR, fun V k hk => ?_⟩
  obtain ⟨-, x₀, α, hα⟩ := hRlift hk
  exact exists_fiber_mapOfComp_iso_pullbackFiber B S hS q.hom x k x₀ α hα

/-- **A gerbe acquires a section after a single surjective, flat, locally finitely presented
1-morphism onto its target out of the algebraic stack of an object of the site.** Let
`f : 𝒳 ⟶ 𝒴` make `𝒳` a gerbe over `𝒴`. Then there are an object `U` of the big fppf site of `S`,
a surjective, flat and locally finitely presented `g : 𝒰 ⟶ 𝒴` and a 1-morphism `s : 𝒰 ⟶ 𝒳` with
`s ≫ f ≅ g`; equivalently, the base change of `f` along `g` admits a section.

This is the **second step** of the source's proof of Stacks 06QH (1) `⟹` (2): the replacement of
a smooth scheme cover `V ⟶ 𝒴` of the target by a member of an fppf covering of `V` over which
the fibre category of `𝒳` is nonempty. The source gathers the covering family produced by the
gerbe condition into its disjoint union; the argument here needs no coproduct of algebraic stacks
and no descent of an object of `𝒳`, because the gathering can be done inside a *smooth scheme
atlas* `a : 𝒲 ⟶ 𝒳` of `𝒳`, where an object of a fibre is an arrow of the site and the arrows glue
by the universal property of the coproduct
(`AlgebraicGeometry.Stack.exists_single_cover_fiber_image_of_locallyEssSurjOnFibers`).

Concretely: `a` is surjective, flat and locally of finite presentation, hence locally essentially
surjective on fibres (`locallyEssSurjOnFibers_of_isSurjective_isFlat_isLfp`), and so is `f`
(`locallyEssSurjOnFibers_of_isGerbeOver`), hence so is `a ≫ f` (**Stacks 06DV**,
`CategoryTheory.Functor.locallyEssSurjOnFibers_comp_iff`). Applied to the object of the fibre of
`𝒴` over `V` that a smooth scheme atlas `c : 𝒱 ⟶ 𝒴` evaluates to under the 2-Yoneda lemma, the
gathering gives one surjective, flat, locally finitely presented `b : U ⟶ V` of the site and an
object of the fibre of `𝒲` over `U` whose `a ≫ f`-image is the restriction along `b`; the 2-Yoneda
passage `AlgebraicGeometry.Stack.schemeMapFactorisationOfFiberImage` turns that object into an
arrow `U ⟶ W` of the site and the comparison into the 2-isomorphism
`schemeStackMap (U ⟶ W) ≫ (a ≫ f) ≅ schemeStackMap b ≫ c`.

The base here is the algebraic stack of an *object of the site*, which clause (2) cannot consume
directly; the implication (1) `⟹` (2) is assembled from the companion
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_space_section_snd_of_isGerbeOver`, whose base is
an algebraic space. -/
theorem exists_isSurjective_isFlat_isLfp_section_of_isGerbeOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsGerbeOver B S hS f) :
    ∃ (U : BigFppfOver B S hS) (g : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒴)
      (s : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒳),
      Stack.IsSurjective B S hS g ∧ IsFlat B S hS g ∧
        IsLocallyOfFinitePresentation B S hS g ∧ Nonempty (s ≫ f ≅ g) := by
  obtain ⟨V, c, hcsm, hcsurj⟩ := Stack.exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒴
  obtain ⟨W, a, hasm, hasurj⟩ := Stack.exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  have hloca := locallyEssSurjOnFibers_of_isSurjective_isFlat_isLfp B S hS a hasurj
    (isFlat_of_isSmooth B S hS a hasm) (isLocallyOfFinitePresentation_of_isSmooth B S hS a hasm)
  have hlocf := locallyEssSurjOnFibers_of_isGerbeOver B S hS f.hom hf
  have hFa := 𝒳.val.isFiberedInGroupoids.isFibredOneMorphism
    (CatFiberedInGroupoids.homFunctor_comp_p a.hom)
  have hGf := 𝒴.val.isFiberedInGroupoids.isFibredOneMorphism
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
  have hlocaf : Functor.LocallyEssSurjOnFibers 𝒴.val.isFiberedInGroupoids.isFibered
      (CatFiberedInGroupoids.homFunctor_comp_p (a ≫ f).hom)
      (BigFppfOver.topology B S hS) :=
    (Functor.locallyEssSurjOnFibers_comp_iff 𝒳.val.isFiberedInGroupoids.isFibered
      𝒴.val.isFiberedInGroupoids.isFibered hFa hGf (BigFppfOver.topology B S hS) hloca).2 hlocf
  obtain ⟨-, h𝒴stack, -, -⟩ := id 𝒴.property
  obtain ⟨U, b, hbflat, hblfp, hbsurj, z, ⟨e⟩⟩ :=
    Stack.exists_single_cover_fiber_image_of_locallyEssSurjOnFibers (a ≫ f).hom
      (Stack.isStack_of_isRepresentableByAlgebraicSpace B S hS _
        (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W))
      (fun T p q => h𝒴stack.1.isMorSheaf T p q) hlocaf V
      (Stack.stackMapFibreObject B S hS V c.hom)
  -- the covering 1-morphism and its three properties
  have hbmapsurj : Stack.IsSurjective B S hS (Stack.schemeStackMap.{u, w} B S hS b) := by
    intro p
    obtain ⟨-, hp⟩ := Stack.exists_mem_range_pointsMap_schemeStackMap.{u, w} B S hS
      (fun _ : Unit => U) (fun _ => b) (fun t => ⟨(), hbsurj.surj t⟩) p
    exact hp
  refine ⟨U, Stack.schemeStackMap.{u, w} B S hS b ≫ c,
    Stack.schemeStackMap.{u, w} B S hS (Stack.fiberArrow z) ≫ a,
    Stack.isSurjective_comp B S hS _ _ hbmapsurj hcsurj,
    isFlat_comp B S hS _ _ (Stack.isFlat_schemeFibredCategoryMap.{u, w} B S hS b hbflat)
      (isFlat_of_isSmooth B S hS c hcsm),
    isLocallyOfFinitePresentation_comp B S hS _ _
      (Stack.isLocallyOfFinitePresentation_schemeFibredCategoryMap.{u, w} B S hS b hblfp)
      (isLocallyOfFinitePresentation_of_isSmooth B S hS c hcsm), ⟨?_⟩⟩
  exact Bicategory.associator (Stack.schemeStackMap.{u, w} B S hS (Stack.fiberArrow z)) a f ≪≫
    Stack.schemeMapFactorisationOfFiberImage B S hS (a ≫ f) c b z e

/-- **A gerbe acquires a section after a surjective, flat, locally finitely presented base
change.** Let `f : 𝒳 ⟶ 𝒴` make `𝒳` a gerbe over `𝒴`. Then there are an object `U` of the big
fppf site of `S` and a surjective, flat, locally finitely presented `g : 𝒰 ⟶ 𝒴` such that *every*
2-fibre product of the cospan `(f, g)` — in particular the canonical one of Stacks 04T2, at which
the descent statements of Stacks 06PZ and Stacks 06Q8 are read — has a section of its
projection to `𝒰`.

This is `exists_isSurjective_isFlat_isLfp_section_of_isGerbeOver` read through the universal
property of the 2-fibre product (**Stacks 003Q**): the 1-morphism `s : 𝒰 ⟶ 𝒳` together with the
2-isomorphism `s ≫ f ≅ g` and the left unitor is a 2-commutative square over `(f, g)` with second
leg `𝟙 𝒰`, and the mediating 1-morphism into a terminal such square carries that leg to a
2-isomorphism `σ ≫ P.snd ≅ 𝟙 𝒰`.

The section is *not* shown here to be flat or locally of finite presentation; that is the
clause of **Stacks 06QG** part (3) proved in
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatLocalSection`, where the two are combined into
the fppf-local flat section that makes **Stacks 06QI** unconditional. -/
theorem exists_section_snd_of_isGerbeOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsGerbeOver B S hS f) :
    ∃ (U : BigFppfOver B S hS) (g : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒴),
      Stack.IsSurjective B S hS g ∧ IsFlat B S hS g ∧
        IsLocallyOfFinitePresentation B S hS g ∧
        ∀ P : Bicategory.TwoCommSq f g, Bicategory.IsTwoFibreProduct P →
          ∃ σ : Stack.schemeStack.{u, w} B S hS U ⟶ P.pt,
            Nonempty (σ ≫ P.snd ≅ 𝟙 (Stack.schemeStack.{u, w} B S hS U)) := by
  obtain ⟨U, g, s, hgsurj, hgflat, hglfp, ⟨κ⟩⟩ :=
    exists_isSurjective_isFlat_isLfp_section_of_isGerbeOver B S hS f hf
  refine ⟨U, g, hgsurj, hgflat, hglfp, fun P hP => ?_⟩
  let Q : Bicategory.TwoCommSq f g :=
    { pt := Stack.schemeStack.{u, w} B S hS U
      fst := s
      snd := 𝟙 _
      iso := κ ≪≫ (Bicategory.leftUnitor g).symm }
  exact ⟨(Bicategory.twoFibreProductPreHom hP Q).hom,
    ⟨(Bicategory.twoFibreProductPreHom hP Q).isoSnd.symm⟩⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
