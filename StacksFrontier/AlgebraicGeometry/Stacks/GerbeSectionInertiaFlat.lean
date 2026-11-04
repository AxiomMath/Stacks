module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaSelfIntersection
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatDescentAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatLocalSection
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionSingleCover
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeInertiaSetoidTarget
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The inertia of a gerbe over the algebraic stack of an object of the site (Stacks 06QJ (2))

This file proves clause (2) of **Stacks 06QJ** — that the forgetful 1-morphism `ℐ_𝒴 ⟶ 𝒴` of the
inertia is flat and locally of finite presentation — for a gerbe `q : 𝒴 ⟶ 𝒮_V` whose base is the
algebraic stack of an object `V` of the big fppf site of `S`. That is the hypothesis
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeInertiaCharacterization` reduces the general case to,
and it is discharged here.

## The two steps

**A gerbe over the algebraic stack of a scheme, with a section.** Let `x : 𝒮_U ⟶ 𝒴` be a section
of a gerbe `q : 𝒴 ⟶ 𝒮_U`. Then

* `x` is surjective (`AlgebraicGeometry.Stack.isSurjective_of_section_of_isGerbeOver`), flat and
  locally of finite presentation
  (`Stack.AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_section_of_isGerbeOver`,
  the clause of **Stacks 06QG** part (3) proved in
  `StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatLocalSection`), so both properties descend along
  it by **Stacks 06PZ** and **Stacks 06Q8**; it is therefore enough to prove them for the base
  change `ℐ_𝒴 ×_𝒴 𝒮_U ⟶ 𝒮_U` of the inertia projection.
* That base change *is* the self-intersection `ℛ = 𝒮_U ×_{x, 𝒴, x} 𝒮_U`, by the first paragraph
  of the source's proof of **Stacks 06QG**: an arrow of `ℛ` over `W` is a triple `(a, b, ψ)` with
  `ψ : x(a) ≅ x(b)` vertical, and applying `q` to `ψ` and conjugating by the 2-isomorphism of the
  section produces a vertical isomorphism `a ≅ b`
  (`AlgebraicGeometry.Stack.nonempty_iso_fiber_of_iso_section_image`), which turns `ψ` into an
  automorphism of `x(a)`. The comparison is the equivalence
  `CategoryTheory.InertiaSelfIntersection.toInertiaBase` of
  `StacksFrontier.CategoryTheory.FiberedCategory.InertiaSelfIntersection`, read here with its two
  inputs supplied: the separating isomorphism just described, and uniqueness of morphisms of
  `𝒮_U` over a fixed morphism of the site, which holds because `𝒮_U` is representable
  (**Stacks 04SV**, **Stacks 02ZX**).
* The projection of `ℛ` to `𝒮_U` is a base change of `x`, hence flat and locally of finite
  presentation by **Stacks 06PY** and **Stacks 06Q4**; the comparison is strictly compatible with
  the two projections, so condition (2) of **Stacks 06FM** moves across it
  (`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_isEquivalence`).

This is the route through **Stacks 06PR** without the groupoid presentation: Stacks 06PR
identifies the pullback of the inertia along a presentation with the stabilizer of the presenting
groupoid, and Stacks 06QG part (1) says that for a section the stabilizer is the self-intersection
itself; what is done here is that composite identification, read directly at the two 2-fibre
products rather than through the groupoid and its stabilizer, which avoids both the group
packaging of **Stacks 06PP** that the library does not have and the passage to the representing
algebraic spaces.

**The section exists fppf-locally.** `exists_section_snd_of_isGerbeOver` gives an object `W` of
the site and a surjective, flat, locally finitely presented `g : 𝒮_W ⟶ 𝒮_V` after which `q`
acquires a section. The base change `𝒴 ×_{𝒮_V} 𝒮_W ⟶ 𝒮_W` is a
gerbe by **Stacks 06QE**, so the first step applies to it, and the conclusion descends to `𝒴` by
`AlgebraicGeometry.Stack.isFlat_inertiaProjection_of_baseChange` and its companion — both bases
`𝒮_V` and `𝒮_W` are representable by algebraic spaces, which is what that step asks for.

Note that this replaces the source's own first step, which passes to the coproduct `∐ Wᵢ` of an
fppf covering and needs an object of `𝒴` over it, that is the descent of an object of a stack
along `{Wᵢ ⟶ ∐ Wᵢ}`. The library's `exists_section_snd_of_isGerbeOver` reaches the same
conclusion without a coproduct: it gathers the covering family inside a smooth *scheme* atlas of
`𝒴`, where an object of a fibre is an arrow of the site. So the coproduct descent is not needed.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.separationData_of_section` and `…thinData_schemeStack`:
  the two inputs of the comparison, at a section of a 1-morphism to the algebraic stack of an
  object of the site.
* `AlgebraicGeometry.Stack.AlgebraicStacks.relationToInertiaBase`: the comparison
  `𝒮_U ×_{x, 𝒴, x} 𝒮_U ⟶ ℐ_𝒴 ×_𝒴 𝒮_U`, as a 1-morphism of algebraic stacks over `S`.

## Main results

* `isFlat_and_isLocallyOfFinitePresentation_inertiaProjection_of_section`:
  clause (2) of **Stacks 06QJ** for a gerbe over the algebraic stack of an object of the site
  which has a section.
* `isFlat_and_isLocallyOfFinitePresentation_inertiaProjection_of_isGerbeOver_schemeStack`:
  clause (2) of **Stacks 06QJ** for a gerbe over the algebraic stack of an object of the site.

No Stacks tag is registered here. The source states Stacks 06QG for a gerbe over an algebraic
space, not over the algebraic stack of an object of the site, exactly as for
`Stack.AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_section_of_isGerbeOver`;
and clause (2) of Stacks 06QJ at a base of this shape is not the tag, which is the equivalence
for an arbitrary algebraic stack. Tag 06QJ is registered in
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeInertiaCharacterization`, which consumes this file.

## Implementation notes

The comparison is read at the *canonical* 2-fibre products of **Stacks 04T2**, which is where
Stacks 06Q8 reads its hypothesis; the flatness descent of Stacks 06PZ is taken at the leg exchange
of that square (`CategoryTheory.Bicategory.isTwoFibreProduct_swap`), so one square serves both
descents. The comparison is strictly over the site and strictly compatible with the two
projections — `relationToInertiaBase_comp_snd` is `rfl` — which is why the 2-isomorphism that
`hasPropertyOnSomeSmoothDiagram_of_isEquivalence` consumes is `Iso.refl`.

## References

* [Stacks Project, Tag 02ZX](https://stacks.math.columbia.edu/tag/02ZX)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
* [Stacks Project, Tag 06PQ](https://stacks.math.columbia.edu/tag/06PQ)
* [Stacks Project, Tag 06PR](https://stacks.math.columbia.edu/tag/06PR)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
* [Stacks Project, Tag 06PZ](https://stacks.math.columbia.edu/tag/06PZ)
* [Stacks Project, Tag 06Q4](https://stacks.math.columbia.edu/tag/06Q4)
* [Stacks Project, Tag 06Q8](https://stacks.math.columbia.edu/tag/06Q8)
* [Stacks Project, Tag 06QE](https://stacks.math.columbia.edu/tag/06QE)
* [Stacks Project, Tag 06QG](https://stacks.math.columbia.edu/tag/06QG)
* [Stacks Project, Tag 06QH](https://stacks.math.columbia.edu/tag/06QH)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The fibres of the algebraic stack of an object of the site are thin**, so two of its
morphisms lying over one morphism of the site agree. This is **Stacks 02ZX** for a category
fibred in groupoids representable by an algebraic space, which the algebraic stack of an object of
the site is by **Stacks 04SV**. -/
theorem thinData_schemeStack (U : BigFppfOver B S hS) :
    InertiaSelfIntersection.ThinData
      (Stack.schemeStack.{u, w} B S hS U).val.val.p := by
  have hset : (Stack.schemeStack.{u, w} B S hS U).val.val.p.IsFiberedInSetoids :=
    Stack.isFiberedInSetoids_of_isRepresentableByAlgebraicSpace B S hS
      (Stack.schemeStack.{u, w} B S hS U).val
      (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
  have : (Stack.schemeStack.{u, w} B S hS U).val.val.p.IsFibered :=
    hset.isFiberedInGroupoids.isFibered
  intro R T k a b φ₁ φ₂ h₁ h₂
  exact Functor.hom_unique_of_fiber_isThin _ k (hset.fiber_isThin _) φ₁ φ₂ h₁ h₂

/-- **A section separates the two ends of an arrow of the self-intersection.** Let `x : 𝒮_U ⟶ 𝒴`
be a section of `q : 𝒴 ⟶ 𝒮_U`. The two ends of an object of `𝒮_U ×_{x, 𝒴, x} 𝒮_U` are objects of
one fibre of `𝒮_U` whose `x`-images are isomorphic in the corresponding fibre of `𝒴`, so they are
themselves isomorphic there: that is
`AlgebraicGeometry.Stack.nonempty_iso_fiber_of_iso_section_image`, which applies `q` to the
comparison isomorphism and conjugates by the 2-isomorphism of the section. The choice of such an
isomorphism is the `SeparationData` the comparison functor consumes. -/
noncomputable def separationData_of_section {U : BigFppfOver B S hS}
    {𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (q : 𝒴 ⟶ Stack.schemeStack.{u, w} B S hS U)
    (x : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒴)
    (hx : x ≫ q ≅ 𝟙 (Stack.schemeStack.{u, w} B S hS U)) :
    InertiaSelfIntersection.SeparationData
      (Stack.schemeStack.{u, w} B S hS U).val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor x.hom) := fun R =>
  let ε := (Stack.nonempty_iso_fiber_of_iso_section_image q.hom x.hom
      (Bicategory.InducedBicategory.isoHom (f := x ≫ q)
        (g := 𝟙 (Stack.schemeStack.{u, w} B S hS U)) hx)
      (⟨R.x, R.hx⟩ : (Stack.schemeStack.{u, w} B S hS U).val.val.p.Fiber R.base)
      (⟨R.y, R.hy⟩ : (Stack.schemeStack.{u, w} B S hS U).val.val.p.Fiber R.base)
      { hom := ⟨R.iso.hom, R.vertical⟩
        inv := ⟨R.iso.inv,
          InertiaSelfIntersection.isHomLift_inv 𝒴.val.val.p R.iso R.vertical⟩
        hom_inv_id := Functor.Fiber.hom_ext R.iso.hom_inv_id
        inv_hom_id := Functor.Fiber.hom_ext R.iso.inv_hom_id }).some
  ⟨{ hom := ε.hom.val
     inv := ε.inv.val
     hom_inv_id := congrArg (fun h => Functor.Fiber.fiberInclusion.map h) ε.hom_inv_id
     inv_hom_id := congrArg (fun h => Functor.Fiber.fiberInclusion.map h) ε.inv_hom_id },
   ε.hom.2⟩

/-- **The comparison 1-morphism `𝒮_U ×_{x, 𝒴, x} 𝒮_U ⟶ ℐ_𝒴 ×_𝒴 𝒮_U`**, for `x` a section of a
1-morphism `q : 𝒴 ⟶ 𝒮_U`: the equivalence
`CategoryTheory.InertiaSelfIntersection.toInertiaBase` read in the 2-category of algebraic
stacks over `S`, with the separating isomorphism of the section and the thinness of the fibres of
`𝒮_U` as its two inputs. It is strictly over the site, so no `w` field has to be proved. -/
noncomputable def relationToInertiaBase {U : BigFppfOver B S hS}
    {𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (q : 𝒴 ⟶ Stack.schemeStack.{u, w} B S hS U)
    (x : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒴)
    (hx : x ≫ q ≅ 𝟙 (Stack.schemeStack.{u, w} B S hS U)) :
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS x x).pt ⟶
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒴) x).pt :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom
      { toFunctor := InertiaSelfIntersection.toInertiaBase
          (Stack.schemeStack.{u, w} B S hS U).val.val.p 𝒴.val.val.p
          (CatFiberedInGroupoids.homFunctor x.hom)
          (CatFiberedInGroupoids.homFunctor_comp_p x.hom)
          (separationData_of_section B S hS q x hx)
          (thinData_schemeStack.{u, w} B S hS U)
        w := rfl })

/-- The comparison carries the projection to `𝒮_U` of the base change of the inertia to the
first projection of the self-intersection, on the nose. -/
lemma relationToInertiaBase_comp_snd {U : BigFppfOver B S hS}
    {𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (q : 𝒴 ⟶ Stack.schemeStack.{u, w} B S hS U)
    (x : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒴)
    (hx : x ≫ q ≅ 𝟙 (Stack.schemeStack.{u, w} B S hS U)) :
    relationToInertiaBase B S hS q x hx ≫
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS
          (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒴) x).snd =
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS x x).fst := rfl

/-- The comparison is an equivalence of the underlying categories, by
`CategoryTheory.InertiaSelfIntersection.isEquivalence_toInertiaBase`. -/
lemma isEquivalence_relationToInertiaBase {U : BigFppfOver B S hS}
    {𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (q : 𝒴 ⟶ Stack.schemeStack.{u, w} B S hS U)
    (x : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒴)
    (hx : x ≫ q ≅ 𝟙 (Stack.schemeStack.{u, w} B S hS U)) :
    Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor
      (relationToInertiaBase B S hS q x hx).hom) :=
  InertiaSelfIntersection.isEquivalence_toInertiaBase
    (CatFiberedInGroupoids.homFunctor_comp_p x.hom)
    (separationData_of_section B S hS q x hx) (thinData_schemeStack.{u, w} B S hS U)

/-- **Clause (2) of Stacks 06QJ for a gerbe over the algebraic stack of an object of the site
with a section.** Let `q : 𝒴 ⟶ 𝒮_U` make the algebraic stack `𝒴` over `S` a gerbe over the
algebraic stack of an object `U` of the big fppf site of `S`, and let `x : 𝒮_U ⟶ 𝒴` be a section
of `q`. Then the forgetful 1-morphism `ℐ_𝒴 ⟶ 𝒴` of the inertia of `𝒴` is flat and locally of
finite presentation.

The section is surjective, flat and locally of finite presentation — the last two by the clause
of **Stacks 06QG** part (3) that `GerbeFlatLocalSection` proves — so it is enough to prove the
two properties for the base change `ℐ_𝒴 ×_𝒴 𝒮_U ⟶ 𝒮_U`, which then descend by **Stacks 06PZ**
and **Stacks 06Q8**. That base change is the self-intersection `𝒮_U ×_{x, 𝒴, x} 𝒮_U` by
`AlgebraicGeometry.Stack.AlgebraicStacks.relationToInertiaBase`, whose projection to `𝒮_U` is a
base change of `x`. -/
theorem isFlat_and_isLocallyOfFinitePresentation_inertiaProjection_of_section
    {U : BigFppfOver B S hS} {𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (q : 𝒴 ⟶ Stack.schemeStack.{u, w} B S hS U)
    (x : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒴)
    (hx : x ≫ q ≅ 𝟙 (Stack.schemeStack.{u, w} B S hS U))
    (hq : IsGerbeOver B S hS q) :
    IsFlat B S hS (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒴) ∧
      IsLocallyOfFinitePresentation B S hS
        (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒴) := by
  obtain ⟨hxflat, hxlfp⟩ :=
    isFlat_and_isLocallyOfFinitePresentation_section_of_isGerbeOver B S hS q x hx hq
      (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
  have hxsurj : Stack.IsSurjective B S hS x :=
    Stack.isSurjective_of_section_of_isGerbeOver B S hS q x hx hq
  have hRflat : IsFlat B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS x x).fst :=
    isFlat_baseChange B S hS x x (Stack.twoFibreProductSquareAlgebraicStacks B S hS x x)
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS x x) hxflat
  have hRlfp : IsLocallyOfFinitePresentation B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS x x).fst :=
    isLocallyOfFinitePresentation_baseChange B S hS x x
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS x x)
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS x x) hxlfp
  have hPflat : IsFlat B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS
      (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒴) x).snd :=
    Stack.hasPropertyOnSomeSmoothDiagram_of_isEquivalence B S hS
      (fun _ _ h => Space.IsFlat B S hS h)
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒴) x).snd.hom
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS x x).fst.hom
      (relationToInertiaBase B S hS q x hx).hom
      (isEquivalence_relationToInertiaBase B S hS q x hx) (Iso.refl _) hRflat
  have hQ : Space.IsSmoothLocalOnSourceAndTarget B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h) :=
    Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS
  have hPlfp : IsLocallyOfFinitePresentation B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒴) x).snd := by
    refine (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _ hQ
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒴) x).pt.property
      (Stack.schemeStack.{u, w} B S hS U).property _).2 ?_
    refine Stack.hasPropertyOnSomeSmoothDiagram_of_isEquivalence B S hS _ _ _
      (relationToInertiaBase B S hS q x hx).hom
      (isEquivalence_relationToInertiaBase B S hS q x hx) (Iso.refl _) ?_
    exact (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _ hQ
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS x x).pt.property
      (Stack.schemeStack.{u, w} B S hS U).property _).1 hRlfp
  refine ⟨isFlat_twoFibreProduct_fst_descent B S hS
    (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒴) x
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS
      (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒴) x).swap
    (Bicategory.isTwoFibreProduct_swap
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
        (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒴) x))
    hxsurj hxflat hPflat, ?_⟩
  exact isLocallyOfFinitePresentation_of_baseChange B S hS
    (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒴) x hxsurj hxflat hxlfp hPlfp

/-- **Clause (2) of Stacks 06QJ for a gerbe over the algebraic stack of an object of the site.**
Let `q : 𝒴 ⟶ 𝒮_V` make the algebraic stack `𝒴` over `S` a gerbe over the algebraic stack of an
object `V` of the big fppf site of `S`. Then the forgetful 1-morphism `ℐ_𝒴 ⟶ 𝒴` of the inertia
of `𝒴` is flat and locally of finite presentation.

Fppf-locally on `𝒮_V` the gerbe has a section
(`AlgebraicGeometry.Stack.AlgebraicStacks.exists_section_snd_of_isGerbeOver`), over the algebraic
stack of another object `W` of the site; the base change is a gerbe over `𝒮_W` by
**Stacks 06QE**, so the previous theorem applies to it, and the conclusion descends to `𝒴` by
`AlgebraicGeometry.Stack.isFlat_inertiaProjection_of_baseChange` and its companion, both bases
being representable by algebraic spaces. -/
theorem isFlat_and_isLocallyOfFinitePresentation_inertiaProjection_of_isGerbeOver_schemeStack
    (V : BigFppfOver B S hS) (𝒴 : Stack.AlgebraicStacks.{u, w} B S hS)
    (q : 𝒴 ⟶ Stack.schemeStack.{u, w} B S hS V) (hq : IsGerbeOver B S hS q) :
    IsFlat B S hS (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒴) ∧
      IsLocallyOfFinitePresentation B S hS
        (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒴) := by
  obtain ⟨W, g, hgsurj, hgflat, hglfp, hsection⟩ :=
    exists_section_snd_of_isGerbeOver B S hS q hq
  obtain ⟨σ, ⟨hσ⟩⟩ := hsection (Stack.twoFibreProductSquareAlgebraicStacks B S hS q g)
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS q g)
  have hgerbe : IsGerbeOver B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS q g).snd :=
    isGerbeOver_of_isTwoFibreProduct B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS q g)
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS q g) hq
  obtain ⟨h1, h2⟩ := isFlat_and_isLocallyOfFinitePresentation_inertiaProjection_of_section
    B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS q g).snd σ hσ hgerbe
  exact ⟨Stack.isFlat_inertiaProjection_of_baseChange B S hS q g
      (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V)
      (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W)
      hgsurj hgflat h1,
    Stack.isLocallyOfFinitePresentation_inertiaProjection_of_baseChange B S hS q g
      (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V)
      (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W)
      hgsurj hgflat hglfp h2⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
