module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreObjectTwoYoneda
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionSingleCover
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactDiagonalGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFiniteCoverDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStackFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties

/-!
# Reading a section of a gerbe at a single cover as a 1-morphism (the 2-Yoneda step)

Let `π : 𝒳 ⟶ 𝒰` make the algebraic stack `𝒳` a gerbe over the algebraic stack `𝒰` of an object
`U` of the big fppf site of `S`, and let `x : 𝒰 ⟶ 𝒳` be a section of `π`. The route to the
flatness and local finite presentation of `x` — the clause of **Stacks 06QG** part (3) that
**Stacks 06QI** takes fppf-locally on its target — begins by producing a surjective, flat,
locally finitely presented 1-morphism `q : 𝒱 ⟶ 𝒳` which factors through `x`.

`AlgebraicGeometry.Stack.exists_single_cover_section_image_of_isGerbeOver` produces the *object*
half of that datum: a smooth scheme atlas `a : 𝒯 ⟶ 𝒳` of `𝒳` evaluates, under the 2-Yoneda lemma
(**Stacks 004B**), to an object `ξ` of the fibre of `𝒳` over `T`, and the gerbe condition makes
`ξ` the `x`-image of an object `z` of the fibre of `𝒰` over a *single* surjective, flat, locally
finitely presented `b : V ⟶ T` of the site. **This file turns that object into the 1-morphism
and the factorisation**: `z` names a morphism `g : V ⟶ U` of the site, and the comparison
isomorphism of `ξ` and the `x`-image of `z` becomes a 2-isomorphism

`schemeStackMap g ≫ x ≅ schemeStackMap b ≫ a`,

whose right-hand side is surjective, flat and locally of finite presentation because `b` and `a`
are. So `q := schemeStackMap g ≫ x` is the 1-morphism the route asks for, on the nose rather than
up to a 2-isomorphism.

## What this still does not give

The remaining step of that route is **Stacks 06NR** applied to
`𝒱 ×_𝒳 𝒱 ⟶ 𝒰 ×_𝒳 𝒱 ⟶ 𝒱`, followed by the descent along `q` of **Stacks 06PZ** and
**Stacks 06Q8**. That step is
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_of_factorisation`
in `StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeFactorisationFppfDescent`, and it is proved
there unconditionally: its surjectivity input, that `𝒱 ×_𝒳 𝒱 ⟶ 𝒰 ×_𝒳 𝒱` induces a surjection of
fppf sheaves, is
`Stack.AlgebraicStacks.isLocallySurjective_representingMap_factorisationMediatingMap`,
which rests on the separation of the objects of a fibre by a section,
`AlgebraicGeometry.Stack.nonempty_iso_fiber_of_iso_section_image`, reduced to that fibre-level
statement by `AlgebraicGeometry.Stack.isLocallySurjective_representingMap_of_isoClassMap`.

The translation of the 2-fibre products into morphisms of presheaves that the 06NR step needs is
*not* `AlgebraicGeometry.Stack.hasRelativeProperty_iff_forall_space_baseChange` (**Stacks 04XC**),
which is about the relative property of Stacks 03YK carried by a 1-morphism representable by
algebraic spaces — a different proposition from the flatness of Stacks 06PW that Stacks 06PZ and
Stacks 06Q8 consume. It is **Stacks 06FM** read at a represented source and target,
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_iff_represented`.

What this file contributes is therefore only the factorisation; the rest of that route, and the
three representability data the Stacks 06NR step needs, are supplied in
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatLocalSection`, where it is combined with the
fppf-local section of Stacks 06QH (1) `⟹` (2) to make Stacks 06QI unconditional.

Nothing about the inertia is proved here, but the flat, locally finitely presented section that
`GerbeFlatLocalSection` assembles out of this factorisation is also what clause (2) of
**Stacks 06QJ** is proved from, in
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionInertiaFlat`: the pullback of the inertia along
a section is the self-intersection of that section, so flatness and local finite presentation of
the section give clause (2) after one fppf descent.

## Main definitions

* `AlgebraicGeometry.Stack.fibreObjectStackMapRepresentedIso`: at a *represented* target the
  2-Yoneda 1-morphism of an object of a fibre is the 1-morphism of the arrow of the site that
  object names.
* `AlgebraicGeometry.Stack.fibreObjectStackMapCompIso`: **2-Yoneda naturality across a
  1-morphism and over an arrow of the site.** A comparison of the `f`-image of an object `z` over
  `V` with the restriction along `b : V ⟶ T` of the object a 1-morphism `a` out of the algebraic
  stack of `T` evaluates to, read as a 2-isomorphism of the two composites.
* `AlgebraicGeometry.Stack.schemeMapFactorisationOfFiberImage`: the same at a *represented*
  source, where the factorisation reads `schemeStackMap g ≫ x ≅ schemeStackMap b ≫ a` for the
  morphism `g` of the site that the object names.

## Main results

* `AlgebraicGeometry.Stack.exists_single_cover_section_factorisation_of_isGerbeOver`: the
  conclusion above, for the section of a gerbe over the algebraic stack of a scheme: a morphism
  `g : V ⟶ U` of the site for which `schemeStackMap g ≫ x` is surjective, flat and locally of
  finite presentation.

## Implementation notes

The three ingredients are already in the library and none of them is re-proved here:
`CategoryTheory.Functor.TwoYoneda.liftBased_overMap_iso` identifies the 2-Yoneda lift at a
represented target with an `Over.map`, and
`AlgebraicGeometry.Stack.fibreObjectStackMapFactorIso` and
`AlgebraicGeometry.Stack.fibreObjectStackMapEvaluationIso` are the naturality of
the 2-Yoneda 1-morphism over an arrow of the base and its inverse on 1-morphisms. What this file
adds is the chaining, and the one computation they do not contain: the arrow of `𝒳` needed by
the naturality statement is the given fibre isomorphism followed by the *cartesian* arrow of the
chosen pullback `AlgebraicGeometry.Stack.pullbackFiber`, which is what lies over `b`.

The flatness and local finite presentation of `schemeStackMap b` are
`AlgebraicGeometry.Stack.isFlat_schemeFibredCategoryMap` and
`AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_schemeFibredCategoryMap`; its surjectivity
is `AlgebraicGeometry.Stack.exists_mem_range_pointsMap_schemeStackMap` at a one-element family.
Transporting the three properties across the 2-isomorphism uses
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_of_twoIso`,
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_iff_of_twoIso` and
`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap_eq_of_hom₂`.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
* [Stacks Project, Tag 06PJ](https://stacks.math.columbia.edu/tag/06PJ)
* [Stacks Project, Tag 06PZ](https://stacks.math.columbia.edu/tag/06PZ)
* [Stacks Project, Tag 06Q8](https://stacks.math.columbia.edu/tag/06Q8)
* [Stacks Project, Tag 06QG](https://stacks.math.columbia.edu/tag/06QG)
* [Stacks Project, Tag 06QI](https://stacks.math.columbia.edu/tag/06QI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.BasedFunctor.comp CategoryTheory.BasedFunctor.overMap

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The underlying category of an algebraic stack over `S` is fibered over the big fppf site. -/
local instance instIsFibered_algebraicStack (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    𝒳.val.val.p.IsFibered :=
  𝒳.val.isFiberedInGroupoids.isFibered

/-- **At a represented target the 2-Yoneda 1-morphism of an object of a fibre is the 1-morphism
of the arrow it names.** An object `z` of the fibre over `V` of the algebraic stack of `U` is an
arrow `V ⟶ U` of the site (`AlgebraicGeometry.Stack.fiberArrow`), and the 1-morphism the
2-Yoneda lemma (**Stacks 004B**) attaches to `z` is the one that arrow induces. -/
noncomputable def fibreObjectStackMapRepresentedIso {U V : BigFppfOver B S hS}
    (z : (schemeFibredCategory B S hS U).val.p.Fiber V) :
    Bicategory.InducedBicategory.mkHom (X := schemeStack.{u, w} B S hS V)
        (Y := schemeStack.{u, w} B S hS U)
        (fibreObjectFibredMap B S hS (schemeFibredCategory B S hS U) V z) ≅
      schemeStackMap.{u, w} B S hS (fiberArrow z) :=
  Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (Functor.TwoYoneda.liftBased_overMap_iso (V := U) z
      (schemeFibredCategory B S hS U).isFiberedInGroupoids))

/-- **2-Yoneda naturality across a 1-morphism and over an arrow of the site.** Let `f : 𝒴 ⟶ 𝒳`
be a 1-morphism of algebraic stacks over `S`, let `a` be a 1-morphism from the algebraic stack of
an object `T` of the site to `𝒳`, let `b : V ⟶ T`, and let `z` be an object of the fibre of `𝒴`
over `V` whose `f`-image is isomorphic in the fibre of `𝒳` over `V` to the restriction along `b`
of the object `a` evaluates to. Then the 1-morphism named by `z`, followed by `f`, is
2-isomorphic to `b` followed by `a`.

The arrow of `𝒳` that the naturality of the 2-Yoneda 1-morphism over `b` consumes is the given
fibre isomorphism followed by the cartesian arrow of the chosen pullback, which is the arrow
lying over `b`. -/
noncomputable def fibreObjectStackMapCompIso
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒴 ⟶ 𝒳)
    {T V : BigFppfOver B S hS} (a : schemeStack.{u, w} B S hS T ⟶ 𝒳) (b : V ⟶ T)
    (z : 𝒴.val.val.p.Fiber V)
    (e : (Functor.Fiber.mapOfComp 𝒴.val.val.p 𝒳.val.val.p
            (CatFiberedInGroupoids.homFunctor f.hom)
            (CatFiberedInGroupoids.homFunctor_comp_p f.hom) V).obj z ≅
          Functor.pullbackFiber 𝒳.val.val.p
            (stackMapFibreObject B S hS T a.hom) b) :
    (Bicategory.InducedBicategory.mkHom (fibreObjectFibredMap B S hS 𝒴.val V z) :
        schemeStack.{u, w} B S hS V ⟶ 𝒴) ≫ f ≅
      schemeStackMap.{u, w} B S hS b ≫ a := by
  set ξ := stackMapFibreObject B S hS T a.hom
  have h₁ : 𝒳.val.val.p.IsHomLift (𝟙 V) (Functor.Fiber.fiberInclusion.map e.hom) := e.hom.2
  have h₂ : 𝒳.val.val.p.IsHomLift b (Functor.IsPreFibered.pullbackMap ξ.2 b) :=
    (Functor.IsPreFibered.pullbackMap.IsCartesian ξ.2 b).toIsHomLift
  have hψ : 𝒳.val.val.p.IsHomLift b
      (Functor.Fiber.fiberInclusion.map e.hom ≫
        Functor.IsPreFibered.pullbackMap ξ.2 b) :=
    @CategoryTheory.IsHomLift.comp_lift_id_left' _ _ _ _ 𝒳.val.val.p _ _ _ V
      (Functor.Fiber.fiberInclusion.map e.hom) h₁ _ _ b
      (Functor.IsPreFibered.pullbackMap ξ.2 b) h₂
  exact Bicategory.InducedBicategory.isoMk
    (fibreObjectStackMapFactorIso B S hS f.hom b z ξ _ hψ ≪≫
      Bicategory.whiskerLeftIso (schemeFibredCategoryMap B S hS b)
        (fibreObjectStackMapEvaluationIso B S hS T a.hom))

/-- **The 2-Yoneda passage at a represented source.** In the situation of
`AlgebraicGeometry.Stack.fibreObjectStackMapCompIso` with `𝒴` the algebraic stack of an object
`U` of the site, the object `z` names a morphism `g : V ⟶ U` of the site and the factorisation
becomes `schemeStackMap g ≫ x ≅ schemeStackMap b ≫ a`. -/
noncomputable def schemeMapFactorisationOfFiberImage
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {U : BigFppfOver B S hS}
    (x : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    {T V : BigFppfOver B S hS} (a : schemeStack.{u, w} B S hS T ⟶ 𝒳) (b : V ⟶ T)
    (z : (schemeFibredCategory B S hS U).val.p.Fiber V)
    (e : (Functor.Fiber.mapOfComp (schemeFibredCategory B S hS U).val.p 𝒳.val.val.p
            (CatFiberedInGroupoids.homFunctor x.hom)
            (CatFiberedInGroupoids.homFunctor_comp_p x.hom) V).obj z ≅
          Functor.pullbackFiber 𝒳.val.val.p
            (stackMapFibreObject B S hS T a.hom) b) :
    schemeStackMap.{u, w} B S hS (fiberArrow z) ≫ x ≅ schemeStackMap.{u, w} B S hS b ≫ a :=
  (Bicategory.whiskerRightIso (fibreObjectStackMapRepresentedIso B S hS z) x).symm ≪≫
    fibreObjectStackMapCompIso B S hS x a b z e

/-- **A section of a gerbe over the algebraic stack of a scheme is hit by a surjective, flat,
locally finitely presented 1-morphism out of the algebraic stack of a scheme, through a morphism
of the site.** Let `π : 𝒳 ⟶ 𝒰` make the algebraic stack `𝒳` a gerbe over the algebraic stack `𝒰`
of an object `U` of the big fppf site of `S` and let `x : 𝒰 ⟶ 𝒳` be a section of `π`. Then there
are an object `V` of the site and a morphism `g : V ⟶ U` such that the composite
`schemeStackMap g ≫ x : 𝒱 ⟶ 𝒳` is surjective, flat and locally of finite presentation.

This is the 1-morphism called `q` in the route to the unproved half of **Stacks 06QG** part (3)
described in the module documentation: a smooth surjective scheme atlas `a : 𝒯 ⟶ 𝒳` is, by
`AlgebraicGeometry.Stack.exists_single_cover_section_image_of_isGerbeOver`, the `x`-image of an
object of `𝒰` after one surjective flat locally finitely presented `b : V ⟶ T`, and
`AlgebraicGeometry.Stack.schemeMapFactorisationOfFiberImage` turns that object into `g` and the
comparison into a 2-isomorphism `schemeStackMap g ≫ x ≅ schemeStackMap b ≫ a`, whose right-hand
side has all three properties.

What the route still needs after this is the surjectivity hypothesis of the **Stacks 06NR**
step; see the module documentation. -/
theorem exists_single_cover_section_factorisation_of_isGerbeOver
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (π : 𝒳 ⟶ 𝒰) (x : 𝒰 ⟶ 𝒳) (hx : x ≫ π ≅ 𝟙 𝒰)
    (hπ : AlgebraicStacks.IsGerbeOver B S hS π) :
    ∃ (V : BigFppfOver B S hS) (γ : schemeStack.{u, w} B S hS V ⟶ 𝒰),
      IsSurjective B S hS (γ ≫ x) ∧
      AlgebraicStacks.IsFlat B S hS (γ ≫ x) ∧
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (γ ≫ x) := by
  obtain ⟨T, a, hasm, hasurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  obtain ⟨-, h𝒰stack, -, -⟩ := id 𝒰.property
  obtain ⟨V, b, hbflat, hblfp, hbsurj, z, ⟨e⟩⟩ :=
    exists_single_cover_section_image_of_isGerbeOver 𝒳.property h𝒰stack.1 π.hom x.hom
      (Bicategory.InducedBicategory.isoHom (f := x ≫ π) (g := 𝟙 𝒰) hx) hπ T
      (stackMapFibreObject B S hS T a.hom)
  -- the properties of the right-hand side `schemeStackMap b ≫ a`
  have hbmapsurj : IsSurjective B S hS (schemeStackMap.{u, w} B S hS b) := by
    intro p
    obtain ⟨-, hp⟩ := exists_mem_range_pointsMap_schemeStackMap.{u, w} B S hS
      (fun _ : Unit => V) (fun _ => b) (fun t => ⟨(), hbsurj.surj t⟩) p
    exact hp
  have hcompsurj : IsSurjective B S hS (schemeStackMap.{u, w} B S hS b ≫ a) :=
    isSurjective_comp B S hS _ _ hbmapsurj hasurj
  have hcompflat : AlgebraicStacks.IsFlat B S hS (schemeStackMap.{u, w} B S hS b ≫ a) :=
    AlgebraicStacks.isFlat_comp B S hS _ _
      (isFlat_schemeFibredCategoryMap.{u, w} B S hS b hbflat)
      (AlgebraicStacks.isFlat_of_isSmooth B S hS a hasm)
  have hcomplfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (schemeStackMap.{u, w} B S hS b ≫ a) :=
    AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS _ _
      (isLocallyOfFinitePresentation_schemeFibredCategoryMap.{u, w} B S hS b hblfp)
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS a hasm)
  -- the factorisation, and the transport of the three properties across it
  let θ := fibreObjectStackMapCompIso B S hS x a b z e
  refine ⟨V, Bicategory.InducedBicategory.mkHom (X := schemeStack.{u, w} B S hS V) (Y := 𝒰)
    (fibreObjectFibredMap B S hS 𝒰.val V z), ?_, ?_, ?_⟩
  · show Function.Surjective (AlgebraicStacks.pointsMap B S hS
      (Bicategory.InducedBicategory.mkHom (X := schemeStack.{u, w} B S hS V) (Y := 𝒰)
        (fibreObjectFibredMap B S hS 𝒰.val V z) ≫ x))
    rw [AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS θ.hom]
    exact hcompsurj
  · exact (AlgebraicStacks.isFlat_iff_of_twoIso B S hS _ _
      (Bicategory.InducedBicategory.isoHom θ.symm)).1 hcompflat
  · exact (AlgebraicStacks.isLocallyOfFinitePresentation_iff_of_twoIso B S hS _ _
      (Bicategory.InducedBicategory.isoHom θ.symm)).1 hcomplfp

end AlgebraicGeometry.Stack

end
