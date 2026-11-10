module

public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfCohomologyProductDictionary
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSchemeStack
public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksCore.Tactic.StacksAttribute

/-!
# Condition (2)(c) of Stacks 0GMS for the fppf site of an algebraic stack

Let `𝒳` be an algebraic stack over a scheme `S` contained in a big fppf site `B`, and give its
total category the fppf topology of **Stacks 06TP**. Condition (2)(c) of **Stacks 0GMS** —
equivalently condition (3) of **Stacks 0GN4** — asks, for two objects `x`, `x'` of that site
lying over affine schemes, for a finite family `V_i` of such objects with morphisms
`p_i : V_i ⟶ x` and `q_i : V_i ⟶ x'` for which `∐_i h_{V_i}^# ⟶ h_x^# ⨯ h_{x'}^#` is a surjection
of fppf sheaves of sets. This file proves that condition, with one member, for a stack which is
quasi-separated over a quasi-separated base scheme.

The source produces the family by covering the 2-fibre product `U ×_{x, 𝒳, x'} U'` of the slices
`x` and `x'` represent by an affine scheme. All of that argument except its last step is in
`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomologyProductDictionary.lean`: the objects of
that 2-fibre product are the quadruples of **Stacks 0040**, a quadruple `Q` amounts to a pair of
morphisms `p_Q : V ⟶ x`, `q_Q : V ⟶ x'` of the site, and one quadruple which dominates every
other quadruple locally discharges condition (2)(c), by
`AlgebraicGeometry.Stack`
`.isLocallySurjective_prodLift_fppfTopology_of_exists_quadruple_dominating_base`.
What is added here is the quadruple.

## Main results

* `AlgebraicGeometry.Stack`
  `.isQuasiCompactStack_and_isQuasiSeparatedOver_twoFibreProductAlgebraicStack_objectMorphism`: the
  2-fibre product of the two 2-Yoneda 1-morphisms of two objects lying over affine schemes is a
  quasi-compact algebraic stack and is quasi-separated over `S`, when `𝒳` is quasi-separated over
  a quasi-separated base. Its two conjuncts are
  `AlgebraicGeometry.Stack.isQuasiCompactStack_twoFibreProductAlgebraicStack_objectMorphism` and
  `AlgebraicGeometry.Stack.isQuasiSeparatedOver_twoFibreProductAlgebraicStack_objectMorphism`;
  condition (3) of Stacks 0GN4 uses the first, condition (4) needs the second.
* `AlgebraicGeometry.Stack.isHomLift_quadMap`: the morphism of the site a morphism of quadruples
  induces lies over the same morphism of the base as the morphism of quadruples does.
* `AlgebraicGeometry.Stack.exists_quadruple_dominating`: the quadruple condition (2)(c) needs —
  one quadruple lying over an affine scheme which dominates every quadruple after a covering taken
  in the big fppf category over `S`.
* `AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_prodLift`: **condition
  (2)(c)** itself, in the shape
  `AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_fppf` consumes as its
  hypothesis `h_product`.
* `AlgebraicGeometry.Stack`
  `.isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiSeparatedOver`:
  Stacks 0GQV for a quasi-compact algebraic stack quasi-separated over a quasi-separated base,
  with condition (4) of Stacks 0GN4 as a hypothesis — it is proved in
  `StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomologyEqualizerAffineCover.lean`, which
  discharges it there.

## Implementation notes

Quasi-compactness of the 2-fibre product comes from **Stacks 075S** part (3), which asks the two
slices to be quasi-compact *and quasi-separated over* `S` and the ambient `𝒳` to be
quasi-separated over `S`. All three are available at an affine object: the slice there is
`AlgebraicGeometry.Stack.schemeStack` at that object on the nose, which is quasi-compact by
`AlgebraicGeometry.Stack.isQuasiCompactStack_schemeStack_of_isAffine` and quasi-separated over `S`
by `AlgebraicGeometry.Stack.isQuasiSeparatedOver_schemeStack_of_isAffine`.

Part (3) is used in place of part (1) — which would suffice for quasi-compactness alone, the
2-Yoneda 1-morphism of `x'` having quasi-compact source and quasi-separated target, hence being a
quasi-compact 1-morphism in the sense of **Stacks 050U** — because it delivers in the same breath
the *quasi-separatedness over* `S` of the 2-fibre product, and that is what condition (4) of
Stacks 0GN4 needs and condition (3) does not. Condition (4) base-changes along a 1-morphism whose
target is a 2-fibre product rather than `𝒳`, and part (1) asks for quasi-separatedness over `S` of
the target; see
`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomologyEqualizerDictionary.lean`.

The quadruple is produced exactly as condition (1) is produced in
`AlgebraicGeometry.Stack.exists_isAffineObject_cover_nonempty_hom`. **Stacks 04YC** parts (1) and
(2) turn quasi-compactness of the 2-fibre product into an affine object `U₀` of the big fppf
category over `S` and a surjective, relatively smooth 1-morphism `f` from the slice it represents;
`Q` is `f(1_{U₀})`, and it lies over `U₀` because `f` is a based functor. Relative smoothness gives
flatness and local finite presentation through **Stacks 06FM**, **Stacks 075U** and
**Stacks 0DNP**, and **Stacks 06QA** then covers the base of any quadruple `P` by objects over
each of which `P` is the image under `f` of an object `a` of the slice over `U₀`. That image is the
dominating datum: the morphism of quadruples is the one `f` attaches to `a`, and the morphism to
`Q` is the image under `f` of the structure morphism `a ⟶ 1_{U₀}` of the slice.

Two identifications make that passage free of transport. First, the 2-fibre product of algebraic
stacks at the two 2-Yoneda 1-morphisms has the quadruples as its total category and the projection
of a quadruple to its base object as its structure functor, both on the nose; this is
`AlgebraicGeometry.Stack.obj_twoFibreProductAlgebraicStack_objectMorphism` and the definition of
`CategoryTheory.TwoFibreProductOver.structureFunctor`. Second, the object of the site a quadruple
classifies lies over the base object of the quadruple
(`AlgebraicGeometry.Stack.obj_quadObj`), so the covering sieve Stacks 06QA produces downstairs is
already a sieve on the object the consumer wants it on, once the quadruple is presented as an
object of the fibre over that object rather than over its own base.

`AlgebraicGeometry.Stack.isHomLift_quadMap` is the only genuinely new bookkeeping. A morphism of
quadruples lying over `k` has first component lying over `k` in the slice `(Sch/S)/U`, because the
first projection of a 2-fibre product is strictly over the base
(`CategoryTheory.TwoFibreProductOver.fst_comp_eq`); and the 2-Yoneda functor is strictly over the
base as well (`CategoryTheory.Functor.TwoYoneda.liftBased`), so it carries that lift to a lift of
`k` in `𝒳`. Both steps are
`CategoryTheory.Functor.isHomLift_map_of_comp_eq`.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 075S](https://stacks.math.columbia.edu/tag/075S)
* [Stacks Project, Tag 0GMS](https://stacks.math.columbia.edu/tag/0GMS)
* [Stacks Project, Tag 0GN4](https://stacks.math.columbia.edu/tag/0GN4)
* [Stacks Project, Tag 0GQV](https://stacks.math.columbia.edu/tag/0GQV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.ColimitsOfCohomology

attribute [local instance] essentiallySmall_join hasSheafify_ab_join enoughInjectives_sheaf_join
  globalSections_additive_join

universe v₀ u₀

/-- Sheaves of sets on a site have colimits of the size of the join of the two universes of the
site. The instance is needed to form the finite coproducts of sheafified representables the
conditions of Stacks 0GN4 speak of, and is restated in its constructed form, as in the files
proving Stacks 0GN3 and Stacks 0GN4 and in
`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomology.lean`, because the search that finds
it is not cheap. It is anonymous because both of those files export a declaration of the same name
whose `instance` attribute is local to them. -/
local instance {C : Type u₀} [Category.{v₀} C] (J : GrothendieckTopology C) :
    HasColimitsOfSize.{max u₀ v₀, max u₀ v₀} (Sheaf J (Type max u₀ v₀)) :=
  Sheaf.instHasColimitsOfSize

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Dictionary

variable (𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- **The 2-Yoneda functor of an object of the fppf site is strictly over the big fppf category
over `S`.** This is the structural equality of the based functor
`CategoryTheory.Functor.TwoYoneda.liftBased`, named at the spelling
`CategoryTheory.Functor.TwoYoneda.liftFunctor` that the quadruples of
`AlgebraicGeometry.Stack.twoFibreProductObjects` are stated with. -/
theorem twoYonedaLiftFunctor_comp_p (x : 𝒞.val.obj) :
    Functor.TwoYoneda.liftFunctor 𝒞.val.p 𝒞.isFiberedInGroupoids (𝒞.val.p.obj x)
        (fibreObj B S hS 𝒞 x) ⋙ 𝒞.val.p =
      Over.forget (𝒞.val.p.obj x) :=
  (Functor.TwoYoneda.liftBased 𝒞.val.p 𝒞.isFiberedInGroupoids (𝒞.val.p.obj x)
    (fibreObj B S hS 𝒞 x)).w

variable {x x' : 𝒞.val.obj}

/-- **The object of the fppf site a quadruple classifies lies over the base object of the
quadruple.** The object is the chosen pullback of `x` along the first component of the quadruple,
so it lies over the source of that component, which is the base object. -/
theorem obj_quadObj (P : twoFibreProductObjects B S hS 𝒞 x x') :
    𝒞.val.p.obj (quadObj B S hS 𝒞 P) = P.base :=
  (Functor.congr_obj (twoYonedaLiftFunctor_comp_p B S hS 𝒞 x) P.x).trans P.hx

/-- **A morphism of quadruples and the morphism of the fppf site it induces lie over the same
morphism of the big fppf category over `S`.**

The first projection of a 2-fibre product is strictly over the base, so the first component of a
morphism of quadruples lying over `k` lies over `k` in the slice; and the 2-Yoneda functor of `x`
is strictly over the base, so it carries that lift to a lift of `k` in the fppf site of `𝒞`. -/
theorem isHomLift_quadMap {P P' : twoFibreProductObjects B S hS 𝒞 x x'} (ψ : P ⟶ P')
    {T T' : BigFppfOver B S hS} (k : T ⟶ T')
    (h : (TwoFibreProductOver.structureFunctor (Over.forget (𝒞.val.p.obj x))
      (Over.forget (𝒞.val.p.obj x')) 𝒞.val.p
      (Functor.TwoYoneda.liftFunctor 𝒞.val.p 𝒞.isFiberedInGroupoids (𝒞.val.p.obj x)
        (fibreObj B S hS 𝒞 x))
      (Functor.TwoYoneda.liftFunctor 𝒞.val.p 𝒞.isFiberedInGroupoids (𝒞.val.p.obj x')
        (fibreObj B S hS 𝒞 x'))).IsHomLift k ψ) :
    𝒞.val.p.IsHomLift k (quadMap B S hS 𝒞 ψ) := by
  have := h
  have hfst : (Over.forget (𝒞.val.p.obj x)).IsHomLift k ψ.a :=
    Functor.isHomLift_map_of_comp_eq
      (TwoFibreProductOver.fst_comp_eq (p𝒳 := Over.forget (𝒞.val.p.obj x))
        (p𝒴 := Over.forget (𝒞.val.p.obj x')) (p𝒮 := 𝒞.val.p)
        (F := Functor.TwoYoneda.liftFunctor 𝒞.val.p 𝒞.isFiberedInGroupoids (𝒞.val.p.obj x)
          (fibreObj B S hS 𝒞 x))
        (G := Functor.TwoYoneda.liftFunctor 𝒞.val.p 𝒞.isFiberedInGroupoids (𝒞.val.p.obj x')
          (fibreObj B S hS 𝒞 x'))) k ψ
  have := hfst
  exact Functor.isHomLift_map_of_comp_eq (twoYonedaLiftFunctor_comp_p B S hS 𝒞 x) k ψ.a

end Dictionary

section AffineQuadruple

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **The 2-fibre product of the 2-Yoneda 1-morphisms of two objects lying over affine schemes is
a quasi-compact algebraic stack *and* is quasi-separated over `S`**, for an algebraic stack
quasi-separated over a quasi-separated base scheme.

This is **Stacks 075S** part (3) at the two 2-Yoneda 1-morphisms. All five of its hypotheses are
available at an affine object: the slice at one is `AlgebraicGeometry.Stack.schemeStack` at that
object on the nose, which is quasi-compact by
`AlgebraicGeometry.Stack.isQuasiCompactStack_schemeStack_of_isAffine` and quasi-separated over `S`
by `AlgebraicGeometry.Stack.isQuasiSeparatedOver_schemeStack_of_isAffine`, and the fifth
hypothesis is quasi-separatedness over `S` of `𝒳` itself.

The quasi-separated conjunct is the one condition (4) of Stacks 0GN4 needs and condition (3) does
not: condition (3) is discharged from the quasi-compact conjunct alone, which part (1) of the same
tag already gave, but condition (4) base-changes along a 1-morphism whose *target* is this 2-fibre
product rather than `𝒳`, and part (1) asks for quasi-separatedness over `S` of the target. It is
used in that way by
`AlgebraicGeometry.Stack.isQuasiCompactStack_equalizerTwoFibreProduct` in
`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomologyEqualizerAffineCover.lean`. -/
theorem isQuasiCompactStack_and_isQuasiSeparatedOver_twoFibreProductAlgebraicStack_objectMorphism
    (hqsS : QuasiSeparatedSpace S) (h𝒳 : IsQuasiSeparatedOver.{u, w} B S hS 𝒳)
    {y y' : 𝒳.val.val.obj} (hy : IsAffineObject B S hS 𝒳.val.val.p y)
    (hy' : IsAffineObject B S hS 𝒳.val.val.p y') :
    IsQuasiCompactStack.{u, w} B S hS
        (twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y)
          (objectMorphismAlgebraicStacks B S hS 𝒳 y')).val
        (twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y)
          (objectMorphismAlgebraicStacks B S hS 𝒳 y')).property ∧
      IsQuasiSeparatedOver.{u, w} B S hS
        (twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y)
          (objectMorphismAlgebraicStacks B S hS 𝒳 y')) :=
  isQuasiCompactStack_and_isQuasiSeparatedOver_twoFibreProduct.{u, w} B S hS hqsS
    (objectMorphismAlgebraicStacks B S hS 𝒳 y) (objectMorphismAlgebraicStacks B S hS 𝒳 y')
    (isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS (𝒳.val.val.p.obj y) hy)
    (isQuasiSeparatedOver_schemeStack_of_isAffine.{u, w} B S hS (𝒳.val.val.p.obj y) hy)
    (isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS (𝒳.val.val.p.obj y') hy')
    (isQuasiSeparatedOver_schemeStack_of_isAffine.{u, w} B S hS (𝒳.val.val.p.obj y') hy')
    h𝒳

/-- **The 2-fibre product of the 2-Yoneda 1-morphisms of two objects lying over affine schemes is
a quasi-compact algebraic stack**, for an algebraic stack quasi-separated over a quasi-separated
base scheme. This is the first conjunct of
`AlgebraicGeometry.Stack`
`.isQuasiCompactStack_and_isQuasiSeparatedOver_twoFibreProductAlgebraicStack_objectMorphism`. -/
theorem isQuasiCompactStack_twoFibreProductAlgebraicStack_objectMorphism
    (hqsS : QuasiSeparatedSpace S) (h𝒳 : IsQuasiSeparatedOver.{u, w} B S hS 𝒳)
    {y y' : 𝒳.val.val.obj} (hy : IsAffineObject B S hS 𝒳.val.val.p y)
    (hy' : IsAffineObject B S hS 𝒳.val.val.p y') :
    IsQuasiCompactStack.{u, w} B S hS
        (twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y)
          (objectMorphismAlgebraicStacks B S hS 𝒳 y')).val
        (twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y)
          (objectMorphismAlgebraicStacks B S hS 𝒳 y')).property :=
  (isQuasiCompactStack_and_isQuasiSeparatedOver_twoFibreProductAlgebraicStack_objectMorphism.{u, w}
    B S hS 𝒳 hqsS h𝒳 hy hy').1

/-- **The 2-fibre product of the 2-Yoneda 1-morphisms of two objects lying over affine schemes is
quasi-separated over `S`**, for an algebraic stack quasi-separated over a quasi-separated base
scheme. This is the second conjunct of
`AlgebraicGeometry.Stack`
`.isQuasiCompactStack_and_isQuasiSeparatedOver_twoFibreProductAlgebraicStack_objectMorphism`, and
it is the input condition (4) of Stacks 0GN4 needs in order to apply Stacks 075S part (1) to a
1-morphism whose target is that 2-fibre product. -/
theorem isQuasiSeparatedOver_twoFibreProductAlgebraicStack_objectMorphism
    (hqsS : QuasiSeparatedSpace S) (h𝒳 : IsQuasiSeparatedOver.{u, w} B S hS 𝒳)
    {y y' : 𝒳.val.val.obj} (hy : IsAffineObject B S hS 𝒳.val.val.p y)
    (hy' : IsAffineObject B S hS 𝒳.val.val.p y') :
    IsQuasiSeparatedOver.{u, w} B S hS
      (twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y)
        (objectMorphismAlgebraicStacks B S hS 𝒳 y')) :=
  (isQuasiCompactStack_and_isQuasiSeparatedOver_twoFibreProductAlgebraicStack_objectMorphism.{u, w}
    B S hS 𝒳 hqsS h𝒳 hy hy').2

variable {y y' : 𝒳.val.val.obj}

/-- **A quasi-compact 2-fibre product of two 2-Yoneda 1-morphisms has a quadruple over an affine
scheme which dominates every quadruple after a covering taken downstairs.**

This is the hypothesis of
`AlgebraicGeometry.Stack`
`.isLocallySurjective_prodLift_fppfTopology_of_exists_quadruple_dominating_base`
together with the affineness of the object the dominating quadruple classifies.

**Stacks 04YC** parts (1) and (2) turn quasi-compactness into an affine object `U₀` and a
surjective, relatively smooth 1-morphism `f` from the slice `(Sch/S)/U₀` onto the 2-fibre product;
the quadruple is `Q = f(1_{U₀})`, which lies over `U₀` because `f` is a based functor. Relative
smoothness supplies flatness and local finite presentation, so **Stacks 06QA** covers the base
object of any quadruple `P` by objects over each of which `P` receives a morphism from `f(a)` for
an object `a` of the slice; `f(a)` is the dominating quadruple over that member of the covering,
and its morphism to `Q` is the image under `f` of the structure morphism `a ⟶ 1_{U₀}`. -/
theorem exists_quadruple_dominating
    (hqc : IsQuasiCompactStack.{u, w} B S hS
      (twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y)
        (objectMorphismAlgebraicStacks B S hS 𝒳 y')).val
      (twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y)
        (objectMorphismAlgebraicStacks B S hS 𝒳 y')).property) :
    ∃ Q : twoFibreProductObjects B S hS 𝒳.val y y',
      IsAffineObject B S hS 𝒳.val.val.p (quadObj B S hS 𝒳.val Q) ∧
        ∀ P : twoFibreProductObjects B S hS 𝒳.val y y',
          ∃ R ∈ BigFppfOver.topology B S hS (𝒳.val.val.p.obj (quadObj B S hS 𝒳.val P)),
            ∀ ⦃T : BigFppfOver B S hS⦄
              ⦃k : T ⟶ 𝒳.val.val.p.obj (quadObj B S hS 𝒳.val P)⦄, R.arrows k →
              ∃ (P' : twoFibreProductObjects B S hS 𝒳.val y y') (ψ : P' ⟶ P) (_ : P' ⟶ Q),
                𝒳.val.val.p.IsHomLift k (quadMap B S hS 𝒳.val ψ) := by
  classical
  set 𝒬 := twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y)
    (objectMorphismAlgebraicStacks B S hS 𝒳 y') with h𝒬
  obtain ⟨U₀, hU₀, f, hsurj, hsmooth⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒬).1 hqc
  obtain ⟨hfrep, hrel⟩ := hsmooth
  have hsm : AlgebraicStacks.IsSmooth B S hS f :=
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ h => Space.IsSmooth B S hS h) 𝒬.property f.hom hfrep hrel
  have hflat : AlgebraicStacks.IsFlat B S hS f :=
    AlgebraicStacks.isFlat_of_isSmooth B S hS f hsm
  have hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f :=
    AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS f hsm
  set F := CatFiberedInGroupoids.homFunctor f.hom with hF
  have hw : F ⋙ 𝒬.val.val.p = (schemeFibredCategory B S hS U₀).val.p := f.hom.hom.w
  -- The dominating quadruple is the image of the terminal object of the slice over `U₀`.
  refine ⟨F.obj (Over.mk (𝟙 U₀)), ?_, ?_⟩
  · have hproj : 𝒳.val.val.p.obj (quadObj B S hS 𝒳.val (F.obj (Over.mk (𝟙 U₀)))) = U₀ :=
      (obj_quadObj B S hS 𝒳.val (F.obj (Over.mk (𝟙 U₀)))).trans
        (Functor.congr_obj hw (Over.mk (𝟙 U₀)))
    change IsAffine ((BigFppfOver.toScheme B S hS).obj
      (𝒳.val.val.p.obj (quadObj B S hS 𝒳.val (F.obj (Over.mk (𝟙 U₀))))))
    rw [hproj]
    exact hU₀
  · intro P
    obtain ⟨R, hR, hlift⟩ := exists_fppfCovering_fibre_lift B S hS f hsurj hflat hlfp
      (𝒳.val.val.p.obj (quadObj B S hS 𝒳.val P))
      (Functor.Fiber.mk (a := P) (obj_quadObj B S hS 𝒳.val P).symm)
    refine ⟨R, hR, ?_⟩
    intro T k hk
    obtain ⟨a, φ, hφ⟩ := hlift hk
    exact ⟨F.obj a, φ, F.map (Over.homMk a.hom (Category.comp_id a.hom)),
      isHomLift_quadMap B S hS 𝒳.val φ k hφ⟩

/-- **The hom-set form of condition (2)(c) of Stacks 0GMS for the fppf site of an algebraic stack
quasi-separated over a quasi-separated base scheme.** For two objects `U`, `U'` of the site lying
over affine schemes there is a *single* object `V` lying over an affine scheme, with morphisms
`p : V ⟶ U` and `q : V ⟶ U'`, through which every pair of morphisms `α : y ⟶ U`, `β : y ⟶ U'` of
the site factors after passing to a covering of `y`.

This is the site-level content of
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_prodLift`, and the form in
which condition (2)(c) survives transport to an equi-universe model of the fppf site: it mentions
only the hom-sets of the site, so `CategoryTheory.exists_covering_hom_pair_inverse` carries it
across the universe gap that the sheaf-level condition does not cross.

`V` is the object the quadruple of
`AlgebraicGeometry.Stack.exists_quadruple_dominating` classifies, with the two morphisms that
quadruple classifies; the factorisation is
`AlgebraicGeometry.Stack.exists_covering_hom_pair_of_exists_quadruple_dominating` composed with
`AlgebraicGeometry.Stack.exists_covering_quadMap_of_exists_quadruple_dominating_base`.
Quasi-compactness of the 2-fibre product, which is what produces the quadruple, is
`AlgebraicGeometry.Stack.isQuasiCompactStack_twoFibreProductAlgebraicStack_objectMorphism`. -/
theorem exists_affineObject_exists_covering_hom_pair
    (hqsS : QuasiSeparatedSpace S) (h𝒳 : IsQuasiSeparatedOver.{u, w} B S hS 𝒳)
    (U : 𝒳.val.val.obj) (hU : U ∈ affineObjects B S hS 𝒳.val)
    (U' : 𝒳.val.val.obj) (hU' : U' ∈ affineObjects B S hS 𝒳.val) :
    ∃ V : 𝒳.val.val.obj, V ∈ affineObjects B S hS 𝒳.val ∧
      ∃ (p : V ⟶ U) (q : V ⟶ U'),
        ∀ (y : 𝒳.val.val.obj) (α : y ⟶ U) (β : y ⟶ U'),
          ∃ T : Sieve y, T ∈ fppfTopology B S hS 𝒳.val y ∧
            ∀ ⦃z : 𝒳.val.val.obj⦄ (g : z ⟶ y), T.arrows g →
              ∃ r : z ⟶ V, r ≫ p = g ≫ α ∧ r ≫ q = g ≫ β := by
  obtain ⟨Q, hQaff, hQ⟩ := exists_quadruple_dominating B S hS 𝒳
    (isQuasiCompactStack_twoFibreProductAlgebraicStack_objectMorphism B S hS 𝒳 hqsS h𝒳 hU hU')
  refine ⟨quadObj B S hS 𝒳.val Q, hQaff, quadFst B S hS 𝒳.val Q, quadSnd B S hS 𝒳.val Q, ?_⟩
  intro y α β
  obtain ⟨T, hT, hfac⟩ := exists_covering_hom_pair_of_exists_quadruple_dominating B S hS 𝒳.val Q
    (exists_covering_quadMap_of_exists_quadruple_dominating_base B S hS 𝒳.val Q hQ) y α β
  refine ⟨T, hT, ?_⟩
  intro z g hg
  obtain ⟨_, r, hr, hr'⟩ := hfac g hg
  exact ⟨r, hr, hr'⟩

/-- **Condition (2)(c) of Stacks 0GMS for the fppf site of an algebraic stack quasi-separated over
a quasi-separated base scheme**, in the shape
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_fppf` consumes as its
hypothesis `h_product`: for two objects `x`, `x'` of the site lying over affine schemes there is a
finite family of such objects, with a morphism to `x` and a morphism to `x'` from each, whose
sheafified representables jointly cover `h_x^# ⨯ h_{x'}^#`.

The family has one member, as in the source: it is the one of
`AlgebraicGeometry.Stack.exists_affineObject_exists_covering_hom_pair`, and the passage from the
factorisation of pairs of morphisms there to the surjection of sheaves here is
`AlgebraicGeometry.Stack.isLocallySurjective_prodLift_fppfTopology_of_exists_covering`. -/
@[stacks 0GMS "condition (2)(c) for the fppf site of an algebraic stack quasi-separated over a \
quasi-separated base scheme, with the collection B of Stacks 0GQV: the objects of the site lying \
over affine schemes; the family produced has one member, as in the source"]
theorem exists_fin_affineObjects_isLocallySurjective_prodLift
    (hqsS : QuasiSeparatedSpace S) (h𝒳 : IsQuasiSeparatedOver.{u, w} B S hS 𝒳) :
    ∀ U ∈ affineObjects B S hS 𝒳.val, ∀ U' ∈ affineObjects B S hS 𝒳.val,
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳.val) ∧
          ∃ (p : ∀ i, V i ⟶ U) (q : ∀ i, V i ⟶ U'),
            Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
              prod.lift ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map (p i))
                ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map (q i))) := by
  intro U hU U' hU'
  obtain ⟨V, hVaff, p, q, hcond⟩ :=
    exists_affineObject_exists_covering_hom_pair B S hS 𝒳 hqsS h𝒳 U hU U' hU'
  refine ⟨1, fun _ => V, fun _ => hVaff, fun _ => p, fun _ => q, ?_⟩
  refine isLocallySurjective_prodLift_fppfTopology_of_exists_covering B S hS 𝒳.val
    (fun _ : Fin 1 => V) (fun _ => p) (fun _ => q) ?_
  intro y α β
  obtain ⟨T, hT, hfac⟩ := hcond y α β
  refine ⟨T, hT, ?_⟩
  intro z g hg
  obtain ⟨r, hr, hr'⟩ := hfac g hg
  exact ⟨0, r, hr, hr'⟩

/-- **Stacks 0GQV in the fppf topology for a quasi-compact algebraic stack which is quasi-separated
over a quasi-separated base scheme, from condition (4) of Stacks 0GN4 alone.**

This is `Stack.isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompactStack` with
its condition (3) discharged by
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_prodLift`. Condition (4), the
corresponding assertion for the equalizer of two parallel morphisms, remains a hypothesis here
because the quadruple of this file does not give it: the 2-fibre product it is about is not the one
of two 2-Yoneda 1-morphisms but the one of the two *graphs* of `a` and `b` over that one. It is
proved, for a stack quasi-separated over a quasi-separated base scheme, as
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_equalizerLift` in
`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomologyEqualizerAffineCover.lean`, and
discharging it there turns this result into the full fppf assertion of Stacks 0GQV,
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompact`. -/
@[stacks 0GQV "for a quasi-compact algebraic stack quasi-separated over a quasi-separated base; \
condition (3) of 0GN4 is proved here and condition (4) is a hypothesis, discharged in \
ColimitsOfCohomologyEqualizerAffineCover"]
theorem isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiSeparatedOver
    (hqsS : QuasiSeparatedSpace S)
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒳 : IsQuasiSeparatedOver.{u, w} B S hS 𝒳)
    (h_equalizer : ∀ {U U' : 𝒳.val.val.obj} (a b : U ⟶ U'),
      U ∈ affineObjects B S hS 𝒳.val → U' ∈ affineObjects B S hS 𝒳.val →
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳.val) ∧
          ∃ (p : ∀ i, V i ⟶ U) (hp : ∀ i, p i ≫ a = p i ≫ b),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            equalizer.lift
              (f := (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map a)
              (g := (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map b)
              ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map (p i)) (by
                simpa only [Functor.map_comp] using
                  congrArg (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map (hp i))))
    (p : ℕ) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (fppfTopology B S hS 𝒳.val) Ab.{u + 1}) :
    IsIso (colimit.post F
      ((Sheaf.Γ (fppfTopology B S hS 𝒳.val) Ab.{u + 1}).rightDerived p)) :=
  isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompactStack.{u, w} B S hS 𝒳 hqc
    (exists_fin_affineObjects_isLocallySurjective_prodLift B S hS 𝒳 hqsS h𝒳) h_equalizer p F

end AffineQuadruple

end AlgebraicGeometry.Stack

end
