module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialityComparisonFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.BaseChangeGroupoidArrows
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.BaseChangeQuotientStackComparisonFull
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.BaseChangeQuotientStackComparisonSurjective
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackEquivalence

/-!
# Stacks 0DTG: the base-change square of quotient stacks is a 2-fibre product

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, let `φ : U ⟶ X` be an `R`-invariant morphism of algebraic spaces
over `B`, let `g : X' ⟶ X` be a morphism of algebraic spaces over `B` and let
`(U', R', s', t', c')` be the base change of Stacks 048G. This file proves the **fullness** of the
comparison 1-morphism `c : [U'/R'] ⟶ [U/R] ×_{𝒮_X} 𝒮_{X'}` of
`AlgebraicGeometry.Stack.baseChangeQuotientStackComparison`, which was the one hypothesis left
standing in `AlgebraicGeometry.Stack.isTwoFibreProduct_baseChangeQuotientStackSquare`, and
concludes that the square

    [U'/R'] ---> [U/R]
      |            |
      v            v
     𝒮_{X'} ---> 𝒮_X

is a 2-fibre product.

## Main definitions

* `AlgebraicGeometry.Stack.baseChangeQuotientStackSquare_isTwoFibreProduct`: **Stacks 0DTG**, the
  2-fibre-product assertion for the square
  `AlgebraicGeometry.Stack.baseChangeQuotientStackSquare`.

## Main results

* `AlgebraicGeometry.Stack.full_and_faithful_toQuotientStack_comp_comparison`: the restriction of
  the comparison 1-morphism to the presentation of `[U'/R']` is full and faithful — **not** merely
  locally so.
* `AlgebraicGeometry.Stack.isLocallyBijective_morPresheafMap_comparison`: the hypothesis of
  `AlgebraicGeometry.Stack.full_baseChangeQuotientStackComparison_of_morPresheafMap`.
* `AlgebraicGeometry.Stack.full_baseChangeQuotientStackComparison`: **the comparison 1-morphism of
  Stacks 0DTG is full.**

## Implementation notes

*The argument.* Fullness of the restriction to the presentation is checked fibrewise, by
Stacks 003Z (1) in the form
`CategoryTheory.Functor.IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber`. On the fibre
over a test object `T` a vertical morphism `Φ` of the 2-fibre product between the images of two
`T`-points `u₁, u₂` of `U'` has two components. Its `𝒮_{X'}`-component is a vertical morphism of
a category fibred in **sets**, so it forces the two `T`-points of `X'` that `u₁` and `u₂` name to
agree. Its `[U/R]`-component, transported along the 2-isomorphism of Stacks 046Q
(`AlgebraicGeometry.Stack.quotientStackMap_commutes`), is a vertical morphism of `[U/R]` between
the objects presented by the images of `u₁` and `u₂` in `U`, so by Stacks 044X (2) in the form
`AlgebraicGeometry.Stack.exists_evaluationArrow` it is the image of an arrow `r` of the evaluated
groupoid `G(T)`. Since the two `T`-points of `X'` agree, the cartesian square `R' = X' ×_X R`
lifts `r` to an arrow of the evaluated groupoid of the base change
(`AlgebraicGeometry.Space.exists_baseChangeEvaluationArrow`), and the image of that arrow is `Φ`:
the `[U/R]`-components agree by the naturality of Stacks 046Q, and a morphism of this 2-fibre
product is determined by its `[U/R]`-component
(`AlgebraicGeometry.Stack.baseChangeTwoFibreProduct_hom_ext`), the 2-fibre product being taken
over a category fibred in sets.

Full faithfulness of the restriction then makes the induced maps of morphism presheaves
**isomorphisms** (`CategoryTheory.Comma.isIso_morPresheafMap_of_fullyFaithful`), hence locally
bijective, which is what Stacks 04WQ consumes.

*Why the proof is split.* The destructuring of an object of a fibre of the presentation as a
`T`-point of `U'` is isolated in `exists_vertical_hom_of_fiber`. Carried out inside the
fibrewise-fullness proof it makes the term the kernel has to check large enough to hit its
deterministic timeout: the identifications it leaves behind unfold
`AlgebraicGeometry.Space.baseChange` and the three stages of the stackification. For the same
reason the base morphism of `Φ` is never
compared with `𝟙 T` — that comparison asks the kernel to see through the stackification — and the
verticality of the two components is read off `Φ` itself instead, by
`CategoryTheory.TwoFibreProductOver.isHomLift_a` and
`CategoryTheory.TwoFibreProductOver.isHomLift_b`.

*The vacuous universe.* `AlgebraicGeometry.Stack.liftedQuotientStackToBase_obj_presented` and
`AlgebraicGeometry.Stack.baseChangeQuotientStackComparison` each carry a universe parameter that
their statements do not constrain, since `CategoryTheory.ULiftHom.{w} C` is an alias for `C`;
every use below instantiates it explicitly, as otherwise the elaborator leaves a universe
metavariable and rejects the declaration.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 048G](https://stacks.math.columbia.edu/tag/048G)
* [Stacks Project, Tag 04WQ](https://stacks.math.columbia.edu/tag/04WQ)
* [Stacks Project, Tag 0DTG](https://stacks.math.columbia.edu/tag/0DTG)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Pseudofunctor

namespace AlgebraicGeometry.Stack

universe u w

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

/- Cancellation of a conjugating isomorphism, over plain variables. -/
private theorem cancel_conj_aux {D : Type*} [Category* D] {P₁ P₂ Q₁ Q₂ : D}
    (H₁ : P₁ ⟶ Q₁) (I₁ : Q₁ ⟶ P₁) (H₂ : P₂ ⟶ Q₂) (I₂ : Q₂ ⟶ P₂)
    (Φa A : Q₁ ⟶ Q₂) (M : P₁ ⟶ P₂)
    (hM : M = H₁ ≫ Φa ≫ I₂) (hN : M ≫ H₂ = H₁ ≫ A)
    (h₁ : I₁ ≫ H₁ = 𝟙 Q₁) (h₂ : I₂ ≫ H₂ = 𝟙 Q₂) : A = Φa := by
  calc A = (I₁ ≫ H₁) ≫ A := by rw [h₁, Category.id_comp]
    _ = I₁ ≫ M ≫ H₂ := by rw [Category.assoc, hN]
    _ = Φa := by simp [hM, reassoc_of% h₁, h₂]

section BaseChange

variable (G : GroupoidInAlgebraicSpaces C S hS B) {X X' : AlgebraicSpaces C S hS}
  (XtoB : X ⟶ B) (X'toB : X' ⟶ B) (g : X' ⟶ X) (hg : g ≫ XtoB = X'toB)
  (φ : G.objects ⟶ X) (hφB : φ ≫ XtoB = G.objectsToBase)
  (hφ : Space.IsInvariant (Space.groupoidPreRelation G) φ.hom)

/- The 2-isomorphism of Stacks 046Q for the base-change morphism of groupoids. -/
private noncomputable abbrev baseChangeCommutes :=
  quotientStackMap_commutes (invariantBaseChangeGroupoidHom (G := G) (XtoB := XtoB)
    (X'toB := X'toB) (g := g) (hg := hg) (φ := φ) (hφB := hφB) (hφ := hφ))

/- The vertical half of fullness of the restriction of the Stacks 0DTG comparison to the
presentation. -/
private theorem exists_prestack_hom_of_vertical (T : BigFppfOver C S hS)
    (u₁ u₂ : (invariantBaseChangeGroupoid G XtoB g φ hφB hφ).objects.obj.obj (op T))
    (Φ : (baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).obj
        ((pointwiseToQuotientStack
          (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).obj ⟨T, u₁⟩) ⟶
      (baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).obj
        ((pointwiseToQuotientStack
          (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).obj ⟨T, u₂⟩))
    (hΦa : (quotientStack (invariantTargetGroupoid G XtoB φ hφB hφ)).p.IsHomLift (𝟙 T) Φ.a)
    (hΦb : (liftedFibredCategory X').p.IsHomLift (𝟙 T) Φ.b) :
    ∃ ψ : (⟨T, u₁⟩ : (presheafOfGroupoids (evaluationGroupoidFunctor
        (invariantBaseChangeGroupoid G XtoB g φ hφB hφ).toGroupoidInFunctors)).obj) ⟶ ⟨T, u₂⟩,
      (baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).map
        ((pointwiseToQuotientStack
          (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).map ψ) = Φ := by
  -- the `𝒮_{X'}`-components agree, so the two `T`-points of `X'` agree
  have hy := obj_eq_of_isHomLift_lifted (𝟙 T) Φ.b (𝟙 _) hΦb
    (IsHomLift.id (IsHomLift.codomain_eq (liftedFibredCategory X').p (𝟙 T) Φ.b))
  have hx : (invariantBaseChangeGroupoid G XtoB g φ hφB hφ).objectsToBase.hom.app (op T) u₁ =
      (invariantBaseChangeGroupoid G XtoB g φ hφB hφ).objectsToBase.hom.app (op T) u₂ :=
    eq_of_fibredObj_eq (congrArg (liftedFibredCategoryDown X').obj
      ((liftedQuotientStackToBase_obj_presented.{u, u}
          (invariantBaseChangeGroupoid G XtoB g φ hφB hφ) T u₁).symm.trans
        (hy.trans (liftedQuotientStackToBase_obj_presented.{u, u}
          (invariantBaseChangeGroupoid G XtoB g φ hφB hφ) T u₂))))
  -- the `[U/R]`-component, read on the presentation of `[U/R]`
  have hHom₁ := (baseChangeCommutes G XtoB X'toB g hg φ hφB hφ).hom.isHomLift'
    (⟨T, u₁⟩ : (presheafOfGroupoids (evaluationGroupoidFunctor
      (invariantBaseChangeGroupoid G XtoB g φ hφB hφ).toGroupoidInFunctors)).obj)
  have hInv₂ := (baseChangeCommutes G XtoB X'toB g hg φ hφB hφ).inv.isHomLift'
    (⟨T, u₂⟩ : (presheafOfGroupoids (evaluationGroupoidFunctor
      (invariantBaseChangeGroupoid G XtoB g φ hφB hφ).toGroupoidInFunctors)).obj)
  have hm : (quotientStack (invariantTargetGroupoid G XtoB φ hφB hφ)).p.IsHomLift (𝟙 T)
      ((baseChangeCommutes G XtoB X'toB g hg φ hφB hφ).hom.toNatTrans.app ⟨T, u₁⟩ ≫ Φ.a ≫
        (baseChangeCommutes G XtoB X'toB g hg φ hφB hφ).inv.toNatTrans.app ⟨T, u₂⟩) :=
    isHomLift_id_comp _ (𝟙 T) _ _ hHom₁ (isHomLift_id_comp _ (𝟙 T) _ _ hΦa hInv₂)
  obtain ⟨arr, harr⟩ := exists_evaluationArrow (invariantTargetGroupoid G XtoB φ hφB hφ) T _ _ _ hm
  obtain ⟨arr', harr'⟩ := Space.exists_baseChangeEvaluationArrow
    (invariantTargetGroupoid G XtoB φ hφB hφ) g T u₁ u₂ hx arr
  refine ⟨(CoGrothendieck.ι (evaluationGroupoidFunctor
      (invariantBaseChangeGroupoid G XtoB g φ hφB hφ).toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor' T).map arr', ?_⟩
  refine baseChangeTwoFibreProduct_hom_ext G XtoB g φ hφB hφ _ _ ?_
  refine cancel_conj_aux _
    ((baseChangeCommutes G XtoB X'toB g hg φ hφB hφ).inv.toNatTrans.app ⟨T, u₁⟩) _ _ Φ.a _ _ rfl ?_
    (quotientStackMap_commutes_inv_hom_app _ _) (quotientStackMap_commutes_inv_hom_app _ _)
  refine Eq.trans ?_ (quotientStackMap_commutes_naturality
    (invariantBaseChangeGroupoidHom (G := G) (XtoB := XtoB) (X'toB := X'toB) (g := g) (hg := hg)
      (φ := φ) (hφB := hφB) (hφ := hφ)) _)
  exact congrArg
    (fun k => k ≫ (baseChangeCommutes G XtoB X'toB g hg φ hφB hφ).hom.toNatTrans.app ⟨T, u₂⟩)
    (harr.symm.trans (congrArg
      (fun k => (pointwiseToQuotientStack (invariantTargetGroupoid G XtoB φ hφB hφ)).map k)
      ((congrArg (fun k => (CoGrothendieck.ι (evaluationGroupoidFunctor
          (invariantTargetGroupoid G XtoB φ hφB hφ).toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor' T).map k) harr').symm.trans
        (quotientPointwiseMap_map_ι (invariantBaseChangeGroupoidHom (G := G) (XtoB := XtoB)
          (X'toB := X'toB) (g := g) (hg := hg) (φ := φ) (hφB := hφB) (hφ := hφ)) T arr').symm)))

/- **The vertical half of fullness, read on a pair of objects of a fibre of the presentation.** -/
private theorem exists_vertical_hom_of_fiber (T : BigFppfOver C S hS)
    (W₁ W₂ : (quotientPrestack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p.Fiber T)
    (Φ : (toQuotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ) ⋙
          baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).obj W₁.1 ⟶
        (toQuotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ) ⋙
          baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).obj W₂.1)
    (hΦ : (baseChangeTwoFibreProduct G XtoB g φ hφB hφ).IsHomLift (𝟙 T) Φ) :
    ∃ χ : W₁.1 ⟶ W₂.1,
      (toQuotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ) ⋙
        baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).map χ = Φ := by
  obtain ⟨⟨b₁, u₁⟩, h₁⟩ := W₁
  obtain ⟨⟨b₂, u₂⟩, h₂⟩ := W₂
  have e₁ : b₁ = T := h₁
  subst e₁
  have e₂ : b₂ = b₁ := h₂
  subst e₂
  have hΦa := TwoFibreProductOver.isHomLift_a Φ (𝟙 b₂) hΦ
  have hΦb := TwoFibreProductOver.isHomLift_b Φ (𝟙 b₂) hΦ
  obtain ⟨ψ, hψ⟩ := exists_prestack_hom_of_vertical.{u, w} G XtoB X'toB g hg φ hφB hφ
    b₂ u₁ u₂ Φ hΦa hΦb
  exact ⟨ULift.up ψ, hψ⟩

/- **Stacks 003Z (1) for fullness of the restriction, on one fibre.** -/
private theorem full_fiber_toQuotientStack_comp_comparison (T : BigFppfOver C S hS) :
    (Functor.Fiber.mapOfComp
      (quotientPrestack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p
      (baseChangeTwoFibreProduct G XtoB g φ hφB hφ)
      (toQuotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ) ⋙
        baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ)
      ((isFibredOneMorphism_toQuotientStack
            (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).comp
          (isFibredOneMorphism_baseChangeQuotientStackComparison.{u, w}
            G XtoB X'toB g hg φ hφB hφ)).comp_eq T).Full := by
  refine ⟨fun {W₁ W₂} Ψ => ?_⟩
  obtain ⟨χ, hχ⟩ := exists_vertical_hom_of_fiber.{u, w} G XtoB X'toB g hg φ hφB hφ T W₁ W₂
    (Functor.Fiber.fiberInclusion.map Ψ) Ψ.2
  have hχlift : (quotientPrestack
      (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p.IsHomLift (𝟙 T) χ :=
    (Functor.isHomLift_map_iff_of_comp_eq
      (quotientPrestack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p
      (baseChangeTwoFibreProduct G XtoB g φ hφB hφ) _
      ((isFibredOneMorphism_toQuotientStack
            (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).comp
          (isFibredOneMorphism_baseChangeQuotientStackComparison.{u, w}
            G XtoB X'toB g hg φ hφB hφ)).comp_eq (𝟙 T) χ).mp (by rw [hχ]; exact Ψ.2)
  refine ⟨Functor.Fiber.homMk
    (quotientPrestack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p T χ,
    Functor.Fiber.hom_ext ?_⟩
  refine (Functor.Fiber.fiberInclusion_map_mapOfComp_map
    (quotientPrestack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p
    (baseChangeTwoFibreProduct G XtoB g φ hφB hφ)
    (toQuotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ) ⋙
      baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ)
    ((isFibredOneMorphism_toQuotientStack
          (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).comp
        (isFibredOneMorphism_baseChangeQuotientStackComparison.{u, w}
          G XtoB X'toB g hg φ hφB hφ)).comp_eq T _).trans ?_
  refine Eq.trans (congrArg (fun k =>
    (toQuotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ) ⋙
      baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).map k)
    (Functor.Fiber.fiberInclusion_homMk
      (quotientPrestack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p T χ)) hχ

/- **Stacks 003Z (1) for faithfulness of the restriction, on one fibre.** -/
private theorem faithful_fiber_toQuotientStack_comp_comparison (T : BigFppfOver C S hS) :
    (Functor.Fiber.mapOfComp
      (quotientPrestack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p
      (baseChangeTwoFibreProduct G XtoB g φ hφB hφ)
      (toQuotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ) ⋙
        baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ)
      ((isFibredOneMorphism_toQuotientStack
            (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).comp
          (isFibredOneMorphism_baseChangeQuotientStackComparison.{u, w}
            G XtoB X'toB g hg φ hφB hφ)).comp_eq T).Faithful := by
  have := faithful_comparison.{u, w} G XtoB X'toB g hg φ hφB hφ
  have := (toQuotientStackFullyFaithful
    (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).faithful
  have : (Functor.Fiber.fiberInclusion
      (p := (quotientPrestack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p) (S := T) ⋙
    toQuotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ) ⋙
      baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).Faithful :=
    Functor.Faithful.comp _ _
  exact Functor.Faithful.of_comp_eq (Functor.Fiber.mapOfComp_comp_fiberInclusion
    (quotientPrestack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p
    (baseChangeTwoFibreProduct G XtoB g φ hφB hφ) _
    ((isFibredOneMorphism_toQuotientStack
          (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).comp
        (isFibredOneMorphism_baseChangeQuotientStackComparison.{u, w}
          G XtoB X'toB g hg φ hφB hφ)).comp_eq T)

/-- **The restriction of the Stacks 0DTG comparison to the presentation is full and faithful.** -/
theorem full_and_faithful_toQuotientStack_comp_comparison :
    (toQuotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ) ⋙
        baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).Full ∧
      (toQuotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ) ⋙
        baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).Faithful :=
  (Functor.IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber
    (quotientPrestack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p
    (baseChangeTwoFibreProduct G XtoB g φ hφB hφ)
    (isFiberedInGroupoids_quotientPrestack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ))
    (isFiberedInGroupoids_baseChangeTwoFibreProduct G XtoB g φ hφB hφ) _
    ((isFibredOneMorphism_toQuotientStack
          (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).comp
        (isFibredOneMorphism_baseChangeQuotientStackComparison.{u, w}
          G XtoB X'toB g hg φ hφB hφ)).comp_eq).mpr
    (fun T => ⟨full_fiber_toQuotientStack_comp_comparison.{u, w} G XtoB X'toB g hg φ hφB hφ T,
      faithful_fiber_toQuotientStack_comp_comparison.{u, w} G XtoB X'toB g hg φ hφB hφ T⟩)

/-- **The last hypothesis of Stacks 0DTG.** -/
theorem isLocallyBijective_morPresheafMap_comparison :
    have := isFibered_baseChangeTwoFibreProduct G XtoB g φ hφB hφ
    ∀ (T : BigFppfOver C S hS)
      (x y : (quotientPrestack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p.Fiber T),
      Presheaf.IsLocallyInjective ((BigFppfOver.topology C S hS).over T)
          (((isFibredOneMorphism_toQuotientStack
                (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).comp
              (isFibredOneMorphism_baseChangeQuotientStackComparison.{u, w}
                G XtoB X'toB g hg φ hφB hφ)).morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective ((BigFppfOver.topology C S hS).over T)
          (((isFibredOneMorphism_toQuotientStack
                (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).comp
              (isFibredOneMorphism_baseChangeQuotientStackComparison.{u, w}
                G XtoB X'toB g hg φ hφB hφ)).morPresheafMap x y) := by
  obtain ⟨hfull, hfaith⟩ :=
    full_and_faithful_toQuotientStack_comp_comparison.{u, w} G XtoB X'toB g hg φ hφB hφ
  have := hfull
  have := hfaith
  intro hfib T x y
  have := hfib
  have := Comma.isIso_morPresheafMap_of_fullyFaithful
    ((isFibredOneMorphism_toQuotientStack
          (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).comp
        (isFibredOneMorphism_baseChangeQuotientStackComparison.{u, w}
          G XtoB X'toB g hg φ hφB hφ)) x y
  exact ⟨inferInstance, inferInstance⟩

/-- **The comparison 1-morphism of Stacks 0DTG is full.** This discharges the last hypothesis of
`AlgebraicGeometry.Stack.isTwoFibreProduct_baseChangeQuotientStackSquare`. -/
theorem full_baseChangeQuotientStackComparison :
    (baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).Full :=
  full_baseChangeQuotientStackComparison_of_morPresheafMap.{u, w} G XtoB X'toB g hg φ hφB hφ
    (isLocallyBijective_morPresheafMap_comparison.{u, w} G XtoB X'toB g hg φ hφB hφ)

/-- **Stacks 0DTG, the 2-fibre product.** For a groupoid in algebraic spaces `(U, R, s, t, c)`
over an algebraic space `B` over a scheme `S` of a big fppf site, an `R`-invariant morphism
`φ : U ⟶ X` of algebraic spaces over `B` and a morphism `g : X' ⟶ X` of algebraic spaces over
`B`, the 2-commutative square

    [U'/R'] ---> [U/R]
      |            |
      v            v
     𝒮_{X'} ---> 𝒮_X

of `AlgebraicGeometry.Stack.baseChangeQuotientStackSquare` is a 2-fibre product (Stacks 003Q),
where `(U', R', s', t', c')` is the base change of Stacks 048G.

Its comparison 1-morphism is faithful by
`AlgebraicGeometry.Stack.faithful_comparison`, locally essentially surjective on fibres by
`AlgebraicGeometry.Stack.locallyEssSurjOnFibers_baseChangeQuotientStackComparison` and full by
`AlgebraicGeometry.Stack.full_baseChangeQuotientStackComparison`. -/
@[stacks 0DTG]
noncomputable def baseChangeQuotientStackSquare_isTwoFibreProduct :
    Bicategory.IsTwoFibreProduct
      (baseChangeQuotientStackSquare.{u, w} G XtoB X'toB g hg φ hφB hφ) :=
  isTwoFibreProduct_baseChangeQuotientStackSquare.{u, w} G XtoB X'toB g hg φ hφB hφ
    (full_baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ)
    (faithful_comparison.{u, w} G XtoB X'toB g hg φ hφB hφ)
    (locallyEssSurjOnFibers_baseChangeQuotientStackComparison.{u, w}
      G XtoB X'toB g hg φ hφB hφ)

end BaseChange

end AlgebraicGeometry.Stack

end
