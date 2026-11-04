module

public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDeligneMumford

/-!
# Essential smallness of fibres descends along a flat presentation

`StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness` proves that the fibres of an
*algebraic* stack are essentially small, by feeding the descent bound
`CategoryTheory.Functor.essentiallySmall_fiber_of_exists_localIso` with the scheme atlas of
Stacks 026O. The bound itself asks for much less than an atlas: a 1-morphism whose source has
essentially small fibres and which is locally essentially surjective on fibres. This file states
it that way.

The immediate consequence is that essential smallness of the fibres is available for a category
fibred in groupoids *before* it is known to be algebraic, as soon as it receives a 1-morphism
representable by algebraic spaces whose base changes along scheme-valued points are surjective,
flat and locally of finite presentation: such a 1-morphism is locally essentially surjective by
**Stacks 04XD**, and when its source is representable by an algebraic space the source's fibres
are essentially small because a category representable by an algebraic space is an algebraic
stack.

That is exactly the input the engine
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids_of_flatPresentation`
needs and which `AlgebraicGeometry.Stack.essentiallySmall_fiber_algebraicStack` cannot supply
without circularity, algebraicity of the target being the conclusion rather than a hypothesis
there.

## Main results

* `AlgebraicGeometry.Stack.essentiallySmall_fiber_of_isRepresentableByAlgebraicSpace`: the fibres
  of a category representable by an algebraic space are essentially small.
* `AlgebraicGeometry.Stack.essentiallySmall_fiber_of_localEssSurj`: **the descent statement** —
  the fibres of a stack receiving a locally essentially surjective 1-morphism from a category
  with essentially small fibres are essentially small.
* `AlgebraicGeometry.Stack.essentiallySmall_fiber_of_flatPresentation`: the same with local
  essential surjectivity replaced by the hypotheses of Stacks 03YK on the 1-morphism.

## Implementation notes

The small family the descent bound is fed with is the *skeleton* of the fibre of the source,
rather than the fibre itself as in
`AlgebraicGeometry.Stack.essentiallySmall_fiber_algebraicStack`: the bound needs the indexing
family to be small, which the fibre of a scheme-valued point is but the fibre of a category
merely representable by an algebraic space need not be, being only equivalent to a small
category. Composing the skeleton's chosen representatives with the 1-morphism loses nothing,
since a lift is only ever used up to isomorphism.

## References

* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The fibres of a category representable by an algebraic space are essentially small**: such
a category is an algebraic stack by Stacks 026O, so
`AlgebraicGeometry.Stack.essentiallySmall_fiber_algebraicStack` applies. -/
theorem essentiallySmall_fiber_of_isRepresentableByAlgebraicSpace
    (𝒱 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒱 : IsRepresentableByAlgebraicSpace B S hS 𝒱) (V : BigFppfOver B S hS) :
    EssentiallySmall.{u} (𝒱.val.p.Fiber V) :=
  essentiallySmall_fiber_algebraicStack B S hS
    (⟨𝒱, isAlgebraicStack_of_isRepresentableByAlgebraicSpace.{u, u} B S hS 𝒱 h𝒱⟩ :
      AlgebraicStacks.{u, u} B S hS) V

variable {B S hS}
variable {𝒱 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **Essential smallness of fibres descends along a locally essentially surjective
1-morphism.** Let `f : 𝒱 ⟶ 𝒳` be a 1-morphism of categories fibred in groupoids over the big
fppf site of `S` with `𝒳` a stack and the fibres of `𝒱` essentially small, and suppose every
object of every fibre of `𝒳` becomes, along every arrow of some covering sieve, isomorphic to the
image of an object of `𝒱`. Then every fibre of `𝒳` is essentially small.

This is the descent bound `CategoryTheory.Functor.essentiallySmall_fiber_of_exists_localIso` fed
with the skeleta of the fibres of `𝒱` as its small family; the sheaf condition it needs is
condition (2) of Stacks 026F, a projection of the stack hypothesis on `𝒳`. -/
theorem essentiallySmall_fiber_of_localEssSurj (f : 𝒱 ⟶ 𝒳)
    (h𝒳 : Functor.IsStack 𝒳.val.p (BigFppfOver.topology B S hS))
    (hess : ∀ V : BigFppfOver B S hS, EssentiallySmall.{u} (𝒱.val.p.Fiber V))
    (hlift : ∀ (V : BigFppfOver B S hS) (y : 𝒳.val.p.Fiber V),
      ∃ R ∈ BigFppfOver.topology B S hS V,
        ∀ ⦃T : BigFppfOver B S hS⦄ ⦃k : T ⟶ V⦄, R.arrows k →
          ∃ (z : 𝒱.val.obj) (φ : (CatFiberedInGroupoids.homFunctor f).obj z ⟶ y.1),
            𝒳.val.p.IsHomLift k φ)
    (U : BigFppfOver B S hS) : EssentiallySmall.{u} (𝒳.val.p.Fiber U) := by
  classical
  have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have := essentiallySmall_bigFppfOver B S hS
  have hsmall : ∀ V : BigFppfOver B S hS, Small.{u} (Skeleton (𝒱.val.p.Fiber V)) :=
    fun V => ((essentiallySmall_iff (𝒱.val.p.Fiber V)).1 (hess V)).1
  set G := CatFiberedInGroupoids.homFunctor f
  have hG : G ⋙ 𝒳.val.p = 𝒱.val.p := CatFiberedInGroupoids.homFunctor_comp_p f
  refine Functor.essentiallySmall_fiber_of_exists_localIso 𝒳.val.p
    (Zs := fun V => Skeleton (𝒱.val.p.Fiber V))
    (fun V z => (Functor.Fiber.mapOfComp 𝒱.val.p 𝒳.val.p G hG V).obj
      ((fromSkeleton (𝒱.val.p.Fiber V)).obj z))
    (fun V a b => h𝒳.isMorSheaf V a b) ?_ U
  intro V x
  obtain ⟨R, hR, hR'⟩ := hlift V x
  refine ⟨R, hR, fun {T} {k} hk => ?_⟩
  obtain ⟨z, φ, hφ⟩ := hR' hk
  have hzb : 𝒳.val.p.obj (G.obj z) = T := IsHomLift.domain_eq 𝒳.val.p k φ
  have hcart : 𝒳.val.p.IsStronglyCartesian k φ :=
    𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift k φ
  set zT : 𝒱.val.p.Fiber T := Functor.Fiber.mk ((Functor.congr_obj hG z).symm.trans hzb)
  have hmk : (Functor.Fiber.mapOfComp 𝒱.val.p 𝒳.val.p G hG T).obj zT
      = (Functor.Fiber.mk hzb : 𝒳.val.p.Fiber T) := rfl
  exact ⟨toSkeleton zT, ⟨(Functor.Restriction.ofCartesian hzb x.2 φ hcart).fiberIso ≪≫
    eqToIso hmk.symm ≪≫
    ((Functor.Fiber.mapOfComp 𝒱.val.p 𝒳.val.p G hG T).mapIso
      (fromSkeletonToSkeletonIso zT)).symm⟩⟩

/-- **Essential smallness of fibres descends along a flat presentation.** Let `f : 𝒱 ⟶ 𝒳` be a
1-morphism of categories fibred in groupoids over the big fppf site of `S` with `𝒳` a stack and
the fibres of `𝒱` essentially small, representable by algebraic spaces, and with every algebraic
space representing a base change of `f` along a scheme-valued point of `𝒳` surjective, flat and
locally of finite presentation. Then every fibre of `𝒳` is essentially small.

Stacks 04XD makes such an `f` locally essentially surjective, so
`AlgebraicGeometry.Stack.essentiallySmall_fiber_of_localEssSurj` applies. -/
theorem essentiallySmall_fiber_of_flatPresentation (f : 𝒱 ⟶ 𝒳)
    (h𝒳 : Functor.IsStack 𝒳.val.p (BigFppfOver.topology B S hS))
    (hess : ∀ V : BigFppfOver B S hS, EssentiallySmall.{u} (𝒱.val.p.Fiber V))
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hprop : ∀ (V : BigFppfOver B S hS)
      (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
      (_hy : y ⋙ 𝒳.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒱.val.p 𝒳.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let g := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS g ∧ Space.IsFlat B S hS g ∧
         Space.IsLocallyOfFinitePresentation B S hS g))
    (U : BigFppfOver B S hS) : EssentiallySmall.{u} (𝒳.val.p.Fiber U) :=
  essentiallySmall_fiber_of_localEssSurj f h𝒳 hess
    (localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS f hf hprop) U

end AlgebraicGeometry.Stack

end
