module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteQuotientLocalObjects
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackGroupoid
public import StacksFrontier.CategoryTheory.Sites.Stackification.ExtensionFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Stackification.GroupoidStackification
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalProperty

/-!
# From the comparison of quotient stacks to an equivalence after enlarging the big site

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B`, let `G` be
a groupoid in algebraic spaces over an algebraic space over `S` for `B`, and let `f` be the
morphism of sites determined by the localized inclusion. This file turns the canonical comparison

`u_p [U/R] ⟶ [f⁻¹U/f⁻¹R]`

into an equivalence `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]` of stacks over the enlarged localized big fppf
site, given that the comparison sheafifies the morphism presheaves of `u_p [U/R]`.

`f⁻¹[U/R]` is by Stacks 04WJ the stackification of `u_p [U/R]`, and the comparison satisfies
clause (2) of Stacks 02ZN. So as soon as it satisfies clause (1) it exhibits `[f⁻¹U/f⁻¹R]` as a
second stackification of `u_p [U/R]`, and the two agree: the universal property of Stacks 0435
produces a 1-morphism `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]` restricting to the canonical 1-morphism into
`f⁻¹[U/R]`, Stacks 04WQ makes that 1-morphism fully faithful because the composite is locally
fully faithful, clause (2) for `f⁻¹[U/R]` makes it locally essentially surjective on fibres, and
Stacks 046N converts the two into an equivalence over the enlarged site.

The remaining clause is isolated as `AlgebraicGeometry.Stack.SheafifiesMorPresheaves`, and
`AlgebraicGeometry.Stack.sheafifiesMorPresheaves_of_locally` reduces it to two statements about
raw morphisms: that the comparison identifies only locally equal morphisms, and that every
morphism between its values is locally in its image. No `@[stacks 04WX]` attribute is placed in
this file, because the equivalence is proved only under that hypothesis.

## Main definitions

* `AlgebraicGeometry.Stack.SheafifiesMorPresheaves`: clause (1) of Stacks 02ZN for the canonical
  comparison.
* `AlgebraicGeometry.Stack.changeBigSiteQuotientEquivalenceFunctor`: the 1-morphism
  `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]`.
* `AlgebraicGeometry.Stack.changeBigSiteQuotientEquivalenceUnit`: its restriction along the
  comparison is the canonical 1-morphism `u_p [U/R] ⟶ f⁻¹[U/R]`.

## Main results

* `AlgebraicGeometry.Stack.isFiberedInGroupoids_pullbackQuotientStackProj`: **Stacks 04WH** for
  `u_p [U/R]`.
* `AlgebraicGeometry.Stack.isLocallyBijective_toPullbackQuotientStack` and
  `AlgebraicGeometry.Stack.essImage_toPullbackQuotientStack`: the two clauses of Stacks 02ZN for
  the canonical 1-morphism `u_p [U/R] ⟶ f⁻¹[U/R]`.
* `AlgebraicGeometry.Stack.isFiberedInGroupoids_pullbackQuotientStack`: **Stacks 02ZP** for
  `f⁻¹[U/R]`.
* `AlgebraicGeometry.Stack.sheafifiesMorPresheaves_of_locally`: the reduction of clause (1) to
  local injectivity and local surjectivity on raw morphisms.
* `AlgebraicGeometry.Stack.full_changeBigSiteQuotientEquivalenceFunctor` and
  `AlgebraicGeometry.Stack.faithful_changeBigSiteQuotientEquivalenceFunctor`: **Stacks 04WQ** for
  the 1-morphism `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]`.
* `AlgebraicGeometry.Stack.isEquivalenceOver_changeBigSiteQuotientEquivalenceFunctor`: the
  1-morphism is an equivalence of stacks over the enlarged localized big fppf site.

## Implementation notes

`CategoryTheory.Comma.pullbackProj` reports its codomain in the unfolded `CategoryTheory.Over`
form, which the enlarged site's fppf topology is not accepted against, so the statements below are
taken relative to `AlgebraicGeometry.Stack.pullbackQuotientStackProj`, which fixes the codomain.
The comparison of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteQuotientComparison`
is restated against that functor by
`AlgebraicGeometry.Stack.isFibredOneMorphism_changeBigSiteQuotientComparison'`.

Clause (2) of Stacks 02ZN is consumed in the form
`CategoryTheory.Functor.IsLocallyEssImageOnFibers` of
`StacksFrontier.CategoryTheory.FiberedCategory.FibreClause`, which states it for a generic
1-morphism of fibred categories so that the category structure of a fibre is instantiated rather
than synthesised.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 02ZP](https://stacks.math.columbia.edu/tag/02ZP)
* [Stacks Project, Tag 0435](https://stacks.math.columbia.edu/tag/0435)
* [Stacks Project, Tag 046N](https://stacks.math.columbia.edu/tag/046N)
* [Stacks Project, Tag 04WH](https://stacks.math.columbia.edu/tag/04WH)
* [Stacks Project, Tag 04WJ](https://stacks.math.columbia.edu/tag/04WJ)
* [Stacks Project, Tag 04WQ](https://stacks.math.columbia.edu/tag/04WQ)
* [Stacks Project, Tag 04WX](https://stacks.math.columbia.edu/tag/04WX)
-/

@[expose] public noncomputable section


open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) {Bs : AlgebraicSpaces B S hS}
  (G : GroupoidInAlgebraicSpaces B S hS Bs)

/-- `f⁻¹[U/R]` is a fibred category over the enlarged localized big fppf site. -/
instance isFibered_pullbackQuotientStack :
    (pullbackQuotientStack h S hS G).p.IsFibered :=
  (isStack_pullbackQuotientStack h S hS G).isFibered

/-- **Stacks 04WH** for the quotient stack along the localized inclusion of big fppf sites:
`u_p [U/R]` is fibred in groupoids, because `[U/R]` is. -/
theorem isFiberedInGroupoids_pullbackQuotientStackProj :
    (pullbackQuotientStackProj h S hS G).IsFiberedInGroupoids :=
  have : HasNonemptyFiniteLimits (BigFppfOver B S hS) :=
    hasNonemptyFiniteLimits_bigFppfOver S hS
  Comma.isFiberedInGroupoids_pullbackProj _ _ (isFiberedInGroupoids_quotientStack G)
    (inclusionOver_preservesLimitsOfShape_of_nonempty h S hS)

/-- **Clause (1) of Stacks 02ZN for `u_p [U/R] ⟶ f⁻¹[U/R]`**: the canonical 1-morphism
sheafifies the morphism presheaves of `u_p [U/R]`. -/
theorem isLocallyBijective_toPullbackQuotientStack (V : BigFppfOver B' S (largerContains h hS))
    (x y : (pullbackQuotientStackProj h S hS G).Fiber V) :
    Presheaf.IsLocallyInjective ((BigFppfOver.topology B' S (largerContains h hS)).over V)
        ((isFibredOneMorphism_toPullbackQuotientStack h S hS G).morPresheafMap x y) ∧
      Presheaf.IsLocallySurjective ((BigFppfOver.topology B' S (largerContains h hS)).over V)
        ((isFibredOneMorphism_toPullbackQuotientStack h S hS G).morPresheafMap x y) :=
  Functor.isLocallyBijective_morPresheafMap_toStageThree.{u, u, u + 1, u + 1} _ _ V x y

/-- **Clause (2) of Stacks 02ZN for `u_p [U/R] ⟶ f⁻¹[U/R]`**: every object of a fibre of
`f⁻¹[U/R]` is, along a covering sieve, in the essential image on fibres of the canonical
1-morphism. -/
theorem essImage_toPullbackQuotientStack (V : BigFppfOver B' S (largerContains h hS))
    (x : (pullbackQuotientStack h S hS G).p.Fiber V) :
    ∃ R ∈ BigFppfOver.topology B' S (largerContains h hS) V,
      ∀ ⦃W : BigFppfOver B' S (largerContains h hS)⦄ ⦃g : W ⟶ V⦄, R.arrows g →
        (Functor.fiberFunctorOfCompEq
            (isFibredOneMorphism_toPullbackQuotientStack h S hS G).comp_eq W).essImage
          (Functor.pullbackFiber (pullbackQuotientStack h S hS G).p x g) :=
  Functor.essImage_pullbackFiber_toStageThree.{u, u, u + 1, u + 1} _ _ V x

/-- **Stacks 02ZP** for `f⁻¹[U/R]`: the stackification of a category fibred in groupoids is
fibred in groupoids. -/
theorem isFiberedInGroupoids_pullbackQuotientStack :
    (pullbackQuotientStack h S hS G).p.IsFiberedInGroupoids :=
  Functor.Stackification.isFiberedInGroupoids_of_isStackification
    (isFiberedInGroupoids_pullbackQuotientStackProj B B' h S hS G)
    (isStack_pullbackQuotientStack h S hS G)
    (isFibredOneMorphism_toPullbackQuotientStack h S hS G)
    (isLocallyBijective_toPullbackQuotientStack B B' h S hS G)
    (essImage_toPullbackQuotientStack B B' h S hS G)

/-- The canonical comparison `u_p [U/R] ⟶ [f⁻¹U/f⁻¹R]` is a 1-morphism of fibred categories
over the enlarged localized big fppf site, with its source projection written in the folded
form. -/
theorem isFibredOneMorphism_changeBigSiteQuotientComparison' :
    (pullbackQuotientStackProj h S hS G).IsFibredOneMorphism
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p
      (changeBigSiteQuotientComparison B B' h S hS G) :=
  isFibredOneMorphism_changeBigSiteQuotientComparison B B' h S hS G

/-- **Clause (1) of Stacks 02ZN for the canonical comparison `u_p [U/R] ⟶ [f⁻¹U/f⁻¹R]`**: the
induced maps of morphism presheaves are locally injective and locally surjective. -/
abbrev SheafifiesMorPresheaves : Prop :=
  ∀ (V : BigFppfOver B' S (largerContains h hS))
      (a b : (pullbackQuotientStackProj h S hS G).Fiber V),
    Presheaf.IsLocallyInjective ((BigFppfOver.topology B' S (largerContains h hS)).over V)
        ((isFibredOneMorphism_changeBigSiteQuotientComparison' B B' h S hS G).morPresheafMap
          a b) ∧
      Presheaf.IsLocallySurjective ((BigFppfOver.topology B' S (largerContains h hS)).over V)
        ((isFibredOneMorphism_changeBigSiteQuotientComparison' B B' h S hS G).morPresheafMap a b)

/-- **Clause (2) of Stacks 02ZN for the canonical comparison**, with its source projection
written in the folded form. -/
theorem essImage_changeBigSiteQuotientComparison'
    (V : BigFppfOver B' S (largerContains h hS))
    (x : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.Fiber V) :
    ∃ R ∈ BigFppfOver.topology B' S (largerContains h hS) V,
      ∀ ⦃W : BigFppfOver B' S (largerContains h hS)⦄ ⦃g : W ⟶ V⦄, R.arrows g →
        (Functor.fiberFunctorOfCompEq
            (isFibredOneMorphism_changeBigSiteQuotientComparison' B B' h S hS G).comp_eq
              W).essImage
          (Functor.pullbackFiber (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p x g) :=
  essImage_changeBigSiteQuotientComparison B B' h S hS G V x

/-- **Clause (1) of Stacks 02ZN for the comparison, from its two raw forms.** It suffices that
the comparison identify only locally equal morphisms, and that every morphism between values of
the comparison be, over a covering sieve of the base, the image of a morphism. -/
theorem sheafifiesMorPresheaves_of_locally
    (hinj : ∀ {A Bo : Comma.pullbackLocalization (quotientStack G).p (inclusionOver h S hS)}
      (v v' : A ⟶ Bo),
      (changeBigSiteQuotientComparison B B' h S hS G).map v =
        (changeBigSiteQuotientComparison B B' h S hS G).map v' →
      (pullbackQuotientStackProj h S hS G).LocallyEqual
        (BigFppfOver.topology B' S (largerContains h hS)) v v')
    (hsurj : ∀ {A Bo : Comma.pullbackLocalization (quotientStack G).p (inclusionOver h S hS)}
      (θ : (changeBigSiteQuotientComparison B B' h S hS G).obj A ⟶
        (changeBigSiteQuotientComparison B B' h S hS G).obj Bo),
      ∃ T ∈ BigFppfOver.topology B' S (largerContains h hS)
        ((pullbackQuotientStackProj h S hS G).obj A),
      ∀ ⦃w : Comma.pullbackLocalization (quotientStack G).p (inclusionOver h S hS)⦄ (ρ : w ⟶ A),
        T.arrows ((pullbackQuotientStackProj h S hS G).map ρ) →
        ∃ k : w ⟶ Bo, (changeBigSiteQuotientComparison B B' h S hS G).map ρ ≫ θ =
          (changeBigSiteQuotientComparison B B' h S hS G).map k) :
    SheafifiesMorPresheaves B B' h S hS G := fun V a b =>
  ⟨Functor.isLocallyInjective_morPresheafMap
      (isFibredOneMorphism_changeBigSiteQuotientComparison' B B' h S hS G) hinj V a b,
    Functor.isLocallySurjective_morPresheafMap
      (isFibredOneMorphism_changeBigSiteQuotientComparison' B B' h S hS G) hsurj V a b⟩

variable (hmor : SheafifiesMorPresheaves B B' h S hS G)

/-- **The 1-morphism `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]`**, the extension along the canonical comparison
of the canonical 1-morphism `u_p [U/R] ⟶ f⁻¹[U/R]` by the universal property of Stacks 0435. -/
def changeBigSiteQuotientEquivalenceFunctor :
    (quotientStack (changeBigSiteGroupoid B B' h S hS G)).obj ⥤
      (pullbackQuotientStack h S hS G).obj :=
  Functor.Stackification.extend
    (isFibredOneMorphism_changeBigSiteQuotientComparison' B B' h S hS G)
    (isFibredOneMorphism_toPullbackQuotientStack h S hS G)
    hmor
    (fun U x y => (isStack_pullbackQuotientStack h S hS G).isMorSheaf U x y)
    (essImage_changeBigSiteQuotientComparison' B B' h S hS G)
    (isStack_pullbackQuotientStack h S hS G).hasEffectiveDescent

/-- The 1-morphism `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]` is strictly over the enlarged localized big fppf
site. -/
theorem changeBigSiteQuotientEquivalenceFunctor_comp :
    changeBigSiteQuotientEquivalenceFunctor B B' h S hS G hmor ⋙
        (pullbackQuotientStack h S hS G).p =
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p :=
  Functor.Stackification.extend_comp_eq _ _ _ _ _ _

/-- The 1-morphism `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]` is a 1-morphism of fibred categories over the
enlarged localized big fppf site. -/
theorem isFibredOneMorphism_changeBigSiteQuotientEquivalenceFunctor :
    (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsFibredOneMorphism
      (pullbackQuotientStack h S hS G).p
      (changeBigSiteQuotientEquivalenceFunctor B B' h S hS G hmor) :=
  (isFiberedInGroupoids_pullbackQuotientStack B B' h S hS G).isFibredOneMorphism
    (changeBigSiteQuotientEquivalenceFunctor_comp B B' h S hS G hmor)

/-- **The 1-morphism `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]` restricts along the comparison to the canonical
1-morphism `u_p [U/R] ⟶ f⁻¹[U/R]`.** This is the 2-isomorphism of the universal property of
Stacks 0435. -/
def changeBigSiteQuotientEquivalenceUnit :
    changeBigSiteQuotientComparison B B' h S hS G ⋙
        changeBigSiteQuotientEquivalenceFunctor B B' h S hS G hmor ≅
      toPullbackQuotientStack h S hS G :=
  Functor.Stackification.unit _ _ _ _ _ _

/-- The composite of the comparison with the 1-morphism `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]` sheafifies the
morphism presheaves of `u_p [U/R]`, being 2-isomorphic to the canonical 1-morphism into
`f⁻¹[U/R]`. -/
theorem isLocallyBijective_comp_changeBigSiteQuotientEquivalenceFunctor
    (V : BigFppfOver B' S (largerContains h hS))
    (a b : (pullbackQuotientStackProj h S hS G).Fiber V) :
    Presheaf.IsLocallyInjective ((BigFppfOver.topology B' S (largerContains h hS)).over V)
        (((isFibredOneMorphism_changeBigSiteQuotientComparison' B B' h S hS G).comp
          (isFibredOneMorphism_changeBigSiteQuotientEquivalenceFunctor
            B B' h S hS G hmor)).morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective ((BigFppfOver.topology B' S (largerContains h hS)).over V)
        (((isFibredOneMorphism_changeBigSiteQuotientComparison' B B' h S hS G).comp
          (isFibredOneMorphism_changeBigSiteQuotientEquivalenceFunctor
            B B' h S hS G hmor)).morPresheafMap a b) :=
  Functor.Stackification.isLocallyBijective_morPresheafMap_of_natIso
    (isFibredOneMorphism_changeBigSiteQuotientComparison' B B' h S hS G)
    (isFibredOneMorphism_changeBigSiteQuotientEquivalenceFunctor B B' h S hS G hmor)
    (BigFppfOver.topology B' S (largerContains h hS))
    (isFibredOneMorphism_toPullbackQuotientStack h S hS G)
    (changeBigSiteQuotientEquivalenceUnit B B' h S hS G hmor)
    (Functor.Stackification.isHomLift_unit_app _ _ _ _ _ _)
    (isLocallyBijective_toPullbackQuotientStack B B' h S hS G) V a b

/-- **Stacks 04WQ** for the 1-morphism `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]`: it is full. -/
theorem full_changeBigSiteQuotientEquivalenceFunctor :
    (changeBigSiteQuotientEquivalenceFunctor B B' h S hS G hmor).Full :=
  Functor.Stackification.full_of_extension
    (isFibredOneMorphism_changeBigSiteQuotientComparison' B B' h S hS G)
    (isFibredOneMorphism_changeBigSiteQuotientEquivalenceFunctor B B' h S hS G hmor)
    (BigFppfOver.topology B' S (largerContains h hS))
    hmor
    (essImage_changeBigSiteQuotientComparison' B B' h S hS G)
    (isLocallyBijective_comp_changeBigSiteQuotientEquivalenceFunctor B B' h S hS G hmor)
    (isStack_quotientStack (changeBigSiteGroupoid B B' h S hS G)).isMorSheaf
    (isStack_pullbackQuotientStack h S hS G).isMorSheaf

/-- **Stacks 04WQ** for the 1-morphism `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]`: it is faithful. -/
theorem faithful_changeBigSiteQuotientEquivalenceFunctor :
    (changeBigSiteQuotientEquivalenceFunctor B B' h S hS G hmor).Faithful :=
  Functor.Stackification.faithful_of_extension
    (isFibredOneMorphism_changeBigSiteQuotientComparison' B B' h S hS G)
    (isFibredOneMorphism_changeBigSiteQuotientEquivalenceFunctor B B' h S hS G hmor)
    (BigFppfOver.topology B' S (largerContains h hS))
    hmor
    (essImage_changeBigSiteQuotientComparison' B B' h S hS G)
    (isLocallyBijective_comp_changeBigSiteQuotientEquivalenceFunctor B B' h S hS G hmor)
    (isStack_quotientStack (changeBigSiteGroupoid B B' h S hS G)).isMorSheaf
    (isStack_pullbackQuotientStack h S hS G).isMorSheaf

/-- **The 1-morphism `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]` is locally essentially surjective on fibres.**
Every object of a fibre of `f⁻¹[U/R]` is, along a covering sieve, in the essential image on
fibres of the canonical 1-morphism out of `u_p [U/R]`, which factors through it. -/
theorem locallyEssSurjOnFibers_changeBigSiteQuotientEquivalenceFunctor :
    Functor.LocallyEssSurjOnFibers (isStack_pullbackQuotientStack h S hS G).isFibered
      (isFibredOneMorphism_changeBigSiteQuotientEquivalenceFunctor
        B B' h S hS G hmor).comp_eq
      (BigFppfOver.topology B' S (largerContains h hS)) := by
  intro V x
  obtain ⟨R, hR, hloc⟩ := essImage_toPullbackQuotientStack B B' h S hS G V x
  refine ⟨R, hR, ?_⟩
  intro W f hf
  obtain ⟨z, ⟨e⟩⟩ := hloc hf
  refine ⟨(Functor.fiberFunctorOfCompEq
      (isFibredOneMorphism_changeBigSiteQuotientComparison' B B' h S hS G).comp_eq W).obj z, ⟨?_⟩⟩
  refine ?_ ≪≫ e
  refine Functor.Fiber.isoMk
    ((changeBigSiteQuotientEquivalenceUnit B B' h S hS G hmor).app z.1) ?_
  have hz : (pullbackQuotientStack h S hS G).p.IsHomLift
      (𝟙 ((pullbackQuotientStackProj h S hS G).obj z.1))
      ((changeBigSiteQuotientEquivalenceUnit B B' h S hS G hmor).hom.app z.1) :=
    Functor.Stackification.isHomLift_unit_app _ _ _ _ _ _ z.1
  rw [z.2] at hz
  exact hz

/-- **The canonical equivalence `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]`**, as an equivalence in the 2-category
of fibred categories over the enlarged localized big fppf site: a quasi-inverse strictly over the
site, with vertical unit and counit. Both sides are stacks and the 1-morphism is fully faithful,
so Stacks 046N turns local essential surjectivity on fibres into an equivalence.

This is the assertion of Stacks 04WX, under the hypothesis that the canonical comparison
sheafifies the morphism presheaves of `u_p [U/R]`. -/
theorem isEquivalenceOver_changeBigSiteQuotientEquivalenceFunctor :
    Nonempty (Functor.IsEquivalenceOver
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p
      (pullbackQuotientStack h S hS G).p
      (changeBigSiteQuotientEquivalenceFunctor B B' h S hS G hmor)) :=
  have := full_changeBigSiteQuotientEquivalenceFunctor B B' h S hS G hmor
  have := faithful_changeBigSiteQuotientEquivalenceFunctor B B' h S hS G hmor
  (Functor.isEquivalenceOver_iff_locallyEssSurjOnFibers
    (isStack_quotientStack (changeBigSiteGroupoid B B' h S hS G))
    (isStack_pullbackQuotientStack h S hS G)
    (isFibredOneMorphism_changeBigSiteQuotientEquivalenceFunctor B B' h S hS G hmor)).2
    (locallyEssSurjOnFibers_changeBigSiteQuotientEquivalenceFunctor B B' h S hS G hmor)

end AlgebraicGeometry.Stack

end
