module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatDescentAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Gerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeOfFlatInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Gerbes are the algebraic stacks with flat, locally finitely presented inertia (Stacks 06QJ)

**Stacks 06QJ** is the equivalence, for an algebraic stack `𝒳` over `S`, of

1. `𝒳` is a gerbe (**Stacks 06QC**: there is a 1-morphism `𝒳 ⟶ X` to an algebraic stack
   representable by an algebraic space which makes `𝒳` a gerbe over `X`), and
2. the forgetful 1-morphism `I_𝒳 ⟶ 𝒳` of the inertia of `𝒳` is flat and locally of finite
   presentation.

The inertia and its forgetful 1-morphism are the canonical `AlgebraicGeometry.Stack.inertia` and
`CategoryTheory.RelativeInertia.basedProjection`, read in the 2-category of algebraic stacks as
`AlgebraicGeometry.Stack.inertiaAlgebraicStack` and
`AlgebraicGeometry.Stack.inertiaProjectionAlgebraicStacks`; the inertia is an algebraic stack by
**Stacks 050Q**, so clause (2) is a condition on an ordinary 1-morphism of algebraic stacks.

## The two implications and what they rest on

(1) `⟹` (2) is proved directly from a smooth groupoid presentation `𝒳 ≃ [U/R]` (**Stacks 04T3**),
following the argument of Stacks 06PJ and Stacks 06PL rather than the route through Stacks 06QH,
06QG and 06PR. For the gerbe `𝒳 ⟶ Y`, the arrows of `R` cover the related pairs `U ×_Y U` (Stacks
06P1 (2)(b) and Stacks 044X), so the stabilizer of the groupoid is flat and locally of finite
presentation (Stacks 06NR, after one flat cover of `U ×_Y U` over which the arrows have a section);
the automorphism sheaves of `𝒳` are fppf-locally these stabilizers (Stacks 044V), and the two
properties descend (Stacks 041W, Stacks 041T).

The fppf-local form of clause (2) is still named
`AlgebraicGeometry.Stack.AlgebraicStacks.HasFlatLfpLocalInertia`, with its descent by
**Stacks 06PZ** and **Stacks 06Q8**, for the other consumers of that form.

(2) `⟹` (1) is a construction. From a smooth groupoid presentation `𝒳 = [U/R]` (**Stacks 04T3**)
clause (2) makes the stabilizer group `G ⟶ U` of the groupoid flat and locally of finite
presentation, again by Stacks 06PR with **Stacks 06PY** and **Stacks 06Q4**; the quotient
`R' = R/G` of the free action `(g, r) ↦ c(g, r)` is then an algebraic space (**Stacks 06PH**),
`j' = (t', s') : R' ⟶ U × U` is an equivalence relation (**Stacks 043X**, **Stacks 05VY**,
**Stacks 06EV**), the quotient `X = U/R'` is an algebraic space (**Stacks 04S6**, **Stacks 04S1**)
and `[U/R] ⟶ X` is a gerbe (**Stacks 06PE**). This implication is proved unconditionally, as
`Stack.AlgebraicStacks.isGerbe_of_isFlat_and_isLocallyOfFinitePresentation_inertiaProjection`
in `StacksFrontier/AlgebraicGeometry/Stacks/GerbeOfFlatInertia.lean`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasFlatLfpLocalInertia`: an algebraic stack has
  *fppf-locally flat and locally finitely presented inertia* when there is a surjective, flat,
  locally finitely presented 1-morphism `g : 𝒵 ⟶ 𝒳` along which the base change of `I_𝒳 ⟶ 𝒳` is
  flat and locally of finite presentation.

## Main results

All of these live in the namespace `AlgebraicGeometry.Stack.AlgebraicStacks`.

* `isFlat_inertiaProjection_of_hasFlatLfpLocalInertia` and
  `isLocallyOfFinitePresentation_inertiaProjection_of_hasFlatLfpLocalInertia`: clause (2)
  descends from its fppf-local form, by Stacks 06PZ and Stacks 06Q8.
* `isFlat_and_isLocallyOfFinitePresentation_inertiaProjection_of_isGerbe`: **Stacks 06QJ**, the
  implication (1) `⟹` (2).
* `isGerbe_iff_isFlat_and_isLocallyOfFinitePresentation_inertiaProjection`: **Stacks 06QJ**, the
  full equivalence.

## Implementation notes

The fppf-local form of clause (2) is phrased at the *canonical* 2-fibre product of
**Stacks 04T2**, which is the square at which Stacks 06Q8 reads its own hypothesis;
its swap is a 2-fibre product of the reversed cospan
(`CategoryTheory.Bicategory.isTwoFibreProduct_swap`), which is the form Stacks 06PZ takes. One
square serves both descents, so no two apexes of the same cospan have to be compared.

The hypothesis of the implication (1) `⟹` (2) is an implication from the gerbe condition rather
than the local condition itself, so that the equivalence does not degenerate: assuming
`HasFlatLfpLocalInertia` outright would already give clause (2), and the equivalence would say
nothing.

## References

* [Stacks Project, Tag 043X](https://stacks.math.columbia.edu/tag/043X)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
* [Stacks Project, Tag 06PB](https://stacks.math.columbia.edu/tag/06PB)
* [Stacks Project, Tag 06PE](https://stacks.math.columbia.edu/tag/06PE)
* [Stacks Project, Tag 06PQ](https://stacks.math.columbia.edu/tag/06PQ)
* [Stacks Project, Tag 06PR](https://stacks.math.columbia.edu/tag/06PR)
* [Stacks Project, Tag 06PZ](https://stacks.math.columbia.edu/tag/06PZ)
* [Stacks Project, Tag 06Q8](https://stacks.math.columbia.edu/tag/06Q8)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
* [Stacks Project, Tag 06QG](https://stacks.math.columbia.edu/tag/06QG)
* [Stacks Project, Tag 06QH](https://stacks.math.columbia.edu/tag/06QH)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

open GroupoidInAlgebraicSpaces

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic stack `𝒳` over `S` has *fppf-locally flat and locally finitely presented
inertia* when there are an algebraic stack `𝒵` over `S` and a surjective, flat, locally finitely
presented 1-morphism `g : 𝒵 ⟶ 𝒳` such that the base change `𝒵 ×_𝒳 I_𝒳 ⟶ 𝒵` of the forgetful
1-morphism of the inertia is flat and locally of finite presentation.

For a gerbe this is what Stacks 06QH together with Stacks 06QG and Stacks 06PR produce: over a
surjective, flat, locally finitely presented base change the gerbe is a quotient stack `[U/G]`
whose inertia pulls back to the flat, locally finitely presented group `G ⟶ U`. -/
abbrev HasFlatLfpLocalInertia (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) : Prop :=
  ∃ (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) (g : 𝒵 ⟶ 𝒳),
    Stack.IsSurjective B S hS g ∧ IsFlat B S hS g ∧
      IsLocallyOfFinitePresentation B S hS g ∧
      IsFlat B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳) g).snd ∧
      IsLocallyOfFinitePresentation B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳) g).snd

/-- **The inertia projection of an algebraic stack with fppf-locally flat inertia is flat.**
Flatness of the base change descends along the surjective flat 1-morphism by **Stacks 06PZ**,
read at the swap of the canonical 2-fibre-product square. -/
theorem isFlat_inertiaProjection_of_hasFlatLfpLocalInertia
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) (hloc : HasFlatLfpLocalInertia B S hS 𝒳) :
    IsFlat B S hS (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳) := by
  obtain ⟨𝒵, g, hgsurj, hgflat, -, hflat, -⟩ := hloc
  exact isFlat_twoFibreProduct_fst_descent B S hS
    (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳) g
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS
      (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳) g).swap
    (Bicategory.isTwoFibreProduct_swap
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
        (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳) g))
    hgsurj hgflat hflat

/-- **The inertia projection of an algebraic stack with fppf-locally locally finitely presented
inertia is locally of finite presentation.** Local finite presentation of the base change
descends along the surjective, flat, locally finitely presented 1-morphism by
**Stacks 06Q8**. -/
theorem isLocallyOfFinitePresentation_inertiaProjection_of_hasFlatLfpLocalInertia
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) (hloc : HasFlatLfpLocalInertia B S hS 𝒳) :
    IsLocallyOfFinitePresentation B S hS
      (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳) := by
  obtain ⟨𝒵, g, hgsurj, hgflat, hglfp, -, hlfp⟩ := hloc
  exact isLocallyOfFinitePresentation_of_baseChange B S hS
    (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳) g hgsurj hgflat hglfp hlfp

/-- **Stacks 06QJ, the implication (1) `⟹` (2).** If an algebraic stack `𝒳` over `S` is a gerbe,
then the forgetful 1-morphism `I_𝒳 ⟶ 𝒳` of its inertia is flat and locally of finite
presentation.

Let `𝒳 ⟶ Y` make `𝒳` a gerbe over an algebraic space `Y` and choose a smooth groupoid presentation
`𝒳 ≃ [U/R]` (Stacks 04T3). The composite `[U/R] ⟶ Y` is a gerbe, so for its restriction
`ψ : U ⟶ Y` the arrows cover the related pairs `U ×_Y U`
(`AlgebraicGeometry.Stack.isLocallySurjective_of_isGerbeOver_restrictedMorphism`), and the
stabilizer of the groupoid is flat and locally of finite presentation
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isFlat_stabilizer_of_isLocallySurjective`, the
argument of Stacks 06PL and Stacks 06PJ). The automorphism sheaves of `𝒳` are, fppf-locally,
these stabilizers (Stacks 044V), and flatness and local finite presentation descend
(Stacks 041W, Stacks 041T); that is clause (2), by
`AlgebraicGeometry.Stack.isFlat_inertiaProjection_iff_isomSpace`. -/
@[stacks 06QJ "(1) implies (2)"]
theorem isFlat_and_isLocallyOfFinitePresentation_inertiaProjection_of_isGerbe
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsGerbe B S hS 𝒳) :
    IsFlat B S hS (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳) ∧
      IsLocallyOfFinitePresentation B S hS
        (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳) := by
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  obtain ⟨𝒴, ⟨F, hF, ⟨e⟩⟩, f, hf⟩ := h𝒳
  obtain ⟨P⟩ := nonempty_groupoidPresentation B S hS 𝒳.val 𝒳.property
  let G := P.groupoid
  let Yo : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let J := BigFppfOver.topology B S hS
  let r := (fibredCategory B S hS Yo.obj).val.p
  let eF : 𝒴.val.val ⥤ᵇ (fibredCategory B S hS Yo.obj).val := ⟨e.hom.functor, e.hom.w⟩
  let fF : 𝒳.val.val ⥤ᵇ (fibredCategory B S hS Yo.obj).val := BasedFunctor.comp f.hom.hom eF
  let Φ : quotientStack G ⥤ᵇ (fibredCategory B S hS Yo.obj).val :=
    BasedFunctor.comp ⟨P.equivalence.hom.functor, P.equivalence.hom.w⟩ fF
  -- `Φ` is a gerbe: a composite of a gerbe and two equivalences over the site.
  have he : CategoryTheory.IsGerbeOver J r eF.toFunctor :=
    CategoryTheory.IsGerbeOver.of_equivalenceOver
      (fibredCategory B S hS Yo.obj).isFiberedInGroupoids e
  have hfF : CategoryTheory.IsGerbeOver J r fF.toFunctor :=
    CategoryTheory.IsGerbeOver.comp ((congrArg (fun q => CategoryTheory.IsGerbeOver J q
      (CatFiberedInGroupoids.homFunctor f.hom)) eF.w).mpr hf) he
  have hΦ : CategoryTheory.IsGerbeOver J r Φ.toFunctor :=
    CategoryTheory.IsGerbeOver.comp ((congrArg (fun q => CategoryTheory.IsGerbeOver J q
      P.equivalence.hom.functor) fF.w).mpr
        (CategoryTheory.IsGerbeOver.of_equivalenceOver 𝒳.val.isFiberedInGroupoids
          P.equivalence)) hfF
  -- The stabilizer of the presentation is flat and locally of finite presentation.
  let ψ := (restrictedMorphism G Φ).hom
  have hq : G.source.hom ≫ ψ = G.target.hom ≫ ψ := by
    have h := restrictedMorphism_isInvariant G Φ
    rw [Space.IsInvariant, groupoidPreRelation_target_left, groupoidPreRelation_source_left] at h
    exact h.symm
  have hstab := isFlat_stabilizer_of_isLocallySurjective G hF ψ hq
    (isLocallySurjective_of_isGerbeOver_restrictedMorphism G Φ hΦ hq)
    (Space.isFlat_of_isSmooth B S hS _ P.smooth.1)
    (Space.isLocallyOfFinitePresentation_of_isSmooth B S hS P.smooth.1)
  refine ⟨(isFlat_inertiaProjection_iff_isomSpace B S hS 𝒳).2 fun U x => ?_,
    (isLocallyOfFinitePresentation_inertiaProjection_iff_isomSpace B S hS 𝒳).2 fun U x => ?_⟩ <;>
  exact holdsOnEveryEtaleChart_isomPresheaf_of_presentation B S hS 𝒳.val 𝒳.property G
    P.equivalence _ U x x (fun V x' y' hxy => by
      obtain rfl := hxy rfl
      exact (hstab V (yonedaEquiv.symm x')).elim fun _ _ => by assumption)

/-- **Stacks 06QJ.** An algebraic stack `𝒳` over `S` is a gerbe if and only if the forgetful
1-morphism `I_𝒳 ⟶ 𝒳` of its inertia is flat and locally of finite presentation.

The implication (1) `⟹` (2) is
`isFlat_and_isLocallyOfFinitePresentation_inertiaProjection_of_isGerbe`, and the implication
(2) `⟹` (1) is `isGerbe_of_isFlat_and_isLocallyOfFinitePresentation_inertiaProjection`. -/
@[stacks 06QJ]
theorem isGerbe_iff_isFlat_and_isLocallyOfFinitePresentation_inertiaProjection
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    IsGerbe B S hS 𝒳 ↔
      IsFlat B S hS (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳) ∧
        IsLocallyOfFinitePresentation B S hS
          (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳) :=
  ⟨isFlat_and_isLocallyOfFinitePresentation_inertiaProjection_of_isGerbe B S hS 𝒳,
    fun h => isGerbe_of_isFlat_and_isLocallyOfFinitePresentation_inertiaProjection B S hS 𝒳
      h.1 h.2⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
