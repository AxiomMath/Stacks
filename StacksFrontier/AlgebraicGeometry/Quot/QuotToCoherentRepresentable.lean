module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFibreRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.QuotModelFromRepresentableStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaAlgebraicSpaceSources
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStackUniverses

/-!
# `Quot_{F/X/B} ⟶ Coh_{X/B}` is representable by algebraic spaces

This file assembles the proof of Stacks 09TU from its two inputs: a representation of the relative
Hom functor `Hom(F_T, 𝒢)` of Stacks 08JT by an algebraic space for every object `(T, 𝒢)` of
`Coh_{X/B}` (Stacks 08K6), and the algebraicity of `Coh_{X/B}` (Stacks 09DS).

The 2-fibre product of `Quot_{F/X/B} ⟶ Coh_{X/B}` with a scheme-valued point `y` of `Coh_{X/B}`
is classified by the locus of surjections in the space representing the relative Hom functor of
`y(V)` (`AlgebraicGeometry.Space.QuotSituation.fibreClassifier`), which is an open subspace by
Stacks 09TP (`AlgebraicGeometry.Space.HomSituation.isOpenSubspace_surjLocus`); so the 1-morphism
is representable by algebraic spaces, and Stacks 05UM transfers algebraicity from `Coh_{X/B}`.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.isRepresentableByAlgebraicSpaces_quotToCoherent`: the
  1-morphism `Quot_{F/X/B} ⟶ Coh_{X/B}` is representable by algebraic spaces as soon as every
  relative Hom functor `Hom(F_T, 𝒢)` is represented by an algebraic space.
* `AlgebraicGeometry.Space.QuotSitePresheafModel.isAlgebraicSpace_of_homRepresentations`: every
  model of the Quot presheaf is an algebraic space, given those representations and the
  algebraicity of `Coh_{X/B}`.

## References

* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local implicit_reducible] AlgebraicGeometry.Space.QuotSituation.toCoherentSituation

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- The relative Hom functor of an object `(T, 𝒢)` of `Coh_{X/B}` is represented by an algebraic
space: the conclusion Stacks 08K6 supplies for `Hom(F_T, 𝒢)`. -/
def HasHomRepresentation (A : CoherentObject D.toCoherentSituation) : Prop :=
  ∃ (H : AlgebraicSpaces B S hS) (p : H ⟶ (D.fibreHomSituation A).base),
    Nonempty (spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅
      (D.fibreHomSituation A).homFunctor (modulePushforwardCoherence B S hS))

/-- **The locus of surjections in a representation of the relative Hom functor of an object of
`Coh_{X/B}` is an open subspace**, by Stacks 09TP: the module of the object is of finite type and
has support proper over its test scheme. -/
theorem isOpenSubspace_surjLocus_fibre (A : CoherentObject D.toCoherentSituation)
    {H : AlgebraicSpaces B S hS} (p : H ⟶ (D.fibreHomSituation A).base)
    (c : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅
      (D.fibreHomSituation A).homFunctor (modulePushforwardCoherence B S hS)) :
    IsOpenSubspace B S hS
      ((D.fibreHomSituation A).surjLocus (modulePushforwardCoherence B S hS) p c) := by
  obtain ⟨_, hU, hP⟩ := A.properSupport
  exact (D.fibreHomSituation A).isOpenSubspace_surjLocus (modulePushforwardCoherence B S hS) p c
    (Space.isLocallyOfFinitePresentation_projection D.toCoherentSituation A.T)
    (@SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite _ _ _ _ A.F
      A.finitePresentation) ⟨hU, hP⟩

/-- **`Quot_{F/X/B} ⟶ Coh_{X/B}` is representable by algebraic spaces**, as soon as the relative
Hom functor `Hom(F_T, 𝒢)` of every object `(T, 𝒢)` of `Coh_{X/B}` is represented by an algebraic
space. -/
theorem isRepresentableByAlgebraicSpaces_quotToCoherent
    (hHom : ∀ A : CoherentObject D.toCoherentSituation, D.HasHomRepresentation A) :
    Stack.IsRepresentableByAlgebraicSpaces B S hS D.quotToCoherentCFG.hom := by
  refine Stack.isRepresentableByAlgebraicSpaces_of_forall_twoFibreProduct B S hS
    D.toCoherentSituation.coherentCFG D.quotCatFiberedInGroupoids D.quotToCoherentCFG.hom
    fun V y => ?_
  obtain ⟨H, p, ⟨c⟩⟩ := hHom (D.fibreBase y)
  exact D.isRepresentableByAlgebraicSpace_fibreProduct_of_homRepresentation y p c
    (D.isOpenSubspace_surjLocus_fibre (D.fibreBase y) p c)

/-- **`Quot_{F/X/B}` is an algebraic stack**, given representations of the relative Hom functors
and the algebraicity of `Coh_{X/B}`, by Stacks 05UM. -/
theorem isAlgebraicStack_quotCatFiberedInGroupoids.{w}
    (hHom : ∀ A : CoherentObject D.toCoherentSituation, D.HasHomRepresentation A)
    (hCoh : Stack.IsAlgebraicStack.{u, w} B S hS D.toCoherentSituation.coherentCFG.val) :
    Stack.IsAlgebraicStack.{u, w} B S hS D.quotCatFiberedInGroupoids.val :=
  Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces_homUniverse B S hS
    D.quotToCoherentCFG (D.isRepresentableByAlgebraicSpaces_quotToCoherent hHom) hCoh

end QuotSituation

namespace QuotSitePresheafModel

variable {D : QuotSituation B S hS}

/-- **The first clause of Stacks 09TU, from its two inputs.** Given a representation of the
relative Hom functor of every object of `Coh_{X/B}` by an algebraic space (Stacks 08K6) and the
algebraicity of `Coh_{X/B}` (Stacks 09DS), every model of the Quot presheaf is an algebraic
space. -/
theorem isAlgebraicSpace_of_homRepresentations.{w} (N : QuotSitePresheafModel D)
    (hHom : ∀ A : CoherentObject D.toCoherentSituation, D.HasHomRepresentation A)
    (hCoh : Stack.IsAlgebraicStack.{u, w} B S hS D.toCoherentSituation.coherentCFG.val) :
    IsAlgebraicSpace B S hS N.presheaf :=
  N.isAlgebraicSpace_of_isAlgebraicStack_quotCatFiberedInGroupoids
    (D.isAlgebraicStack_quotCatFiberedInGroupoids hHom hCoh)

end QuotSitePresheafModel

end AlgebraicGeometry.Space

end
