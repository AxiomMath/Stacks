module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stack.GroupoidTransport

/-!
# Algebraic stacks are invariant under equivalence over the site (Stacks 03YQ)

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳`, `𝒴` be categories over the big
fppf site of `S` which are equivalent as categories over that site. Stacks 03YQ says that `𝒳` is
an algebraic stack if and only if `𝒴` is.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_iff_of_equivalence'`: **Stacks 03YQ**, the
  algebraic-stack assertion, for categories over the site in the universes
  `CategoryTheory.BasedCategory.{u, u + 1}`. The universe-polymorphic form, with the two
  categories implicit, is `AlgebraicGeometry.Stack.isAlgebraicStack_iff_of_equivalence`.

## Implementation notes

Neither category is assumed fibred in groupoids in advance; that is the first clause of the
algebraic-stack condition and it transports by **Stacks 042G**,
`CategoryTheory.BasedCategory.Equivalence.isFiberedInGroupoids`.

The remaining three clauses of `AlgebraicGeometry.Stack.IsAlgebraicStack` transport as follows.

* The stack clause is a conjunction of the sieve-indexed condition of **Stacks 026F** and the
  family-indexed condition of **Stacks 02ZI** at the descent universe. The first transports by
  **Stacks 042W**, `CategoryTheory.BasedCategory.isStack_iff_of_equivalence`; the second is then
  *recovered* from it by `CategoryTheory.Functor.IsStack.isStackInGroupoids`, the implication
  026F ⟹ 02ZI of **Stacks 02ZJ**, which holds at every descent universe and needs nothing but
  fibredness in groupoids. No transport of the 02ZI condition itself is needed, and none is
  available.
* The diagonal clause transports by `AlgebraicGeometry.Stack`
  `.isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_iff_of_equivalence`, which routes it
  through conditions (2) and (3) of **Stacks 045G**.
* The presentation clause is carried by the *same* scheme `U`, with the atlas postcomposed with
  the forward 1-morphism of the equivalence. Its representability moves by **Stacks 0457** and its
  relative surjectivity-and-smoothness by **Stacks 0459**, both applied to the 2-commutative
  square whose horizontal 1-morphisms are the identity of the atlas source and the equivalence.
  The two instance hypotheses of Stacks 0459 are discharged for the meet of
  `AlgebraicGeometry.Space.surjectiveMorphismProperty` and
  `AlgebraicGeometry.Space.smoothMorphismProperty` from the four instances the two factors carry
  (**Stacks 03MH**, **Stacks 03ZE**, **Stacks 041Q** and **Stacks 0429**, the last two at the fppf
  precoverage).

The Deligne-Mumford assertion of Stacks 03YQ is **not** proved here: it is the same argument with
the presentation clause taken at the meet of surjectivity with
`AlgebraicGeometry.Space.etaleMorphisms`, and Stacks 0459 then needs étaleness of morphisms of
algebraic spaces to be local at the target for the fppf precoverage. That is **Stacks 042B** read
for algebraic spaces, and it is not in this library — only the scheme-level statement is, as a
private theorem in `StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient`.

## References

* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 02ZJ](https://stacks.math.columbia.edu/tag/02ZJ)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 042G](https://stacks.math.columbia.edu/tag/042G)
* [Stacks Project, Tag 042W](https://stacks.math.columbia.edu/tag/042W)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 0459](https://stacks.math.columbia.edu/tag/0459)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03YQ, the algebraic-stack assertion.** Two categories over the big fppf site of `S`
which are equivalent as categories over the site are algebraic stacks at the same time.

Stated for categories in the universes `CategoryTheory.BasedCategory.{u, u + 1}`, with both of
them explicit; `AlgebraicGeometry.Stack.isAlgebraicStack_iff_of_equivalence` is the same
assertion for categories in arbitrary universes. -/
@[stacks 03YQ "algebraic stacks"]
theorem isAlgebraicStack_iff_of_equivalence'
    (𝒳 𝒴 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (e : BasedCategory.Equivalence 𝒳 𝒴) :
    IsAlgebraicStack.{u, w} B S hS 𝒳 ↔ IsAlgebraicStack.{u, w} B S hS 𝒴 := by
  have forward : ∀ (𝒳 𝒴 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
      (e : BasedCategory.Equivalence 𝒳 𝒴),
      IsAlgebraicStack.{u, w} B S hS 𝒳 → IsAlgebraicStack.{u, w} B S hS 𝒴 := by
    intro 𝒳 𝒴 e h𝒳
    obtain ⟨h𝒳fib, ⟨hst, -⟩, h𝒳diag, U, f, hf, hAtlas⟩ := h𝒳
    have h𝒴fib : 𝒴.p.IsFiberedInGroupoids := e.isFiberedInGroupoids h𝒳fib
    have h𝒴st : 𝒴.p.IsStack (BigFppfOver.topology B S hS) :=
      (BasedCategory.isStack_iff_of_equivalence e (BigFppfOver.topology B S hS)).mp hst
    have hequiv : Functor.IsEquivalence e.functor.toFunctor := e.equiv.isEquivalence_functor
    have hid : Functor.IsEquivalence
        (BasedFunctor.id (schemeFibredCategory B S hS U).val).toFunctor := by
      show Functor.IsEquivalence (𝟭 _)
      infer_instance
    have hα : BasedFunctor.comp (BasedFunctor.id (schemeFibredCategory B S hS U).val)
        (BasedFunctor.comp f e.functor) ≅ BasedFunctor.comp f e.functor := Iso.refl _
    have hfNew : IsRepresentableByAlgebraicSpaces B S hS (BasedFunctor.comp f e.functor) :=
      (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS
        (𝒳' := schemeFibredCategory B S hS U) (𝒳 := schemeFibredCategory B S hS U)
        (𝒴' := CatFiberedInGroupoids.mk 𝒳 h𝒳fib) (𝒴 := CatFiberedInGroupoids.mk 𝒴 h𝒴fib)
        f (BasedFunctor.comp f e.functor)
        (BasedFunctor.id (schemeFibredCategory B S hS U).val) e.functor hα).mpr hf
    refine ⟨h𝒴fib, ⟨h𝒴st, h𝒴st.isStackInGroupoids h𝒴fib⟩, ?_, U,
      BasedFunctor.comp f e.functor, hfNew, ?_⟩
    · exact (isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_iff_of_equivalence B S hS
        (𝒳 := CatFiberedInGroupoids.mk 𝒳 h𝒳fib) (𝒴 := CatFiberedInGroupoids.mk 𝒴 h𝒴fib)
        e).mp h𝒳diag
    · have : (Space.surjectiveMorphismProperty B S hS ⊓
          Space.smoothMorphismProperty B S hS).IsStableUnderBaseChange := inferInstance
      have : (Space.surjectiveMorphismProperty B S hS ⊓
          Space.smoothMorphismProperty B S hS).IsLocalAtTarget
            (Space.Topology.fppf.precoverage B S hS) := inferInstance
      exact (hasRelativeProperty_iff_of_equivalences.{u, u, u, u + 1, u + 1, u + 1} B S hS
        (Space.surjectiveMorphismProperty B S hS ⊓ Space.smoothMorphismProperty B S hS)
        (Bicategory.InducedBicategory.mkHom
          (X := schemeFibredCategory B S hS U) (Y := CatFiberedInGroupoids.mk 𝒳 h𝒳fib) f)
        (Bicategory.InducedBicategory.mkHom
          (X := schemeFibredCategory B S hS U) (Y := CatFiberedInGroupoids.mk 𝒴 h𝒴fib)
          (BasedFunctor.comp f e.functor))
        (BasedFunctor.id (schemeFibredCategory B S hS U).val) e.functor hα hfNew).mpr hAtlas
  exact ⟨forward 𝒳 𝒴 e, forward 𝒴 𝒳 e.symm⟩

end AlgebraicGeometry.Stack

end
