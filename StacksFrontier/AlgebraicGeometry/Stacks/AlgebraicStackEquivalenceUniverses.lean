module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverBased

/-!
# Algebraicity transports along an equivalence over the site in independent universes

Two categories over the big fppf site of a scheme `S` which are equivalent as categories over
that site are algebraic stacks at the same time, and Deligne-Mumford stacks at the same time. Here
the two categories are allowed independent object and morphism universes.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableFromSchemes_of_equivalenceOver`: condition (3) of
  Stacks 045G transports along an equivalence over the site between categories in independent
  universes.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_equivalenceOver`: a category over the big fppf site
  of `S` equivalent over the site to an algebraic stack is an algebraic stack, in independent
  universes.
* `AlgebraicGeometry.Stack.isDeligneMumfordStackUniv_of_equivalenceOver`: the same for
  Deligne-Mumford stacks.

## References

* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 042W](https://stacks.math.columbia.edu/tag/042W)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 0459](https://stacks.math.columbia.edu/tag/0459)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w v₁ t₁ v₂ t₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The unit of an equivalence over the site, whiskered by a 1-morphism into its source, with the
two sides of the equivalence in independent universes: an isomorphism `f ≅ (f ⋙ a) ⋙ a⁻¹` of
1-morphisms over the site. -/
private noncomputable def whiskerUnitIsoOver
    {𝒳 : BasedCategory.{v₁, t₁} (BigFppfOver B S hS)}
    {𝒴 : BasedCategory.{v₂, t₂} (BigFppfOver B S hS)}
    (e : BasedCategory.Equivalence 𝒳 𝒴)
    {𝒵 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)} (f : 𝒵 ⥤ᵇ 𝒳) :
    BasedFunctor.comp (BasedFunctor.id 𝒵) f ≅
      BasedFunctor.comp (BasedFunctor.comp f e.functor) e.inverse :=
  BasedNatIso.mkNatIso
    (Functor.isoWhiskerLeft f.toFunctor
      (BasedFunctor.toFunctorIso e.functor e.inverse e.unitIso).symm)
    (fun a => e.unitIso.inv.isHomLift (f.w_obj a))

/-- **Condition (3) of Stacks 045G transports along an equivalence over the site between
categories in independent universes.** If every 1-morphism to `𝒳` from the category represented by
a scheme over `S` is representable by algebraic spaces, and `𝒴` is equivalent to `𝒳` as a category
over the big fppf site of `S`, then the same holds for `𝒴`. -/
theorem isRepresentableFromSchemes_of_equivalenceOver
    {𝒳 : CatFiberedInGroupoids.{u, v₁, u + 1, t₁} (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₂, u + 1, t₂} (BigFppfOver B S hS)}
    (e : BasedCategory.Equivalence 𝒳.val 𝒴.val)
    (h : IsRepresentableFromSchemes B S hS 𝒳) :
    IsRepresentableFromSchemes B S hS 𝒴 := by
  intro U y
  have hid : Functor.IsEquivalence
      (BasedFunctor.id (schemeFibredCategory B S hS U).val).toFunctor := by
    change Functor.IsEquivalence (𝟭 _)
    infer_instance
  have hinv : Functor.IsEquivalence e.inverse.toFunctor := e.symm.equiv.isEquivalence_functor
  exact (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS y
    (BasedFunctor.comp y e.inverse)
    (BasedFunctor.id (schemeFibredCategory B S hS U).val) e.inverse
    (Iso.refl _)).mp (h U (BasedFunctor.comp y e.inverse))

/-- A category over the big fppf site of `S` which is equivalent over that site to an algebraic
stack is an algebraic stack, the two categories being allowed independent object and morphism
universes. -/
@[stacks 03YQ "the two categories in independent universes"]
theorem isAlgebraicStack_of_equivalenceOver
    {𝒳 : BasedCategory.{v₁, t₁} (BigFppfOver B S hS)}
    {𝒴 : BasedCategory.{v₂, t₂} (BigFppfOver B S hS)}
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.p 𝒴.p)
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳) :
    IsAlgebraicStack.{u, w} B S hS 𝒴 := by
  obtain ⟨h𝒳fib, ⟨hst, -⟩, h𝒳diag, U, f, hf, hAtlas⟩ := h𝒳
  have h𝒴fib : 𝒴.p.IsFiberedInGroupoids :=
    StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver e.symm h𝒳fib
  let E : BasedCategory.Equivalence 𝒳 𝒴 := e.toBasedEquivalence
  have h𝒴st : 𝒴.p.IsStack (BigFppfOver.topology B S hS) :=
    (BasedCategory.isStack_iff_of_equivalence E (BigFppfOver.topology B S hS)).mp hst
  have hequiv : Functor.IsEquivalence E.functor.toFunctor := E.equiv.isEquivalence_functor
  have hid : Functor.IsEquivalence
      (BasedFunctor.id (schemeFibredCategory B S hS U).val).toFunctor := by
    change Functor.IsEquivalence (𝟭 _)
    infer_instance
  have hinvE : Functor.IsEquivalence E.inverse.toFunctor := E.symm.equiv.isEquivalence_functor
  have h₃ : IsRepresentableFromSchemes B S hS (CatFiberedInGroupoids.mk 𝒳 h𝒳fib) :=
    (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS
        (CatFiberedInGroupoids.mk 𝒳 h𝒳fib)).mp
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS
        (CatFiberedInGroupoids.mk 𝒳 h𝒳fib)).mp h𝒳diag)
  have h₃' : IsRepresentableFromSchemes B S hS (CatFiberedInGroupoids.mk 𝒴 h𝒴fib) :=
    isRepresentableFromSchemes_of_equivalenceOver B S hS
      (𝒳 := CatFiberedInGroupoids.mk 𝒳 h𝒳fib) (𝒴 := CatFiberedInGroupoids.mk 𝒴 h𝒴fib) E h₃
  have hfNew : IsRepresentableByAlgebraicSpaces B S hS (BasedFunctor.comp f E.functor) :=
    h₃' U (BasedFunctor.comp f E.functor)
  refine ⟨h𝒴fib, ⟨h𝒴st, h𝒴st.isStackInGroupoids h𝒴fib⟩,
    (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS
        (CatFiberedInGroupoids.mk 𝒴 h𝒴fib)).mpr
      ((isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS
        (CatFiberedInGroupoids.mk 𝒴 h𝒴fib)).mpr h₃'),
    U, BasedFunctor.comp f E.functor, hfNew, fun V y hy F hF hEq => ⟨?_, ?_⟩⟩
  · exact relativeProperty_of_equivalences B S hS (Space.surjectiveMorphismProperty B S hS)
      (𝒳' := schemeFibredCategory B S hS U) (𝒴' := CatFiberedInGroupoids.mk 𝒴 h𝒴fib)
      (𝒳 := schemeFibredCategory B S hS U) (𝒴 := CatFiberedInGroupoids.mk 𝒳 h𝒳fib)
      (BasedFunctor.comp f E.functor) f (BasedFunctor.id _) E.inverse
      (whiskerUnitIsoOver B S hS E f)
      (fun V y hy F hF hh => (hAtlas V y hy F hF hh).1) V y hy F hF hEq
  · exact relativeProperty_of_equivalences B S hS (Space.smoothMorphismProperty B S hS)
      (𝒳' := schemeFibredCategory B S hS U) (𝒴' := CatFiberedInGroupoids.mk 𝒴 h𝒴fib)
      (𝒳 := schemeFibredCategory B S hS U) (𝒴 := CatFiberedInGroupoids.mk 𝒳 h𝒳fib)
      (BasedFunctor.comp f E.functor) f (BasedFunctor.id _) E.inverse
      (whiskerUnitIsoOver B S hS E f)
      (fun V y hy F hF hh => (hAtlas V y hy F hF hh).2) V y hy F hF hEq

/-- A category over the big fppf site of `S` which is equivalent over that site to a
Deligne-Mumford stack is a Deligne-Mumford stack, the two categories being allowed independent
object and morphism universes. -/
theorem isDeligneMumfordStackUniv_of_equivalenceOver
    {𝒳 : BasedCategory.{v₁, t₁} (BigFppfOver B S hS)}
    {𝒴 : BasedCategory.{v₂, t₂} (BigFppfOver B S hS)}
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.p 𝒴.p)
    (h𝒳 : IsDeligneMumfordStackUniv.{u, w} B S hS 𝒳) :
    IsDeligneMumfordStackUniv.{u, w} B S hS 𝒴 := by
  obtain ⟨halg, hfib, U, f, -, hprops⟩ := h𝒳
  have halg' : IsAlgebraicStack.{u, w} B S hS 𝒴 := isAlgebraicStack_of_equivalenceOver B S hS e halg
  have hfib' : 𝒴.p.IsFiberedInGroupoids := halg'.1
  let E : BasedCategory.Equivalence 𝒳 𝒴 := e.toBasedEquivalence
  have hid : Functor.IsEquivalence
      (BasedFunctor.id (schemeFibredCategory B S hS U).val).toFunctor := by
    change Functor.IsEquivalence (𝟭 _)
    infer_instance
  have hinvE : Functor.IsEquivalence E.inverse.toFunctor := E.symm.equiv.isEquivalence_functor
  have h₃ : IsRepresentableFromSchemes B S hS (CatFiberedInGroupoids.mk 𝒳 hfib) :=
    (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS
        (CatFiberedInGroupoids.mk 𝒳 hfib)).mp
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS
        (CatFiberedInGroupoids.mk 𝒳 hfib)).mp halg.2.2.1)
  have h₃' : IsRepresentableFromSchemes B S hS (CatFiberedInGroupoids.mk 𝒴 hfib') :=
    isRepresentableFromSchemes_of_equivalenceOver B S hS
      (𝒳 := CatFiberedInGroupoids.mk 𝒳 hfib) (𝒴 := CatFiberedInGroupoids.mk 𝒴 hfib') E h₃
  refine ⟨halg', hfib', U, BasedFunctor.comp f E.functor, h₃' U (BasedFunctor.comp f E.functor),
    fun V y hy F hF hEq => ⟨?_, ?_⟩⟩
  · exact relativeProperty_of_equivalences B S hS (Space.surjectiveMorphismProperty B S hS)
      (𝒳' := schemeFibredCategory B S hS U) (𝒴' := CatFiberedInGroupoids.mk 𝒴 hfib')
      (𝒳 := schemeFibredCategory B S hS U) (𝒴 := CatFiberedInGroupoids.mk 𝒳 hfib)
      (BasedFunctor.comp f E.functor) f (BasedFunctor.id _) E.inverse
      (whiskerUnitIsoOver B S hS E f)
      (fun V y hy F hF hh => (hprops V y hy F hF hh).1) V y hy F hF hEq
  · exact relativeProperty_of_equivalences B S hS (Space.etaleMorphisms B S hS)
      (𝒳' := schemeFibredCategory B S hS U) (𝒴' := CatFiberedInGroupoids.mk 𝒴 hfib')
      (𝒳 := schemeFibredCategory B S hS U) (𝒴 := CatFiberedInGroupoids.mk 𝒳 hfib)
      (BasedFunctor.comp f E.functor) f (BasedFunctor.id _) E.inverse
      (whiskerUnitIsoOver B S hS E f)
      (fun V y hy F hF hh => (hprops V y hy F hF hh).2) V y hy F hF hEq

end AlgebraicGeometry.Stack

end
