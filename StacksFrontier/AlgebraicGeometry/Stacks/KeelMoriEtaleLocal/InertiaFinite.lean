module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DenseOpenGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.StabilizerPreservingUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralFiniteMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleStabilizerPreservingIsomorphism

/-!
# Finite inertia along a stabilizer preserving unramified 1-morphism

Let `h : 𝒳' ⟶ 𝒳` be an unramified 1-morphism of algebraic stacks inducing isomorphisms between
automorphism groups at every point (Stacks 0DTW). By Stacks 0DU9 the comparison
`I_𝒳' ⟶ 𝒳' ×_𝒳 I_𝒳` of Stacks 06R5 is an isomorphism, so the inertia projection of `𝒳'` is a
base change of the inertia projection of `𝒳`. In particular, if `I_𝒳 ⟶ 𝒳` is finite, so is
`I_𝒳' ⟶ 𝒳'` (Stacks 0CHV).

## Main results

* `AlgebraicGeometry.Stack.inertiaComparisonSquareAlgebraicStacks`: the inertia square of `h`.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_inertiaComparisonSquareAlgebraicStacks`: it is a
  2-fibre product when the comparison of Stacks 06R5 is an equivalence over the site.
* `AlgebraicGeometry.Stack.isFinite_inertiaProjection_of_isUnramified_of_inducesIsomorphismAt`:
  finite inertia ascends along an unramified 1-morphism inducing isomorphisms between automorphism
  groups.
* `AlgebraicGeometry.Stack.isFinite_inertiaProjection_of_isEtale_of_inducesIsomorphismAt`: the
  same along an étale one.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section InertiaComparison

variable {𝒳' 𝒳 : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳)
  (E : IsEquivalenceOver
      (RelativeInertia.toBase 𝒳'.val.val.p)
      (TwoFibreProductOver.structureFunctor (RelativeInertia.toBase 𝒳.val.val.p)
        𝒳'.val.val.p 𝒳.val.val.p (RelativeInertia.π 𝒳.val.val.p)
        (CatFiberedInGroupoids.homFunctor h.hom))
      (inertiaPullbackComparison 𝒳'.val.val.p 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor h.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p h.hom)))

/-- The comparison `I_𝒳' ⟶ I_𝒳 ×_𝒳 𝒳'` of Stacks 06R5 for a 1-morphism of algebraic stacks whose
comparison is an equivalence over the site, as a 1-morphism of categories fibred in groupoids
into the canonical 2-fibre product. -/
noncomputable def inertiaComparisonAlgebraicStacks :
    (inertiaAlgebraicStack B S hS 𝒳').val ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom h.hom).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := inertiaPullbackComparison 𝒳'.val.val.p 𝒳.val.val.p h.hom.hom.toFunctor
        h.hom.hom.w
      w := E.functor_over }

/-- The inertia square of `h`, as a square of categories fibred in groupoids: the canonical
2-fibre product square of `I_𝒳 ⟶ 𝒳 ⟵ 𝒳'` reindexed along the comparison of Stacks 06R5. -/
noncomputable def inertiaComparisonCatSquare :
    Bicategory.TwoCommSq (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom h.hom :=
  (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom h.hom).precompose
    (inertiaComparisonAlgebraicStacks B S hS h E)

/-- **The inertia square of `h` in the 2-category of algebraic stacks**, with apex `I_𝒳'`, first
leg `I_𝒳' ⟶ I_𝒳` and second leg the inertia projection of `𝒳'`. -/
noncomputable def inertiaComparisonSquareAlgebraicStacks :
    Bicategory.TwoCommSq (inertiaProjectionAlgebraicStacks B S hS 𝒳) h where
  pt := inertiaAlgebraicStack B S hS 𝒳'
  fst := Bicategory.InducedBicategory.mkHom (inertiaComparisonCatSquare B S hS h E).fst
  snd := Bicategory.InducedBicategory.mkHom (inertiaComparisonCatSquare B S hS h E).snd
  iso := Bicategory.InducedBicategory.isoMk (inertiaComparisonCatSquare B S hS h E).iso

/-- The second leg of the inertia square of `h` is the inertia projection of `𝒳'`. -/
theorem inertiaComparisonSquareAlgebraicStacks_snd :
    (inertiaComparisonSquareAlgebraicStacks B S hS h E).snd =
      inertiaProjectionAlgebraicStacks B S hS 𝒳' :=
  rfl

/-- **Stacks 06R5 with an invertible comparison.** When the comparison `I_𝒳' ⟶ 𝒳' ×_𝒳 I_𝒳` is
an equivalence over the site, the inertia square of `h` is a 2-fibre product: the inertia of `𝒳'`
is the base change of the inertia of `𝒳` along `h`. -/
noncomputable def isTwoFibreProduct_inertiaComparisonSquareAlgebraicStacks :
    Bicategory.IsTwoFibreProduct (inertiaComparisonSquareAlgebraicStacks B S hS h E) :=
  Bicategory.isTwoFibreProduct_of_underlying
    (Bicategory.isTwoFibreProduct_of_isEquivalence_to
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
      (Bicategory.TwoCommSq.PreHom.ofPrecompose _ _) E.isEquivalence)

end InertiaComparison

/-- **Finite inertia along a stabilizer preserving unramified 1-morphism.** Let `h : 𝒳' ⟶ 𝒳` be
unramified and induce isomorphisms between automorphism groups at every point of `𝒳'`
(Stacks 0DTW). If the inertia projection `I_𝒳 ⟶ 𝒳` is finite, so is `I_𝒳' ⟶ 𝒳'`. -/
theorem isFinite_inertiaProjection_of_isUnramified_of_inducesIsomorphismAt
    {𝒳' 𝒳 : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳) (hu : IsUnramified B S hS h)
    (hauto : ∀ q : points B S hS 𝒳'.val.val 𝒳'.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS h q)
    (hI : AlgebraicStacks.IsFinite B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    AlgebraicStacks.IsFinite B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳') := by
  obtain ⟨E⟩ := inertiaPullbackComparison_isEquivalenceOver_of_inducesIsomorphismAt B S hS h hu
    hauto
  exact AlgebraicStacks.isFinite_baseChange B S hS h (inertiaProjectionAlgebraicStacks B S hS 𝒳)
    (inertiaComparisonSquareAlgebraicStacks B S hS h E).swap
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_inertiaComparisonSquareAlgebraicStacks B S hS h E)) hI

/-- **Finite inertia along an étale stabilizer preserving 1-morphism.** Let `h : 𝒳' ⟶ 𝒳` be
étale and induce isomorphisms between automorphism groups at every point of `𝒳'`. If the inertia
projection `I_𝒳 ⟶ 𝒳` is finite, so is `I_𝒳' ⟶ 𝒳'`. -/
theorem isFinite_inertiaProjection_of_isEtale_of_inducesIsomorphismAt
    {𝒳' 𝒳 : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳) (he : IsEtale B S hS h)
    (hauto : ∀ q : points B S hS 𝒳'.val.val 𝒳'.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS h q)
    (hI : AlgebraicStacks.IsFinite B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    AlgebraicStacks.IsFinite B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳') :=
  isFinite_inertiaProjection_of_isUnramified_of_inducesIsomorphismAt B S hS h
    (isUnramified_of_isEtale B S hS he) hauto hI

end AlgebraicGeometry.Stack

end
