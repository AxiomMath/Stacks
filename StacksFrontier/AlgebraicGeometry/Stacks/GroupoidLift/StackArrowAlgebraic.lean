module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackArrowSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase

/-!
# The space of arrows of the groupoid of a chart is an algebraic space

With the notation of `AlgebraicGeometry.Stack.GroupoidLift.StackChart.arrSpace`, when `𝒳` is an
algebraic stack its diagonal is representable by algebraic spaces, so the isomorphism presheaf
`Isom(x₀, x₁)` on the slice over `Spec (P ⊗ P)` is an algebraic space over `Spec (P ⊗ P)`
(Stacks 045G, (1) ⇒ (2)); its coproduct presheaf, the space of arrows, is then the algebraic
space over `S` it defines through the smaller base (Stacks 04SG).

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.isAlgebraicSpace_arrSpace`.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} (a : schemeFibredCategory B S hS U₀ ⟶ 𝒳)
  {P : SmallAlg (ringOf B S hS T') B.cutoff} (ι : specOver P ⟶ U₀)

namespace StackChart

/-- The projection of a category fibred in groupoids to its base is a fibred category. -/
local instance : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered

/-- **The space of arrows of the groupoid of a chart of an algebraic stack is an algebraic
space.** -/
theorem isAlgebraicSpace_arrSpace (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    IsAlgebraicSpace B S hS (arrSpace a ι) := by
  set V := specOver (pairAlg P)
  obtain ⟨F, hF, ⟨e⟩⟩ := (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mp
    (SelfIntersection.hasRepresentableDiagonal_of_isAlgebraicStack B S hS 𝒳 h𝒳) V
    (pairObj₀ a ι) (pairObj₁ a ι)
  let e' : F ≅ (Over.iteratedSliceBackward V).op ⋙ pairIsom a ι :=
    ((Functor.FullyFaithful.ofFullyFaithful uliftFunctor.{u, u}).whiskeringRight _).preimageIso e
  let E := (Over.iteratedSliceEquiv V).op.congrLeft (E := Type u)
  let e'' : E.inverse.obj F ≅ pairIsom a ι := E.inverse.mapIso e' ≪≫ (E.unitIso.app _).symm
  exact isAlgebraicSpace_of_iso B S hS (OverShriek.presheafFunctor.mapIso e''.symm)
    ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩).property

end StackChart

end AlgebraicGeometry.Stack.GroupoidLift

end
