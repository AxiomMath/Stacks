module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Gerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSurjective

/-!
# The relative diagonal of a gerbe is surjective

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which makes `𝒳` a gerbe over `𝒴`
([Stacks, Tag 06QC]). This file proves that the relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is
surjective, the surjectivity clause of part (2) of [Stacks, Tag 0CPR].

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isSurjective_relativeDiagonal_of_isGerbeOver`: the
  relative diagonal of a gerbe is surjective.

## Implementation notes

Condition (2)(b) of [Stacks, Tag 06P1] says exactly that `Δ_f` is surjective on objects in the
sense of [Stacks, Tag 06D4]: for an object `(x₁, x₂, φ)` of `𝒳 ×_𝒴 𝒳` over `U`, it lifts `φ`,
along every member `g : V ⟶ U` of a covering of `U`, to a vertical morphism between restrictions
of `x₁` and `x₂`, which is a morphism to `(x₁, x₂, φ)` out of a diagonal object. A covering sieve
of the spectrum of a field contains an arrow from the spectrum of a field
(`AlgebraicGeometry.Stack.exists_isFieldObject_arrow_of_mem_topology`), and [Stacks, Tag 04XI]
turns surjectivity on objects into surjectivity on points.

## References

* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 06P1](https://stacks.math.columbia.edu/tag/06P1)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
* [Stacks Project, Tag 0CPR](https://stacks.math.columbia.edu/tag/0CPR)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

/-- If a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` makes `𝒳` a gerbe over `𝒴`, then
its relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is surjective. -/
theorem isSurjective_relativeDiagonal_of_isGerbeOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsGerbeOver B S hS f) :
    Stack.IsSurjective B S hS (Stack.relativeDiagonalAlgebraicStacks B S hS f) := by
  have hlift : ∀ {m n : 𝒳.val.val.obj} {R T : BigFppfOver B S hS} (k : R ⟶ T) (φ : m ⟶ n),
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p).IsHomLift k φ →
      𝒳.val.val.p.IsHomLift k φ := by
    intro m n R T k φ h
    exact (BasedFunctor.isHomLift_iff f.hom.hom k φ).1
      ((Functor.isHomLift_comp_iff _ _ k φ).1 h)
  refine Stack.pointsMap_surjective_of_isSurjectiveOnObjects B S hS _ ?_
  intro U hU P hP
  subst hP
  obtain ⟨R, hR, hcov⟩ := hf.locally_full P.iso.hom P.vertical
  obtain ⟨V, g, hV, hgR⟩ := Stack.exists_isFieldObject_arrow_of_mem_topology B S hS hU hR
  obtain ⟨x₁, x₂, ξ, ξ', c, hξ, hξ', hc, hcomm⟩ := hcov g hgR
  have hξX : 𝒳.val.val.p.IsHomLift g ξ := hlift g ξ hξ
  have hξ'X : 𝒳.val.val.p.IsHomLift g ξ' := hlift g ξ' hξ'
  have hcX : 𝒳.val.val.p.IsHomLift (𝟙 V) c := hlift (𝟙 V) c hc
  have hx₁V : 𝒳.val.val.p.obj x₁ = V := IsHomLift.domain_eq 𝒳.val.val.p g ξ
  have hbX : 𝒳.val.val.p.IsHomLift g (c ≫ ξ') := by
    simpa using IsHomLift.comp 𝒳.val.val.p (𝟙 V) g c ξ'
  subst hx₁V
  have hw : f.hom.hom.toFunctor.map ξ ≫ P.iso.hom =
      𝟙 (f.hom.hom.toFunctor.obj x₁) ≫ f.hom.hom.toFunctor.map (c ≫ ξ') := by
    simpa using hcomm.symm
  let m : (Stack.relativeDiagonalAlgebraicStacks B S hS f).hom.hom.obj x₁ ⟶ P :=
    ⟨g, ξ, c ≫ ξ', hξX, hbX, hw⟩
  exact ⟨_, hV, g, x₁, rfl, m,
    IsHomLift.map (Stack.twoFibreProductAlgebraicStack B S hS f f).val.val.p m⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
