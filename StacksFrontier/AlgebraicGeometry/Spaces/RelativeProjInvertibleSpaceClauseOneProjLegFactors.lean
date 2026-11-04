module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOne

/-!
# The `ψ_P` leg of clause (1) of Stacks 0D2Z as the composite of its three factors

The `ψ_P` leg `…InvertibleTwistingRestriction.clauseOneProjLeg` of the square of clause (1) of
[Stacks, Tag 0D2Z] is by definition the composite `e ≫ i ≫ m` of three factors: the transport
along `r ≫ π = π_{U(ψ)}`, the comparison of Stacks 03LU, and the inverse image along `r` of
`ψ_{P,d}`.  The paste of the three squares of clause (1)
(`…InvertibleTwistingRestriction.modulePullback_map_comp_eq_of_shaped_squares`) consumes this
factorisation as its hypothesis `ha`, read in the category of modules on `U(ψ)` as the paste
spells it.

That factorisation is not cheaply proved by `rfl`.  The body of the definition carries its own
abstracted proofs in the category and instance of its composites (the proof that the site
contains the base, and that `U(ψ)` is an algebraic space), so the category of those composites
agrees with the category of the paste only up to proof irrelevance, and comparing the outer
composite, which holds the `eqToHom`, across the two spellings makes the kernel unfold that
`eqToHom`.  Here the body is read off the defining equation with its own category
(`HEq.trans (heq_of_eq _) HEq.rfl` lets the unifier match the body against a composite in a free
category), and the composite is moved to the paste's category at variables
(`…InvertibleTwistingRestriction.eq_comp_comp_of_heq_modules`), where the two categories, their
instances and the leaves are compared only as types.

## Main results

* `…InvertibleTwistingRestriction.eq_comp_comp_of_heq_comp_comp`: a composite of three morphisms
  read in a second spelling of the category.
* `…InvertibleTwistingRestriction.clauseOneProjLeg_eq_comp_comp`: **the `ψ_P` leg is the
  composite of its three factors, in the category of the paste.**

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe v₁ u₁ u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

/-- **A composite of three morphisms, read in a second spelling of the category**: if `a` is
heterogeneously equal to `e₁ ≫ i₁ ≫ m₁` in a category `C₁` equal to `C₂`, with heterogeneously
equal instances and leaves, then `a = e₂ ≫ i₂ ≫ m₂` in `C₂`.  The instance of `C₁` is an implicit
argument, so that an instance reads it off the composite. -/
theorem eq_comp_comp_of_heq_comp_comp {C₁ C₂ : Type u₁} {inst₁ : Category.{v₁} C₁}
    [inst₂ : Category.{v₁} C₂]
    {G₁ M₁ N₁ H₁ : C₁} {e₁ : G₁ ⟶ M₁} {i₁ : M₁ ⟶ N₁} {m₁ : N₁ ⟶ H₁}
    {G₂ M₂ N₂ H₂ : C₂} (a : G₂ ⟶ H₂) {e₂ : G₂ ⟶ M₂} {i₂ : M₂ ⟶ N₂} {m₂ : N₂ ⟶ H₂}
    (h : HEq a (e₁ ≫ i₁ ≫ m₁)) (hC : C₁ = C₂) (hI : HEq inst₁ inst₂)
    (hG : HEq G₁ G₂) (hM : HEq M₁ M₂) (hN : HEq N₁ N₂) (hH : HEq H₁ H₂)
    (he : HEq e₁ e₂) (hi : HEq i₁ i₂) (hm : HEq m₁ m₂) :
    a = e₂ ≫ i₂ ≫ m₂ := by
  subst hC
  have hI' := eq_of_heq hI
  subst hI'
  subst hG hM hN hH
  subst he hi hm
  exact eq_of_heq h

/-- `…eq_comp_comp_of_heq_comp_comp` with the second category the modules on an algebraic space,
its instance found at variables (the spelling of the paste
`…InvertibleTwistingRestriction.modulePullback_map_comp_eq_of_shaped_squares`). -/
theorem eq_comp_comp_of_heq_modules {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : AlgebraicSpaces B S hS} {C₁ : Type _} {inst₁ : Category C₁}
    {G₁ M₁ N₁ H₁ : C₁} {e₁ : G₁ ⟶ M₁} {i₁ : M₁ ⟶ N₁} {m₁ : N₁ ⟶ H₁}
    {G₂ M₂ N₂ H₂ : Modules.{u, u} B S hS X.1 X.2} (a : G₂ ⟶ H₂) {e₂ : G₂ ⟶ M₂}
    {i₂ : M₂ ⟶ N₂} {m₂ : N₂ ⟶ H₂}
    (h : HEq a (e₁ ≫ i₁ ≫ m₁)) (hC : C₁ = Modules.{u, u} B S hS X.1 X.2)
    (hI : HEq inst₁ (inferInstance : Category (Modules.{u, u} B S hS X.1 X.2)))
    (hG : HEq G₁ G₂) (hM : HEq M₁ M₂) (hN : HEq N₁ N₂) (hH : HEq H₁ H₂)
    (he : HEq e₁ e₂) (hi : HEq i₁ i₂) (hm : HEq m₁ m₂) :
    a = e₂ ≫ i₂ ≫ m₂ :=
  eq_comp_comp_of_heq_comp_comp a h hC hI hG hM hN hH he hi hm

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property) (d : ℕ)

/-- **The `ψ_P` leg of clause (1) is the composite of its three factors**, the transport along
`r ≫ π = π_{U(ψ)}`, the comparison `π_{U(ψ)}^*𝒜_d ≅ r^*(π^*𝒜_d)` of Stacks 03LU and `r^*ψ_{P,d}`,
in the category of modules on `U(ψ)` as the paste
`…InvertibleTwistingRestriction.modulePullback_map_comp_eq_of_shaped_squares` spells it: its
hypothesis `ha` at `a₂ := …clauseOneProjLeg`.  The factors are the definition's own, read off
its defining equation. -/
theorem clauseOneProjLeg_eq_comp_comp :
    type_of% (eq_comp_comp_of_heq_modules (X := locusSpaceOfUnitalHom s f L ψ)
      (clauseOneProjLeg s f L ψ Px d)
      (HEq.trans (heq_of_eq (clauseOneProjLeg.eq_1 s f L ψ Px d)) HEq.rfl) rfl HEq.rfl
      HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl) :=
  eq_comp_comp_of_heq_modules (X := locusSpaceOfUnitalHom s f L ψ)
    (clauseOneProjLeg s f L ψ Px d)
    (HEq.trans (heq_of_eq (clauseOneProjLeg.eq_1 s f L ψ Px d)) HEq.rfl) rfl HEq.rfl
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
