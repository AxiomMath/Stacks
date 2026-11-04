module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOne

/-!
# The `ψ` leg of clause (1) of Stacks 0D2Z, as the composite of its factors

The target square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)`
(`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares`) consumes the `ψ` leg
`…InvertibleTwistingRestriction.clauseOnePsiLeg` only through its two factors: its hypothesis
`hb`.  The factorisation is read off the defining equation, so that its factors are the
definition's own (with the instance terms of the stored body), never a re-elaboration of the same
text: a lemma at variables (`AlgebraicGeometry.Space.eq_compIso_inv_comp_map`) fixes the shape, and
its instance at the defining equation is stated with `type_of%`.

## Main results

* `…InvertibleTwistingRestriction.clauseOnePsiLeg_eq`: **the `ψ` leg is `κ⁻¹ ≫ ι^*ψ_d`**, the
  inverse comparison of Stacks 03LU for `ι : U(ψ) ⟶ X` and `f` followed by `ι^*ψ_d`, in the shape
  of the hypothesis `hb` of `AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space

section Generic

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism equal to the inverse comparison `(ι ≫ f)^*M ≅ ι^*f^*M` of Stacks 03LU followed by
the inverse image `ι^*ψ` of a morphism `ψ : f^*M ⟶ L`, read at variables. -/
theorem eq_compIso_inv_comp_map {U X Y : AlgebraicSpaces B S hS} {ι : U ⟶ X} {f : X ⟶ Y}
    {M : Modules.{u, u} B S hS Y.1 Y.2} {Lx : Modules.{u, u} B S hS X.1 X.2}
    {ψd : (modulePullback B S hS f).obj M ⟶ Lx}
    {b : (modulePullback B S hS (ι ≫ f)).obj M ⟶ (modulePullback B S hS ι).obj Lx}
    (h : b = ((modulePullbackCompIso B S hS ι f).app M).inv ≫ (modulePullback B S hS ι).map ψd) :
    b = ((modulePullbackCompIso B S hS ι f).app M).inv ≫ (modulePullback B S hS ι).map ψd :=
  h

end Generic

namespace RelativeProjSituation.InvertibleTwistingRestriction

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
  {W : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj)

/-- **The `ψ` leg of clause (1) is the composite of its two factors**: `clauseOnePsiLeg` is the
inverse comparison of Stacks 03LU for `ι : U(ψ) ⟶ X` and `f`, followed by `ι^*ψ_d`.  This is the
hypothesis `hb` of `AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares` at
`Φ = modulePullback` and `κ = modulePullbackCompIso` over the site of `s.shrink`; the factors are
the definition's own, read off its defining equation. -/
theorem clauseOnePsiLeg_eq (d : ℕ) :
    type_of% (eq_compIso_inv_comp_map (clauseOnePsiLeg.eq_1 s f L ψ d)) :=
  eq_compIso_inv_comp_map (clauseOnePsiLeg.eq_1 s f L ψ d)

end RelativeProjSituation.InvertibleTwistingRestriction

end AlgebraicGeometry.Space

end
