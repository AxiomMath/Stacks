module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneSiteHT

/-!
# The slot `hT` of the target square of clause (1) of Stacks 0D2Z, in the syntax of the slot

The target square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)`
(`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares`, at `Φ = modulePullback` and
`κ = modulePullbackCompIso` over the site of `s`) takes as its hypothesis `hT` the factorisation
of the target identification `chartTargetIso`, at the module `ℒ^{⊗ d}` spelled as the target of the
degree-`d` component `ψ_d` of `ψ` (the degree-`d` piece of the Laurent algebra of `ℒ` over the
ringed topos of `X`), the spelling fixed by its binder `ψd`.  This file states that factorisation
at that spelling of `ℒ^{⊗ d}`, so that it is the hypothesis `hT` syntactically.

## Main results

* `…InvertibleTwistingRestriction.chartTargetIso_hom_eq_over_site_slot`: the hypothesis `hT` in
  the syntax of the slot.

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

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction


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
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) (d : ℤ)

set_option maxHeartbeats 0 in
-- Checking `chartTargetIso.eq_1` against the factorisation at the full chart data in the
-- statement exceeds the default heartbeat budget.
/-- **The target identification of the chart map is the composite of its three factors, over the
site of `s`, in the syntax of the slot `hT`**: `chartTargetIso` is the inverse of
`AlgebraicGeometry.Space.pointTargetIso`, the transport along `pointHom_locusPoint` and the inverse
comparison of Stacks 03LU for `w` and the inclusion `U(ψ) ⊆ X`, each over
`s.site s.base s.containsBase`, at `ℒ^{⊗ d}` spelled as the degree-`d` piece of the Laurent algebra
of `ℒ` over the ringed topos of `X` (the target of `ψ_d`).  This is the hypothesis `hT` of
`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares` at `Φ = modulePullback` and
`κ = modulePullbackCompIso` over the site of `s`, read off the defining equation of
`chartTargetIso`. -/
theorem chartTargetIso_hom_eq_over_site_slot :
    type_of% (eq_symm_hom_comp_eqToIso_hom_comp_compIso_symm_hom (B := s.site) (S := s.base)
      (hS := s.containsBase)
      (p := pointHom (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := locusSpaceOfUnitalHom s f L ψ) w)
      (ι := locusInclusionOfUnitalHom s f L ψ)
      (x := pointHom (B := s.site) (S := s.base) (hS := s.containsBase) (X := X) (locusPoint w))
      (pointHom_locusPoint w)
      (Lx := @SheafOfModules.GradedAlgebra.piece
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).C
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).category
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).J
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)
        (Stacks.SheafOfModules.TensorPower.laurentAlgebra
          (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property
            L)
        d)
      (θT := pointTargetIso (B := s.site) (S := s.base) (hS := s.containsBase) (X := X) (hL := hL)
        L W (locusPoint w) d)
      (T := (chartTargetIso w d).hom)
      (congrArg Iso.hom (chartTargetIso.eq_1 (s := s) (f := f) (L := L) (ψ := ψ) w d))) :=
  eq_symm_hom_comp_eqToIso_hom_comp_compIso_symm_hom (B := s.site) (S := s.base)
    (hS := s.containsBase)
    (p := pointHom (B := s.site) (S := s.base) (hS := s.containsBase)
      (X := locusSpaceOfUnitalHom s f L ψ) w)
    (ι := locusInclusionOfUnitalHom s f L ψ)
    (x := pointHom (B := s.site) (S := s.base) (hS := s.containsBase) (X := X) (locusPoint w))
    (pointHom_locusPoint w)
    (Lx := @SheafOfModules.GradedAlgebra.piece
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).C
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).category
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).J
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)
        (Stacks.SheafOfModules.TensorPower.laurentAlgebra
          (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property
            L)
        d)
    (θT := pointTargetIso (B := s.site) (S := s.base) (hS := s.containsBase) (X := X) (hL := hL)
      L W (locusPoint w) d)
    (T := (chartTargetIso w d).hom)
    (congrArg Iso.hom (chartTargetIso.eq_1 (s := s) (f := f) (L := L) (ψ := ψ) w d))

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
