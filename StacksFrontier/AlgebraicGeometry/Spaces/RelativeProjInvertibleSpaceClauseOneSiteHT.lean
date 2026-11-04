module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartMap

/-!
# The target identification of the chart map as a composite, over the site of `s`

At a scheme point `w : W ⟶ U(ψ)`, the target identification
`…InvertibleTwistingRestriction.chartTargetIso` of the chart map is the inverse of
`AlgebraicGeometry.Space.pointTargetIso`, the transport along `pointHom_locusPoint` and the
inverse comparison of Stacks 03LU for `w` and `U(ψ) ⊆ X`, all over the site
`s.site s.base s.containsBase` of `s`.

## Main results

* `AlgebraicGeometry.Space.eq_symm_hom_comp_eqToIso_hom_comp_compIso_symm_hom`: the `.hom` of a
  composite of three isomorphisms of this shape is the composite of their `.hom`s, at variables.
* `…InvertibleTwistingRestriction.chartTargetIso_hom_eq_over_site`: the target identification of
  the chart map is the composite of its three factors, over the site of `s`.

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

/-- A morphism equal to the composite of three isomorphisms `θ⁻¹ ≪≫ e_x ≪≫ κ⁻¹` — the inverse of
`θ : x^*L ≅ L'`, the transport along `x = p ≫ ι` and the inverse comparison
`p^*ι^*L ≅ (p ≫ ι)^*L` of Stacks 03LU — is the composite of their `.hom`s, read at variables. -/
theorem eq_symm_hom_comp_eqToIso_hom_comp_compIso_symm_hom {R U X : AlgebraicSpaces B S hS}
    {p : R ⟶ U} {ι : U ⟶ X} {x : R ⟶ X} (hx : x = p ≫ ι) {Lx : Modules.{u, u} B S hS X.1 X.2}
    {Lr : Modules.{u, u} B S hS R.1 R.2} {θT : (modulePullback B S hS x).obj Lx ≅ Lr}
    {T : Lr ⟶ (modulePullback B S hS p).obj ((modulePullback B S hS ι).obj Lx)}
    (h : T = (θT.symm ≪≫ eqToIso (congrArg (fun k => (modulePullback B S hS k).obj Lx) hx) ≪≫
      ((modulePullbackCompIso B S hS p ι).app Lx).symm).hom) :
    T = θT.symm.hom ≫ (eqToIso (congrArg (fun k => (modulePullback B S hS k).obj Lx) hx)).hom ≫
      ((modulePullbackCompIso B S hS p ι).app Lx).symm.hom :=
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
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) (d : ℤ)

set_option maxHeartbeats 0 in
-- Checking the `type_of%` statement against the defining equation of `chartTargetIso` over
-- `s.site` times out in `isDefEq` at the default limit.
/-- The target identification of the chart map is the composite of its three factors, over the
site of `s`: `chartTargetIso` is the inverse of `AlgebraicGeometry.Space.pointTargetIso`, the
transport along `pointHom_locusPoint` and the inverse comparison of Stacks 03LU for `w` and the
inclusion `U(ψ) ⊆ X`, each over `s.site s.base s.containsBase`. -/
theorem chartTargetIso_hom_eq_over_site :
    type_of% (eq_symm_hom_comp_eqToIso_hom_comp_compIso_symm_hom (B := s.site) (S := s.base)
      (hS := s.containsBase)
      (p := pointHom (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := locusSpaceOfUnitalHom s f L ψ) w)
      (ι := locusInclusionOfUnitalHom s f L ψ)
      (x := pointHom (B := s.site) (S := s.base) (hS := s.containsBase) (X := X) (locusPoint w))
      (pointHom_locusPoint w)
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
    (θT := pointTargetIso (B := s.site) (S := s.base) (hS := s.containsBase) (X := X) (hL := hL)
      L W (locusPoint w) d)
    (T := (chartTargetIso w d).hom)
    (congrArg Iso.hom (chartTargetIso.eq_1 (s := s) (f := f) (L := L) (ψ := ψ) w d))

end RelativeProjSituation.InvertibleTwistingRestriction

end AlgebraicGeometry.Space

end
