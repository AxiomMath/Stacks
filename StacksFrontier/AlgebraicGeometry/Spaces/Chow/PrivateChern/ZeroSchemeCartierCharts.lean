module

public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeAssertionsInvertible

/-!
# The zero scheme of a section is an effective Cartier divisor, read on affine charts

Let `X` be an algebraic space, `ℒ` an invertible `𝒪_X`-module and `s` a global section. If every
point of the zero scheme `Z(s)` has an affine étale neighbourhood `U` on which `ℒ` is free of rank
one, with generator `t` and coordinate functional `l₀`, such that the local function `l₀(s|_U)` is
a nonzerodivisor of `Γ(U, 𝒪_U)`, then `Z(s)` is an effective Cartier divisor: on `U` it is cut
out by that function (Stacks 0846 (4) chartwise), which is condition (4) of Stacks 083C.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.isEffectiveCartierDivisor_zeroScheme_of_affineCharts`:
  `Z(s)` is an effective Cartier divisor when it is cut out by a nonzerodivisor on affine étale
  charts trivializing `ℒ`.

## References

* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.PrivateChern

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The zero scheme `Z(s)` of a global section `s` of an invertible module `ℒ` is an effective
Cartier divisor if every point of `Z(s)` has an affine étale neighbourhood `U` on which `ℒ` is free
with generator `t` and coordinate functional `l₀`, and `l₀(s|_U)` is a nonzerodivisor of
`Γ(U, 𝒪_U)`. -/
theorem isEffectiveCartierDivisor_zeroScheme_of_affineCharts (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (s : L.sections)
    (h : ∀ x : points B S hS (zeroScheme B S hS X L s).1.toFunctor,
      ∃ (U : SmallEtale B S hS X.1) (_ : IsAffine ((SmallEtale.toSchemes B S hS X.1).obj U).1)
        (v : points B S hS (yoneda.obj U.obj.left))
        (_ : pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom v =
          pointsMap B S hS (zeroScheme B S hS X L s).1.toFunctor
            (zeroScheme B S hS X L s).1.ι x)
        (t : ToType (L.val.obj (op U)))
        (l₀ : Module.Dual ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op U)) (L.val.obj (op U)))
        (_ : ∀ y, l₀ y • t = y), IsRegular (l₀ (s.eval (op U)))) :
    IsEffectiveCartierDivisor B S hS X (zeroScheme B S hS X L s) := by
  refine isEffectiveCartierDivisor_of_hasAffinePrincipalEtaleNeighborhoods B S hS X _
    ((hasAffinePrincipalEtaleNeighborhoods_iff B S hS X _).2 fun x => ?_)
  obtain ⟨U, hU, v, hv, t, l₀, hb, hreg⟩ := h x
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.obj.left) := hU
  refine ⟨U.obj.left, U.obj.hom, v, hU,
    (isEtale_iff_presheaf_of_yoneda B S hS U.obj.hom).mpr U.property, hv, l₀ (s.eval (op U)),
    hreg, ?_⟩
  rw [ker_rep_snd_eq_ofIdealTop_definingIdealAt B S hS X _ U,
    definingIdealAt_zeroScheme_eq_span_generator_of_isInvertible B S hS X L hinv s U hU t l₀ hb]
  rfl

end AlgebraicGeometry.Space.PrivateChern

end
