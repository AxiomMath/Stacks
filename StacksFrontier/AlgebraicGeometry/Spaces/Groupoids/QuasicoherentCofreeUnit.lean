module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentCofree

/-!
# The unit of the right adjoint to the forgetful functor on a groupoid in algebraic spaces

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces with `s` flat, quasi-compact and
quasi-separated, so that by Stacks 0GPP the forgetful functor
`F : QCoh(U, R, s, t, c) ⟶ QCoh(𝒪_U)`, `(ℱ, β) ↦ ℱ`, has the right adjoint
`G : 𝒢 ↦ (s_*t^*𝒢, α)`.  **Stacks 0GPQ** describes the unit `η : id ⟶ G ∘ F` of this
adjunction: at `(ℱ, β)` it is the map

`ℱ ⟶ s_*s^*ℱ ⟶ s_*t^*ℱ`

whose first factor is the unit of the adjunction `s^* ⊣ s_*` of Stacks 03LU and whose second
factor is the direct image along `s` of `β⁻¹`; the transition morphism `β` is invertible by
Stacks 077W.

## Main results

* `AlgebraicGeometry.Space.QuasicoherentModule.forgetAdjunction_unit_app`: **Stacks 0GPQ**.

## References

* [Stacks Project, Tag 0GPQ](https://stacks.math.columbia.edu/tag/0GPQ)
* [Stacks Project, Tag 0GPP](https://stacks.math.columbia.edu/tag/0GPP)
* [Stacks Project, Tag 077W](https://stacks.math.columbia.edu/tag/077W)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.QuasicoherentModule

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  (hsflat : IsFlat B S hS G.source.hom) (hsqc : IsQuasiCompact B S hS G.source.hom)
  (hsqs : IsQuasiSeparated B S hS G.source.hom)

attribute [local instance] isIso_alpha

/-- **Stacks 0GPQ.**  Let `(U, R, s, t, c)` be a groupoid in algebraic spaces with `s` flat,
quasi-compact and quasi-separated (then so is `t = s ∘ i`), and let
`forgetQuasicoherent G ⊣ cofree G` be the adjunction of Stacks 0GPP between the forgetful functor
`(ℱ, β) ↦ ℱ` and `𝒢 ↦ (s_*t^*𝒢, α)`.  The unit of this adjunction at a quasi-coherent module
`(ℱ, β)` on the groupoid is

`ℱ ⟶ s_*s^*ℱ ⟶ s_*t^*ℱ`,

the unit of the adjunction `s^* ⊣ s_*` at `ℱ` followed by the direct image along `s` of the
inverse of `β : t^*ℱ ⟶ s^*ℱ`. -/
@[stacks 0GPQ]
theorem forgetAdjunction_unit_app (M : QuasicoherentModule B S hS G) :
    ((forgetAdjunction G hsflat hsqc hsqs).unit.app M).hom =
      (modulePullbackAdjunction B S hS G.source).unit.app M.F.obj ≫
        (modulePushforward B S hS G.source).map (inv M.alpha) :=
  forgetAdjunction_unit_app_hom G hsflat hsqc hsqs M

end AlgebraicGeometry.Space.QuasicoherentModule

end
