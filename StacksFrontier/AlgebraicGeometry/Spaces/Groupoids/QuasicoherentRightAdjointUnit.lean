module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# The unit of the right adjoint to the forgetful functor on a groupoid in algebraic spaces

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces and let `(ℱ, β)` be a quasi-coherent
module on it, so that `β : t^*ℱ ⟶ s^*ℱ` is an isomorphism by Stacks 077W.  The composite

`ℱ ⟶ s_*s^*ℱ ⟶ s_*t^*ℱ`

of the unit of the adjunction `s^* ⊣ s_*` of Stacks 03LU and the direct image of `β⁻¹` is the
map that Stacks 0GPQ identifies with the unit of the adjunction of Stacks 0GPP between the
forgetful functor `(ℱ, β) ↦ ℱ` and its right adjoint `𝒢 ↦ (s_*t^*𝒢, α)`.

## Main definitions

* `AlgebraicGeometry.Space.QuasicoherentModule.sourceUnitInvAlpha` is the composite
  `ℱ ⟶ s_*s^*ℱ ⟶ s_*t^*ℱ`.

## Main results

* `AlgebraicGeometry.Space.QuasicoherentModule.sourceUnitInvAlpha_naturality`: the composite is
  natural in the quasi-coherent module `(ℱ, β)`.

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
  {A : AlgebraicSpaces B S hS} {G : GroupoidInAlgebraicSpaces B S hS A}

attribute [local instance] isIso_alpha

/-- The composite `ℱ ⟶ s_*s^*ℱ ⟶ s_*t^*ℱ` of the unit of the adjunction `s^* ⊣ s_*` of
Stacks 03LU at `ℱ` and the direct image along the source of the inverse of the transition
morphism `β : t^*ℱ ⟶ s^*ℱ`, which is invertible by Stacks 077W. -/
def sourceUnitInvAlpha (M : QuasicoherentModule B S hS G) :
    M.F.obj ⟶ (modulePushforward B S hS G.source).obj
      ((modulePullback B S hS G.target).obj M.F.obj) :=
  (modulePullbackAdjunction B S hS G.source).unit.app M.F.obj ≫
    (modulePushforward B S hS G.source).map (inv M.alpha)

/-- The inverse of the transition morphism commutes with the inverse images of a morphism of
quasi-coherent modules on the groupoid. -/
@[reassoc]
theorem inv_alpha_naturality {M N : QuasicoherentModule B S hS G} (φ : M ⟶ N) :
    (modulePullback B S hS G.source).map φ.hom ≫ inv N.alpha =
      inv M.alpha ≫ (modulePullback B S hS G.target).map φ.hom := by
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  exact φ.comm

/-- The composite `ℱ ⟶ s_*s^*ℱ ⟶ s_*t^*ℱ` is natural in the quasi-coherent module `(ℱ, β)`. -/
@[reassoc]
theorem sourceUnitInvAlpha_naturality {M N : QuasicoherentModule B S hS G} (φ : M ⟶ N) :
    φ.hom ≫ sourceUnitInvAlpha N =
      sourceUnitInvAlpha M ≫ (modulePushforward B S hS G.source).map
        ((modulePullback B S hS G.target).map φ.hom) := by
  rw [sourceUnitInvAlpha, sourceUnitInvAlpha, ← Adjunction.unit_naturality_assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, inv_alpha_naturality]

end AlgebraicGeometry.Space.QuasicoherentModule

end
