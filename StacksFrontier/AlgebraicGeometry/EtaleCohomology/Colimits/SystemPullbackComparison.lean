module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageOfPushforward

/-!
# The comparison of inverse images along a composite, with the composite named

For `f : X ⟶ Y` and `g : Y ⟶ Z` the comparison
`Stacks.EtaleCohomology.smallEtalePullbackAbCompIso` of the inverse image of abelian small étale
sheaves along `f ≫ g` with the composite of the inverse images is
`CategoryTheory.Adjunction.leftAdjointCompIso` at the comparison of direct images. Consequently
the comparisons `Stacks.EtaleCohomology.systemPullbackComp` and
`Stacks.EtaleCohomology.conePullbackComp` attached to an inverse system of schemes, which keep the
composite as a named morphism, agree with it up to transport along the naming equation.

## Main definitions

* `Stacks.EtaleCohomology.smallEtalePullbackAbComp'` — the comparison
  `g^{-1} ∘ f^{-1} ≅ (fg)^{-1}` with the composite `fg` named rather than written out, the
  inverse-image counterpart of `Stacks.EtaleCohomology.smallEtalePushforwardAbComp'`.

## Main results

* `Stacks.EtaleCohomology.smallEtalePullbackAbCompIso_eq_leftAdjointCompIso` — the comparison of
  inverse images along a composite is Mathlib's
  `CategoryTheory.Adjunction.leftAdjointCompIso` at the comparison of direct images.
* `Stacks.EtaleCohomology.smallEtalePullbackAbComp'_eq_leftAdjointCompIso` — the same with the
  composite named.
* `Stacks.EtaleCohomology.systemPullbackComp_eq` and
  `Stacks.EtaleCohomology.conePullbackComp_eq` — the two comparisons of inverse images attached
  to an inverse system of schemes are `smallEtalePullbackAbComp'`.

## References

* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

/-! ### The comparison with a named composite -/

/-- The inverse image along a composite is the composite of the inverse images, for abelian
coefficients and with the composite named: `Stacks.EtaleCohomology.smallEtalePullbackAbCompIso`
followed by the transport along the naming equation. -/
def smallEtalePullbackAbComp' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    smallEtalePullbackAb g ⋙ smallEtalePullbackAb f ≅ smallEtalePullbackAb fg :=
  smallEtalePullbackAbCompIso f g ≪≫ eqToIso (congrArg smallEtalePullbackAb hfg.symm)

/-! ### Identification with the generic comparison of left adjoints -/

/-- The comparison of inverse images along a composite is Mathlib's comparison of left adjoints
at the comparison `f_* ∘ g_* ≅ (fg)_*` of direct images. -/
theorem smallEtalePullbackAbCompIso_eq_leftAdjointCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    smallEtalePullbackAbCompIso f g =
      Adjunction.leftAdjointCompIso (smallEtaleAdjunctionAb g) (smallEtaleAdjunctionAb f)
        (smallEtaleAdjunctionAb (f ≫ g)) (smallEtalePushforwardAbCompIso f g) := by
  refine Iso.symm_eq_iff.1 (Iso.ext <|
    (conjugateEquiv ((smallEtaleAdjunctionAb g).comp (smallEtaleAdjunctionAb f))
      (smallEtaleAdjunctionAb (f ≫ g))).injective ?_)
  exact (conjugateEquiv_smallEtalePullbackAbCompIso_inv f g).trans
    (Adjunction.conjugateEquiv_leftAdjointCompIso_inv (smallEtaleAdjunctionAb g)
      (smallEtaleAdjunctionAb f) (smallEtaleAdjunctionAb (f ≫ g))
      (smallEtalePushforwardAbCompIso f g)).symm

/-- The comparison of inverse images along a named composite is Mathlib's comparison of left
adjoints at `Stacks.EtaleCohomology.smallEtalePushforwardAbComp'`. -/
theorem smallEtalePullbackAbComp'_eq_leftAdjointCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    smallEtalePullbackAbComp' f g fg hfg =
      Adjunction.leftAdjointCompIso (smallEtaleAdjunctionAb g) (smallEtaleAdjunctionAb f)
        (smallEtaleAdjunctionAb fg) (smallEtalePushforwardAbComp' f g fg hfg) := by
  subst hfg
  rw [smallEtalePullbackAbComp', smallEtalePushforwardAbComp'_rfl,
    smallEtalePullbackAbCompIso_eq_leftAdjointCompIso]
  simp

/-! ### The two comparisons attached to an inverse system of schemes -/

variable {I : Type v} [Preorder I]

/-- The comparison of inverse images along a composite transition of an inverse system of
schemes is `Stacks.EtaleCohomology.smallEtalePullbackAbComp'` at the two transitions, with the
composite transition as the name of their composite. -/
theorem systemPullbackComp_eq (D : Iᵒᵖ ⥤ Scheme.{u}) {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    systemPullbackComp D Ab.{u + 1} a b =
      smallEtalePullbackAbComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b) := by
  rw [smallEtalePullbackAbComp'_eq_leftAdjointCompIso]
  rfl

/-- The comparison of inverse images along the factorisation of a projection of a cone over
an inverse system of schemes is `Stacks.EtaleCohomology.smallEtalePullbackAbComp'` at that
factorisation, with the projection as the name of the composite. -/
theorem conePullbackComp_eq {D : Iᵒᵖ ⥤ Scheme.{u}} (c : Cone D) {i j : Iᵒᵖ} (a : i ⟶ j) :
    conePullbackComp c a =
      smallEtalePullbackAbComp' (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm := by
  rw [smallEtalePullbackAbComp'_eq_leftAdjointCompIso]
  rfl

end Stacks.EtaleCohomology

end
