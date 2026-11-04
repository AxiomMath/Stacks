module

public import StacksFrontier.AlgebraicGeometry.AmpleFibreLimit.Basic
public import StacksFrontier.AlgebraicGeometry.ResidueFieldClosedImmersion

/-!
# Fibres of a base change along a closed immersion

Let `X₀ = X ×_S S₀` for a closed immersion `i : S₀ ⟶ S`. For a point `s₀` of `S₀` the fibre of
`X₀ ⟶ S₀` over `s₀` is the fibre of `X ⟶ S` over `i s₀`, compatibly with the two inclusions of
fibres into `X`. This is how invertibility and ampleness of a module on `X₀` are read on the
fibres of `X` over the points of `S₀`.

## Main definitions

* `Stacks.PolarizedAlgebraization.fiberIsoOfIsPullback`: the identification of fibres.

## Main results

* `Stacks.PolarizedAlgebraization.fiberIsoOfIsPullback_hom_fiberι`: its compatibility with the
  inclusions of the fibres.
* `Stacks.PolarizedAlgebraization.isClosedImmersion_fiberι`: the fibre over a closed point is a
  closed subscheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.PolarizedAlgebraization

variable {X S X₀ S₀ : Scheme.{u}} {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {j : X₀ ⟶ X} {i : S₀ ⟶ S}
  (h : IsPullback j f₀ f i) [IsClosedImmersion i]

include h in
/-- **The fibre of `X₀ = X ×_S S₀` over `s₀` is the fibre of `X` over `i s₀`.** -/
def fiberIsoOfIsPullback (s₀ : S₀) : f₀.fiber s₀ ≅ f.fiber (i s₀) :=
  haveI := residueFieldMap_isIso_of_isClosedImmersion i s₀
  @asIso _ _ _ _ _ (isPullback_fiberToSpecResidueField_of_isPullback h s₀).isIso_fst_of_isIso

/-- The identification of fibres commutes with the inclusions of the fibres into `X`. -/
theorem fiberIsoOfIsPullback_hom_fiberι (s₀ : S₀) :
    (fiberIsoOfIsPullback h s₀).hom ≫ f.fiberι (i s₀) = f₀.fiberι s₀ ≫ j := by
  simp only [fiberIsoOfIsPullback, Scheme.Hom.fiberι]
  exact pullback.lift_fst _ _ _

/-- The fibre of a morphism over a closed point is a closed subscheme of the source. -/
theorem isClosedImmersion_fiberι {Y T : Scheme.{u}} (g : Y ⟶ T) {t : T}
    (ht : IsClosed ({t} : Set T)) : IsClosedImmersion (g.fiberι t) :=
  have := isClosed_singleton_iff_isClosedImmersion.mp ht
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (IsPullback.of_hasPullback g (T.fromSpecResidueField t)).flip inferInstance

end Stacks.PolarizedAlgebraization

end
