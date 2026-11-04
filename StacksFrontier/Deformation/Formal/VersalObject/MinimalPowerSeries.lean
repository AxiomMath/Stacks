module

public import StacksFrontier.Deformation.Formal.MinimalVersal.DescentVersality
public import StacksFrontier.Deformation.Formal.MinimalVersal.Existence
public import StacksFrontier.Deformation.Formal.MinimalVersal.PowerSeriesDecomposition
public import StacksFrontier.Deformation.MinimalVersal
public import StacksFrontier.Deformation.Schlessinger.VersalImpliesS1
public import StacksCore.Tactic.StacksAttribute

/-!
# Versal formal objects are pushforwards along power series extensions

Every versal formal object of a predeformation category is the pushforward of a minimal versal
formal object along a power series ring extension of its base.

## Main results

* `Deformation.exists_minimalVersal_powerSeries` produces, for a versal formal object `ξ`, a
  minimal versal formal object `η` together with a cocartesian morphism `η ⟶ ξ` whose base map
  identifies `ξ.base` with a power series algebra `η.base[[x_1, …, x_r]]`.

## Implementation notes

The minimal versal object is a smallest descent of `ξ` in the sense of Stacks 06T2, which exists
because a versal formal object forces Schlessinger's condition (S1) (Stacks 06SY). Its
versality is Stacks 06T3 and its minimality is the no-proper-further-descent field of
`Deformation.SmallestDescent`, exactly as in `Deformation.exists_minimalVersalFormalObject`; the
power series identification of the two bases is the other half of Stacks 06T3,
`Deformation.exists_mvPowerSeries_algEquiv_of_smallestDescent`.

The pushforward relation is recorded explicitly as strong cocartesianness of the morphism
`η ⟶ ξ` over the projection to complete local algebras. Since that projection is cofibered in
groupoids (Stacks 06H4), this is automatic for any morphism of formal objects, but stating it
makes the conclusion the pushforward assertion of the source rather than the bare existence of
a morphism.

The Noetherian and finite-module hypotheses are the chapter conventions of Stacks 06G9.

## References

* [Stacks Project, Tag 06T5](https://stacks.math.columbia.edu/tag/06T5)
-/

@[expose] public section

namespace Deformation

open CategoryTheory

universe u v w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

/-- **Stacks 06T5.** Any versal formal object `ξ` of a predeformation category is the
pushforward of a minimal versal formal object `η` along a power series ring extension: there is
a morphism `η ⟶ ξ` which is strongly cocartesian over its base map, and an isomorphism of
`Λ`-algebras `η.base[[x_1, …, x_r]] ≃ ξ.base` carrying a constant to the image of its
coefficient under that base map. -/
@[stacks 06T5 "power_series_extension"]
public theorem exists_minimalVersal_powerSeries [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hp : IsPredeformationCategory p) (ξ : FormalObject p) (hξ : IsVersal hp.cofibered ξ) :
    ∃ η : FormalObject p, ∃ f : η ⟶ ξ, IsMinimalVersal hp.cofibered η ∧
      (FormalObject.projection (p := p)).IsStronglyCocartesian f.base f ∧
      ∃ r : ℕ, ∃ e : MvPowerSeries (Fin r) η.base ≃ₐ[Λ] ξ.base,
        ∀ a : η.base, e (MvPowerSeries.C a) = f.base.hom a := by
  let d : SmallestDescent ξ :=
    smallestDescent hp.cofibered (schlessingerConditionS1_of_versal p hp ξ hξ) ξ hξ
  refine ⟨d.object, d.inclusion,
    ⟨isVersal_smallestDescent hp.cofibered hξ d, d.further_descent_surjective⟩, ?_,
    exists_mvPowerSeries_algEquiv_of_smallestDescent hp.cofibered ξ hξ d⟩
  exact isStronglyCocartesian_of_isCofiberedInGroupoids
    (formalObjectProjection_isCofiberedInGroupoids p hp.cofibered)
    d.inclusion.base d.inclusion
    (IsHomLift.of_fac _ d.inclusion.base d.inclusion rfl rfl
      (FormalObject.projection_map d.inclusion).symm)

end Deformation

end
