module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety

/-!
# The zero abelian variety

The trivial group scheme `Spec k ⟶ Spec k`, the tensor unit of the slice over `Spec k`, is an
abelian variety in the sense of Tag 03RO: `Spec k` is a proper, geometrically integral variety
over `k`, every base change of it to a field `K` being `Spec K`.

## Main results

* `AlgebraicGeometry.isAbelianVariety_tensorUnit`: the zero group scheme is an abelian variety.

## References

* [Stacks Project, Tag 03RO](https://stacks.math.columbia.edu/tag/03RO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

universe u

/-- The zero group scheme over `k`, the trivial group `Spec k ⟶ Spec k`, is an abelian variety:
`Spec k` is a proper, geometrically integral variety over `k`, every base change of it to a field
`K` being `Spec K`. -/
instance isAbelianVariety_tensorUnit (k : Type u) [Field k] :
    IsAbelianVariety k (𝟙_ (Over (Spec (.of k)))) := by
  have e : (𝟙_ (Over (Spec (.of k)))).hom = 𝟙 _ := rfl
  have : IsIso (𝟙_ (Over (Spec (.of k)))).hom := by rw [e]; infer_instance
  have : Nonempty (𝟙_ (Over (Spec (.of k)))).left :=
    ⟨(inv (𝟙_ (Over (Spec (.of k)))).hom).base (Nonempty.some inferInstance)⟩
  have : IsIntegral (𝟙_ (Over (Spec (.of k)))).left :=
    isIntegral_of_isOpenImmersion (𝟙_ (Over (Spec (.of k)))).hom
  have hgi : GeometricallyIntegral (𝟙_ (Over (Spec (.of k)))).hom := by
    refine ⟨fun K _ y X' fst snd h => ?_⟩
    have : IsIso snd := h.isIso_snd_of_isIso
    have : Nonempty X' := ⟨(inv snd).base (Nonempty.some inferInstance)⟩
    exact isIntegral_of_isOpenImmersion snd
  exact .mk (toIsProperVariety := .mk (toIsVariety := .mk)) (toGeometricallyIntegral := hgi)

end AlgebraicGeometry
