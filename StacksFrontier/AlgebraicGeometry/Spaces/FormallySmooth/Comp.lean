module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Composition of formally smooth, étale and unramified transformations

The composite of two transformations of set-valued functors on the big fppf site over a
scheme is formally smooth, formally étale, or formally unramified as soon as both factors
are.

## Main results

* `AlgebraicGeometry.Space.FormallySmooth.comp` states that formal smoothness is preserved
  by composition.
* `AlgebraicGeometry.Space.formallyEtale_comp` states that formal étaleness is preserved by
  composition.
* `AlgebraicGeometry.Space.formallyUnramified_comp` states that formal unramifiedness is
  preserved by composition.

## Implementation notes

The three statements use the same big fppf site, base scheme and affine square-zero lifting
problems for both factors and for the composite, and the composite is the categorical
composition of natural transformations.

## References

* [Stacks Project, Tag 049T](https://stacks.math.columbia.edu/tag/049T)
-/

public section

open CategoryTheory Opposite

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}

/-- **Stacks 049T, formal smoothness under composition.** -/
@[stacks 049T "formally_smooth_comp",
  ega "IV 17.1.3" "(ii) smooth",
  ega "IV 17.1.5" "sufficiency, smooth"]
public theorem FormallySmooth.comp (a : F ⟶ G) (b : G ⟶ H)
    (ha : FormallySmooth a) (hb : FormallySmooth b) :
    FormallySmooth (a ≫ b) := by
  intro T T' hT hT' i hi x y hxy
  obtain ⟨g, hg₁, hg₂⟩ := hb T T' hT hT' i hi (a.app (op T) x) y (by simpa using hxy)
  obtain ⟨z, hz₁, hz₂⟩ := ha T T' hT hT' i hi x g (by simpa using hg₁.symm)
  exact ⟨z, hz₁, by simpa [hz₂] using hg₂⟩

/-- The composite of two formally étale transformations is formally étale. -/
@[stacks 049T "formally_etale_comp",
  ega "IV 17.1.3" "(ii) étale",
  ega "IV 17.1.5" "sufficiency, étale"]
public theorem formallyEtale_comp {a : F ⟶ G} {b : G ⟶ H}
    (ha : FormallyEtale a) (hb : FormallyEtale b) :
    FormallyEtale (a ≫ b) := by
  intro T T' hT hT' i hi x y hxy
  obtain ⟨yG, hyG, hyG_unique⟩ := hb T T' hT hT' i hi _ y (by simpa using hxy)
  obtain ⟨z, hz, hz_unique⟩ := ha T T' hT hT' i hi x yG hyG.1.symm
  exact ⟨z, ⟨hz.1, by simpa [hz.2] using hyG.2⟩, fun z' hz' => hz_unique _ ⟨hz'.1,
    hyG_unique _ ⟨by rw [← a.naturality_apply i.op z', hz'.1], by simpa using hz'.2⟩⟩⟩

/-- **Stacks 049T, composition part.** A composite of formally unramified
transformations is formally unramified. -/
@[stacks 049T "formally_unramified_comp",
  ega "IV 17.1.3" "(ii) unramified",
  ega "IV 17.1.5" "sufficiency, unramified"]
public theorem formallyUnramified_comp (a : F ⟶ G) (b : G ⟶ H)
    (ha : FormallyUnramified a) (hb : FormallyUnramified b) :
    FormallyUnramified (a ≫ b) := by
  intro T T' hT hT' i hi x y hxy z₁ z₂ hz₁ hz₂
  have lift (z : F.obj (op T')) (hz : IsLift (a ≫ b) i x y z) :
      IsLift b i (a.app (op T) x) y (a.app (op T') z) :=
    ⟨by rw [← a.naturality_apply i.op z, hz.1], by simpa using hz.2⟩
  exact ha T T' hT hT' i hi x _ (lift z₁ hz₁).1.symm z₁ z₂
    ⟨hz₁.1, rfl⟩ ⟨hz₂.1, (hb T T' hT hT' i hi _ y (by simpa using hxy)
      _ _ (lift z₁ hz₁) (lift z₂ hz₂)).symm⟩

end AlgebraicGeometry.Space

end
