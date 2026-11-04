module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.CenteredGermDeathOfValuation
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite

/-!
# Open sets of `U ×_Y Y'` along the fibre over a point of an étale `U`

This file proves the input `AlgebraicGeometry.Scheme.ZariskiRiemann.FibreOpenOverEtale` of the
Zariski–Riemann step of Gabber's germ-killing argument: for `U ⟶ Y` étale, `π : Y' ⟶ Y`, an open
`O ⊆ U ×_Y Y'` and `w ∈ U`, if `O` contains every point over `w` and `y₀`, then it contains every
point over `w` and `y'` for all `y'` in an open neighbourhood of `y₀` in the fibre of `π`.

Let `y` be the image of `w` in `Y`. The points of `U ×_Y Y'` over `w` are the image of the fibre
of `U ×_Y Y' ⟶ U` over `w`, which is the base change of `Spec κ(w) ⟶ Spec κ(y)` along the fibre
`Y'_y ⟶ Spec κ(y)` (Mathlib's `isPullback_fiberToSpecResidueField_of_isPullback`). Since
`U ⟶ Y` is étale, hence locally quasi-finite, `κ(w)` is finite over `κ(y)`, so this base change
is finite, in particular a closed map. The image in `Y'_y` of the closed set of points over `w`
outside `O` is therefore closed in `Y'_y`, and it misses `y₀`; its complement is the required
neighbourhood. If `y₀` does not lie over `y`, there is nothing to prove.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.isFinite_spec_residueFieldMap_of_etale`: the
  residue field extension at a point of an étale morphism is finite.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.fibreOpenOverEtale`: the proposition
  `AlgebraicGeometry.Scheme.ZariskiRiemann.FibreOpenOverEtale` holds.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

/-- For an étale morphism `f : X ⟶ Y` and `x ∈ X`, the morphism `Spec κ(x) ⟶ Spec κ(f x)` induced
by the residue field extension is finite: it factors as the `κ(x)`-point of the fibre of `f` over
`f x` followed by the fibre's structure morphism, both locally quasi-finite, and its target is the
spectrum of a field. -/
theorem isFinite_spec_residueFieldMap_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    (x : X) : IsFinite (Spec.map (f.residueFieldMap x)) := by
  have := (locallyQuasiFinite_of_etale f).2
  have : LocallyQuasiFinite (Spec.map (f.residueFieldMap x)) := by
    rw [← f.asFiberHom_fiberToSpecResidueField x]
    infer_instance
  exact IsFinite.of_locallyQuasiFinite _

/-- A point `x` of `X` lying over `y` is in the image of the fibre inclusion `f.fiberι y`. -/
private theorem exists_fiberι_eq {X Y : Scheme.{u}} {f : X ⟶ Y} {y : Y} {x : X} (hx : f x = y) :
    ∃ a, f.fiberι y a = x := by
  rw [← Set.mem_range, Scheme.Hom.range_fiberι]
  exact hx

/-- **Open sets of `U ×_Y Y'` along the fibre over a point of an étale `U`**:
`AlgebraicGeometry.Scheme.ZariskiRiemann.FibreOpenOverEtale` holds. -/
theorem fibreOpenOverEtale : FibreOpenOverEtale.{u} := by
  intro Y Y' π U O hO w y₀ hO₀
  by_cases hy : π y₀ = U.hom w
  swap
  · refine ⟨Set.univ, isOpen_univ, trivial, fun y' _ hy' u' hu₁ hu₂ => (hy ?_).elim⟩
    have hc : (pullback.fst U.hom π ≫ U.hom) u' = (pullback.snd U.hom π ≫ π) u' := by
      rw [pullback.condition]
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hu₁, hu₂] at hc
    rw [← hy', hc]
  obtain ⟨h, H, hh⟩ : ∃ h : (pullback.fst U.hom π).fiber w ⟶ π.fiber (U.hom w),
      IsPullback h ((pullback.fst U.hom π).fiberToSpecResidueField w)
        (π.fiberToSpecResidueField (U.hom w)) (Spec.map (U.hom.residueFieldMap w)) ∧
      h ≫ π.fiberι (U.hom w) = (pullback.fst U.hom π).fiberι w ≫ pullback.snd U.hom π :=
    ⟨_, isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback U.hom π).flip w, pullback.lift_fst _ _ _⟩
  have := isFinite_spec_residueFieldMap_of_etale U.hom w
  have : UniversallyClosed h :=
    MorphismProperty.of_isPullback (P := @UniversallyClosed) H.flip inferInstance
  set ι := (pullback.fst U.hom π).fiberι w with hι
  have hrange : ∀ a, pullback.fst U.hom π (ι a) = w := fun a =>
    (Scheme.Hom.range_fiberι _ _).le ⟨a, rfl⟩
  have he : ∀ a, π.fiberι (U.hom w) (h a) = pullback.snd U.hom π (ι a) := fun a => by
    rw [← Scheme.Hom.comp_apply, hh, Scheme.Hom.comp_apply]
  have hZ : IsClosed (h '' (ι ⁻¹' Oᶜ)) :=
    h.isClosedMap _ (hO.isClosed_compl.preimage ι.continuous)
  obtain ⟨F, hF, hFZ⟩ := (π.fiberι (U.hom w)).isEmbedding.isInducing.isClosed_iff.mp hZ
  refine ⟨Fᶜ, hF.isOpen_compl, fun hy₀ => ?_, fun y' hy' _ u' hu₁ hu₂ => ?_⟩
  · obtain ⟨z, hz⟩ := exists_fiberι_eq hy
    have hzF : z ∈ (π.fiberι (U.hom w)) ⁻¹' F := by
      rw [Set.mem_preimage, hz]; exact hy₀
    rw [hFZ] at hzF
    obtain ⟨a, ha, rfl⟩ := hzF
    exact ha (hO₀ _ (hrange a) (by rw [← he, hz]))
  · by_contra hnO
    obtain ⟨a, rfl⟩ := exists_fiberι_eq hu₁
    have hmem : h a ∈ (π.fiberι (U.hom w)) ⁻¹' F := hFZ ▸ ⟨a, hnO, rfl⟩
    exact hy' (by rw [← hu₂, ← he]; exact hmem)

end AlgebraicGeometry.Scheme.ZariskiRiemann
