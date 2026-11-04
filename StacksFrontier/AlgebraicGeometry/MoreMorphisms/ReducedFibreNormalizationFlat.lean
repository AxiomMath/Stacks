module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.DedekindBase
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Reduction

/-!
# Flatness of the normalization over a Dedekind base

Let `A` be a Dedekind domain and let `q : Z ⟶ Spec A` be a flat morphism whose source may be
normalized, that is, whose quasi-compact opens have finitely many irreducible components.  Then
the composite of the normalization morphism of `Z` with `q` is again flat.

## Main results

* `AlgebraicGeometry.flat_normalization_comp_of_isDedekindDomain`: the normalization morphism
  composed with a flat morphism to the spectrum of a Dedekind domain is flat.
* `AlgebraicGeometry.flat_normalization_pullback_snd_of_isDedekindDomain`: the same for the base
  change of a flat morphism along a morphism from the spectrum of a Dedekind domain.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 0AUW](https://stacks.math.columbia.edu/tag/0AUW)
* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Let `A` be a Dedekind domain and `q : Z ⟶ Spec A` flat, with `Z` normalizable. The composite
of the normalization morphism of `Z` with `q` is flat. -/
theorem flat_normalization_comp_of_isDedekindDomain {A : Type u} [CommRing A]
    [IsDedekindDomain A] {Z : Scheme.{u}} (q : Z ⟶ Spec (.of A)) [Flat q]
    (hZ : ∀ U : Z.Opens, IsCompact (U : Set Z) → (irreducibleComponents U).Finite) :
    Flat (Z.normalization hZ ≫ q) := by
  have : IsReduced (Z.normalizationScheme hZ) := Scheme.isReduced_normalizationScheme Z hZ
  refine flat_of_forall_genericPoint_map_eq _ fun η hη ↦ ?_
  have h : q (Z.normalization hZ η) ∈ genericPoints (Spec (.of A)) :=
    q.mem_genericPoints_of_flat (Scheme.normalization_mem_genericPoints Z hZ hη)
  rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at h
  simpa using h

/-- Let `f : X ⟶ Spec A` be flat and `g : Spec B ⟶ Spec A` with `B` a Dedekind domain, and let
`X ×_{Spec A} Spec B` be normalizable. The composite of its normalization morphism with the
second projection to `Spec B` is flat. -/
theorem flat_normalization_pullback_snd_of_isDedekindDomain {A B : Type u} [CommRing A]
    [CommRing B] [IsDedekindDomain B] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f]
    (g : Spec (.of B) ⟶ Spec (.of A))
    (hZ : ∀ U : (pullback f g : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback f g : Scheme.{u})) → (irreducibleComponents U).Finite) :
    Flat ((pullback f g : Scheme.{u}).normalization hZ ≫ pullback.snd f g) :=
  flat_normalization_comp_of_isDedekindDomain _ hZ

end AlgebraicGeometry

end
