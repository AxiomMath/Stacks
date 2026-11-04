module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen

/-!
# Opens which are dense in the fibres

Let `Ȳ ⟶ T` be smooth with geometrically connected fibres, let `Y ⊆ Ȳ` be open and let
`ν : Y ⟶ X` be a morphism over a base `V` to which `T` maps. If `ν⁻¹(W)` meets every fibre of
`Y ⟶ T` for an open `W ⊆ X`, then `ν⁻¹(W)` is dense in every fibre of `Y ⟶ T`, because these
fibres are open in the fibres of `Ȳ ⟶ T`, which are irreducible; and if moreover `ν` is
surjective, then `W` is dense in every fibre of `X ⟶ V`. This is the last paragraph of the proof
of [Stacks, Tag 0GK7].

## Main results

* `AlgebraicGeometry.dense_preimage_fiberι_of_smooth`: the density of `ν⁻¹(W)` in the fibres of
  `Y ⟶ T`.
* `AlgebraicGeometry.dense_preimage_fiberι_of_surjective`: the density of `W` in the fibres of
  `X ⟶ V`.

## Implementation notes

A fibre is the scheme-theoretic fibre `Scheme.Hom.fiber`, and density in it is density of the
preimage under `Scheme.Hom.fiberι`. The arguments are carried out on the set-theoretic fibres,
to which the scheme-theoretic fibres are homeomorphic by `Scheme.Hom.fiberHomeo`.

## References

* [Stacks Project, Tag 0GK7](https://stacks.math.columbia.edu/tag/0GK7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Density in a scheme-theoretic fibre is density in the set-theoretic fibre. -/
theorem dense_preimage_fiberι_iff (f : X ⟶ Y) (y : Y) (A : Set X) :
    Dense ((f.fiberι y) ⁻¹' A) ↔ Dense {x : (f : X → Y) ⁻¹' {y} | x.1 ∈ A} := by
  have h : (f.fiberι y) ⁻¹' A = (f.fiberHomeo y) ⁻¹' {x : (f : X → Y) ⁻¹' {y} | x.1 ∈ A} := by
    ext x
    simp [Scheme.Hom.fiberHomeo_apply]
  rw [h]
  exact ⟨fun hd => by
      simpa using hd.preimage (f.fiberHomeo y).symm.isOpenMap,
    fun hd => hd.preimage (f.fiberHomeo y).isOpenMap⟩

/-- The set-theoretic fibres of a smooth morphism with geometrically connected fibres are
irreducible. -/
theorem isIrreducible_preimage_singleton_of_smooth {Z T : Scheme.{u}} (q : Z ⟶ T) [Smooth q]
    [GeometricallyConnected q] (s : T) : IsIrreducible ((q : Z → T) ⁻¹' {s}) := by
  have : Smooth (q.fiberToSpecResidueField s) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback q _).flip.flip ‹_›
  have : IsIntegral (q.fiber s) :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (k := T.residueField s)
      (q.fiberToSpecResidueField s)
  rw [isIrreducible_iff_irreducibleSpace]
  exact (q.fiberHomeo s).irreducibleSpace_iff.mp inferInstance

/-- **Density of `ν⁻¹(W)` in the fibres of `Y ⟶ T`.** Let `q̄ : Ȳ ⟶ T` be smooth with
geometrically connected fibres and `j : Y ⟶ Ȳ` an open immersion. An open subset `O` of `Y` which
meets every fibre of `j ≫ q̄` is dense in every fibre of `j ≫ q̄`. -/
theorem dense_preimage_fiberι_of_smooth {Ybar T : Scheme.{u}} (qbar : Ybar ⟶ T) (jY : Y ⟶ Ybar)
    [Smooth qbar] [GeometricallyConnected qbar] [IsOpenImmersion jY] {O : Set Y} (hO : IsOpen O)
    (hmeet : ∀ s : T, ∃ y ∈ O, qbar (jY y) = s) (s : T) :
    Dense (((jY ≫ qbar).fiberι s) ⁻¹' O) := by
  rw [dense_preimage_fiberι_iff, dense_iff_inter_open]
  rintro U ⟨U', hU', rfl⟩ ⟨⟨y₁, hy₁⟩, hyU⟩
  obtain ⟨y₂, hy₂O, hy₂⟩ := hmeet s
  have hirr := isIrreducible_preimage_singleton_of_smooth qbar s
  have hcomp : ∀ y : Y, (jY ≫ qbar) y = qbar (jY y) := fun y => rfl
  obtain ⟨z, hzs, hzU, hzO⟩ := hirr.2 _ _ (jY.isOpenMap _ hU') (jY.isOpenMap _ hO)
    ⟨jY y₁, by simpa [hcomp] using hy₁, y₁, hyU, rfl⟩ ⟨jY y₂, hy₂, y₂, hy₂O, rfl⟩
  obtain ⟨a, haU, rfl⟩ := hzU
  obtain ⟨b, hbO, hb⟩ := hzO
  obtain rfl := jY.isOpenEmbedding.injective hb
  exact ⟨⟨b, by simpa [hcomp] using hzs⟩, haU, hbO⟩

/-- **Density of `W` in the fibres of `X ⟶ V`.** Let `ν : Y ⟶ X` be surjective, let `q : Y ⟶ T`
and `t : T ⟶ V` with `ν ≫ p = q ≫ t`, and let `W ⊆ X`. If `ν⁻¹(W)` is dense in every fibre of
`q`, then `W` is dense in every fibre of `p`. -/
theorem dense_preimage_fiberι_of_surjective {T V : Scheme.{u}} (p : X ⟶ V) (t : T ⟶ V)
    (q : Y ⟶ T) (ν : Y ⟶ X) [Surjective ν] (hcomm : ν ≫ p = q ≫ t) (W : Set X)
    (hdense : ∀ s : T, Dense ((q.fiberι s) ⁻¹' (ν ⁻¹' W))) (s : V) :
    Dense ((p.fiberι s) ⁻¹' W) := by
  rw [dense_preimage_fiberι_iff]
  intro x
  obtain ⟨y, hy⟩ := ν.surjective x.1
  have hpt : ∀ y' : Y, p (ν y') = t (q y') := fun y' => by
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  have hys : t (q y) = s := by rw [← hpt, hy]; exact x.2
  let φ : (q : Y → T) ⁻¹' {q y} → (p : X → V) ⁻¹' {s} := fun y' =>
    ⟨ν y'.1, by
      show p (ν y'.1) = s
      rw [hpt, show q y'.1 = q y from y'.2, hys]⟩
  rw [← show φ ⟨y, rfl⟩ = x from Subtype.ext hy]
  exact map_mem_closure ((ν.continuous.comp continuous_subtype_val).subtype_mk _)
    ((dense_preimage_fiberι_iff q (q y) _).mp (hdense (q y)) ⟨y, rfl⟩) fun _ h => h

end AlgebraicGeometry

end
