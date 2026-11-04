module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource

/-!
# Local quasi-finiteness is étale local on the source and target

Being locally of finite type *and* locally quasi-finite is étale local on the source and
target in the sense of Stacks 04QZ. This is the case of Tag 04R3 listed there as "locally
quasi-finite"; the conjunction with local finite type is the form in which the condition is
used, both in Mathlib, where `AlgebraicGeometry.LocallyQuasiFinite` does not include finite
type, and in the definition of a locally quasi-finite morphism of algebraic spaces
(`AlgebraicGeometry.Space.IsLocallyQuasiFinite`, Stacks 03XJ, part (1)).

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget`:
  **Stacks 04R3**, the case of being locally quasi-finite.

## Implementation notes

Stability under étale precomposition and under étale base change are formal: an étale morphism
is both locally of finite type and locally quasi-finite, both properties are stable under
composition, and both are stable under arbitrary base change.

Only the criterion by étale neighbourhoods has content, and only in the direction from the
neighbourhoods to the morphism. For local finite type it is Tag 04R3 in that case,
`AlgebraicGeometry.LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget`. For local
quasi-finiteness the argument is topological, through the characterization of a locally
quasi-finite morphism locally of finite type by discreteness of its fibres,
`AlgebraicGeometry.locallyQuasiFinite_iff_isDiscrete_preimage_singleton`: in a commutative
square `k ≫ b = a ≫ f` with `a` and `b` étale and `k` locally quasi-finite, the fibre of `b`
above a point `y` of the target is discrete because `b` is étale, hence so is its preimage
under `k`, which is the preimage under `a` of the fibre of `f` above `y`. An étale morphism is
an open map, so the image under `a` of an open set isolating a point in that preimage isolates
its image in the fibre of `f`. Since every point of the source has such a square, every point
of every fibre of `f` is isolated in it.

## References

* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- In a commutative square `k ≫ b = a ≫ f` of morphisms of schemes with `a` and `b` étale and
`k` locally quasi-finite, a point of the source of `a` is isolated in the fibre of `f` above
the image of its image. -/
private theorem isOpen_singleton_preimage_of_etale_square {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    {a : U ⟶ X} {b : V ⟶ Y} {k : U ⟶ V} [Etale a] [Etale b] [LocallyQuasiFinite k]
    (hcomm : k ≫ b = a ≫ f) (y : Y) (u : U) (hu : f (a u) = y)
    (z : (f ⁻¹' {y} : Set X)) (hz : a u = z.1) :
    IsOpen ({z} : Set (f ⁻¹' {y} : Set X)) := by
  have hbk : ∀ w : U, b (k w) = f (a w) := fun w ↦ by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomm]
  have hset : (k ⁻¹' (b ⁻¹' {y}) : Set U) = a ⁻¹' (f ⁻¹' {y}) := by
    ext w; simp only [Set.mem_preimage, Set.mem_singleton_iff, hbk w]
  have hD : _root_.IsDiscrete (a ⁻¹' (f ⁻¹' {y}) : Set U) :=
    hset ▸ k.isDiscrete_preimage (b.isDiscrete_preimage_singleton y)
  have huD : u ∈ (a ⁻¹' (f ⁻¹' {y}) : Set U) := by simpa using hu
  have : DiscreteTopology (a ⁻¹' (f ⁻¹' {y}) : Set U) := hD.to_subtype
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp
    (isOpen_discrete ({(⟨u, huD⟩ : (a ⁻¹' (f ⁻¹' {y}) : Set U))} : Set _))
  have hOu : ∀ w (hw : w ∈ (a ⁻¹' (f ⁻¹' {y}) : Set U)), w ∈ O ↔ w = u := fun w hw ↦ by
    simpa [Subtype.ext_iff] using Set.ext_iff.mp hOeq ⟨w, hw⟩
  have huO : u ∈ O := (hOu u huD).2 rfl
  refine isOpen_induced_iff.mpr ⟨a '' O, a.isOpenMap O hO, ?_⟩
  ext w
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  refine ⟨?_, fun hw ↦ ⟨u, huO, hz.trans (congrArg Subtype.val hw.symm)⟩⟩
  rintro ⟨u', hu'O, hu'w⟩
  have hu'D : u' ∈ (a ⁻¹' (f ⁻¹' {y}) : Set U) := by
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hu'w]
    exact w.2
  exact Subtype.ext (hu'w.symm.trans ((congrArg a ((hOu u' hu'D).1 hu'O)).trans hz))

/-- **Stacks 04R3, the case of being locally quasi-finite.** Being a morphism of schemes
locally of finite type and locally quasi-finite is étale local on the source and target. -/
@[stacks 04R3 "locally quasi-finite"]
theorem locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget :
    IsEtaleLocalOnSourceAndTarget
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) where
  precomp :=
    { precomp := fun i hi _f hf ↦ by
        have : Etale i := hi
        have : LocallyOfFiniteType _f := hf.1
        have : LocallyQuasiFinite _f := hf.2
        exact ⟨inferInstance, inferInstance⟩ }
  pullbackSnd_of_etale f hf g _ := by
    have : LocallyOfFiniteType f := hf.1
    have : LocallyQuasiFinite f := hf.2
    exact ⟨inferInstance, inferInstance⟩
  iff_forall_exists_etale_neighborhood {X Y} f := by
    refine ⟨fun hf x ↦ ⟨X, Y, 𝟙 X, 𝟙 Y, f, x, inferInstance, inferInstance, by simp, by simp,
      hf⟩, fun h ↦ ?_⟩
    have hft : LocallyOfFiniteType f :=
      (LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget.iff_forall_exists_etale_neighborhood
        f).mpr fun x ↦ by
          obtain ⟨U, V, a, b, k, u, ha, hb, hau, hcomm, hP⟩ := h x
          exact ⟨U, V, a, b, k, u, ha, hb, hau, hcomm, hP.1⟩
    refine ⟨hft, ?_⟩
    rw [locallyQuasiFinite_iff_isDiscrete_preimage_singleton]
    intro y
    rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton]
    intro z
    obtain ⟨U, V, a, b, k, u, ha, hb, hau, hcomm, hP⟩ := h z.1
    have : Etale a := ha
    have : Etale b := hb
    have : LocallyQuasiFinite k := hP.2
    exact isOpen_singleton_preimage_of_etale_square hcomm y u
      (by rw [hau]; exact z.2) z hau

end AlgebraicGeometry

end
