module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Constructions
public import StacksFrontier.RingTheory.Spectrum.Prime.Constructible.GenericFinitePresentation
public import StacksCore.Tactic.StacksAttribute

/-!
# Nonempty generic fibre

A finite type morphism to an irreducible scheme whose generic fibre is nonempty is surjective
after restriction to some nonempty open subscheme of the target.

## Main results

* `AlgebraicGeometry.exists_nonempty_open_surjective_baseChange` gives a nonempty open
  subscheme over which the morphism becomes surjective.

## Implementation notes

An open subset is represented by an element `V : Y.Opens`. Its base change is the pullback
along the canonical open immersion `V.ι`, and the morphism to the open subscheme is the second
pullback projection.

## References

* [Stacks Project, Tag 05F5](https://stacks.math.columbia.edu/tag/05F5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 05F5.** A finite type morphism to an irreducible scheme
with nonempty generic fibre is surjective over some nonempty open subscheme of
the target. -/
@[stacks 05F5, ega "IV 1.8.6" "first assertion"]
theorem exists_nonempty_open_surjective_baseChange
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (η : Y) (hη : IsGenericPoint η Set.univ) (h : Nonempty (f.fiber η)) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ Surjective (pullback.snd f V.ι) := by
  classical
  let x : X := f.fiberι η (Classical.choice h)
  have hxη : f x = η := (f.range_fiberι η).subset ⟨Classical.choice h, rfl⟩
  obtain ⟨V₀, hV₀, hηV₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := η) (U := ⊤) (by simp)
  have hxV₀ : x ∈ f ⁻¹ᵁ V₀ := by
    change f x ∈ (V₀ : Set Y)
    rwa [hxη]
  obtain ⟨U₀, hU₀, hxU₀, hU₀V₀⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := f ⁻¹ᵁ V₀) hxV₀
  let φ := (f.appLE V₀ U₀ hU₀V₀).hom
  have hφ : φ.FiniteType := LocallyOfFiniteType.finiteType_appLE f hV₀ hU₀ hU₀V₀
  let ξ : PrimeSpectrum Γ(Y, V₀) := hV₀.primeIdealOf ⟨η, hηV₀⟩
  let q : PrimeSpectrum Γ(X, U₀) := hU₀.primeIdealOf ⟨x, hxU₀⟩
  have hqξ : q.comap φ = ξ := by
    dsimp [q, ξ, φ]
    have hqfx := IsAffineOpen.comap_primeIdealOf_appLE V₀ hV₀ U₀ hU₀ hU₀V₀ hxU₀
    have hsub : (⟨f x, hU₀V₀ hxU₀⟩ : V₀) = ⟨η, hηV₀⟩ := Subtype.ext hxη
    simpa [hsub] using hqfx
  have hξgen : IsGenericPoint ξ (Set.univ : Set (PrimeSpectrum Γ(Y, V₀))) := by
    have hξη : hV₀.fromSpec ξ = η := by
      simpa [ξ] using hV₀.fromSpec_primeIdealOf ⟨η, hηV₀⟩
    rw [isGenericPoint_iff_specializes]
    intro r
    constructor
    · intro _
      simp
    · intro _
      apply hV₀.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp
      simpa [hξη] using hη.specializes (Set.mem_univ _)
  obtain ⟨D, hDopen, hDdense, hDimg⟩ :=
    image_constructible_contains_open_dense_in_closure φ hφ Set.univ
      Topology.IsConstructible.univ ξ ⟨q, Set.mem_univ _, hqξ⟩
  have hclosure : closure ({ξ} : Set (PrimeSpectrum Γ(Y, V₀))) = Set.univ := hξgen.def
  obtain ⟨W, hWopen, hWdense, hWpre⟩ :=
    exists_open_dense_of_open_dense_subtype (s := closure ({ξ} : Set (PrimeSpectrum Γ(Y, V₀))))
      (by simp [hclosure]) hDopen hDdense
  let V : Y.Opens := ⟨hV₀.fromSpec.base '' W, hV₀.fromSpec.isOpenEmbedding.isOpenMap _ hWopen⟩
  have hV_nonempty : (V : Set Y).Nonempty := by
    have : Nonempty (PrimeSpectrum Γ(Y, V₀)) := ⟨ξ⟩
    obtain ⟨r, hr⟩ := hWdense.nonempty
    exact ⟨hV₀.fromSpec r, ⟨r, hr, rfl⟩⟩
  have hV_range : (V : Set Y) ⊆ Set.range f := by
    rintro y ⟨r, hrW, rfl⟩
    obtain ⟨r', -, hr'⟩ :=
      (hDimg ⟨⟨r, by rw [hclosure]; trivial⟩, by rwa [← hWpre], rfl⟩).2
    refine ⟨hU₀.fromSpec r', ?_⟩
    have hpt := congrArg (fun g : Spec Γ(X, U₀) ⟶ Y => g r')
      (IsAffineOpen.SpecMap_appLE_fromSpec f hV₀ hU₀ hU₀V₀)
    change hV₀.fromSpec (PrimeSpectrum.comap φ r') = f (hU₀.fromSpec r') at hpt
    rwa [hr', eq_comm] at hpt
  refine ⟨V, hV_nonempty, ⟨fun y => Set.mem_range.mp ?_⟩⟩
  rw [Scheme.Pullback.range_snd]
  exact hV_range y.2

end AlgebraicGeometry

end
