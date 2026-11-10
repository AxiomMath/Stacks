module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantFibreFinite
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Basic

/-!
# Invariance of an open from a specialization-stable invariant subset

An open subset `V` of the object scheme of a groupoid scheme is invariant as soon as it contains
an invariant subset `Z` into which every point of `V` specializes, provided the source map is a
closed map. For a closed morphism to the spectrum of a local ring, every point specializes into
the fibre over the closed point; the fibres of the quotient morphism of a groupoid scheme are
invariant.

## Main results

* `AlgebraicGeometry.mem_of_isOpen_of_mem_closure`: an open set is stable under generization.
* `AlgebraicGeometry.exists_mem_closure_fibre_closedPoint`: for a closed morphism to the spectrum
  of a local ring, every point specializes into the closed fibre.
* `Stacks.Groupoids.isInvariantSet_of_forall_exists_mem_closure`: **the invariance criterion.**
* `AlgebraicGeometry.GroupoidScheme.isInvariantSet_fibre_objectsToInvariantSpectrum`: the fibre of
  the quotient morphism over a point of the invariant spectrum is invariant.
* `AlgebraicGeometry.GroupoidScheme.isClosedMap_source` and `isClosedMap_target`: the source and
  target maps of a groupoid scheme with finite locally free structure maps are closed.

## References

* [Stacks Project, Tag 03BC](https://stacks.math.columbia.edu/tag/03BC)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Stacks.Groupoids Stacks.Morphisms

noncomputable section

universe u

namespace AlgebraicGeometry

/-- **An open set is stable under generization.** If a point of the closure of `x` lies in an
open set, then so does `x`. -/
theorem mem_of_isOpen_of_mem_closure {X : Type*} [TopologicalSpace X] {V : Set X} (hV : IsOpen V)
    {x y : X} (hy : y ∈ closure ({x} : Set X)) (hyV : y ∈ V) : x ∈ V := by
  obtain ⟨_, hz, hzx⟩ := mem_closure_iff.mp hy V hV hyV
  rwa [Set.mem_singleton_iff.mp hzx] at hz

/-- **A nonempty closed subset of the spectrum of a local ring contains the closed point.** -/
theorem closedPoint_mem_of_isClosed_of_nonempty {R : CommRingCat.{u}} [IsLocalRing R]
    {Z : Set (Spec R)} (hZ : IsClosed Z) (hne : Z.Nonempty) :
    (IsLocalRing.closedPoint R : Spec R) ∈ Z := by
  by_contra hmem
  have htop := (IsLocalRing.closedPoint_mem_iff (R := R) ⟨Zᶜ, hZ.isOpen_compl⟩).mp hmem
  have hc : (Zᶜ : Set (Spec R)) =
      ((⊤ : TopologicalSpace.Opens (Spec R)) : Set (Spec R)) :=
    congrArg (fun U : TopologicalSpace.Opens (Spec R) => (U : Set (Spec R))) htop
  rw [TopologicalSpace.Opens.coe_top] at hc
  obtain ⟨z, hz⟩ := hne
  exact absurd (hc.symm.subset (Set.mem_univ z)) (not_not.mpr hz)

/-- **For a closed morphism to the spectrum of a local ring, every point specializes into the
fibre over the closed point.** -/
theorem exists_mem_closure_fibre_closedPoint {X : Scheme.{u}} {R : CommRingCat.{u}}
    [IsLocalRing R] (g : X ⟶ Spec R) (hg : IsClosedMap g.base) (x : X) :
    ∃ w ∈ closure ({x} : Set X), g.base w = (IsLocalRing.closedPoint R : Spec R) := by
  have hcl : IsClosed (g.base '' closure ({x} : Set X)) := hg _ isClosed_closure
  have hne : (g.base '' closure ({x} : Set X)).Nonempty :=
    ⟨g.base x, x, subset_closure rfl, rfl⟩
  obtain ⟨w, hw, hwg⟩ := closedPoint_mem_of_isClosed_of_nonempty hcl hne
  exact ⟨w, hw, hwg⟩

end AlgebraicGeometry

namespace Stacks.Groupoids

/-- **An open set containing an invariant subset into which every one of its points specializes
is invariant**, provided the source map is a closed map. -/
theorem isInvariantSet_of_forall_exists_mem_closure {S : AlgebraicGeometry.Scheme.{u}}
    (G : GroupoidScheme S) (hs : IsClosedMap G.source.left.base)
    {V Z : Set G.objects.left} (hV : IsOpen V) (hZV : Z ⊆ V) (hZ : IsInvariantSet G Z)
    (hspec : ∀ v ∈ V, ∃ w ∈ Z, w ∈ closure ({v} : Set G.objects.left)) :
    IsInvariantSet G V := by
  intro r hr
  obtain ⟨w, hwZ, hw⟩ := hspec _ hr
  have hclosed : IsClosed (G.source.left.base '' closure ({r} : Set G.arrows.left)) :=
    hs _ isClosed_closure
  have hmem : w ∈ G.source.left.base '' closure ({r} : Set G.arrows.left) := by
    have hsub : closure ({G.source.left.base r} : Set G.objects.left) ⊆
        G.source.left.base '' closure ({r} : Set G.arrows.left) := by
      refine hclosed.closure_subset_iff.mpr ?_
      exact Set.singleton_subset_iff.mpr ⟨r, subset_closure rfl, rfl⟩
    exact hsub hw
  obtain ⟨ρ, hρ, hρs⟩ := hmem
  have htρ : G.target.left.base ρ ∈ Z := hZ ρ (hρs ▸ hwZ)
  have hclos : G.target.left.base ρ ∈
      closure ({G.target.left.base r} : Set G.objects.left) :=
    specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr hρ).map G.target.left.base.hom.continuous)
  exact AlgebraicGeometry.mem_of_isOpen_of_mem_closure hV hclos (hZV htρ)

end Stacks.Groupoids

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}}

/-- The source map of a groupoid scheme with finite locally free source is a closed map. -/
theorem isClosedMap_source (G : GroupoidScheme S) [IsFiniteLocallyFree G.source.left] :
    IsClosedMap G.source.left.base := by
  have := IsFiniteLocallyFree.isFinite G.source.left
  exact G.source.left.isClosedMap

/-- The target map of a groupoid scheme with finite locally free target is a closed map. -/
theorem isClosedMap_target (G : GroupoidScheme S) [IsFiniteLocallyFree G.target.left] :
    IsClosedMap G.target.left.base := by
  have := IsFiniteLocallyFree.isFinite G.target.left
  exact G.target.left.isClosedMap

/-- **The fibre of the quotient morphism over a point of the invariant spectrum is invariant.** -/
theorem isInvariantSet_fibre_objectsToInvariantSpectrum (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] (p : Spec (.of (invariantRing G))) :
    IsInvariantSet G {u : G.objects.left | (objectsToInvariantSpectrum G).base u = p} := by
  intro r hr
  have h : (objectsToInvariantSpectrum G).base (G.target.left.base r) =
      (objectsToInvariantSpectrum G).base (G.source.left.base r) := by
    change (G.target.left ≫ objectsToInvariantSpectrum G).base r =
      (G.source.left ≫ objectsToInvariantSpectrum G).base r
    rw [source_comp_objectsToInvariantSpectrum]
  exact h.trans hr

end AlgebraicGeometry.GroupoidScheme

end

end
