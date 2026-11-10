module

public import StacksFrontier.AlgebraicGeometry.AmpleReducedDimensionOne.Sections
public import StacksFrontier.AlgebraicGeometry.AmpleReducedDimensionOne.AffineLocus
public import StacksFrontier.AlgebraicGeometry.AmpleReducedDimensionOne.Criterion

/-!
# An invertible sheaf with an affine nonvanishing locus containing the overlap

This file assembles the first four steps of the proof of
[Stacks, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX) into one statement, and then states
the reduction with which that proof's last paragraph begins.

On a Noetherian reduced separated scheme of dimension at most one there are an invertible sheaf `M`
and a global section `t` of it such that

* `X_t` is affine,
* `X_t` contains the set `T` of points lying on more than one irreducible component, and
* on each component `C` the preimage of `X_t` is the affine nonvanishing locus of a section of an
  *ample* invertible sheaf on `C`, isomorphic to the pullback of `M` by the comparison
  isomorphism Tag 09NE supplies.

The third item is what the rest of the argument needs: the proof of Tag 09NX finishes by producing,
for a
point `x` outside `T` lying on the single component `Z₁`, a section of a power of the ideal sheaf
of the other components twisted by `M`, and it does so using ampleness *on `Z₁`* — which the
comparison isomorphism transports to the pullback of `M`.  That step is
`StacksDraft.AlgebraicGeometry.F3b.AmpleReducedDimensionOne.Extension`.

## Main results

* `Stacks.AmpleReducedDimensionOne.exists_isAffineOpen_nonvanishingOpen_componentOverlap_subset`:
  the four steps, assembled.
* `Stacks.AmpleReducedDimensionOne.isAmple_of_forall_notMem_componentOverlap`: **the reduction** —
  with such an `M` and `t` in hand, `M` is ample as soon as every point off `T` lies in an affine
  nonvanishing locus of a section of a positive power of `M`.  This is the sentence "to finish the
  proof, it suffices to find for every `x ∈ X`, `x ∉ T` …" of the source, and it is the interface
  the remaining step has to meet.

## Implementation notes

The containment `T ⊆ X_t` is not one of the facts Tag 09NV hands over: that tag gives, on each
component separately, `(componentι C)⁻¹ T ⊆ (Z_C)_{s_C}`.  It becomes a statement about `X_t` only
through the identification of `(Z_C)_{s_C}` with `(componentι C)⁻¹ X_t`, and then because every
point of `T` lies on *some* component.

Quasi-compactness of `X` is not a hypothesis of the reduction: `AlgebraicGeometry.IsNoetherian`
extends `CompactSpace`, so it is already there.

## References

* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Topology.Irreducible
open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AmpleReducedDimensionOne

variable (X : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X]

/-- **The first four steps of the proof of Tag 09NX.**  A Noetherian reduced separated scheme of
dimension at most one carries an invertible sheaf `M` with a global section `t` whose nonvanishing
locus is affine and contains the overlap `T` of the irreducible components, and which restricts on
each component to a section of an ample invertible sheaf with the corresponding nonvanishing
locus, the comparison isomorphism of Tag 09NE being handed over as well.

The components are chosen with ample sheaves by Tag 09ND, the sections by Tag 09NV, the glueing is
Tag 09NE, and the affineness of `X_t` is the reduced case of Tag 09NL. -/
theorem exists_isAffineOpen_nonvanishingOpen_componentOverlap_subset
    [AlgebraicGeometry.IsReduced X] [X.IsSeparated]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (M : X.Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M)
      (t : M.sections),
      IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace) M t) ∧
        componentOverlap X ⊆ (nonvanishingOpen (X := X.toRingedSpace) M t : Set X) ∧
        ∀ C : irreducibleComponents (X : Type u),
          ∃ (L : (componentScheme X C).Modules)
            (_ : AlgebraicGeometry.SheafOfModules.IsInvertible
                  (componentScheme X C).presheaf (componentScheme X C).ringCatSheaf.2 L)
            (s : L.sections)
            (_ : (modulePullback (componentι X C).toLRSHom.toShHom).obj M ≅ L),
            AlgebraicGeometry.Scheme.Modules.IsAmple (componentScheme X C) L ∧
              componentι X C ⁻¹ᵁ nonvanishingOpen (X := X.toRingedSpace) M t
                = nonvanishingOpen (X := (componentScheme X C).toRingedSpace) L s := by
  classical
  obtain ⟨M, hM, t, L, hL, s, haff, hample, hEs, he⟩ := exists_glued_invertible_section X hdim
  have := hM
  have := hL
  have hpre : ∀ C : irreducibleComponents (X : Type u),
      componentι X C ⁻¹ᵁ nonvanishingOpen (X := X.toRingedSpace) M t
        = nonvanishingOpen (X := (componentScheme X C).toRingedSpace) (L C) (s C) := by
    intro C
    obtain ⟨e, hev⟩ := he C
    exact preimage_nonvanishingOpen_eq_of_iso (componentι X C) M t (L C) (s C) e hev
  have htaff : IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace) M t) :=
    isAffineOpen_of_isAffineOpen_preimage_components X _ fun C => (hpre C) ▸ haff C
  refine ⟨M, hM, t, htaff, fun x hx => ?_,
    fun C => ⟨L C, hL C, s C, (he C).choose, hample C, hpre C⟩⟩
  obtain ⟨C, z, hz⟩ := exists_componentι_eq X x
  have hzmem : z ∈ componentι X C ⁻¹ᵁ nonvanishingOpen (X := X.toRingedSpace) M t := by
    rw [hpre C]; exact hEs C (by rw [Set.mem_preimage, hz]; exact hx)
  rw [← hz]; exact hzmem

/-- **The reduction with which the last paragraph of the proof of Tag 09NX begins.**  Given an
invertible sheaf `M` and a global section `t` with `X_t` affine and containing the overlap `T`, the
sheaf `M` is ample as soon as every point *off* `T` lies in an affine nonvanishing locus of a
global section of a positive tensor power of `M`.

The points of `T` are served by `t` itself, at exponent one; the points outside `X_t` are outside
`T` because `T ⊆ X_t`, so the hypothesis covers them. -/
theorem isAmple_of_forall_notMem_componentOverlap (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M]
    (t : M.sections)
    (htaff : IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace) M t))
    (hT : componentOverlap X ⊆ (nonvanishingOpen (X := X.toRingedSpace) M t : Set X))
    (hrest : ∀ x : X, x ∉ componentOverlap X →
      ∃ n : ℕ, 1 ≤ n ∧
        ∃ s : (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property M (n : ℤ)).sections,
          x ∈ nonvanishingOpen (X := X.toRingedSpace)
              (tensorPower X.toRingedSpace.presheaf
                (structureSheafRing X.toRingedSpace).property M (n : ℤ)) s ∧
            IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace)
              (tensorPower X.toRingedSpace.presheaf
                (structureSheafRing X.toRingedSpace).property M (n : ℤ)) s)) :
    AlgebraicGeometry.Scheme.Modules.IsAmple X M :=
  isAmple_preimage_nonvanishingOpen_of_forall_notMem M t htaff
    fun x hx => hrest x fun hmem => hx (hT hmem)

end Stacks.AmpleReducedDimensionOne

end
