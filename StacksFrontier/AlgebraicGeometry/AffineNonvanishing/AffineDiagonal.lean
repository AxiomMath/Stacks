module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# An affine diagonal from a cover by affine nonvanishing loci

If every point of a scheme `X` lies in the nonvanishing locus `X_s` of a global section `s` of
an invertible `𝒪_X`-module, and each such locus is affine, then the diagonal of `X` is affine
([Stacks, Tag 0FXS]).

## Main results

* `AlgebraicGeometry.Scheme.Modules.isAffineHom_diagonal_of_affine_nonvanishingOpen_cover`:
  **Tag 0FXS**.

## Implementation notes

The nonvanishing locus is the open of Tag 01CY and affineness means that the corresponding open
subscheme is affine. The diagonal is the pullback diagonal of the structure morphism to the
terminal scheme, so the criterion of Tag 0BDX applies: it suffices to exhibit one affine open
cover whose nonempty finite intersections are affine. Tag 01PV intersects an affine open with a
single nonvanishing locus, and an induction on the index finset turns that into the finite
intersections, the base case being the affineness of a single member of the cover.

## References

* [Stacks Project, Tag 0FXS](https://stacks.math.columbia.edu/tag/0FXS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules

/-- The intersection of a nonempty finite family of nonvanishing loci of global sections of
invertible modules, each of them affine, is affine. -/
private theorem affine_finset_inf_nonvanishing {X : Scheme.{u}} {ι : Type*}
    (t : Finset ι) (U : ι → X.Opens) (L : ι → X.Modules)
    (hInv : ∀ i, IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property (L i))
    (s : ∀ i, (L i).sections)
    (hShape : ∀ i, U i = @nonvanishingOpen X.toRingedSpace _ (L i) (hInv i) (s i))
    (hAffine : ∀ i, IsAffineOpen (U i)) :
    t.Nonempty → IsAffineOpen (⨅ i ∈ t, U i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
      intro _
      by_cases htn : t.Nonempty
      · rw [Finset.iInf_insert]
        simpa [inf_comm, hShape a] using
          @isAffineOpen_inf_nonvanishingOpen X (L a) (hInv a) (s a) (⨅ i ∈ t, U i) (ih htn)
      · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp htn
        simpa [Finset.iInf_insert, hShape a] using hAffine a

/-- **Stacks Project, Tag 0FXS.** A cover by affine nonvanishing loci of sections of invertible
modules implies that the diagonal is affine. -/
@[stacks 0FXS]
theorem isAffineHom_diagonal_of_affine_nonvanishingOpen_cover (X : Scheme.{u})
    (h : ∀ x : X, ∃ L : X.Modules,
      ∃ _ : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L,
      ∃ s : L.sections,
        x ∈ nonvanishingOpen (X := X.toRingedSpace) L s ∧
          IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace) L s)) :
    IsAffineHom (pullback.diagonal (terminal.from X)) := by
  classical
  choose L hInv s hxs using h
  let U : X → X.Opens := fun x => @nonvanishingOpen X.toRingedSpace _ (L x) (hInv x) (s x)
  have hAffine (x : X) : IsAffineOpen (U x) := (hxs x).2
  have hcover : IsOpenCover U := by
    apply IsOpenCover.mk
    ext x
    simp only [Opens.coe_iSup, Opens.coe_top, Set.mem_iUnion, Set.mem_univ]
    exact ⟨fun _ => trivial, fun _ => ⟨x, (hxs x).1⟩⟩
  let 𝒰 : X.AffineOpenCover := Scheme.AffineOpenCover.ofIsOpenCover U hcover hAffine
  have hRange (x : X) :
      @Scheme.Hom.opensRange (Spec (𝒰.X x)) X (𝒰.f x) (𝒰.map_prop x) = U x := by
    show (hAffine x).fromSpec.opensRange = U x
    exact (hAffine x).opensRange_fromSpec
  have hfinite : ∀ p (i : Fin (p + 1) → 𝒰.I₀),
      IsAffineOpen (⨅ j, @Scheme.Hom.opensRange (Spec (𝒰.X (i j))) X
        (𝒰.f (i j)) (𝒰.map_prop (i j))) := by
    intro p i
    have hv := affine_finset_inf_nonvanishing (X := X) (t := Finset.univ)
      (U := fun j => U (i j)) (L := fun j => L (i j)) (hInv := fun j => hInv (i j))
      (s := fun j => s (i j)) (hShape := fun j => rfl)
      (hAffine := fun j => hAffine (i j)) Finset.univ_nonempty
    have hEq : (⨅ j, @Scheme.Hom.opensRange (Spec (𝒰.X (i j))) X
        (𝒰.f (i j)) (𝒰.map_prop (i j))) = ⨅ j, U (i j) := iInf_congr fun j => hRange (i j)
    rw [hEq]
    simpa using hv
  apply ((isAffineHom_diagonal_tfae X).out 3 1).mp
  exact ⟨𝒰, hfinite⟩

end AlgebraicGeometry.Scheme.Modules

end
