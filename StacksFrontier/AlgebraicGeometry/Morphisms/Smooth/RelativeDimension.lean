module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.ShortExact
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsLocallyFree

/-!
# Smooth morphisms of relative dimension `d`

Stacks Definition 02G2: a morphism of schemes `f : X ⟶ S` is smooth of relative dimension `d` if
`f` is smooth and the sheaf of relative differentials `Ω_{X/S}` is finite locally free of
constant rank `d`. Mathlib's `AlgebraicGeometry.SmoothOfRelativeDimension d f` is instead defined
chart-wise: every point of `X` lies in an affine chart on which the map of coordinate rings is
standard smooth of relative dimension `d`, i.e. has a submersive presentation with `d` more
variables than relations. This file states the Stacks notion and proves the two agree.

## Main definitions

* `AlgebraicGeometry.IsSmoothOfRelativeDimension`: Stacks' notion of a smooth morphism of
  relative dimension `d`.

## Main results

* `AlgebraicGeometry.smoothOfRelativeDimension_iff_smooth_and_isFiniteLocallyFreeOfRank`:
  Mathlib's chart-wise notion is smoothness together with finite local freeness of rank `d` of
  `Ω_{X/S}`.
* `AlgebraicGeometry.smoothOfRelativeDimension_iff_isSmoothOfRelativeDimension`: the two
  notions of a smooth morphism of relative dimension `d` agree.

## Implementation notes

Finite local freeness of rank `d` is the Tag 01C6 class
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`.

On an affine chart on which the map of coordinate rings is standard smooth with a submersive
presentation of dimension `n`, the sheaf `Ω_{X/S}` is free of rank `n`
(`AlgebraicGeometry.exists_restrict_relativeDifferentials_iso_free`). This gives the forward
direction. For the converse, a smooth morphism has standard smooth charts around every point; on
such a chart `Ω_{X/S}` is free of the dimension `n` of the presentation and also finite locally
free of rank `d`, so comparing the ranks of its stalk at a point of the chart over the local ring,
which is nonzero, gives `n = d`.

## References

* [Stacks Project, Tag 02G2](https://stacks.math.columbia.edu/tag/02G2)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **Stacks 02G2.** A morphism of schemes `f : X ⟶ S` is smooth of relative dimension `d` if it
is smooth and its sheaf of relative differentials `Ω_{X/S}` is finite locally free of constant
rank `d`. -/
@[stacks 02G2]
def IsSmoothOfRelativeDimension (d : ℕ) (f : X ⟶ S) : Prop :=
  Smooth f ∧ SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (R := X.ringCatSheaf) (Scheme.Hom.relativeDifferentials f) d

/-- If `f` is smooth of relative dimension `d` in the chart-wise sense, its sheaf of relative
differentials is finite locally free of rank `d`. -/
theorem isFiniteLocallyFreeOfRank_relativeDifferentials (d : ℕ) (f : X ⟶ S)
    [SmoothOfRelativeDimension d f] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) (Scheme.Hom.relativeDifferentials f) d := by
  rw [← Scheme.Modules.isFiniteLocallyFreeOfRank_iff]
  intro x
  obtain ⟨V, hV, U, hU, hxU, hUV, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := d) (f := f) x
  obtain ⟨ρ, _, hcard, ⟨e⟩⟩ := exists_restrict_relativeDifferentials_iso_free f hU hV hUV hstd
  exact ⟨U, hxU, ⟨e ≪≫ (SheafOfModules.freeFunctor (R := (U : Scheme.{u}).ringCatSheaf)).mapIso
    ((Finite.equivFinOfCardEq hcard).trans Equiv.ulift.symm).toIso⟩⟩

/-- A smooth morphism whose sheaf of relative differentials is finite locally free of rank `d` is
smooth of relative dimension `d` in the chart-wise sense. -/
theorem SmoothOfRelativeDimension.of_isFiniteLocallyFreeOfRank (d : ℕ) (f : X ⟶ S) [Smooth f]
    (h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) (Scheme.Hom.relativeDifferentials f) d) :
    SmoothOfRelativeDimension d f := by
  refine ⟨fun x => ?_⟩
  obtain ⟨V, hV, U, hU, hxU, hUV, hstd⟩ := Smooth.exists_isStandardSmooth f x
  refine ⟨V, hV, U, hU, hxU, hUV, ?_⟩
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have hsm : Algebra.IsStandardSmooth Γ(S, V) Γ(X, U) := hstd
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hsm.out
  have hP : (f.appLE V U hUV).hom.IsStandardSmoothOfRelativeDimension P.dimension :=
    P.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨ρ, _, hcard, ⟨e⟩⟩ := exists_restrict_relativeDifferentials_iso_free f hU hV hUV hP
  let Ω := (Scheme.Hom.relativeDifferentials f).restrict U.ι
  have hn : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Ω P.dimension :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e.symm
      (SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv ρ _
        (Finite.equivFinOfCardEq hcard))
  have hd : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Ω d :=
    (Scheme.Modules.isFiniteLocallyFreeOfRank_iff Ω d).1
      (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ d).2 h).restrict U.ι)
  have en := @SheafOfModules.rank_stalk_of_isFiniteLocallyFreeOfRank _ Ω _ hn ⟨x, hxU⟩
  have ed := @SheafOfModules.rank_stalk_of_isFiniteLocallyFreeOfRank _ Ω _ hd ⟨x, hxU⟩
  rw [en] at ed
  have hdim : P.dimension = d := by exact_mod_cast ed
  rw [← hdim]
  exact hP

/-- **Stacks 02G2, Mathlib's notion.** A morphism of schemes is smooth of relative dimension `d`
in the chart-wise sense of `AlgebraicGeometry.SmoothOfRelativeDimension` exactly when it is
smooth and its sheaf of relative differentials is finite locally free of rank `d`. -/
@[stacks 02G2 "Mathlib's chart-wise definition agrees with Stacks'"]
theorem smoothOfRelativeDimension_iff_smooth_and_isFiniteLocallyFreeOfRank (d : ℕ) (f : X ⟶ S) :
    SmoothOfRelativeDimension d f ↔
      Smooth f ∧ SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (R := X.ringCatSheaf) (Scheme.Hom.relativeDifferentials f) d :=
  ⟨fun _ => ⟨SmoothOfRelativeDimension.smooth d f,
      isFiniteLocallyFreeOfRank_relativeDifferentials d f⟩,
    fun ⟨_, h⟩ => SmoothOfRelativeDimension.of_isFiniteLocallyFreeOfRank d f h⟩

/-- Mathlib's chart-wise `AlgebraicGeometry.SmoothOfRelativeDimension` is Stacks' notion of a
smooth morphism of relative dimension `d`. -/
theorem smoothOfRelativeDimension_iff_isSmoothOfRelativeDimension (d : ℕ) (f : X ⟶ S) :
    SmoothOfRelativeDimension d f ↔ IsSmoothOfRelativeDimension d f :=
  smoothOfRelativeDimension_iff_smooth_and_isFiniteLocallyFreeOfRank d f

end AlgebraicGeometry

end
