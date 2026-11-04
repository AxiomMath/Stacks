module

public import Mathlib.Algebra.Category.Grp.Zero
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.ComplexComparison

/-!
# Čech cohomology vanishes above the number of members of the covering family

Let `X` be a topological space, let `U : I → Opens X` be a family of open subsets indexed by a
finite linearly ordered type and let `F` be an abelian presheaf on `X`. Then

`Ȟᵖ(𝒰, F) = 0` for every `p ≥ #I`.

The reason is that the *alternating* Čech complex has no room above degree `#I - 1`: a degree-`p`
alternating cochain is indexed by the tuples `Fin (p + 1) → I`, it vanishes on every tuple with
a repeated index, and once `#I ≤ p` there are no injective tuples at all. The canonical
inclusion of the alternating Čech complex into the usual one is a homotopy equivalence — Tag
01FM, available for Mathlib's Čech complex as
`Stacks.Cech.alternatingCechInclusionToCechComplexFunctor_homotopyEquivalence` — so the two have
the same cohomology and the vanishing transports.

This is the Čech half of the reason that `Hᵠ(ℙⁿ_R, 𝒪(d))` vanishes for `q > n`: projective
`n`-space is covered by the `n + 1` standard opens `D₊(T₀), …, D₊(Tₙ)`, so `#I = n + 1` and the
Čech cohomology of that cover vanishes in every degree `q ≥ n + 1`.

## Main results

* `Stacks.Cech.alternatingSubgroup_eq_bot`: the group of degree-`p` alternating Čech cochains is
  trivial when `#I ≤ p`.
* `Stacks.Cech.isZero_alternatingCechComplex_X`: hence the degree-`p` term of the alternating
  Čech complex is a zero object.
* `Stacks.Cech.isZero_homology_alternatingCechComplex`: hence its cohomology vanishes in degree
  `p`.
* `Stacks.Cech.isZero_homology_cechComplexFunctor`: **the Čech cohomology of the covering family
  vanishes in degree `p`**, for Mathlib's `CategoryTheory.cechComplexFunctor`.

## Implementation notes

The bound is `#I ≤ p` rather than `#I < p` because a degree-`p` cochain is indexed by tuples of
length `p + 1`: the alternating cochains are nonzero only in degrees `p ≤ #I - 1`. For a cover
of `ℙⁿ` by `n + 1` opens this is vanishing in degrees `q > n`, which is the shape Tag 01XT
needs.

No covering hypothesis is used: the statement is about the Čech complex of an indexed family of
opens, which is what `CategoryTheory.cechComplexFunctor` is built from, so a client supplies the
covering equation only where it compares Čech cohomology with sheaf cohomology.

No `@[stacks]` attribute is attached. Tag 01FM is the homotopy equivalence, which is proved
elsewhere and used here; the vanishing itself is an input to Tag 01XT, whose covering set this
file does not complete.

## References

* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v w

namespace Stacks.Cech

open CechCochains

variable {X : TopCat.{u}} {I : Type v} (U : I → Opens X)

/-- **A degree-`p` alternating Čech cochain vanishes once the index type has at most `p`
elements.** Such a cochain is indexed by the tuples `Fin (p + 1) → I` and vanishes on every
tuple with a repeated index, and there is no injective tuple of length `p + 1` in a type with at
most `p` elements. -/
theorem alternatingSubgroup_eq_bot (F : TopCat.Presheaf Ab.{w} X) [Fintype I] {p : ℕ}
    (hp : Fintype.card I ≤ p) : alternatingSubgroup U F p = ⊥ := by
  refine le_antisymm (fun s hs => AddSubgroup.mem_bot.2 (funext fun i => ?_)) bot_le
  refine hs.1 i fun hinj => ?_
  have hcard := Fintype.card_le_of_injective i hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- The degree-`p` term of the alternating Čech complex is a zero object once the index type has
at most `p` elements. -/
theorem isZero_alternatingCechComplex_X (F : TopCat.Presheaf Ab.{w} X) [Fintype I] {p : ℕ}
    (hp : Fintype.card I ≤ p) : IsZero ((alternatingCechComplex U F).X p) := by
  have hbot := (AddSubgroup.eq_bot_iff_forall _).1 (alternatingSubgroup_eq_bot U F hp)
  have : Subsingleton (alternatingSubgroup U F p) :=
    ⟨fun a b => Subtype.ext (by rw [hbot _ a.2, hbot _ b.2])⟩
  rw [alternatingCechComplex_X]
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- The alternating Čech complex has no cohomology in degrees at least the number of members of
the covering family. -/
theorem isZero_homology_alternatingCechComplex (F : TopCat.Presheaf Ab.{w} X) [Fintype I]
    {p : ℕ} (hp : Fintype.card I ≤ p) :
    IsZero ((alternatingCechComplex U F).homology p) :=
  (HomologicalComplex.ExactAt.of_isZero (isZero_alternatingCechComplex_X U F hp)).isZero_homology

/-- **The Čech cohomology of a family of `#I` open subsets vanishes in every degree `p ≥ #I`.**
The canonical inclusion of the alternating Čech complex is a homotopy equivalence (Tag 01FM), so
the two complexes have the same cohomology, and the alternating complex has no term at all in
degree `p`. -/
theorem isZero_homology_cechComplexFunctor [LinearOrder I] [Fintype I]
    (F : TopCat.Presheaf Ab.{max v w} X) {p : ℕ} (hp : Fintype.card I ≤ p) :
    IsZero (((CategoryTheory.cechComplexFunctor U).obj F).homology p) := by
  obtain ⟨e, -⟩ := alternatingCechInclusionToCechComplexFunctor_homotopyEquivalence U F
  exact IsZero.of_iso (isZero_homology_alternatingCechComplex U F hp)
    (e.toHomologyIso p).symm

end Stacks.Cech

end
