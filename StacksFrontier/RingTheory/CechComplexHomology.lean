module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.RingTheory.CechAcyclicity

/-!
# The Čech complex of a family of elements, as a cochain complex

`StacksFrontier.RingTheory.CechAcyclicity` constructs the terms `CechTerm M g f p` of the Čech
complex of a family `g : Fin n → A` with coefficients in an `A`-module `M`, the differentials
`cechD M g f p`, the identity `cechD_comp_cechD` saying that they compose to zero, and the
exactness statement `cech_exact`. This file packages that data as an actual cochain complex of
`A`-modules and records that its homology vanishes in positive degrees.

## Main definitions

* `cechCochainComplex M g f` is the Čech complex of `g` with coefficients in `M`, twisted by
  `f`, as an object of `CochainComplex (ModuleCat A) ℕ`.

## Main results

* `cechCochainComplex_d` identifies the differential of `cechCochainComplex M g f` in degree
  `p` with `cechD M g f p`.
* `exactAt_cechCochainComplex` and `isZero_homology_cechCochainComplex`: if `g` generates the
  unit ideal of `A`, then `cechCochainComplex M g f` is exact in every positive degree, so its
  homology vanishes there.

## Implementation notes

The complex is built with `CochainComplex.of`, whose differential in degree `p` is only
definitionally `cechD M g f p`; `cechCochainComplex_d` is the corresponding `CochainComplex.of_d`
instance and is what every subsequent proof uses. The obligation that consecutive differentials
compose to zero is discharged by `ModuleCat.hom_ext` applied to `cechD_comp_cechD`: one must not
descend further with `ext`, because `CechTerm` is an abbreviation for a Pi type and `ext` would
then introduce a tuple instead of a cochain.

Exactness is proved degreewise rather than by exhibiting a null homotopy: the short complex in
degrees `p`, `p + 1`, `p + 2` is exact by `ShortComplex.moduleCat_exact_iff_ker_sub_range`
together with `cech_exact`, and `HomologicalComplex.ExactAt.isZero_homology` converts that into
the vanishing of homology.

## References

* [Stacks Project, Tag 01EO](https://stacks.math.columbia.edu/tag/01EO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.RingTheory.CechAcyclicity

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M] {n : ℕ}

/-- The Čech complex of the family `g` with coefficients in `M`, twisted by `f`, as a cochain
complex of `A`-modules: its degree `p` term is `CechTerm M g f p` and its differential is the
alternating sum of restrictions `cechD M g f p`. The untwisted Čech complex is the case
`f = 1`. -/
noncomputable def cechCochainComplex (M : Type v) [AddCommGroup M] [Module A M]
    (g : Fin n → A) (f : A) : CochainComplex (ModuleCat.{max u v} A) ℕ :=
  CochainComplex.of (fun p ↦ ModuleCat.of A (CechTerm M g f p))
    (fun p ↦ ModuleCat.ofHom (cechD M g f p))
    (fun p ↦ ModuleCat.hom_ext (cechD_comp_cechD (M := M) g f p))

/-- The differential of the Čech complex in degree `p` is the Čech differential. -/
theorem cechCochainComplex_d (g : Fin n → A) (f : A) (p : ℕ) :
    (cechCochainComplex M g f).d p (p + 1) = ModuleCat.ofHom (cechD M g f p) :=
  CochainComplex.of_d (fun q ↦ ModuleCat.of A (CechTerm M g f q))
    (fun q ↦ ModuleCat.ofHom (cechD M g f q)) p

/-- **Exactness of the Čech cochain complex in positive degrees.** If the family `g` generates
the unit ideal of `A`, then the Čech complex of `g` with coefficients in `M` is exact in every
positive degree. -/
theorem exactAt_cechCochainComplex (g : Fin n → A) (hg : Ideal.span (Set.range g) = ⊤) (f : A)
    (p : ℕ) : (cechCochainComplex M g f).ExactAt (p + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro s hs
  rw [LinearMap.mem_ker, show (HomologicalComplex.sc' (cechCochainComplex M g f) p (p + 1)
      (p + 2)).g = ModuleCat.ofHom (cechD M g f (p + 1)) from
    cechCochainComplex_d g f (p + 1)] at hs
  obtain ⟨u, hu⟩ := cech_exact g hg f p s hs
  refine ⟨u, ?_⟩
  rw [show (HomologicalComplex.sc' (cechCochainComplex M g f) p (p + 1) (p + 2)).f
      = ModuleCat.ofHom (cechD M g f p) from cechCochainComplex_d g f p]
  exact hu

/-- **Vanishing of Čech cohomology in positive degrees.** If the family `g` generates the unit
ideal of `A`, then the homology of the Čech complex of `g` with coefficients in `M` vanishes in
every positive degree. -/
theorem isZero_homology_cechCochainComplex (g : Fin n → A)
    (hg : Ideal.span (Set.range g) = ⊤) (f : A) (p : ℕ) :
    IsZero ((cechCochainComplex M g f).homology (p + 1)) :=
  (exactAt_cechCochainComplex g hg f p).isZero_homology

end Stacks.RingTheory.CechAcyclicity

end
