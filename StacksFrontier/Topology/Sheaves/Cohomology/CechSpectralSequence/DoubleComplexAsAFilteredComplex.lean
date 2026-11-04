module

public import StacksFrontier.Algebra.Homology.SpectralSequence.ConvergenceTransport
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Canonical
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.SequenceAndSecondPage

/-!
# The Čech double complex as a first-quadrant filtered complex

The abutment clause of [Stacks, Tag 01ES] is stated for the filtered complex
`CochainComplex.Filtered`, not for a double complex: the convergence identification
`E_∞^{p,q} ≅ gr^pH^{p+q}` of
`StacksFrontier/Algebra/Homology/SpectralSequence/Convergence.lean` and the abutment assembly
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.ofFunctorialFilteredComplex` both
quantify over a filtered complex together with the two first-quadrant hypotheses

* `htop`: the zeroth step of the filtration exhausts the complex degreewise;
* `hbot`: the `p`-th step vanishes in degrees below `p`.

This file supplies both of those for the Čech double complex of [Stacks, Tag 01ES], and the
identification that lets them be used: the second spectral sequence of a double complex *is* the
spectral sequence of its total complex filtered by the second coordinate.

The two hypotheses hold for a reason that is purely degreewise.  The Čech double complex
`K^{i,j}(F) = Č^j(𝒰, I^i(F))`, `Stacks.Cohomology.CechSpectral.cechDouble`, is extended by
zero from `ℕ` in *both* indices, so `K^{i,j} = 0` as soon as `i < 0` or `j < 0`.  For the
filtration `F_{II}^p Tot^n = ⨁_{i + j = n, j ≥ p} K^{i,j}` of the total complex by the second
coordinate this gives:

* at `p = 0` the summands omitted are those with `j < 0`, which vanish, so the step is the whole
  of `Tot^n`;
* at a step `p > n` every surviving summand has `i = n - j ≤ n - p < 0`, so the step is zero.

Both are proved here at the level of a general double complex, from exactly the degreewise
vanishing each one needs -- `j < 0` for the first, `i < 0` for the second -- and then
instantiated at the Čech double complex.

## Main results

* `HomologicalComplex₂.spectralSequence₂_eq_filteredSpectralSequence`: the second spectral
  sequence of a double complex is the spectral sequence of the filtered complex
  `HomologicalComplex₂.totalFiltration₂`.
* `HomologicalComplex₂.spectralSequenceMap₂_eqToHom`: and the same identification on morphisms.
* `HomologicalComplex₂.isIso_totalFiltration₂_ι_f` and
  `HomologicalComplex₂.isZero_totalFiltration₂_obj_X`: the hypotheses `htop` and `hbot` of
  `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.ofFunctorialFilteredComplex` for
  `totalFiltration₂`, from degreewise vanishing of the double complex.
* `Stacks.Cohomology.CechSpectral.isZero_cechDoubleFunctor_X_X`: the Čech double complex of a
  complex of sheaves vanishes outside the first quadrant.
* `Stacks.Cohomology.CechSpectral.isIso_cechDouble_totalFiltration₂_ι_f` and
  `Stacks.Cohomology.CechSpectral.isZero_cechDouble_totalFiltration₂_obj_X`: `htop` and `hbot`
  for the Čech double complex of the chosen injective resolution of a sheaf of modules.

## Implementation notes

`HomologicalComplex₂.totalProjector_eq_id_of_isZero` and
`HomologicalComplex₂.totalProjector_eq_zero_of_isZero` are the whole content of the two
hypotheses: the step `F_{II}^p Tot^n` is presented as the image of
`HomologicalComplex₂.totalProjector`, so the step is everything exactly when that projector is
the identity and is zero exactly when it is zero, and `HomologicalComplex₂.total.hom_ext` reduces
either equation to one summand at a time.  A summand omitted by the projector contributes nothing
to the equation, and a summand kept by it but zero in the double complex contributes nothing
either -- which is why no first-quadrant hypothesis on the *projector* is needed, only on the
double complex.

The `change` in each of the two proofs crosses from the bundled filtration to the image
presentation.  It is checked at default transparency, which is what makes it go through where
`rw` and `simp` would not: `CochainComplex.Filtered` steps are `Filtration.ofDiagram` of
`HomologicalComplex.subcomplexOfSubobjects`, and the unfolding is a chain of `abbrev`s and
structure projections rather than a rewrite.

`spectralSequenceMap₂_eqToHom` is the companion on morphisms, and it is what makes the
*functorial* convergence identification available: a square of `eqToHom`s conjugating
`spectralSequenceMap₂ φ` to `CochainComplex.filteredSpectralSequenceMap` of
`Stacks.Cohomology.CechSpectral.totalFiltrationMap φ`.

`spectralSequence₂_eq_filteredSpectralSequence` is *not* a definitional equality -- the two sides
present the same degreewise family of subobjects of `Tot^n` differently, one as
`HomologicalComplex₂.stepSubobject` and one as `CochainComplex.filtrationSubobject`, and
`Subobject.mk_arrow` relating them is not `rfl`. It is
`HomologicalComplex₂.spectralSequence_congr` applied to `HomologicalComplex₂.stepSubobject_eq`, in
the same way as `HomologicalComplex₂.spectralSequence₂_eq`, which compares `spectralSequence₂` with
the other presentation of the same sequence.

## References

* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
* [Stacks Project, Tag 012M](https://stacks.math.columbia.edu/tag/012M)
* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace HomologicalComplex₂

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasTotal (ComplexShape.up ℤ)]

/-- The step subobjects of the second filtration are the images of the filtration maps. -/
private lemma stepSubobject₂_eq :
    stepSubobject K (fun (_ : ℤ) j => j) = fun p n =>
      Subobject.mk (((K.totalFiltration₂.filtration.ι.app (op p)).f n)) :=
  funext₂ fun p n => stepSubobject_eq K _ (fun _ _ => le_rfl) (fun _ _ => by omega) p n

/-- **The second spectral sequence of a double complex is the spectral sequence of a filtered
complex**, namely of the total complex filtered by the second coordinate.  This is what makes the
convergence identification `E_∞^{p,q} ≅ gr^pH^{p+q}` of
`CochainComplex.Filtered.canonicalPageInfinityIsoGr` available to it. -/
lemma spectralSequence₂_eq_filteredSpectralSequence :
    spectralSequence₂ K = CochainComplex.filteredSpectralSequence K.totalFiltration₂ :=
  spectralSequence_congr
    (stepSubobject₂_eq K)
    (antitone_stepSubobject₂ K)
    (CochainComplex.filtrationSubobject_antitone K.totalFiltration₂)

/-- **The second spectral sequence of a double complex is the spectral sequence of the total
complex filtered by the second coordinate, naturally in the double complex.**

`spectralSequence₂_eq_filteredSpectralSequence` identifies the two at an object; this is the
square identifying `spectralSequenceMap₂ φ` with `CochainComplex.filteredSpectralSequenceMap` of
`Stacks.Cohomology.CechSpectral.totalFiltrationMap φ`.  Both sides are
`FilteredComplexSpectralSequence.spectralSequenceMap` of the *same* morphism `Tot(φ)` -- the
underlying morphism of `totalFiltrationMap` is `Tot(φ)` by
`Stacks.Cohomology.CechSpectral.totalFiltrationMap_hom` -- differing only in the presentation of
the two filtrations, so this is
`FilteredComplexSpectralSequence.spectralSequenceMap_filtration_congr` at `stepSubobject_eq`. -/
theorem spectralSequenceMap₂_eqToHom
    {K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)] (φ : K ⟶ L) :
    spectralSequenceMap₂ φ ≫ eqToHom (spectralSequence₂_eq_filteredSpectralSequence L) =
      eqToHom (spectralSequence₂_eq_filteredSpectralSequence K) ≫
        CochainComplex.filteredSpectralSequenceMap
          (Stacks.Cohomology.CechSpectral.totalFiltrationMap
            (fun (_ : ℤ) j => j) (fun _ _ => le_rfl) (fun _ _ => by omega) φ) :=
  FilteredComplexSpectralSequence.spectralSequenceMap_filtration_congr _
    (stepSubobject₂_eq K) (stepSubobject₂_eq L) _ _ _ _ _ _

/-- **A projector onto the summands with `p ≤ j` is the identity** as soon as the summands it
omits are zero.  The summands it keeps it fixes, and on a summand it omits both sides are maps out
of a zero object. -/
lemma totalProjector_eq_id_of_isZero (p : ℤ)
    (hz : ∀ i j : ℤ, j < p → IsZero ((K.X i).X j)) (n : ℤ) :
    K.totalProjector (fun (_ : ℤ) j => p ≤ j) n = 𝟙 _ := by
  refine total.hom_ext _ fun i j hij => ?_
  rw [ι_totalProjector, Category.comp_id]
  split_ifs with h
  · rfl
  · exact ((hz i j (by omega)).eq_of_src _ _).symm

/-- **A projector onto the summands with `p ≤ j` in total degree `n < p` is zero** as soon as the
double complex vanishes in negative outer degree: a surviving summand has `i = n - j ≤ n - p < 0`,
so it is zero. -/
lemma totalProjector_eq_zero_of_isZero (hz : ∀ i j : ℤ, i < 0 → IsZero ((K.X i).X j)) (p n : ℤ)
    (hnp : n < p) :
    K.totalProjector (fun (_ : ℤ) j => p ≤ j) n = 0 := by
  refine total.hom_ext _ fun i j hij => ?_
  have hij' : i + j = n := hij
  rw [ι_totalProjector, comp_zero]
  split_ifs with h
  · exact (hz i j (by omega)).eq_of_src _ _
  · rfl

/-- **`htop` for the second total filtration.**  If the double complex vanishes in negative inner
degree then the zeroth step `F_{II}^0 Tot^n = ⨁_{i + j = n, j ≥ 0} K^{i,j}` is the whole of
`Tot^n`.

This is the hypothesis of that name in
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.ofFunctorialFilteredComplex` and in
`CochainComplex.Filtered.functorialFirstQuadrantAbutment`. -/
lemma isIso_totalFiltration₂_ι_f (hz : ∀ i j : ℤ, j < 0 → IsZero ((K.X i).X j)) (n : ℤ) :
    IsIso ((K.totalFiltration₂.filtration.ι.app (op (0 : ℤ))).f n) := by
  show IsIso (imageSubobject (K.totalProjector (fun (_ : ℤ) j => (0 : ℤ) ≤ j) n)).arrow
  have : Epi (K.totalProjector (fun (_ : ℤ) j => (0 : ℤ) ≤ j) n) := by
    rw [totalProjector_eq_id_of_isZero K 0 hz n]; infer_instance
  have := epi_of_epi_fac (imageSubobject_arrow_comp
    (K.totalProjector (fun (_ : ℤ) j => (0 : ℤ) ≤ j) n))
  exact isIso_of_mono_of_epi _

/-- **`hbot` for the second total filtration.**  If the double complex vanishes in negative outer
degree then the step `F_{II}^p Tot^n` is zero in every total degree `n < p`.

This is the hypothesis of that name in
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.ofFunctorialFilteredComplex` and in
`CochainComplex.Filtered.functorialFirstQuadrantAbutment`. -/
lemma isZero_totalFiltration₂_obj_X (hz : ∀ i j : ℤ, i < 0 → IsZero ((K.X i).X j)) (p n : ℤ)
    (hnp : n < p) :
    IsZero ((K.totalFiltration₂.filtration.obj (op p)).X n) := by
  show IsZero ((imageSubobject (K.totalProjector (fun (_ : ℤ) j => p ≤ j) n) : C))
  rw [totalProjector_eq_zero_of_isZero K hz p n hnp, imageSubobject_zero]
  exact IsZero.of_iso (isZero_zero C) Subobject.botCoeIsoZero

end HomologicalComplex₂

namespace Stacks.Cohomology.CechSpectral

universe u r v w

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{r})
  (𝒰 : CechExactFunctor.CechOpenCover.{u, w} (TopCat.of X))

/-- **The Čech double complex of a complex of sheaves vanishes outside the first quadrant.**
Both indices are extended by zero from `ℕ`, the outer one by `cechDoubleOuterFunctor` and the
inner one by `cechDoubleFunctor`, so each negative index kills the term on its own. -/
lemma isZero_cechDoubleFunctor_X_X (Y : CochainComplex (SheafOfModules.{max u r v w} O) ℕ)
    (i j : ℤ) (h : i < 0 ∨ j < 0) :
    IsZero ((((cechDoubleFunctor.{u, r, v, w} O 𝒰).obj Y).X i).X j) := by
  rcases h with hi | hj
  · refine Functor.map_isZero
      (HomologicalComplex.eval (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))
        (ComplexShape.up ℤ) j)
      (Functor.map_isZero (ComplexShape.embeddingUpNat.extendFunctor
        (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))) ?_)
    exact HomologicalComplex.isZero_extend_X
      ((cechDoubleNatFunctor.{u, r, v, w} O 𝒰).obj Y) ComplexShape.embeddingUpNat i
      fun k => by change ((k : ℕ) : ℤ) ≠ i; omega
  · exact HomologicalComplex.isZero_extend_X
      (((cechDoubleOuterFunctor.{u, r, v, w} O 𝒰).obj Y).X i) ComplexShape.embeddingUpNat j
      fun k => by change ((k : ℕ) : ℤ) ≠ j; omega

section Resolution

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u r v w}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u r v w}]
  [EnoughInjectives (SheafOfModules.{max u r v w} O)]

/-- **`htop` for the Čech double complex of a sheaf of modules**: the zeroth step of the
filtration of `Tot(K^{•,•}(F))` by the Čech degree is the whole total complex. -/
lemma isIso_cechDouble_totalFiltration₂_ι_f (F : SheafOfModules.{max u r v w} O) (n : ℤ) :
    IsIso (((cechDouble.{u, r, v, w} O 𝒰 F).totalFiltration₂.filtration.ι.app
      (op (0 : ℤ))).f n) :=
  HomologicalComplex₂.isIso_totalFiltration₂_ι_f _
    (fun i j hj => isZero_cechDoubleFunctor_X_X.{u, r, v, w} O 𝒰 _ i j (Or.inr hj)) n

/-- **`hbot` for the Čech double complex of a sheaf of modules**: the `p`-th step of the
filtration of `Tot(K^{•,•}(F))` by the Čech degree vanishes in total degrees below `p`. -/
lemma isZero_cechDouble_totalFiltration₂_obj_X (F : SheafOfModules.{max u r v w} O) (p n : ℤ)
    (hnp : n < p) :
    IsZero (((cechDouble.{u, r, v, w} O 𝒰 F).totalFiltration₂.filtration.obj (op p)).X n) :=
  HomologicalComplex₂.isZero_totalFiltration₂_obj_X _
    (fun i j hi => isZero_cechDoubleFunctor_X_X.{u, r, v, w} O 𝒰 _ i j (Or.inl hi)) p n hnp

end Resolution

end Stacks.Cohomology.CechSpectral

end
