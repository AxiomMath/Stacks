module

public import StacksFrontier.Algebra.Homology.SpectralSequence.Convergence
public import StacksFrontier.Algebra.Homology.SpectralSequence.ConvergenceNat
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.AbelianSheafSpectralSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The filtered abutment of the spectral sequence of a first-quadrant filtered complex

`Stacks.Cohomology.Leray.FirstQuadrantAbutment E H` is convergence data for a first-quadrant
`E₂` cohomological spectral sequence: a finite decreasing filtration
`H^n = F^0H^n ⊇ F^1H^n ⊇ ⋯ ⊇ F^{n+1}H^n = 0` whose graded pieces are the terms of the infinity
page.  It is what the five-term exact sequence of [Stacks, Tag 01F2] -- and hence the Leray
spectral sequences of [Stacks, Tag 01ES] and [Stacks, Tag 01F6] -- consumes, and nothing in the
development constructed one.

This file constructs it for the spectral sequence of a filtered complex whose filtration is
*first quadrant*: `F^0K^n = K^n` for every `n` and `F^pK^n = 0` for `p > n`.  That is exactly the
input the total filtration of a first-quadrant double complex supplies, and it is what pins the
two endpoints of the induced filtration of cohomology at `0` and `n + 1`: [Stacks, Tag 012W](2)
gives only *some* `a ≤ b` with `F^aH^n = H^n` and `F^bH^n = 0`, which is not enough for the
`FirstQuadrantAbutment` fields `topIso` and `isZero_bot`.

## Main definitions

* `Stacks.Cohomology.Leray.FirstQuadrantAbutment.ofFilteredObject`: a `FirstQuadrantAbutment`
  assembled out of a family of bundled filtered objects `A n : Fil(𝒜)` with `F^0A^n = ⊤` and
  `F^{n+1}A^n = ⊥`, the objectwise counterpart of
  `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.toFirstQuadrantAbutment`.
* `CochainComplex.Filtered.natE₂Sequence`: the spectral sequence of a filtered complex, read as a
  first-quadrant `E₂` cohomological spectral sequence indexed by `ℕ × ℕ`.
* `CochainComplex.Filtered.firstQuadrantAbutment`: **the abutment datum.**  The spectral sequence
  of a first-quadrant filtered complex abuts to its cohomology.
* `CochainComplex.Filtered.firstQuadrantAbutmentOfFiltered`: the same for the canonical spectral
  sequence `CochainComplex.Filtered.spectralSequenceFunctor`, with the presentation of the pages
  as subquotients discharged.

## Main results

* `CochainComplex.Filtered.isFirstQuadrant_of_firstQuadrantFiltration`: a first-quadrant
  filtration makes the spectral sequence vanish outside the first quadrant.  This is the
  hypothesis `CategoryTheory.SpectralSequence.natRestrict` needs, and it was the missing input
  to the reindexing: the page `E_r^{p,q}` vanishes for `q < 0` because `F^pK^{p+q} = 0` already,
  and for `p < 0` because `Z_r^{p,n}` and `Z_{r-1}^{p+1,n}` are then the *same* subobject, the
  second being part of `D_r^{p,n}`.
* `CochainComplex.Filtered.inducedFiltrationStep_zero_eq_top` and
  `CochainComplex.Filtered.inducedFiltrationStep_succ_eq_bot`: the two endpoints,
  `F^0H^n(K^•) = H^n(K^•)` and `F^{n+1}H^n(K^•) = 0`.
* `CochainComplex.Filtered.isDegreewiseFinite_of_firstQuadrant`: a first-quadrant filtration is
  degreewise finite, so the convergence identification of
  `StacksFrontier/Algebra/Homology/SpectralSequence/Convergence.lean` applies with no further
  hypothesis.

## Implementation notes

**What the abutment datum ends up carrying.**  Besides the presentation `(F, Z, D, E, hE)` of the
spectral sequence by its subquotient pages -- the presentation in which [Stacks, Tag 012M],
[Stacks, Tag 012W] and [Stacks, Tag 0132] all state their conclusions, so a consumer which has
invoked one of those already has it -- the two mathematical hypotheses are

* `htop : ∀ n, IsIso ((K.filtration.ι.app (op 0)).f n)`, i.e. `F^0K^n = K^n`, and
* `hbot : ∀ p n, n < p → IsZero ((K.filtration.obj (op p)).X n)`, i.e. `F^pK^n = 0` for `p > n`.

These are stated in exactly the shape of `CategoryTheory.Filtration.IsDegreewiseFinite`, which
they imply (`isDegreewiseFinite_of_firstQuadrant`): no separate degreewise-finiteness hypothesis
is carried, and `isDegreewiseFinite_totalFiltration₁` /
`isDegreewiseFinite_totalFiltration₂` of
`StacksFrontier/Algebra/Homology/SpectralSequence/DoubleComplex.lean` -- which are `private` -- are
not needed by a consumer that can supply `htop` and `hbot`.

**The infinity page across the reindexing.**
`StacksFrontier/Algebra/Homology/SpectralSequence/Convergence.lean` identifies the infinity page of
a `CohomologicalSpectralSequence C 0`, indexed by `ℤ × ℤ`; `FirstQuadrantAbutment` is about a
`CohomologicalSpectralSequenceNat C 2`.  The passage is
`CategoryTheory.SpectralSequence.natRestrictE₂Shift_pageInfinityIso` of
`StacksFrontier/Algebra/Homology/SpectralSequence/ConvergenceNat.lean`.

**Naturality is not here.**  `gradedIso_naturality`, the one field by which
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo` differs from `FirstQuadrantAbutment`, is
not addressed: the identification of [Stacks, Tag 012V] is produced by an existence statement, so
`CochainComplex.Filtered.pageInfinityIsoGr` is a choice and nothing is known about how two choices
at two objects of a parameter category compare.  What is here is the objectwise datum, which is
what [Stacks, Tag 01F2] and [Stacks, Tag 01ES] consume.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex FilteredComplexSpectralSequence

namespace Stacks.Cohomology.Leray

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **A filtered abutment out of a family of bundled filtered objects.**  Given, in each total
degree `n`, a filtered object `A n` of `𝒜` whose filtration is the whole of `A n` in step `0` and
zero in step `n + 1`, whose underlying object is the asserted abutment `H n`, and whose graded
pieces are the terms of the infinity page, the filtration steps `F^pA^n` and their inclusions
assemble into a `FirstQuadrantAbutment`.

This is the objectwise counterpart of
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.toFirstQuadrantAbutment`, with the
functorial filtration `D ⥤ Fil(𝒜)` replaced by a bare family; as there, the `gradedIso` field is
carried across unchanged, because `(FilteredObject.gr p).obj A` *is* the cokernel of the step
`F^{p+1}A ⟶ F^pA` by definition of `FilteredObject.grMap`. -/
def FirstQuadrantAbutment.ofFilteredObject
    (E : CohomologicalSpectralSequenceNat C 2) (H : ℕ → C) (A : ℕ → FilteredObject C ℤᵒᵖ)
    (abutmentIso : ∀ n : ℕ, (A n).X ≅ H n)
    (htop : ∀ n : ℕ, (A n).filtration.subobject (op (0 : ℤ)) = ⊤)
    (hbot : ∀ n : ℕ, (A n).filtration.subobject (op ((n : ℤ) + 1)) = ⊥)
    (gradedIso : ∀ p q : ℕ, E.pageInfinity (p, q) ≅
      (FilteredObject.gr (p : ℤ)).obj (A (p + q))) :
    FirstQuadrantAbutment E H where
  obj n p := (A n).filtration.obj (op (p : ℤ))
  ι n p := (A n).filtration.step (FilteredObject.succHom (p : ℤ))
  mono_ι _ _ := inferInstance
  topIso n :=
    have : IsIso ((A n).filtration.ι.app (op (0 : ℤ))) :=
      (Filtration.subobject_eq_top_iff _ _).1 (htop n)
    asIso ((A n).filtration.ι.app (op (0 : ℤ))) ≪≫ abutmentIso n
  isZero_bot n := ((Filtration.subobject_eq_bot_iff _ _).1 (hbot n)).some.isZero
  gradedIso p q := gradedIso p q

end Stacks.Cohomology.Leray

namespace CochainComplex.Filtered

open Stacks.Cohomology.Leray

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### A quotient by an equality

`StacksFrontier/Algebra/Homology/SpectralSequence/Convergence.lean` has this lemma too, but
`private`; it is repeated rather than exported because exporting it would force a rebuild of that
file and of everything below it. -/

/-- A quotient of nested subobjects which are in fact equal is zero. -/
lemma isZero_cokernel_ofLE_of_le {X : C} {U V : Subobject X} (h : U ≤ V) (h' : V ≤ U) :
    IsZero (cokernel (Subobject.ofLE U V h)) := by
  have hfac : Subobject.ofLE V U h' ≫ Subobject.ofLE U V h = 𝟙 _ := by
    rw [← cancel_mono V.arrow]; simp
  have : Epi (Subobject.ofLE U V h) := epi_of_epi_fac hfac
  exact isZero_cokernel_of_epi _

/-! ### The two endpoints of the induced filtration of cohomology -/

section Induced

variable (K : Filtered C)

/-- **`F^0H^n(K^•) = H^n(K^•)`** for a filtration which exhausts `K^•` degreewise at the index
`0`: the inclusion `F^0K^• ⟶ K^•` is then an isomorphism of complexes, hence an isomorphism on
cohomology, and the image of an isomorphism is everything. -/
@[ega "0 11.2.4" "special case"]
lemma inducedFiltrationStep_zero_eq_top
    (htop : ∀ n : ℤ, IsIso ((K.filtration.ι.app (op (0 : ℤ))).f n)) (n : ℤ) :
    K.inducedFiltrationStep n 0 = ⊤ := by
  have : IsIso (K.filtration.ι.app (op (0 : ℤ))) := HomologicalComplex.Hom.isIso_of_components _
  have : IsIso (HomologicalComplex.homologyMap (K.filtration.ι.app (op (0 : ℤ))) n) :=
    inferInstance
  rw [← Subobject.isIso_arrow_iff_eq_top]
  have : Epi (K.inducedFiltrationStep n 0).arrow :=
    epi_of_epi_fac (imageSubobject_arrow_comp
      (HomologicalComplex.homologyMap (K.filtration.ι.app (op (0 : ℤ))) n))
  exact isIso_of_mono_of_epi _

/-- **`F^{n+1}H^n(K^•) = 0`** for a filtration which vanishes degreewise above the degree: the
complex `F^{n+1}K^•` is zero in degree `n`, so its `n`-th cohomology vanishes and the image of
`H^n(F^{n+1}K^•) ⟶ H^n(K^•)` is zero. -/
lemma inducedFiltrationStep_succ_eq_bot
    (hbot : ∀ p n : ℤ, n < p → IsZero ((K.filtration.obj (op p)).X n)) (n : ℤ) :
    K.inducedFiltrationStep n (n + 1) = ⊥ := by
  have hz : IsZero ((K.filtration.obj (op (n + 1))).homology n) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _ (hbot (n + 1) n (by omega))
  have h0 : HomologicalComplex.homologyMap (K.filtration.ι.app (op (n + 1))) n = 0 :=
    hz.eq_of_src _ _
  rw [show K.inducedFiltrationStep n (n + 1) = imageSubobject
      (HomologicalComplex.homologyMap (K.filtration.ι.app (op (n + 1))) n) from rfl,
    h0, imageSubobject_zero]

/-- The zeroth step of the induced filtration of `H^n(K^•)`, in the bundled form
`inducedFilteredObject` carries it, is everything. -/
lemma inducedFilteredObject_subobject_zero
    (htop : ∀ n : ℤ, IsIso ((K.filtration.ι.app (op (0 : ℤ))).f n)) (n : ℤ) :
    (K.inducedFilteredObject n).filtration.subobject (op (0 : ℤ)) = ⊤ := by
  rw [inducedFilteredObject_subobject]
  exact inducedFiltrationStep_zero_eq_top K htop n

/-- The `(n+1)`-st step of the induced filtration of `H^n(K^•)`, in the bundled form
`inducedFilteredObject` carries it, is zero. -/
lemma inducedFilteredObject_subobject_succ
    (hbot : ∀ p n : ℤ, n < p → IsZero ((K.filtration.obj (op p)).X n)) (n : ℤ) :
    (K.inducedFilteredObject n).filtration.subobject (op (n + 1)) = ⊥ := by
  rw [inducedFilteredObject_subobject]
  exact inducedFiltrationStep_succ_eq_bot K hbot n

end Induced

/-! ### First-quadrant filtrations -/

section FirstQuadrant

variable (K : Filtered C) (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
  (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
  (Z : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
  (hZ : ∀ r p n : ℤ, Z r p n =
    F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)))
  (D : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
  (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
    (Subobject.«exists» (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
  (E : CohomologicalSpectralSequence C 0)
  (hE : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
    cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)))
  (htop : ∀ n : ℤ, IsIso ((K.filtration.ι.app (op (0 : ℤ))).f n))
  (hbot : ∀ p n : ℤ, n < p → IsZero ((K.filtration.obj (op p)).X n))

include hF htop in
/-- A first-quadrant filtration is everything at every non-positive index. -/
lemma step_eq_top_of_nonpos (p n : ℤ) (hp : p ≤ 0) : F p n = ⊤ := by
  have h0 : F 0 n = ⊤ := by
    rw [hF 0 n]
    exact (Subobject.isIso_iff_mk_eq_top _).mp (htop n)
  refine top_le_iff.mp ?_
  rw [← h0, hF 0 n, hF p n]
  exact filtrationSubobject_antitone K p 0 n hp

include hF hbot in
/-- A first-quadrant filtration of `K^n` vanishes at every index above `n`. -/
lemma step_eq_bot_of_lt (p n : ℤ) (hp : n < p) : F p n = ⊥ := by
  rw [hF p n, Subobject.mk_eq_bot_iff_zero]
  exact (hbot p n hp).eq_of_src _ _

include htop hbot in
/-- **A first-quadrant filtration is degreewise finite.**  It exhausts `K^n` at the index `0` and
vanishes at the index `n + 1`, which is the two halves of
`CategoryTheory.Filtration.IsDegreewiseFinite` read off the hypotheses. -/
lemma isDegreewiseFinite_of_firstQuadrant : K.filtration.IsDegreewiseFinite :=
  fun n => ⟨0, n + 1, htop n, hbot (n + 1) n (by omega)⟩

include hF hZ hD hE htop hbot in
/-- **The spectral sequence of a first-quadrant filtered complex vanishes outside the first
quadrant.**

For `q < 0` the total degree `n = p + q` is below `p`, so the filtration step `F^pK^n` has already
vanished and the numerator `Z_r^{p,q}` of the page is zero.  For `p < 0` the two steps `F^pK^n`
and `F^{p+1}K^n` are both the whole of `K^n`, so `Z_r^{p,q}` and `Z_{r-1}^{p+1,q}` are the *same*
subobject of `K^n`; the latter is a summand of the denominator `D_r^{p,q}`, so the page vanishes.
Neither case needs any boundedness or regularity input. -/
lemma isFirstQuadrant_of_firstQuadrantFiltration :
    SpectralSequence.IsFirstQuadrant (u := fun r => ((r, 1 - r) : ℤ × ℤ)) E := by
  rintro r hr ⟨p, q⟩ hx
  refine IsZero.of_iso (isZero_cokernel_ofLE_of_le _ (le_inf ?_ le_rfl))
    (hE r p q (p + q) hr rfl)
  rcases hx with hp | hq
  · have hp' : p < 0 := hp
    rw [hD r p (p + q)]
    refine le_trans (le_of_eq ?_) le_sup_left
    rw [hZ r p (p + q), hZ (r - 1) (p + 1) (p + q), show p + 1 + (r - 1) = p + r by ring,
      step_eq_top_of_nonpos K F hF htop p (p + q) (by omega),
      step_eq_top_of_nonpos K F hF htop (p + 1) (p + q) (by omega)]
  · have hq' : q < 0 := hq
    rw [hZ r p (p + q), step_eq_bot_of_lt K F hF hbot p (p + q) (by omega), bot_inf_eq]
    exact bot_le

include hF hZ hD hE htop hbot in
/-- **The spectral sequence of a first-quadrant filtered complex, as a first-quadrant `E₂`
cohomological spectral sequence.**  The pages are those of `E`, reindexed from `ℤ × ℤ` to `ℕ × ℕ`
and read from the page `2` on; see
`StacksFrontier/Algebra/Homology/SpectralSequence/ConvergenceNat.lean`. -/
def natE₂Sequence : E₂CohomologicalSpectralSequenceNat C :=
  SpectralSequence.natRestrictE₂Shift E
    (isFirstQuadrant_of_firstQuadrantFiltration K F hF Z hZ D hD E hE htop hbot)

include hF hZ hD hE htop hbot in
/-- **`E_∞^{p,q} ≅ gr^pH^{p+q}(K^•)` for the reindexed spectral sequence.**  The convergence
identification `CochainComplex.Filtered.pageInfinityIsoGr` of
`StacksFrontier/Algebra/Homology/SpectralSequence/Convergence.lean`, transported along the
start-page shift and the first-quadrant reindexing. -/
def natE₂Sequence_pageInfinityIsoGr (p q : ℕ) :
    (natE₂Sequence K F hF Z hZ D hD E hE htop hbot).pageInfinity (p, q) ≅
      (FilteredObject.gr (p : ℤ)).obj (K.inducedFilteredObject ((p + q : ℕ) : ℤ)) :=
  SpectralSequence.natRestrictE₂Shift_pageInfinityIso E
    (isFirstQuadrant_of_firstQuadrantFiltration K F hF Z hZ D hD E hE htop hbot) (p, q) ≪≫
  pageInfinityIsoGr K F hF Z hZ D hD E hE
    (isDegreewiseFinite_of_firstQuadrant K htop hbot) (p : ℤ) (q : ℤ)

include hF hZ hD hE htop hbot in
/-- **The abutment datum: the spectral sequence of a first-quadrant filtered complex abuts to its
cohomology.**  The filtration is the one [Stacks, Tag 012P] induces on `H^n(K^•)`, its zeroth step
is the whole of `H^n(K^•)` and its `(n+1)`-st step is zero because the filtration of `K^•` is
first quadrant, and its graded pieces are the terms of the infinity page by [Stacks, Tag 012W](3).

This is the datum the five-term exact sequence of [Stacks, Tag 01F2] -- `inflation`,
`restriction`, `transgression` and the four exactness statements -- consumes. -/
def firstQuadrantAbutment :
    FirstQuadrantAbutment (natE₂Sequence K F hF Z hZ D hD E hE htop hbot)
      (fun n : ℕ => K.X.homology (n : ℤ)) :=
  FirstQuadrantAbutment.ofFilteredObject _ _ (fun n : ℕ => K.inducedFilteredObject (n : ℤ))
    (fun _ => Iso.refl _)
    (fun n => inducedFilteredObject_subobject_zero K htop (n : ℤ))
    (fun n => inducedFilteredObject_subobject_succ K hbot (n : ℤ))
    (natE₂Sequence_pageInfinityIsoGr K F hF Z hZ D hD E hE htop hbot)

end FirstQuadrant

/-! ### The canonical spectral sequence of a first-quadrant filtered complex -/

section Canonical

variable (K : Filtered C)
  (htop : ∀ n : ℤ, IsIso ((K.filtration.ι.app (op (0 : ℤ))).f n))
  (hbot : ∀ p n : ℤ, n < p → IsZero ((K.filtration.obj (op p)).X n))

include htop hbot in
/-- **The canonical spectral sequence of a filtered complex, as a first-quadrant `E₂`
cohomological spectral sequence.**  `natE₂Sequence` for
`CochainComplex.Filtered.spectralSequenceFunctor`, whose pages are the subquotients
`Z_r^{p,q}/(D_r^{p,q} ⊓ Z_r^{p,q})` on the nose. -/
def natE₂SequenceOfFiltered : E₂CohomologicalSpectralSequenceNat C :=
  natE₂Sequence K (filtrationSubobject K) (fun _ _ => rfl)
    (cycles K.X (filtrationSubobject K)) (fun _ _ _ => rfl)
    (boundaries K.X (filtrationSubobject K)) (fun _ _ _ => rfl)
    (spectralSequenceFunctor.obj K)
    (fun r p' q' n' hr hn' => by subst hn'; exact pageIso K r p' q' hr) htop hbot

include htop hbot in
/-- **The abutment datum for the canonical spectral sequence of a first-quadrant filtered
complex.**  `firstQuadrantAbutment` for `CochainComplex.Filtered.spectralSequenceFunctor`: the
only hypotheses left are that the filtration of `K^•` exhausts it at the index `0` and vanishes
above the degree. -/
def firstQuadrantAbutmentOfFiltered :
    FirstQuadrantAbutment (natE₂SequenceOfFiltered K htop hbot)
      (fun n : ℕ => K.X.homology (n : ℤ)) :=
  firstQuadrantAbutment K (filtrationSubobject K) (fun _ _ => rfl)
    (cycles K.X (filtrationSubobject K)) (fun _ _ _ => rfl)
    (boundaries K.X (filtrationSubobject K)) (fun _ _ _ => rfl)
    (spectralSequenceFunctor.obj K)
    (fun r p' q' n' hr hn' => by subst hn'; exact pageIso K r p' q' hr) htop hbot

end Canonical

end CochainComplex.Filtered

end
