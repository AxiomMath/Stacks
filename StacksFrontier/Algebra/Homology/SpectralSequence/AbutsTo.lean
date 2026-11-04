module

public import StacksFrontier.Algebra.Homology.SpectralSequence.Convergence
public import StacksFrontier.Algebra.Homology.SpectralSequence.ConvergenceNat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A spectral sequence abuts to a graded object

[Stacks, Tag 01F2] is the Leray spectral sequence of a morphism of ringed spaces.  Its
convergence clause asks that the spectral sequence *abut* to the hypercohomology of the source,
in the weakest useful sense: there is a finite decreasing filtration of each `H^n` whose graded
pieces are the terms of the infinity page.  Unlike the functorial abutment of
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo`, this is a *proposition* -- the
filtration and the identifications are existentially quantified, and no compatibility between
the identifications at two objects is required.

`CategoryTheory.SpectralSequence.AbutsTo` names that proposition, and
`CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite` proves it for the spectral sequence of a
filtered complex whose filtration is finite in each degree.  Together with
`CategoryTheory.SpectralSequence.AbutsTo.shiftStart`, which moves the statement onto a sequence
read from any later page, this discharges the convergence clause for every spectral sequence the
development builds out of a filtered complex -- in particular for the one [Stacks, Tag 015N]
(`CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp`) produces, which
is delivered in exactly the `(F, Z, D, E, hE)` presentation the hypotheses here ask for.

## Main definitions

* `CategoryTheory.SpectralSequence.AbutsTo`: a cohomological spectral sequence abuts to a graded
  object `H` when it has an infinity page everywhere and some finite decreasing filtration of
  each `H n` has the terms of the infinity page as its graded pieces.

## Main results

* `CategoryTheory.SpectralSequence.AbutsTo.shiftStart`: abutment is unaffected by reading a
  spectral sequence from a later page.
* `CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite`: **the spectral sequence of a
  degreewise finite filtered complex abuts to the cohomology of that complex.**
* `CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite'`: the same for the canonical spectral
  sequence `CochainComplex.Filtered.spectralSequenceFunctor`.

## Implementation notes

Every clause of `AbutsTo` is supplied by
`StacksFrontier/Algebra/Homology/SpectralSequence/Convergence.lean` with no further hypothesis than
degreewise finiteness of the filtration:

* the infinity page exists at every bidegree by
  `CochainComplex.Filtered.hasPageInfinityAt_of_isDegreewiseFinite'`;
* the filtration is the one [Stacks, Tag 012P] induces on cohomology, `inducedFiltrationStep`,
  decreasing by `inducedFiltrationStep_antitone`;
* it reaches `⊤` and `⊥` by the second conclusion of [Stacks, Tag 012W]
  (`CochainComplex.isBounded_and_converges_of_isDegreewiseFinite`), which is stated in exactly
  this shape;
* and the graded pieces are the terms of the infinity page by
  `CochainComplex.Filtered.nonempty_pageInfinityIso_gr'`, whose target
  `(FilteredObject.gr p).obj (K.inducedFilteredObject (p + q))` *is* the cokernel
  `AbutsTo` asks for, by `CochainComplex.Filtered.gr_inducedFilteredObject`.

The existential shape is what makes this provable where the functorial abutment is not.  The
comparison of [Stacks, Tag 012V] is itself produced by an existence statement, so
`CochainComplex.Filtered.pageInfinityIsoGr` is a choice and nothing relates two choices at two
objects of a parameter category; `AbutsTo` never asks.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 012P](https://stacks.math.columbia.edu/tag/012P)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex FilteredComplexSpectralSequence

namespace CategoryTheory.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A cohomological spectral sequence `E`, starting at any page `r₀`, **abuts** to a graded family
`H` if it has an infinity page at every bidegree and, for every `n`, the objects `E_∞^{p,n-p}`
are the successive quotients of a finite decreasing filtration on `H n`.

This is the convergence clause of [Stacks, Tag 01F2].  It is a proposition rather than data: the
filtration and the identifications of its graded pieces with the terms of the infinity page are
existentially quantified.  For the functorial form, carrying the filtration as a functor to
`Fil(𝒜)` and demanding naturality of the identifications, see
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo`. -/
def AbutsTo {r₀ : ℤ} (E : CohomologicalSpectralSequence C r₀) (H : ℤ → C) : Prop :=
  (∀ p q : ℤ, E.HasPageInfinityAt (p, q)) ∧
    ∃ (F : ∀ n : ℤ, ℤ → Subobject (H n)) (hF : ∀ n : ℤ, Antitone (F n)),
      (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ F n a = ⊤ ∧ F n b = ⊥) ∧
      ∀ p q : ℤ, Nonempty
        (E.pageInfinity (p, q) ≅
          cokernel (Subobject.ofLE (F (p + q) (p + 1)) (F (p + q) p)
            (hF (p + q) (by omega))))

/-- **Abutment is unaffected by a start-page shift.**  Reading a spectral sequence from a later
page changes neither the infinity page (`shiftStart_pageInfinityIso`) nor therefore its
identification with the graded pieces of a filtration of the abutment.

This is what lets `CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite`, which is about a
`CohomologicalSpectralSequence C 0`, serve a consumer such as [Stacks, Tag 01F2] whose spectral
sequence is an `E₂CohomologicalSpectralSequence`. -/
theorem AbutsTo.shiftStart {r₀ r₁ : ℤ} {E : CohomologicalSpectralSequence C r₀} {H : ℤ → C}
    (hE : AbutsTo E H) (h : r₀ ≤ r₁) : AbutsTo (E.shiftStart h) H := by
  obtain ⟨hinf, F, hF, hbounds, hgr⟩ := hE
  refine ⟨fun p q => have := hinf p q; inferInstance, F, hF, hbounds, fun p q => ?_⟩
  have : E.HasPageInfinityAt (p, q) := hinf p q
  exact ⟨SpectralSequence.shiftStart_pageInfinityIso E h (p, q) ≪≫ (hgr p q).some⟩

end CategoryTheory.SpectralSequence

namespace CochainComplex.Filtered

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The spectral sequence of a degreewise finite filtered complex abuts to its cohomology.**

The spectral sequence is presented as in [Stacks, Tag 012W]: by an isomorphism `hE` of each page
with the subquotient `Z_r^{p,q}/(D_r^{p,q} ⊓ Z_r^{p,q})` of `K^n`.  This is the presentation in
which [Stacks, Tag 012M], [Stacks, Tag 012W], [Stacks, Tag 0132] and [Stacks, Tag 015N] all state
their conclusions, so a consumer which has invoked one of those already has the data to hand.

The filtration witnessing the abutment is the one [Stacks, Tag 012P] induces on `H^n(K^•)`, and
degreewise finiteness of the filtration of `K^•` is the only hypothesis. -/
@[stacks 012W "(2) and (3) together, in the form `E` abuts to `H^*(K^•)`"]
theorem abutsTo_of_isDegreewiseFinite (K : Filtered C) (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
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
    (hK : K.filtration.IsDegreewiseFinite) :
    SpectralSequence.AbutsTo E (fun n => K.X.homology n) := by
  obtain ⟨-, hbounds, -, -, -⟩ := isBounded_and_converges_of_isDegreewiseFinite K hK F hF Z hZ
    D hD (fun n p => K.inducedFiltrationStep n p) (fun _ _ => rfl) E hE
  refine ⟨hasPageInfinityAt_of_isDegreewiseFinite' K F hF Z hZ D hD E hE hK,
    fun n p => K.inducedFiltrationStep n p, fun n => K.inducedFiltrationStep_antitone n,
    hbounds, fun p q => ?_⟩
  have h := nonempty_pageInfinityIso_gr' K F hF Z hZ D hD E hE hK p q
  rw [gr_inducedFilteredObject K (p + q) p] at h
  exact h

/-- **The canonical spectral sequence of a degreewise finite filtered complex abuts to its
cohomology.**  `abutsTo_of_isDegreewiseFinite` for
`CochainComplex.Filtered.spectralSequenceFunctor`, whose pages are the subquotients
`Z_r^{p,q}/(D_r^{p,q} ⊓ Z_r^{p,q})` on the nose, so that the presentation hypotheses are
discharged and degreewise finiteness is the only one left. -/
@[stacks 012W "(2) and (3), for the canonical spectral sequence of a filtered complex",
  sga "4 Vbis 2.5.2" "partial"]
theorem abutsTo_of_isDegreewiseFinite' (K : Filtered C)
    (hK : K.filtration.IsDegreewiseFinite) :
    SpectralSequence.AbutsTo (spectralSequenceFunctor.obj K) (fun n => K.X.homology n) :=
  abutsTo_of_isDegreewiseFinite K (filtrationSubobject K) (fun _ _ => rfl)
    (cycles K.X (filtrationSubobject K)) (fun _ _ _ => rfl)
    (boundaries K.X (filtrationSubobject K)) (fun _ _ _ => rfl) _
    (fun r p' q' n' hr hn' => by subst hn'; exact pageIso K r p' q' hr) hK

/-- **The canonical spectral sequence of a degreewise finite filtered complex, read from the
second page, abuts to its cohomology.**  This is `abutsTo_of_isDegreewiseFinite'` transported
along `CategoryTheory.SpectralSequence.AbutsTo.shiftStart`, in the shape a consumer whose
spectral sequence is an `E₂CohomologicalSpectralSequence` -- such as [Stacks, Tag 01F2] -- asks
for. -/
theorem abutsTo_shiftStart_of_isDegreewiseFinite (K : Filtered C) {r₁ : ℤ} (h : (0 : ℤ) ≤ r₁)
    (hK : K.filtration.IsDegreewiseFinite) :
    SpectralSequence.AbutsTo ((spectralSequenceFunctor.obj K).shiftStart h)
      (fun n => K.X.homology n) :=
  (abutsTo_of_isDegreewiseFinite' K hK).shiftStart h

end CochainComplex.Filtered

end
