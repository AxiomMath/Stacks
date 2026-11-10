module

public import StacksCore.Algebra.Homology.SpectralSequence.PageInfinity
public import StacksCore.CategoryTheory.Filtration.GradedPieces
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.AbelianSheafSpectralSequence

/-!
# Functorial filtered abutments of first-quadrant spectral sequences

[Stacks, Tag 01F6] is the relative Leray spectral sequence: for morphisms of ringed spaces
`f : X ⟶ Y` and `g : Y ⟶ Z` there is a spectral sequence with `E_2^{p,q} = R^p g_*(R^q f_* ℱ)`
converging to `R^{p+q}(g ∘ f)_* ℱ`, *functorially in `ℱ`*.  Functoriality of the convergence
is what distinguishes the tag from [Stacks, Tag 01F2], and it needs a functorial notion of
filtered abutment.  This file supplies that notion.

`FunctorialFirstQuadrantAbutsTo E H`, for a spectral sequence `E` and an abutment `H` both
*functorial* on a parameter category `D`, is a functorial finite decreasing filtration
`H^n = F^0H^n ⊇ F^1H^n ⊇ ⋯ ⊇ F^{n+1}H^n = 0` whose graded pieces are the terms of the infinity
page, together with the condition that the identification of graded pieces with infinity-page
terms is compatible with the maps a morphism of `D` induces on both.  That last field,
`gradedIso_naturality`, is the whole difference from the non-functorial
`Stacks.Cohomology.Leray.FirstQuadrantAbutment`: without it the graded identifications at
different objects of `D` are unrelated and nothing about the abutment is functorial.

## Main definitions

* `FunctorialFirstQuadrantAbutsTo`: a functorial finite filtered abutment of a functorial
  first-quadrant cohomological spectral sequence, presented from any page; the `E₂` case is the
  one [Stacks, Tag 01F6] needs, and the `E₁` case is the one [Stacks, Tag 09W6] needs.

## Main results

* `FunctorialFirstQuadrantAbutsTo.ofIsoAbutment`: a functorial abutment transports along an
  isomorphism of the abutment, `H` being mentioned in the single field `abutmentIso`.
* `FunctorialFirstQuadrantAbutsTo.toFirstQuadrantAbutment`: at each object of the parameter
  category a functorial abutment restricts to a
  `Stacks.Cohomology.Leray.FirstQuadrantAbutment`, so the five-term exact sequence of
  [Stacks, Tag 01F2], proved for that structure, applies to it.

## Implementation notes

**Tag 01F6 itself is not proved here and nothing in this file carries the tag.**  What is
missing is the construction, which needs two things recorded as unavailable in the
implementation notes of `Stacks.Cohomology.LerayModules`: a *functorial*
Cartan-Eilenberg resolution, since [Stacks, Tag 015N]
(`CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp` of
`StacksFrontier/Algebra/Homology/SpectralSequence/Grothendieck.lean`) is an existence statement
producing the
spectral sequence one object at a time — so no functorial data can be extracted from it at
all — and a construction of the abutment datum `E_∞^{p,q} ≅ gr^p H^{p+q}`, which no spectral
sequence in the development currently satisfies even non-functorially.  So this file is the
*statement* vocabulary of the tag, with the obligation left open.

The filtration is carried by `CategoryTheory.FilteredObject A ℤᵒᵖ`, Mathlib's bundled filtered
object, rather than by the hand-rolled family of steps and inclusions of
`Stacks.Cohomology.Leray.FirstQuadrantAbutment`.  That is what makes the functorial form
expressible: a functor `D ⥤ FilteredObject A ℤᵒᵖ` carries the filtration, its steps and their
inclusions functorially in one object, whereas a family `D → ℕ → ℕ → A` would need its own
naturality field for each of them.  Stacks' decreasing `ℤ`-filtration is the index category
`ℤᵒᵖ`, as in `StacksCore/CategoryTheory/Filtration/Basic.lean`, and the graded pieces are
`CategoryTheory.FilteredObject.gr`.

`toFirstQuadrantAbutment` needs no `HasPageInfinityAt` hypothesis: a first-quadrant
cohomological spectral sequence has an infinity page at every bidegree, which is the instance
`CategoryTheory.SpectralSequence.CohomologicalSpectralSequenceNat.instHasPageInfinityAt` of
`StacksCore/Algebra/Homology/SpectralSequence/PageInfinity.lean`.  Its `gradedIso` field is
literally this structure's: `(FilteredObject.gr p).obj A` *is* the cokernel of the step
`F^{p+1}A ⟶ F^pA`, by definition of `FilteredObject.grMap`.

## References

* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 0121](https://stacks.math.columbia.edu/tag/0121)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.Leray

variable {D A : Type*} [Category* D] [Category* A] [Abelian A]

/-- A **functorial** finite filtered abutment of a first-quadrant cohomological spectral
sequence, presented from any page `r₀` (an `E₂` sequence when `r₀ = 2`): for a spectral
sequence `E` and an abutment `H`, both functorial on a parameter category `D`, a functorial
finite decreasing filtration of each `H^n` which is the whole of `H^n` in step `0` and zero in
step `n + 1`, whose graded pieces are the terms of the infinity page of `E`, and whose graded
identifications are compatible with the maps induced by a morphism of `D` on the infinity page
and on the graded pieces.

This is the shape in which a first-quadrant spectral sequence abuts to `H` functorially; the
non-functorial shape is `FirstQuadrantAbutment`. -/
structure FunctorialFirstQuadrantAbutsTo {r₀ : ℤ}
    (E : D ⥤ CohomologicalSpectralSequenceNat A r₀) (H : ℕ → D ⥤ A) where
  /-- The functorial filtration of the abutment in each total degree. -/
  filtration (n : ℕ) : D ⥤ FilteredObject A ℤᵒᵖ
  /-- The underlying object of the filtration is naturally the asserted abutment. -/
  abutmentIso (n : ℕ) : filtration n ⋙ FilteredObject.forget ≅ H n
  /-- The filtration of every abutment object is finite. -/
  isFinite (K : D) (n : ℕ) : Filtration.IsFinite ((filtration n).obj K).filtration
  /-- In total degree `n`, the zeroth filtration step is the whole abutment. -/
  isTop (K : D) (n : ℕ) :
    ((filtration n).obj K).filtration.subobject (op (0 : ℤ)) = ⊤
  /-- In total degree `n`, the `(n + 1)`-st filtration step is zero. -/
  isBot (K : D) (n : ℕ) :
    ((filtration n).obj K).filtration.subobject (op ((n : ℤ) + 1)) = ⊥
  /-- The infinity term is the corresponding associated graded object. -/
  gradedIso (K : D) (p q : ℕ) :
    (E.obj K).pageInfinity (p, q) ≅
      (FilteredObject.gr (p : ℤ)).obj ((filtration (p + q)).obj K)
  /-- The graded identifications are compatible with the maps a morphism of `D` induces on the
  infinity page and on the graded pieces.  This is the field that makes the abutment
  functorial. -/
  gradedIso_naturality {K L : D} (φ : K ⟶ L) (p q : ℕ) :
    SpectralSequence.Hom.mapPageInfinity (E.map φ) (p, q) ≫
        (gradedIso L p q).hom =
      (gradedIso K p q).hom ≫
        (FilteredObject.gr (p : ℤ)).map ((filtration (p + q)).map φ)

namespace FunctorialFirstQuadrantAbutsTo

section E₂

variable {E : D ⥤ E₂CohomologicalSpectralSequenceNat A} {H : ℕ → D ⥤ A}

/-- **A functorial filtered abutment restricts to an abutment at each object** of the parameter
category.  The filtration steps are the steps of the filtered object `F^•H^n(K)` at the
non-negative integers, the top step is the whole abutment because the zeroth step is, the
bottom step vanishes because the `(n + 1)`-st step does, and the graded identification is the
one carried by the functorial abutment -- `FilteredObject.gr p` is the cokernel of the step
`F^{p+1} ⟶ F^p` by definition.

Consequently the five-term exact sequence of `FirstQuadrantAbutment` -- `inflation`,
`restriction`, `transgression` with `mono_inflation`, `exact_inflation_restriction`,
`exact_restriction_d` and `exact_d_transgression` -- applies to every functorial abutment,
objectwise. -/
def toFirstQuadrantAbutment (h : FunctorialFirstQuadrantAbutsTo E H) (K : D) :
    FirstQuadrantAbutment (E.obj K) (fun n => (H n).obj K) where
  obj n p := ((h.filtration n).obj K).filtration.obj (op (p : ℤ))
  ι n p := ((h.filtration n).obj K).filtration.step (FilteredObject.succHom (p : ℤ))
  mono_ι _ _ := inferInstance
  topIso n :=
    have : IsIso (((h.filtration n).obj K).filtration.ι.app (op (0 : ℤ))) :=
      (Filtration.subobject_eq_top_iff _ _).1 (h.isTop K n)
    asIso (((h.filtration n).obj K).filtration.ι.app (op (0 : ℤ))) ≪≫
      (h.abutmentIso n).app K
  isZero_bot n := ((Filtration.subobject_eq_bot_iff _ _).1 (h.isBot K n)).some.isZero
  gradedIso p q := h.gradedIso K p q

end E₂

variable {r₀ : ℤ} {E : D ⥤ CohomologicalSpectralSequenceNat A r₀} {H : ℕ → D ⥤ A}

/-- **A functorial filtered abutment transports along an isomorphism of the abutment.**  The
structure mentions `H` in the single field `abutmentIso`, so replacing `H` by an isomorphic
functorial family changes nothing else: the filtration, its finiteness, its top and bottom steps,
the graded identification and its naturality are all independent of `H`.

This is what lets the abutment be built against the cohomology that the filtration is literally
the filtration *of*, and the asserted abutment -- for [Stacks, Tag 01ES], the derived evaluation
functor -- be substituted at the end. -/
abbrev ofIsoAbutment (h : FunctorialFirstQuadrantAbutsTo E H) {H' : ℕ → D ⥤ A}
    (e : ∀ n, H n ≅ H' n) : FunctorialFirstQuadrantAbutsTo E H' :=
  { h with abutmentIso n := h.abutmentIso n ≪≫ e n }

/-- The filtration of a transported abutment is the original one. -/
@[simp]
lemma ofIsoAbutment_filtration (h : FunctorialFirstQuadrantAbutsTo E H) {H' : ℕ → D ⥤ A}
    (e : ∀ n, H n ≅ H' n) (n : ℕ) : (h.ofIsoAbutment e).filtration n = h.filtration n :=
  rfl

end FunctorialFirstQuadrantAbutsTo

end Stacks.Cohomology.Leray

end
