module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Contracting an exceptional curve of the first kind

Let `X` be a Noetherian scheme and let `E ⊆ X` be an exceptional curve of the first kind: an
effective Cartier divisor isomorphic to `ℙ¹_k` for some field `k`, whose normal sheaf pulls back
to `𝒪_{ℙ¹}(-1)`. The Stacks Project says that *there exists a contraction of `E`* when there is
a proper morphism of schemes `X → X'` such that `E` maps to a closed point `x ∈ X'`, such that
`𝒪_{X', x}` is regular of dimension `2`, and such that `X` is the blowing up of `X'` at `x`.

`AlgebraicGeometry.IsContractionOfExceptionalCurve` transcribes that definition, with `X'`
written `Z` and the curve presented by its quasi-coherent ideal sheaf `D` on `X`: there is a
closed point `z` of the Noetherian scheme `Z` whose local ring is regular of Krull dimension
two, an isomorphism of `X` with the blowup of `Z` in the reduced closed subscheme `{z}` carrying
`b` to the blowup structure morphism, and `D` is the inverse image along `b` of the vanishing
ideal of `{z}`. The regularity of dimension two and the description of `X` as a blowup are two
of the three clauses the source's definition lists; they are not earlier results about
contractions being assumed here as hypotheses. Properness of `b` is not carried as a separate
clause because the blowing up of a Noetherian scheme in a closed point is projective, hence
proper.

Whether every exceptional curve of the first kind admits a contraction is not known: the source
raises it as a question, not a theorem. That is why the notion appears here as a `Prop` asserted
of a given morphism, to be hypothesised wherever it is needed, rather than as a construction
producing `X'` from `X` and `E`. The results the source proves about contractions — the
universal property and uniqueness up to unique isomorphism — are all of this conditional shape.

The predicate records the whole blowup diagram rather than only the isomorphism type of the
source, so that a consumer can recover the centre `z` and the identification of `D` with the
exceptional ideal. Exhibiting the blowup itself as a contraction of its own exceptional ideal
(`AlgebraicGeometry.isContractionOfExceptionalCurve_blowUpToBase`) shows the predicate is not
vacuous and is the form in which it is usually verified.

## Main definitions

* `AlgebraicGeometry.IsContractionOfExceptionalCurve` — the predicate above.

## Main results

* `AlgebraicGeometry.isContractionOfExceptionalCurve_blowUpToBase` — the blowup of a regular
  closed point of dimension two on a Noetherian scheme contracts its exceptional ideal.
* `AlgebraicGeometry.IsContractionOfExceptionalCurve.isNoetherian` and
  `AlgebraicGeometry.IsContractionOfExceptionalCurve.exists_blowUp_iso` — the two pieces of
  data a consumer reads off the predicate.

## References

* [Stacks Project, Tag 0C2I](https://stacks.math.columbia.edu/tag/0C2I), the section
  *Contracting exceptional curves*. The definition transcribed here is the unlabelled paragraph
  of that section, the one raising the question answered by Tag 0C2L; the definition of an
  exceptional curve of the first kind opens the same section.
* [Stacks Project, Tag 0C5J](https://stacks.math.columbia.edu/tag/0C5J), the universal property
  of a contraction, and [Tag 0C5K](https://stacks.math.columbia.edu/tag/0C5K), its uniqueness up
  to unique isomorphism: the labelled statements nearest the definition, and results *about*
  contractions rather than the definition of one.
* [Stacks Project, Tag 0C2L](https://stacks.math.columbia.edu/tag/0C2L), a sufficient criterion
  for a contraction to exist: a morphism `f : X → Y` with `Y` Noetherian, `f` proper, `E` mapped
  to a point of `Y`, and `f` quasi-finite at every point off `E`. Its conclusions include the
  regularity of dimension two and the blowup description, which the definition above postulates,
  so it is not the citation for the predicate below and is listed to keep the two apart.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- `b : X ⟶ Z` is a contraction of the exceptional curve of the first kind cut out by the ideal
sheaf `D`, in the sense of the Stacks Project: `Z` is Noetherian, the curve maps to a closed
point `z ∈ Z` whose local ring is regular of dimension two, and `X` is the blowing up of `Z` at
`z`, with `D` the exceptional ideal. The regularity of dimension two and the identification of
`X` with that blowup are clauses of the source's definition of *there exists a contraction*, not
results about contractions assumed as hypotheses. -/
public def IsContractionOfExceptionalCurve {X Z : Scheme.{u}}
    (D : X.IdealSheafData) (b : X ⟶ Z) : Prop :=
  ∃ (_hZ : IsNoetherian Z) (z : Z) (hz : IsClosed ({z} : Set Z)),
    IsRegularLocalRing (Z.presheaf.stalk z) ∧
      ringKrullDim (Z.presheaf.stalk z) = 2 ∧
      let I := Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds Z)
      D = I.comap b ∧
        ∃ e : X ≅ blowUp I, e.hom ≫ blowUpToBase I = b

/-- The definition of `AlgebraicGeometry.IsContractionOfExceptionalCurve`, unfolded. -/
public theorem isContractionOfExceptionalCurve_iff {X Z : Scheme.{u}}
    (D : X.IdealSheafData) (b : X ⟶ Z) :
    IsContractionOfExceptionalCurve D b ↔
      ∃ (_hZ : IsNoetherian Z) (z : Z) (hz : IsClosed ({z} : Set Z)),
        IsRegularLocalRing (Z.presheaf.stalk z) ∧
          ringKrullDim (Z.presheaf.stalk z) = 2 ∧
          let I := Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds Z)
          D = I.comap b ∧
            ∃ e : X ≅ blowUp I, e.hom ≫ blowUpToBase I = b :=
  Iff.rfl

/-- The target of a contraction is Noetherian. -/
public theorem IsContractionOfExceptionalCurve.isNoetherian {X Z : Scheme.{u}}
    {D : X.IdealSheafData} {b : X ⟶ Z} (hb : IsContractionOfExceptionalCurve D b) :
    IsNoetherian Z :=
  hb.choose

/-- A contraction exhibits its source as the blowup of a regular closed point of dimension two,
compatibly with the structure morphism, and identifies the contracted ideal with the
exceptional ideal of that blowup. -/
public theorem IsContractionOfExceptionalCurve.exists_blowUp_iso {X Z : Scheme.{u}}
    {D : X.IdealSheafData} {b : X ⟶ Z} (hb : IsContractionOfExceptionalCurve D b) :
    ∃ (z : Z) (hz : IsClosed ({z} : Set Z)),
      IsRegularLocalRing (Z.presheaf.stalk z) ∧
        ringKrullDim (Z.presheaf.stalk z) = 2 ∧
        let I := Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds Z)
        D = I.comap b ∧
          ∃ e : X ≅ blowUp I, e.hom ≫ blowUpToBase I = b :=
  hb.choose_spec

/-- The blowup of a Noetherian scheme in a regular closed point of dimension two contracts its
own exceptional ideal. -/
public theorem isContractionOfExceptionalCurve_blowUpToBase {Z : Scheme.{u}} [IsNoetherian Z]
    (z : Z) (hz : IsClosed ({z} : Set Z))
    (hreg : IsRegularLocalRing (Z.presheaf.stalk z))
    (hdim : ringKrullDim (Z.presheaf.stalk z) = 2) :
    IsContractionOfExceptionalCurve
      (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds Z)))
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds Z))) :=
  ⟨inferInstance, z, hz, hreg, hdim, rfl, Iso.refl _, Category.id_comp _⟩

end AlgebraicGeometry

end
