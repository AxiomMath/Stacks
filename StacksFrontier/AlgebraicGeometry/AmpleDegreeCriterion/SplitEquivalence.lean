module

public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.Vanishing

/-!
# The split vanishing hypothesis of Tag 0B5X is stronger by exactly its first half

`AlgebraicGeometry.isAmple_iff_degree_pos` carries the vanishing paragraph of [Stacks, Tag
0B5X] as one bundled hypothesis `hvan`;
`AlgebraicGeometry.isAmple_iff_degree_pos_of_split` carries it as the two halves
`AlgebraicGeometry.HasAffinePowerOfDegreePos` and
`AlgebraicGeometry.HasIdealSheafH1VanishingOfAffinePower`, rejoined by
`AlgebraicGeometry.forall_exists_isZero_h1_idealSheaf_of_degree_pos`. That rejoin is one
direction of the comparison of the two hypothesis sets; this file supplies the other, and the
two together locate the whole difference in the first half.

The second half is an implication whose antecedent is exactly the first half's conclusion, so
the bundled hypothesis gives it by discarding that antecedent. The first half, by contrast,
asserts the existence of a section of a positive power with nonempty affine nonvanishing locus,
which the bundled hypothesis never mentions — it concludes a vanishing and quantifies over
closed immersions only. So of the two halves exactly one is extra strength.

## Main results

* `AlgebraicGeometry.hasIdealSheafH1VanishingOfAffinePower_of_forall_exists_isZero_h1_idealSheaf`:
  **the bundled hypothesis gives the second half**, the antecedent being discarded.
* `AlgebraicGeometry.forall_exists_isZero_h1_idealSheaf_iff_hasIdealSheafH1Vanishing`:
  **given the first half, the bundled hypothesis and the second half are equivalent.** This is
  the anti-weakening comparison run in both directions, and it says that the split statement's
  additional strength is the first half and nothing else.

## Implementation notes

**No attribute is attached**, for the reason given in
`StacksFrontier/AlgebraicGeometry/AmpleDegreeCriterion/Curve.lean`: neither of the two statements
compared here discharges Tag 0B5X, since both carry hypotheses the tag does not.

**The bundled hypothesis is written out character for character** as it appears in
`AlgebraicGeometry.isAmple_iff_degree_pos`, rather than named by a new definition, so that the
statements below are about that hypothesis and not about a second constant stating the same
thing.

**What this does not establish.** It does not show that the bundled hypothesis fails to imply
the first half; that would need a proper curve carrying an invertible module of positive degree
with no such section, and this development has no invertible module of nonzero degree at all. It
shows that the first half is the only place the implication can fail.

## References

* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Invertible (tensorPower)

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The bundled vanishing hypothesis of [Stacks, Tag 0B5X] gives its second half.** The second
half is an implication whose antecedent is the conclusion of the first half; the bundled
hypothesis concludes the same thing without that antecedent, so it is obtained by discarding
it. In particular no part of the first half is needed here. -/
public theorem hasIdealSheafH1VanishingOfAffinePower_of_forall_exists_isZero_h1_idealSheaf
    [IsProper f] {hdim : topologicalKrullDim X ≤ 1} {L : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hvan : 0 < invertibleCurveDegree k f hdim L →
      ∀ {Z : Scheme.{u}} (i : Z ⟶ X), IsClosedImmersion i → ∃ n : ℕ, 1 ≤ n ∧
        IsZero (((moduleGlobalSections X).rightDerived 1).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
                ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom))).obj
                  ((tensorPower X.toRingedSpace.presheaf
                    (structureSheafRing X.toRingedSpace).property L (n : ℤ))))))) :
    HasIdealSheafH1VanishingOfAffinePower k f hdim L :=
  fun hdeg _ => hvan hdeg

/-- **Given the first half of the vanishing paragraph of [Stacks, Tag 0B5X], its bundled form
and its second half are equivalent.** Forwards this is
`AlgebraicGeometry.hasIdealSheafH1VanishingOfAffinePower_of_forall_exists_isZero_h1_idealSheaf`,
which does not use the first half; backwards it is
`AlgebraicGeometry.forall_exists_isZero_h1_idealSheaf_of_degree_pos`, which does.

So the hypothesis sets of `AlgebraicGeometry.isAmple_iff_degree_pos` and of
`AlgebraicGeometry.isAmple_iff_degree_pos_of_split` differ by the first half alone: anyone
holding the first half may use either statement, and the work the split statement defers beyond
the bundled one is `AlgebraicGeometry.HasAffinePowerOfDegreePos`. -/
public theorem forall_exists_isZero_h1_idealSheaf_iff_hasIdealSheafH1Vanishing [IsProper f]
    {hdim : topologicalKrullDim X ≤ 1} {L : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (h₁ : HasAffinePowerOfDegreePos k f hdim L) :
    (0 < invertibleCurveDegree k f hdim L →
      ∀ {Z : Scheme.{u}} (i : Z ⟶ X), IsClosedImmersion i → ∃ n : ℕ, 1 ≤ n ∧
        IsZero (((moduleGlobalSections X).rightDerived 1).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
                ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom))).obj
                  ((tensorPower X.toRingedSpace.presheaf
                    (structureSheafRing X.toRingedSpace).property L (n : ℤ)))))))
      ↔ HasIdealSheafH1VanishingOfAffinePower k f hdim L where
  mp hvan := hasIdealSheafH1VanishingOfAffinePower_of_forall_exists_isZero_h1_idealSheaf k f hvan
  mpr h₂ := forall_exists_isZero_h1_idealSheaf_of_degree_pos k f h₁ h₂

end AlgebraicGeometry

end
