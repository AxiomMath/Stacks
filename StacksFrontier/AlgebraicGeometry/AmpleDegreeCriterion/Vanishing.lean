module

public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.Curve

/-!
# The two halves of the vanishing hypothesis of Tag 0B5X

`AlgebraicGeometry.isAmple_iff_degree_pos` carries one hypothesis the forward direction does
not: `hvan`, the third paragraph of the proof of [Stacks, Tag 0B5X], which derives the
cohomological vanishing that [Stacks, Tag 0B5P] consumes from positivity of the degree. That
paragraph is two arguments bolted together, and bundling them is what hid its dependence on
[Stacks, Tag 02O6]. This file splits it, names each half, and rejoins them.

## Main results

* `AlgebraicGeometry.HasAffinePowerOfDegreePos`: **the first half.** Positivity of the degree
  gives a positive power of `𝓛` with a global section whose nonvanishing locus is nonempty and
  affine.
* `AlgebraicGeometry.HasIdealSheafH1VanishingOfAffinePower`: **the second half.** Such a section
  makes `H¹` of every closed subscheme's ideal sheaf vanish after a further twist.
* `AlgebraicGeometry.forall_exists_isZero_h1_idealSheaf_of_degree_pos`: **the rejoin.** The two
  halves compose to exactly the `hvan` of `isAmple_iff_degree_pos`.
* `AlgebraicGeometry.isAmple_iff_degree_pos_of_split`: [Stacks, Tag 0B5X] with `hvan` replaced
  by the two halves.
* `AlgebraicGeometry.hasAffinePowerOfDegreePos_of_not_pos` and
  `AlgebraicGeometry.hasIdealSheafH1VanishingOfAffinePower_of_not_pos`: **the gated control.**
  At every invertible module of non-positive degree both halves are inhabited, so the pair
  forces neither side of the biconditional.

## Where the split falls, and what each half owes

The source's paragraph reads: from `deg 𝓛 > 0` the dimension of `H⁰(X, 𝓛^{⊗ n})` grows
linearly in `n`, so for any finite set of closed points there is an `n` and a nonzero section
of `𝓛^{⊗ n}` vanishing on it; choosing the finite set so that its complement is affine makes
`X_s` affine. *That is the first half.* Then, for a quasi-coherent ideal sheaf `ℐ`,
multiplication by `s` gives maps `ℐ ⊗ 𝓛^{⊗ mn} → ℐ ⊗ 𝓛^{⊗ (m+1)n}` which are injective with
cokernel supported off `X_s`, so the induced maps on `H¹` are surjective ([Stacks, Tag 0B3J]);
`H¹(X, ℐ)` is finite dimensional ([Stacks, Tag 02O6]) and each of its elements dies eventually
([Stacks, Tag 01XR]), so `H¹(X, ℐ ⊗ 𝓛^{⊗ en})` vanishes for some `e > 0`. *That is the second
half.*

So the first half owes the Riemann–Roch growth of `h⁰` — [Stacks, Tag 0B40] together with the
finite-dimensionality of [Stacks, Tag 02O6] — and [Stacks, Tag 01PV] for the affineness of
`X_s`; the second owes [Stacks, Tag 0B3J], [Stacks, Tag 01XR] and [Stacks, Tag 02O6] again.
Neither is proved here.

**What discharges the Tag 02O6 debt is already in the statement of `isAmple_iff_degree_pos`.**
Its `hclosed` and `hunit` are that tag's conclusion at the coherent modules supported in a
proper closed subset and at the structure sheaf, and they are in scope wherever the halves are
consumed, so a proof of either half may take them in exactly the shape the proved forward
direction uses. The halves deliberately do **not** re-carry them: duplicating a hypothesis
shape is how two spellings of one debt get created.

## Why both halves are implications out of positivity of the degree

`hvan` is an implication out of `0 < deg 𝓛` on purpose, and both halves keep that shape.
Assumed unconditionally, the vanishing hypothesis of [Stacks, Tag 0B5P] makes `𝓛` ample
outright: the left side of the biconditional becomes constantly true and what remains to prove
is `0 < deg 𝓛`, which the hypothesis set would then have to force. As implications, nothing is forced —
`hasAffinePowerOfDegreePos_of_not_pos` and
`hasIdealSheafH1VanishingOfAffinePower_of_not_pos` inhabit both halves at every invertible
module of non-positive degree, by `fun h => absurd h hneg`, so the pair is consistent with both
sides of the biconditional being false.

The second half does not mathematically need the positivity premise — its content is an implication out of
the existence of an affine `X_s` — and it carries it anyway, so that the pair can be shown
non-forcing without first having to decide whether a non-positive-degree module can have an
affine nonvanishing locus on some power.

## Implementation notes

**`isAmple_iff_degree_pos_of_split` has a strictly stronger hypothesis set than
`isAmple_iff_degree_pos`,** and is therefore the weaker theorem of the two. The split version
follows from the bundled one through the rejoin; the converse does not, because `hvan` gives no
affine nonvanishing locus and nothing else in the hypothesis set produces one. The obstruction
is a real content gap in the first half, not vacuity of either statement: both are inhabited at
non-positive degree by the gated control above. The bundled form in
`AmpleDegreeCriterion.Curve` therefore remains the primary statement, and this one exists so
that the two owed arguments can be discharged and substituted separately.

**No Stacks attribute is attached here.** The tag for the biconditional is withheld in
`AmpleDegreeCriterion.Curve` for the five hypotheses listed there, and splitting one of them
changes nothing about that.

## References

* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 0B3J](https://stacks.math.columbia.edu/tag/0B3J)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01XR](https://stacks.math.columbia.edu/tag/01XR)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules (nonvanishingLocus nonvanishingOpen)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)
-- (open removed: its only name was the merged moduleGlobalSections)

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The first half of the vanishing paragraph of [Stacks, Tag 0B5X].** If the degree of `𝓛`
is positive then some positive tensor power of `𝓛` has a global section whose nonvanishing
locus is nonempty and affine.

In the source this is Riemann–Roch plus the Hilbert Nullstellensatz: `h⁰(𝓛^{⊗ n})` grows
linearly in `n`, so a nonzero section vanishing at any prescribed finite set of closed points
exists once `n` is large, and choosing the finite set with affine complement makes `X_s`
affine. Its owed inputs are [Stacks, Tag 0B40], [Stacks, Tag 02O6] and [Stacks, Tag 01PV].

The nonemptiness of the nonvanishing locus is the formal reading of "nonzero section" that the
proved forward direction already uses, in the `hpos` hypothesis of
`invertibleCurveDegree_pos_of_isAmple_of_devissage`. -/
public def HasAffinePowerOfDegreePos [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] : Prop :=
  0 < invertibleCurveDegree k f hdim L →
    ∃ n : ℕ, 1 ≤ n ∧ ∃ s : (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
      (∃ x : X, x ∈ nonvanishingLocus (X := X.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s) ∧
        IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s)

/-- **The second half of the vanishing paragraph of [Stacks, Tag 0B5X].** Given a positive power
of `𝓛` with a global section whose nonvanishing locus is nonempty and affine, every closed
subscheme of `X` admits a positive power of `𝓛` killing `H¹` of its ideal sheaf twisted by that
power.

In the source this is the surjectivity chain: multiplication by `s` is injective on a
quasi-coherent ideal sheaf with cokernel supported off `X_s`, so the induced maps on `H¹` are
surjective ([Stacks, Tag 0B3J]); `H¹` of the ideal sheaf is finite dimensional
([Stacks, Tag 02O6]) and each element dies eventually ([Stacks, Tag 01XR]), so some twist has
vanishing `H¹`.

The conclusion is the hypothesis of
`AlgebraicGeometry.Scheme.Modules.isAmple_of_forall_exists_isZero_h1_idealSheaf`, written out
character for character, so that it feeds the criterion of [Stacks, Tag 0B5P] with no
intervening step. -/
public def HasIdealSheafH1VanishingOfAffinePower [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] : Prop :=
  0 < invertibleCurveDegree k f hdim L →
    (∃ n : ℕ, 1 ≤ n ∧ ∃ s : (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
      (∃ x : X, x ∈ nonvanishingLocus (X := X.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s) ∧
        IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s)) →
    ∀ {Z : Scheme.{u}} (i : Z ⟶ X), IsClosedImmersion i → ∃ m : ℕ, 1 ≤ m ∧
      IsZero (((moduleGlobalSections X).rightDerived 1).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
            ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom))).obj
          ((tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (m : ℤ))))))

/-- **The rejoin.** The two halves compose to the `hvan` hypothesis of
`AlgebraicGeometry.isAmple_iff_degree_pos`: positivity of the degree is handed to the first
half, and its output to the second. -/
public theorem forall_exists_isZero_h1_idealSheaf_of_degree_pos [IsProper f]
    {hdim : topologicalKrullDim X ≤ 1} {L : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (h₁ : HasAffinePowerOfDegreePos k f hdim L)
    (h₂ : HasIdealSheafH1VanishingOfAffinePower k f hdim L) :
    0 < invertibleCurveDegree k f hdim L →
      ∀ {Z : Scheme.{u}} (i : Z ⟶ X), IsClosedImmersion i → ∃ n : ℕ, 1 ≤ n ∧
        IsZero (((moduleGlobalSections X).rightDerived 1).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
              ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom))).obj
            ((tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)))))) :=
  fun hdeg => h₂ hdeg (h₁ hdeg)

/-- **The first half holds at non-positive degree.** Half of the gated control: the hypothesis
is an implication out of positivity, so where positivity fails it is inhabited and forces
nothing. -/
public theorem hasAffinePowerOfDegreePos_of_not_pos [IsProper f]
    {hdim : topologicalKrullDim X ≤ 1} {L : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hneg : ¬ 0 < invertibleCurveDegree k f hdim L) : HasAffinePowerOfDegreePos k f hdim L :=
  fun h => absurd h hneg

/-- **The second half holds at non-positive degree.** The other half of the gated control. -/
public theorem hasIdealSheafH1VanishingOfAffinePower_of_not_pos [IsProper f]
    {hdim : topologicalKrullDim X ≤ 1} {L : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hneg : ¬ 0 < invertibleCurveDegree k f hdim L) :
    HasIdealSheafH1VanishingOfAffinePower k f hdim L :=
  fun h => absurd h hneg

/-- **The hypothesis set of `isAmple_iff_degree_pos_of_split` forces neither side of the
biconditional.** At every invertible module whose degree is not positive, the two halves hold
jointly and the right-hand side of the biconditional is false.

This is the non-vacuity guard that a biconditional with a positivity condition on one side
needs. It does not exhibit a module at which the halves hold *and* the degree is positive; that
is precisely the content the two halves defer. -/
public theorem hasAffinePowerOfDegreePos_and_hasIdealSheafH1VanishingOfAffinePower_of_not_pos
    [IsProper f] {hdim : topologicalKrullDim X ≤ 1} {L : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hneg : ¬ 0 < invertibleCurveDegree k f hdim L) :
    HasAffinePowerOfDegreePos k f hdim L ∧
      HasIdealSheafH1VanishingOfAffinePower k f hdim L ∧
      ¬ 0 < invertibleCurveDegree k f hdim L :=
  ⟨hasAffinePowerOfDegreePos_of_not_pos k f hneg,
    hasIdealSheafH1VanishingOfAffinePower_of_not_pos k f hneg, hneg⟩

/-- **[Stacks, Tag 0B5X] with the vanishing hypothesis split.** The statement of
`AlgebraicGeometry.isAmple_iff_degree_pos` with its `hvan` replaced by the two halves of the
source's third paragraph; the other four hypotheses are unchanged, character for character,
and are discharged by the same work.

This is the weaker of the two statements: the bundled `hvan` does not recover the first half,
so the hypothesis set here is strictly stronger. See the implementation notes of this file. -/
public theorem isAmple_iff_degree_pos_of_split [IsCurve k f] [IsProper f]
    (hdev : ∀ P : X.Modules → Prop,
      (∀ T : ShortComplex X.Modules, T.ShortExact → SheafOfModules.IsCoherent T.X₁ →
        SheafOfModules.IsCoherent T.X₂ → SheafOfModules.IsCoherent T.X₃ →
        ((P T.X₁ ∧ P T.X₂ → P T.X₃) ∧ (P T.X₁ ∧ P T.X₃ → P T.X₂) ∧
          (P T.X₂ ∧ P T.X₃ → P T.X₁))) →
      (∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
        _root_.SheafOfModules.supp G ⊆ Z → P G) →
      P (SheafOfModules.unit X.ringCatSheaf) →
      ∀ G : X.Modules, SheafOfModules.IsCoherent G → P G)
    (hclosed : ∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
      _root_.SheafOfModules.supp G ⊆ Z → SheafOfModules.IsCoherent G →
        ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (hunit : ∀ m,
      FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) m))
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hpos : ∀ n : ℕ, 1 ≤ n → ∀ s : (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
        (∃ x : X, x ∈ nonvanishingLocus (X := X.toLocallyRingedSpace.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s) →
        nonvanishingLocus (X := X.toLocallyRingedSpace.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ≠ Set.univ →
        0 < @invertibleCurveDegree k _ X f _ hdim
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ))
          (tensorPower_isInvertible X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)))
    (h₁ : HasAffinePowerOfDegreePos k f hdim L)
    (h₂ : HasIdealSheafH1VanishingOfAffinePower k f hdim L) :
    Scheme.Modules.IsAmple X L ↔ 0 < invertibleCurveDegree k f hdim L :=
  isAmple_iff_degree_pos k f hdev hclosed hunit hdim L hpos
    (forall_exists_isZero_h1_idealSheaf_of_degree_pos k f h₁ h₂)

end AlgebraicGeometry

end
