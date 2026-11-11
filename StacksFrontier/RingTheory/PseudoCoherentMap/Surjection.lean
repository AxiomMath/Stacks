module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.TFAE
public import StacksFrontier.Homology.PseudoCoherent.Relative.Composition
public import StacksFrontier.Homology.PseudoCoherent.Relative.Finite
public import StacksFrontier.RingTheory.PseudoCoherentMap.Absolute
public import StacksFrontier.RingTheory.PseudoCoherentMap.Flat

/-!
# Pseudo-coherence along a surjection of flat finitely presented algebras

Let `R → B → A` be maps of commutative rings with `B → A` surjective and both `B` and `A` flat
and of finite presentation over `R`. For an object of `D(A)`, absolute pseudo-coherence, relative
pseudo-coherence over `R`, relative pseudo-coherence over `B`, and the two corresponding
conditions after restriction of scalars to `B` are all equivalent, and likewise for
`m`-pseudo-coherence (Stacks 0E1T, whose item (3) is printed "relative to `A`", a typo for
"relative to `B`"). The literal reading, relative to `A` itself, also holds.

## Main results

* `PseudoCoherence.pseudoCoherent_tfae_of_surjective_base`: the five conditions of Stacks 0E1T,
  item (3) relative to `B`, are equivalent, and likewise their `m`-pseudo-coherent versions.
* `PseudoCoherence.pseudoCoherent_tfae_of_surjective`: the same with item (3) read literally,
  relative to `A`.

## Implementation notes

The five-way equivalences are recorded with `List.TFAE`, and the assertion without a degree bound
and the one with a degree bound `m` are packaged as a conjunction, in the order the source lists
the five conditions.

## References

* [The Stacks Project, Lemma 15.83.13 (0E1T)](https://stacks.math.columbia.edu/tag/0E1T)
-/

@[expose] public section

open CategoryTheory
open StacksDraft.PseudoCoherence

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

/-- For a surjection `B → A` of flat, finitely presented `R`-algebras, absolute
pseudo-coherence in `D(A)`, relative pseudo-coherence over `R` and over `A` itself, and the two
analogous conditions after restriction of scalars to `B` are equivalent; the same holds for
`m`-pseudo-coherence.

This is item (3) of Stacks 0E1T read literally ("relative to `A`"); the item the source's proof
uses is pseudo-coherence relative to `B`, which is
`PseudoCoherence.pseudoCoherent_tfae_of_surjective_base`. -/
public theorem pseudoCoherent_tfae_of_surjective
    {R : Type u} {B : Type u} {A : Type u}
    [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]
    [Module.Flat R B] [Algebra.FinitePresentation R B]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (hsurj : Function.Surjective (algebraMap B A))
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ) :
    let Kₑ := (ModuleCat.restrictScalars.{u} (algebraMap B A)).mapDerivedCategory.obj K
    List.TFAE [
      IsPseudoCoherent K,
      IsRelativelyPseudoCoherent (R := R) K,
      IsRelativelyPseudoCoherent (R := A) K,
      IsPseudoCoherent Kₑ,
      IsRelativelyPseudoCoherent (R := R) Kₑ] ∧
    List.TFAE [
      IsPseudoCoherentFrom K m,
      IsRelativelyPseudoCoherentFrom (R := R) K m,
      IsRelativelyPseudoCoherentFrom (R := A) K m,
      IsPseudoCoherentFrom Kₑ m,
      IsRelativelyPseudoCoherentFrom (R := R) Kₑ m] := by
  let Kₑ := (ModuleCat.restrictScalars.{u} (algebraMap B A)).mapDerivedCategory.obj K
  have hRA := Algebra.PseudoCoherent.of_flat_of_finitePresentation R A
  have hRB := Algebra.PseudoCoherent.of_flat_of_finitePresentation R B
  have hBB := Algebra.PseudoCoherent.of_flat_of_finitePresentation B B
  have : Module.Finite B A := Module.Finite.of_surjective (Algebra.linearMap B A) hsurj
  have hcomp := relativelyPseudoCoherent_iff_of_comp (R := R) (A := A) (B := A)
    (Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent.mp hRA) K m
  have hres := isRelativelyPseudoCoherentFrom_and_isRelativelyPseudoCoherent_iff_restrictScalars
    (R := R) (A := B) (B := A) K m
  have hcompB := relativelyPseudoCoherent_iff_of_comp (R := R) (A := B) (B := B)
    (Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent.mp hRB) Kₑ m
  have hAbsB := relativelyPseudoCoherent_iff_pseudoCoherent hBB Kₑ m
  constructor
  · tfae_have 1 ↔ 2 := (relativelyPseudoCoherent_iff_pseudoCoherent hRA K m).2.symm
    tfae_have 2 ↔ 3 := hcomp.2.symm
    tfae_have 2 ↔ 5 := hres.2
    tfae_have 4 ↔ 5 := hAbsB.2.symm.trans hcompB.2
    tfae_finish
  · tfae_have 1 ↔ 2 := (relativelyPseudoCoherent_iff_pseudoCoherent hRA K m).1.symm
    tfae_have 2 ↔ 3 := hcomp.1.symm
    tfae_have 2 ↔ 5 := hres.1
    tfae_have 4 ↔ 5 := hAbsB.1.symm.trans hcompB.1
    tfae_finish

/-- **Stacks 0E1T.** Let `R → B → A` be ring maps with `B → A` surjective and `B`, `A` flat and of
finite presentation over `R`, and let `K ∈ D(A)` with restriction `Kₑ ∈ D(B)`. Then `K` is
pseudo-coherent, `K` is pseudo-coherent relative to `R`, `K` is pseudo-coherent relative to `B`,
`Kₑ` is pseudo-coherent, and `Kₑ` is pseudo-coherent relative to `R` are equivalent; the same
holds for `m`-pseudo-coherence. Item (3) is printed "relative to `A`" in the source, a typo for
"relative to `B`" (the proof derives (3) ⇔ (4) from the definition using that `B → A` is
surjective); see `errata.md`. -/
@[stacks 0E1T "item (3) relative to `B`; printed `A`, a typo, see errata.md"]
public theorem pseudoCoherent_tfae_of_surjective_base
    {R : Type u} {B : Type u} {A : Type u}
    [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]
    [Module.Flat R B] [Algebra.FinitePresentation R B]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (hsurj : Function.Surjective (algebraMap B A))
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ) :
    letI : Module.Finite B A := Module.Finite.of_surjective (Algebra.linearMap B A) hsurj
    let Kₑ := (ModuleCat.restrictScalars.{u} (algebraMap B A)).mapDerivedCategory.obj K
    List.TFAE [
      IsPseudoCoherent K,
      IsRelativelyPseudoCoherent (R := R) K,
      IsRelativelyPseudoCoherent (R := B) K,
      IsPseudoCoherent Kₑ,
      IsRelativelyPseudoCoherent (R := R) Kₑ] ∧
    List.TFAE [
      IsPseudoCoherentFrom K m,
      IsRelativelyPseudoCoherentFrom (R := R) K m,
      IsRelativelyPseudoCoherentFrom (R := B) K m,
      IsPseudoCoherentFrom Kₑ m,
      IsRelativelyPseudoCoherentFrom (R := R) Kₑ m] := by
  have : Module.Finite B A := Module.Finite.of_surjective (Algebra.linearMap B A) hsurj
  let Kₑ := (ModuleCat.restrictScalars.{u} (algebraMap B A)).mapDerivedCategory.obj K
  have hRA := Algebra.PseudoCoherent.of_flat_of_finitePresentation R A
  have hRB := Algebra.PseudoCoherent.of_flat_of_finitePresentation R B
  have hBB := Algebra.PseudoCoherent.of_flat_of_finitePresentation B B
  have hcomp := relativelyPseudoCoherent_iff_of_comp (R := R) (A := B) (B := A)
    (Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent.mp hRB) K m
  have hres := isRelativelyPseudoCoherentFrom_and_isRelativelyPseudoCoherent_iff_restrictScalars
    (R := R) (A := B) (B := A) K m
  have hcompB := relativelyPseudoCoherent_iff_of_comp (R := R) (A := B) (B := B)
    (Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent.mp hRB) Kₑ m
  have hAbsB := relativelyPseudoCoherent_iff_pseudoCoherent hBB Kₑ m
  constructor
  · tfae_have 1 ↔ 2 := (relativelyPseudoCoherent_iff_pseudoCoherent hRA K m).2.symm
    tfae_have 2 ↔ 3 := hcomp.2.symm
    tfae_have 2 ↔ 5 := hres.2
    tfae_have 4 ↔ 5 := hAbsB.2.symm.trans hcompB.2
    tfae_finish
  · tfae_have 1 ↔ 2 := (relativelyPseudoCoherent_iff_pseudoCoherent hRA K m).1.symm
    tfae_have 2 ↔ 3 := hcomp.1.symm
    tfae_have 2 ↔ 5 := hres.1
    tfae_have 4 ↔ 5 := hAbsB.1.symm.trans hcompB.1
    tfae_finish

end PseudoCoherence
