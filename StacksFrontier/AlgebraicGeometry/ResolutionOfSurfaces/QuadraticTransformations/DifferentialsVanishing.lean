module

public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.Basic
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ConormalComparison

/-!
# The relative differentials vanish along the exceptional curve

This file carries out the second half of the step of [Stacks, Tag 0C5R] (Resolution of Surfaces,
Lemma 54.17.1) whose first half is in `ConormalComparison.lean`: once the conormal comparison map
on the exceptional curve is an isomorphism, [Stacks, Tag 067L] shows that `Ω_{X'/Y'}` restricted to
the exceptional curve vanishes.

[Stacks, Tag 067L] says that for immersions `i : E ⟶ X'` and `j : E ⟶ Y'` in a commutative
triangle `i ≫ f' = j` there is a canonical exact sequence

`𝒞_{E/Y'} ⟶ 𝒞_{E/X'} ⟶ i^* Ω_{X'/Y'} ⟶ 0`

whose first arrow is the comparison map of [Stacks, Tag 01R4]. Only two of its clauses are needed
here: that the composite of the two arrows is zero, and that the second arrow is an epimorphism.
Granted those, an epimorphic first arrow — in particular an isomorphic one — forces the second
arrow to be zero, and a zero epimorphism forces its target to be a zero object.

The theorems take these two clauses as the hypothesis
`Stacks.ResolutionOfSurfaces.ConormalSequenceSecondArrow`, which is quantified over every triangle
of immersions and is proved as `Stacks.ResolutionOfSurfaces.conormalSequenceSecondArrow` in
`ConormalSequenceSecondArrow.lean`. The second arrow is quantified existentially there, which only
weakens the hypothesis: the library's `Stacks.ConormalSequenceRight.conormalDifferential` is stated
on `Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf`, a model of the conormal sheaf
isomorphic but not definitionally equal to the `Stacks.Conormal.conormalSheaf` on which the first
arrow is stated.

## Main definitions

* `Stacks.ResolutionOfSurfaces.ConormalSequenceSecondArrow` — two clauses of
  [Stacks, Tag 067L], as one proposition quantified over every triangle of immersions.

## Main results

* `Stacks.ResolutionOfSurfaces.isZero_pullback_relativeDifferentials_of_epi` — granted
  [Stacks, Tag 067L], an epimorphic first arrow makes `i^* Ω_{X'/Y'}` a zero object.
* `Stacks.ResolutionOfSurfaces.isZero_pullback_relativeDifferentials_of_ne_zero` — the same with
  the hypothesis in the form the source's argument supplies it: the first arrow is nonzero and
  both conormal modules have degree `d` on a presentation `ε : 𝐏¹_k ≅ E` of the exceptional
  curve as the projective line.

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 067L](https://stacks.math.columbia.edu/tag/067L)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open RingedSpaceModuleAdjunction (toShHomIso)

universe u

namespace Stacks.ResolutionOfSurfaces

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The carried clauses of Tag 067L -/

/-- **The second arrow of [Stacks, Tag 067L], with two clauses of that tag.** For every triangle
of immersions `i : Z ⟶ X`, `j : Z ⟶ Y` with `i ≫ p = j` there is a morphism

`ψ : 𝒞_{Z/X} ⟶ i^* Ω_{X/Y}`

which is an epimorphism and which the first arrow `𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` of
`Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap` composes to zero with.

In [Stacks, Tag 067L] this `ψ` is the conormal differential of [Stacks, Tag 01UZ] and the two
clauses are *exactness at the right term* and *the sequence is a complex*. -/
public def ConormalSequenceSecondArrow : Prop :=
  ∀ {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) (p : X ⟶ Y) [IsImmersion i] [IsImmersion j]
    (h : i ≫ p = j),
    ∃ ψ : Stacks.Conormal.conormalSheaf i ⟶
        (modulePullback i.toLRSHom.toShHom).obj (Scheme.Hom.relativeDifferentials p),
      Epi ψ ∧ Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap i j p h ≫ ψ = 0

/-! ### The vanishing -/

/-- Granted the second arrow of [Stacks, Tag 067L] with its two clauses, if the first arrow
`𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` of that tag is an epimorphism then `i^* Ω_{X/Y}` is a zero object. -/
public theorem isZero_pullback_relativeDifferentials_of_epi
    (hsec : ConormalSequenceSecondArrow.{u}) {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    (p : X ⟶ Y) [IsImmersion i] [IsImmersion j] (h : i ≫ p = j)
    (hepi : Epi (Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap i j p h)) :
    IsZero ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)) := by
  obtain ⟨ψ, hψepi, hψ0⟩ := hsec i j p h
  have hzero : ψ = 0 := by
    refine (cancel_epi
      (Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap i j p h)).mp ?_
    rw [hψ0, comp_zero]
  rw [hzero] at hψepi
  have hgoal : IsZero ((modulePullback i.toLRSHom.toShHom).obj
      (Scheme.Hom.relativeDifferentials p)) :=
    IsZero.of_epi_zero (Stacks.Conormal.conormalSheaf i) _
  exact hgoal

/-- Granted the second arrow of [Stacks, Tag 067L] with its two clauses, `i^* Ω_{X'/Y'}` is a zero
object as soon as the comparison map `𝒞_{E/Y'} ⟶ 𝒞_{E/X'}` of [Stacks, Tag 01R4] is nonzero and
both conormal modules have degree `d` on a presentation `ε : 𝐏¹_k ≅ E` of the exceptional curve as
the projective line, recorded as isomorphisms of their pullbacks along `ε` with the `d`-th twist
`𝒪(d)`. The hypothesis `hk` is the equality clause of part (5) of [Stacks, Tag 0B40] at the
projective line. -/
public theorem isZero_pullback_relativeDifferentials_of_ne_zero (k : Type u) [Field k]
    (hk : NonzeroTwistEndoIsIso k) (hsec : ConormalSequenceSecondArrow.{u}) (d : ℤ)
    {E X' Y' : Scheme.{u}} (i : E ⟶ X') (j : E ⟶ Y') (f' : X' ⟶ Y')
    [IsImmersion i] [IsImmersion j] (h : i ≫ f' = j) (ε : projectiveLineProj k ≅ E)
    (α : (modulePullback (toShHomIso ε).hom).obj (Stacks.Conormal.conormalSheaf j) ≅
      projectiveLineTwist k d)
    (β : (modulePullback (toShHomIso ε).hom).obj (Stacks.Conormal.conormalSheaf i) ≅
      projectiveLineTwist k d)
    (hne : Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap i j f' h ≠ 0) :
    IsZero ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials f')) :=
  have : IsIso (Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap i j f' h) :=
    isIso_conormalTransitivityMap_of_ne_zero k hk d i j f' h ε α β hne
  isZero_pullback_relativeDifferentials_of_epi hsec i j f' h inferInstance

end Stacks.ResolutionOfSurfaces

end
