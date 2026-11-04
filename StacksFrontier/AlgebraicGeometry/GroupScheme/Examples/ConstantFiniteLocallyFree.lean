module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Constant
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The constant group scheme of a finite group is finite locally free

For a finite abstract group `G` the constant group scheme `G_S` of
`AlgebraicGeometry.constantGroupScheme` is finite locally free over `S`: over the terminal
scheme it is a coproduct of finitely many copies of `Spec ℤ`, hence the spectrum of the ring of
functions `G → ℤ`, which is a finite free `ℤ`-module; and finite local freeness is stable under
the base change by which `G_S` is defined.

## Main results

* `AlgebraicGeometry.isFiniteLocallyFree_terminal_from_constantSchemeOverIntegers`: the
  structure morphism of the coproduct of finitely many copies of the terminal scheme is finite
  locally free.
* `AlgebraicGeometry.isFiniteLocallyFree_constantGroupScheme`: the structure morphism of the
  constant group scheme of a finite group is finite locally free.

## Implementation notes

The index type `G` may live in a universe larger than that of the schemes, so the coproduct is
reindexed along `equivShrink` before Mathlib's comparison morphism
`AlgebraicGeometry.sigmaSpec` is applied; this is the same bookkeeping as in Mathlib's proof
that a finite coproduct of affine schemes is affine.

Both the terminal scheme and `Spec (ULift ℤ)` are terminal, so no computation identifies the
structure morphism of the coproduct with the spectrum of the diagonal ring map: any two
morphisms to a terminal object agree. Finite local freeness of that ring map is
`Stacks.Morphisms.specMap_finiteLocallyFree_iff_module` together with finiteness and
projectivity of a finite product of copies of the base ring.

The rank is not recorded. The consumer of this file,
`AlgebraicGeometry.nonempty_finiteFlatQuotient_actionGroupoid_of_geometry` for Tag 07S7, asks
only for `Stacks.Morphisms.IsFiniteLocallyFree`, and that predicate is the one whose base-change
stability is available unranked
(`Stacks.Morphisms.isFiniteLocallyFree_isStableUnderBaseChange`, Tag 02KD).

## References

* [Stacks Project, Tag 03YW](https://stacks.math.columbia.edu/tag/03YW)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02KD](https://stacks.math.columbia.edu/tag/02KD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- The coproduct of finitely many copies of the terminal scheme is finite locally free over the
terminal scheme: it is the spectrum of the ring of functions on the index type with values in
`ULift ℤ`, a finite free module over `ULift ℤ`. -/
@[sga "4 VII 2.1" "special case"]
theorem isFiniteLocallyFree_terminal_from_constantSchemeOverIntegers
    (G : Type v) [Small.{u} G] [Finite G] :
    Stacks.Morphisms.IsFiniteLocallyFree
      (terminal.from (constantSchemeOverIntegers.{u} G)) := by
  classical
  have hι : Finite (Shrink.{u} G) := Finite.of_equiv _ (equivShrink.{u} G)
  let _ : MorphismProperty.RespectsIso (@Stacks.Morphisms.IsFiniteLocallyFree.{u}) :=
    Stacks.Morphisms.isFiniteLocallyFree_isStableUnderBaseChange.respectsIso
  let B : CommRingCat.{u} := .of (Shrink.{u} G → ULift.{u} ℤ)
  let φ : CommRingCat.of (ULift.{u} ℤ) ⟶ B :=
    CommRingCat.ofHom (RingHom.pi fun _ : Shrink.{u} G ↦ RingHom.id (ULift.{u} ℤ))
  let e₀ : (⊤_ Scheme.{u}) ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal.{u}
  have hB : Stacks.Morphisms.IsFiniteLocallyFree (terminal.from (Spec B)) := by
    rw [← MorphismProperty.cancel_right_of_respectsIso
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u}) (terminal.from (Spec B)) e₀.hom,
      specULiftZIsTerminal.hom_ext (terminal.from (Spec B) ≫ e₀.hom) (Spec.map φ),
      Stacks.Morphisms.specMap_finiteLocallyFree_iff_module]
    refine (Module.isFiniteLocallyFree_iff_finite_projective _ _).mpr ⟨?_, ?_⟩
    · exact inferInstanceAs (Module.Finite (ULift.{u} ℤ) (Shrink.{u} G → ULift.{u} ℤ))
    · exact Module.Projective.of_free (R := ULift.{u} ℤ) (P := Shrink.{u} G → ULift.{u} ℤ)
  let eT : constantSchemeOverIntegers.{u} G ≅ Spec B :=
    (Sigma.whiskerEquiv (f := fun _ : G ↦ ⊤_ Scheme.{u})
        (g := fun _ : Shrink.{u} G ↦ Spec (CommRingCat.of (ULift.{u} ℤ)))
        (equivShrink.{u} G) fun _ ↦ e₀.symm).trans
      (asIso (sigmaSpec fun _ : Shrink.{u} G ↦ CommRingCat.of (ULift.{u} ℤ)))
  rw [← terminalIsTerminal.hom_ext (eT.hom ≫ terminal.from (Spec B))
    (terminal.from (constantSchemeOverIntegers.{u} G))]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@Stacks.Morphisms.IsFiniteLocallyFree.{u}) eT.hom (terminal.from (Spec B))).mpr hB

/-- The constant group scheme `G_S` of a finite abstract group `G` is finite locally free over
`S`: it is the base change of the coproduct of `|G|` copies of the terminal scheme, and finite
local freeness is stable under base change. -/
@[sga "4 VII 2.1" "For a finite group G"]
instance isFiniteLocallyFree_constantGroupScheme (G : Type v) [Small.{u} G] [Group G] [Finite G]
    (S : Scheme.{u}) :
    Stacks.Morphisms.IsFiniteLocallyFree (constantGroupScheme.{u} G S).X.hom :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Stacks.Morphisms.IsFiniteLocallyFree.{u})
    (IsPullback.of_hasPullback (terminal.from (constantSchemeOverIntegers.{u} G))
      (terminal.from S))
    (isFiniteLocallyFree_terminal_from_constantSchemeOverIntegers.{u, v} G)

end AlgebraicGeometry

end
