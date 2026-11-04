module

public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# A nonempty open on which a finite locally free module is free

On a nonempty scheme a finite locally free module of rank `r` is free of rank `r` on some
nonempty open: the trivialising opens of Tag 01C6's local free presentations cover the space, so
one of them meets it.

This is the field `trivialOpen` of `Stacks.Divisors.BundleSplittingDatum`, together with its
`nonempty_trivialOpen`, and it is the open over which Tag 0AYP wants a section of the projective
bundle.

## Main results

* `Stacks.ProjectiveBundleSplitting.exists_nonempty_free_open`: a finite locally free module of
  rank `r` on a nonempty scheme is free of rank `r` on a nonempty open.
* `Stacks.ProjectiveBundleSplitting.exists_nonempty_free_open_of_irreducibleSpace`: the same on
  an irreducible — in particular an integral — scheme, whose space is nonempty by definition.
* `Stacks.ProjectiveBundleSplitting.exists_nonempty_isFreeOfRankOn`: the same conclusion written
  with the predicate `Stacks.ProjectiveBundleSplitting.IsFreeOfRankOn`.

## Implementation notes

The index type of the free presentation is produced as it stands, with an equivalence to
`Fin r` beside it, rather than transported along that equivalence: `Tag 01C6`'s
`IsFiniteLocallyFreeOfRank` records exactly that, and the consumers of this lemma read the
equivalence.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 0AYP](https://stacks.math.columbia.edu/tag/0AYP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.ProjectiveBundleSplitting

/-- **A module is free of rank `r` on an open** when it is isomorphic there to a free module on
a basis indexed in bijection with `Fin r`. This is the condition the trivialising open of Tag
0AYP satisfies, named so that it can be quoted as a hypothesis. -/
def IsFreeOfRankOn {X : Scheme.{u}} (E : X.Modules) (r : ℕ) (U : X.Opens) : Prop :=
  ∃ I : Type u, Nonempty (I ≃ Fin r) ∧
    Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U)

/-- **A finite locally free module of rank `r` on a nonempty scheme is free of rank `r` on a
nonempty open.** The opens carrying the local free presentations of Tag 01C6 cover the space, so
a point of the space lies in one of them, and on that one the presentation map is an
isomorphism from a free module whose basis is indexed in bijection with `Fin r`. -/
theorem exists_nonempty_free_open {X : Scheme.{u}} (hX : Nonempty X) (E : X.Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    ∃ (U : X.Opens) (I : Type u), Nonempty U ∧ Nonempty (I ≃ Fin r) ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U) := by
  obtain ⟨q, hq, hrank⟩ := hE.exists_isFiniteLocallyFreeOfRankData
  obtain ⟨x⟩ := hX
  have hcover : (⨆ i, q.X i) = ⊤ := (Opens.coversTop_iff _ _).1 q.coversTop
  have hx : x ∈ (⨆ i, q.X i) := by rw [hcover]; trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  have : IsIso (q.generators i).π := hq.isIso i
  exact ⟨q.X i, (q.generators i).I, ⟨⟨x, hxi⟩⟩, hrank i, ⟨asIso (q.generators i).π⟩⟩

/-- **The same on an irreducible scheme**, whose space is nonempty, so in particular on the
integral scheme of Tag 0AYP. -/
theorem exists_nonempty_free_open_of_irreducibleSpace {X : Scheme.{u}} [IrreducibleSpace X]
    (E : X.Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    ∃ (U : X.Opens) (I : Type u), Nonempty U ∧ Nonempty (I ≃ Fin r) ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U) :=
  exists_nonempty_free_open inferInstance E r hE

/-- **A nonempty open on which `ℰ` is free of rank `r`**, in the named form: this is the field
`trivialOpen` of `Stacks.Divisors.BundleSplittingDatum` with its `nonempty_trivialOpen`, on the
integral scheme of Tag 0AYP. -/
theorem exists_nonempty_isFreeOfRankOn {X : Scheme.{u}} [IrreducibleSpace X] (E : X.Modules)
    (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    ∃ U : X.Opens, Nonempty U ∧ IsFreeOfRankOn E r U := by
  obtain ⟨U, I, hU, hI, hfree⟩ := exists_nonempty_free_open_of_irreducibleSpace E r hE
  exact ⟨U, hU, I, hI, hfree⟩

end Stacks.ProjectiveBundleSplitting

end
