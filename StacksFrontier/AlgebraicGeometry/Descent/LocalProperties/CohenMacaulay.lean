module

public import StacksFrontier.AlgebraicGeometry.Chow.Setup.CohenMacaulayBase
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.SerreCondition
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization

/-!
# Being Cohen–Macaulay is local in the syntomic topology

A scheme is Cohen–Macaulay if and only if the members of a jointly surjective family of
syntomic morphisms onto it are Cohen–Macaulay.

## Main results

* `AlgebraicGeometry.isCohenMacaulay_isLocal_syntomic` states syntomic locality of the
  Cohen–Macaulay property.

## Implementation notes

The Cohen–Macaulay property includes local Noetherianity, as in the source, and is the
conjunction over all `k` of local Noetherianity together with Serre's condition `(Sₖ)`; the
locality of each of those conjuncts is the content of Tag 036A.

## References

* [Stacks Project, Tag 036B](https://stacks.math.columbia.edu/tag/036B)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A Cohen–Macaulay scheme is locally Noetherian. -/
private alias isLocallyNoetherian_of_isCohenMacaulay := IsCohenMacaulay.isLocallyNoetherian

/-- Being Cohen–Macaulay is local Noetherianity together with Serre's condition `(Sₖ)` for
every `k`. -/
private lemma isCohenMacaulay_iff_forall_noetherian_and_hasPropertySk (X : Scheme.{u}) :
    IsCohenMacaulay X ↔
      ∀ k : ℕ, ∃ h : IsLocallyNoetherian X, @HasPropertySk X h k := by
  refine ⟨fun h k => ?_, fun h => ?_⟩
  · let : IsLocallyNoetherian X := isLocallyNoetherian_of_isCohenMacaulay h
    exact ⟨inferInstance, (isCohenMacaulay_iff_forall_hasPropertySk X).mp h k⟩
  · let : IsLocallyNoetherian X := (h 0).choose
    exact (isCohenMacaulay_iff_forall_hasPropertySk X).mpr fun k => (h k).choose_spec

/-- **Stacks Project, Tag 036B.** Being Cohen–Macaulay is local for syntomic coverings. -/
@[stacks 036B]
instance isCohenMacaulay_isLocal_syntomic :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsCohenMacaulay X)
      (Scheme.precoverage @Syntomic) where
  of_iso e h := (isCohenMacaulay_iff_forall_noetherian_and_hasPropertySk _).2 fun k =>
    (isLocallyNoetherian_and_hasPropertySk_isLocal_syntomic k).of_iso e
      ((isCohenMacaulay_iff_forall_noetherian_and_hasPropertySk _).1 h k)
  component {_X _R} hR {_Y} f hf h :=
    (isCohenMacaulay_iff_forall_noetherian_and_hasPropertySk _).2 fun k =>
      (isLocallyNoetherian_and_hasPropertySk_isLocal_syntomic k).component hR f hf
        ((isCohenMacaulay_iff_forall_noetherian_and_hasPropertySk _).1 h k)
  of_presieve hR h := (isCohenMacaulay_iff_forall_noetherian_and_hasPropertySk _).2 fun k =>
    (isLocallyNoetherian_and_hasPropertySk_isLocal_syntomic k).of_presieve hR
      fun _ _ hf => (isCohenMacaulay_iff_forall_noetherian_and_hasPropertySk _).1 (h hf) k

end AlgebraicGeometry
