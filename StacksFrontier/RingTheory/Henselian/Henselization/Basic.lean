module

public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Basic properties of henselizations

Let `Rh` be a henselization of the local ring `R` with residue field `L`, in the sense of
`IsLocalRing.IsHenselization`. The residue field map of `R → Rh` is bijective when `L = κ`, and the
prescribed residue extension may always be replaced by the residue field of `Rh` itself.

Locality of `R → Rh` and the equality `𝔪_R Rh = 𝔪_{Rh}` — the two conditions of Lemmas 04GN and
04GP that the definition leaves out because they follow from the others — are
`IsLocalRing.IsHenselization.isLocalHom` and `IsLocalRing.IsHenselization.map_maximalIdeal`, proved
with the definition in `StacksFrontier.RingTheory.Henselian.Henselization.Defs`.

## Main results

* `IsLocalRing.IsHenselization.residueField_map_bijective`: for `L = κ`, the residue field map of
  `R → Rh` is bijective.
* `IsLocalRing.IsHenselization.exists_residueFieldAlgebra`: the prescribed residue field extension
  may be replaced by the residue field of `Rh` itself.
* `IsLocalRing.exists_isHenselization_residueField`: every local ring has a henselization in its
  own universe, packaged as an `IsLocalRing.IsHenselization` instance.
* `IsLocalRing.exists_isHenselization_separableClosure`: every local ring has a strict
  henselization in its own universe, packaged in the same way.

## Implementation notes

The first two are theorems about an instance `IsHenselization R L Rh` whose residue extension `L`
does not appear in the conclusion, so it is passed by name, as `(L := L)`.

The last two repackage the existence statements of Lemmas 04GN and 04GP, whose conclusions spell
out the defining conditions, into the single class `IsLocalRing.IsHenselization`; the separable
algebraic closure of the residue field is taken to be `SeparableClosure`.

## References

* [StacksProject 04GN](https://stacks.math.columbia.edu/tag/04GN)
* [StacksProject 04GP](https://stacks.math.columbia.edu/tag/04GP)
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace IsLocalRing.IsHenselization

variable {R : Type u} [CommRing R] [IsLocalRing R] {L : Type v} [Field L]
  [Algebra (ResidueField R) L] {Rh : Type w} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]

/-- The residue field map of a henselization with residue field `κ` is bijective. -/
theorem residueField_map_bijective [IsHenselization R (ResidueField R) Rh]
    [IsLocalHom (algebraMap R Rh)] : Function.Bijective (ResidueField.map (algebraMap R Rh)) := by
  obtain ⟨e, he⟩ := exists_residueFieldEquiv (R := R) (L := ResidueField R) (Rh := Rh)
  refine ⟨RingHom.injective _, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective y
  obtain ⟨a, rfl⟩ := residue_surjective x
  exact ⟨residue R a, by rw [ResidueField.map_residue, ← he, Algebra.algebraMap_self,
    RingHom.id_apply]⟩

/-- **The prescribed residue field can be replaced by the actual one.** If `Rh` is a henselization
of `R` with residue field `L`, then it is also one with residue field its own residue field, for
the `κ`-algebra structure on `ResidueField Rh` given by the residue map of `R → Rh`; and if `L` is
a separable algebraic closure of `κ`, so is `ResidueField Rh`. -/
theorem exists_residueFieldAlgebra [IsHenselization R L Rh] :
    ∃ _ : Algebra (ResidueField R) (ResidueField Rh),
      IsHenselization R (ResidueField Rh) Rh ∧
        (IsSepClosure (ResidueField R) L → IsSepClosure (ResidueField R) (ResidueField Rh)) ∧
        ∀ x : R, algebraMap (ResidueField R) (ResidueField Rh) (residue R x) =
          residue Rh (algebraMap R Rh x) := by
  obtain ⟨e, he⟩ := exists_residueFieldEquiv (R := R) (L := L) (Rh := Rh)
  let : Algebra (ResidueField R) (ResidueField Rh) :=
    (e.toRingHom.comp (algebraMap (ResidueField R) L)).toAlgebra
  refine ⟨this, ⟨henselian (R := R) (L := L), ind_etale (L := L), RingEquiv.refl _, he⟩,
    fun hsep => ?_, he⟩
  have := IsSepClosure.sep_closed (ResidueField R) (K := L)
  let e' : L ≃ₐ[ResidueField R] ResidueField Rh := { e with commutes' := fun _ => rfl }
  exact ⟨IsSepClosed.of_ringEquiv e'.symm.toRingEquiv, AlgEquiv.Algebra.isSeparable e'⟩

end IsLocalRing.IsHenselization

namespace IsLocalRing

/-- **Stacks Project, Tag 04GN, packaged.** Every local ring `R` admits a henselization in the
universe of `R`, with its residue field as the prescribed residue extension. -/
theorem exists_isHenselization_residueField (R : Type u) [CommRing R] [IsLocalRing R] :
    ∃ (Rh : Type u) (_ : CommRing Rh) (_ : IsLocalRing Rh) (_ : Algebra R Rh),
      IsHenselization R (ResidueField R) Rh := by
  obtain ⟨Rh, _, _, _, _, hh, hi, -, hr⟩ := exists_henselization R
  refine ⟨Rh, inferInstance, inferInstance, inferInstance, IsHenselization.of_ind_etale hh hi
    ⟨RingEquiv.ofBijective (ResidueField.map (algebraMap R Rh)) hr, fun a ↦ ?_⟩⟩
  exact ResidueField.map_residue (algebraMap R Rh) a

/-- **Stacks Project, Tag 04GP, packaged.** Every local ring `R` admits a strict henselization in
the universe of `R`, with the separable closure of its residue field as the prescribed residue
extension. -/
@[ega "IV 18.8.7" "special case"]
theorem exists_isHenselization_separableClosure (R : Type u) [CommRing R] [IsLocalRing R] :
    ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : IsLocalRing Rsh) (_ : Algebra R Rsh),
      IsHenselization R (SeparableClosure (ResidueField R)) Rsh := by
  obtain ⟨Rh, _, _, _, _, _, hi, -, hr⟩ := exists_henselization R
  obtain ⟨Rsh, _, _, _, _, _, _, hsh, -, hsi, -, hsres⟩ :=
    exists_strictHenselization R Rh hi hr.2 (SeparableClosure (ResidueField R))
  exact ⟨Rsh, inferInstance, inferInstance, inferInstance,
    IsHenselization.of_ind_etale hsh hsi hsres⟩

end IsLocalRing
