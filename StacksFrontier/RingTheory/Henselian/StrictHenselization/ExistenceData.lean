module

public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.Henselian.Henselization.Existence
public import StacksFrontier.RingTheory.Henselian.StrictHenselization
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Existence

/-!
# Every local ring has a strict henselization

`StacksFrontier.RingTheory.Henselian.StrictHenselization.Existence` constructs the strict
henselization of a local ring `(R, 𝔪, κ)` with respect to a separable algebraic closure
`κ ⊆ κ^sep`, but states the outcome as a list of properties and takes a henselization `Rh` of
`R` as an extra input. This file packages that construction as the predicate
`Stacks.StrictHenselization.IsStrictHenselization`, which is the form every consumer of a strict
henselization uses, and removes both restrictions: no henselization has to be supplied (one is
produced by `IsLocalRing.exists_henselization`), and the separable algebraic closure may live in
a universe of its own.

## Main results

* `Stacks.StrictHenselization.IsStrictHenselization.reindex`: a strict henselization with respect
  to one separable algebraic closure of the residue field is one with respect to any other.
* `Stacks.StrictHenselization.exists_isStrictHenselization`: a local ring `R` admits a local
  `R`-algebra which is a strict henselization of `R` with respect to a given separable algebraic
  closure of its residue field.

## Implementation notes

*Two residue fields.* `Existence.lean` phrases the separable algebraic closure over
`IsLocalRing.ResidueField R = R ⧸ 𝔪`, while `IsStrictHenselization` phrases it over
`(IsLocalRing.maximalIdeal R).ResidueField = Frac(R ⧸ 𝔪)`, the spelling that makes the maps
`Ideal.ResidueField.map` type-compatible for a prime that is not maximal. The two are identified
by `Ideal.bijective_algebraMap_quotient_residueField`, and the separability of `κ^sep` is
transported across that identification; this is the only reason the proof below mentions
`IsLocalRing.ResidueField` at all.

*The universe of the separable closure.* The construction produces the strict henselization in
the universe of `R`, and `IsLocalRing.exists_strictHenselization` asks for the separable closure
in that universe too. A separable algebraic closure in an arbitrary universe is handled by
running the construction for `SeparableClosure (𝔪).ResidueField`, which lies in the universe of
`R`, and then transporting along the isomorphism `IsSepClosure.equiv` of any two separable
closures; `IsStrictHenselization` records the identification of the residue field of the strict
henselization with the chosen closure as a field of the structure, so transporting it is exactly
`reindex`. The strict henselization itself stays in the universe of `R`, as it must: it is a
colimit of étale `R`-algebras.

## References

* [StacksProject 04GP](https://stacks.math.columbia.edu/tag/04GP)
* [StacksProject 04GQ](https://stacks.math.columbia.edu/tag/04GQ)
* [StacksProject 08HT](https://stacks.math.columbia.edu/tag/08HT)

## Tags

strict henselization, strictly henselian, separable algebraic closure, local ring
-/

@[expose] public section

open IsLocalRing

universe u v w x

namespace Stacks.StrictHenselization

/-- **Changing the separable algebraic closure.** A strict henselization of `R` with respect to
the separable algebraic closure `κ₁` of its residue field is also one with respect to any other
separable algebraic closure `κ₂`: compose the recorded identification of the residue field of
`Rsh` with `κ₁` with an isomorphism `κ₂ ≃ κ₁` over the residue field. The two closures may live
in different universes. -/
public noncomputable def IsStrictHenselization.reindex
    {R : Type u} [CommRing R] [IsLocalRing R]
    {κ₁ : Type v} {κ₂ : Type x} [Field κ₁] [Field κ₂]
    [Algebra (maximalIdeal R).ResidueField κ₁] [IsSepClosure (maximalIdeal R).ResidueField κ₁]
    [Algebra (maximalIdeal R).ResidueField κ₂] [IsSepClosure (maximalIdeal R).ResidueField κ₂]
    {Rsh : Type w} [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    (h : IsStrictHenselization R κ₁ Rsh)
    (e : κ₂ ≃ₐ[(maximalIdeal R).ResidueField] κ₁) :
    IsStrictHenselization R κ₂ Rsh :=
  { h with
    residueFieldEquiv := e.toRingEquiv.trans h.residueFieldEquiv
    residueFieldEquiv_comp := by
      let := h.isLocalHom
      refine RingHom.ext fun y => ?_
      change h.residueFieldEquiv (e (algebraMap (maximalIdeal R).ResidueField κ₂ y)) = _
      rw [e.commutes]
      exact RingHom.congr_fun h.residueFieldEquiv_comp y }

/-- The strict henselization exists when the separable algebraic closure lies in the universe of
the ring: feed `IsLocalRing.exists_strictHenselization` a henselization of `R` and repackage its
conclusion, transporting the separable algebraic closure from `R ⧸ 𝔪` to `Frac(R ⧸ 𝔪)`. -/
private theorem exists_isStrictHenselization_of_univ (R : Type u) [CommRing R] [IsLocalRing R]
    (κ : Type u) [Field κ] [Algebra (maximalIdeal R).ResidueField κ]
    [IsSepClosure (maximalIdeal R).ResidueField κ] :
    ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : IsLocalRing Rsh) (_ : Algebra R Rsh),
      Nonempty (IsStrictHenselization R κ Rsh) := by
  let quotientEquiv := AlgEquiv.ofBijective
    (Algebra.ofId (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))
  let : Algebra.IsSeparable (ResidueField R) (maximalIdeal R).ResidueField :=
    AlgEquiv.Algebra.isSeparable quotientEquiv
  let : Algebra (ResidueField R) κ :=
    ((algebraMap (maximalIdeal R).ResidueField κ).comp
      (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)).toAlgebra
  let : IsScalarTower (ResidueField R) (maximalIdeal R).ResidueField κ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsSepClosure (ResidueField R) κ :=
    ⟨IsSepClosure.sep_closed (maximalIdeal R).ResidueField,
      Algebra.IsSeparable.trans (ResidueField R) (maximalIdeal R).ResidueField κ⟩
  obtain ⟨Rh, ringRh, algebraRh, localRh, localMapRh, _, indRh, _, residueRh⟩ :=
    IsLocalRing.exists_henselization R
  let := ringRh
  let := algebraRh
  let := localRh
  let := localMapRh
  obtain ⟨Rsh, ringRsh, localRsh, algebraRsh, algebraRhRsh, towerRsh,
    localMapRhRsh, henselianRsh, sepClosedRsh, indRsh, maximalRsh,
    residueEquiv, hresidueEquiv⟩ :=
    IsLocalRing.exists_strictHenselization R Rh indRh residueRh.2 κ
  let := ringRsh
  let := localRsh
  let := algebraRsh
  let := algebraRhRsh
  let := towerRsh
  let := localMapRhRsh
  let : IsLocalHom (algebraMap R Rsh) := by
    rw [IsScalarTower.algebraMap_eq R Rh Rsh]
    exact RingHom.isLocalHom_comp _ _
  let quotientEquivSh := AlgEquiv.ofBijective
    (Algebra.ofId (ResidueField Rsh) (maximalIdeal Rsh).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal Rsh))
  let := sepClosedRsh
  refine ⟨Rsh, ringRsh, localRsh, algebraRsh, ⟨{
    isLocalHom := inferInstance
    henselian := henselianRsh
    sepClosed := IsSepClosed.of_ringEquiv quotientEquivSh.symm.toRingEquiv
    isFilteredColimitEtale := StacksDraft.indEtale_iff.mpr indRsh
    maximalIdeal_map := maximalRsh
    residueFieldEquiv := residueEquiv.trans quotientEquivSh.toRingEquiv
    residueFieldEquiv_comp := ?_ }⟩⟩
  ext y
  show quotientEquivSh (residueEquiv (algebraMap (ResidueField R) κ (residue R y))) = _
  rw [hresidueEquiv]
  exact (Ideal.ResidueField.map_algebraMap _ _ _ _ y).symm

/-- **Existence of the strict henselization** (Stacks 04GP). A local ring `(R, 𝔪, κ)` together
with a separable algebraic closure `κ ⊆ κ^sep` of its residue field admits a local `R`-algebra
`R^{sh}` which is a strict henselization of `R` with respect to `κ ⊆ κ^sep`, that is: it is
strictly henselian, `R → R^{sh}` is a local ring map realizing `R^{sh}` as a filtered colimit of
étale `R`-algebras, `𝔪 R^{sh}` is the maximal ideal of `R^{sh}`, and the residue field of
`R^{sh}` is identified with `κ^sep` compatibly with `κ ⊆ κ^sep`. -/
@[stacks 04GP "The five properties of the source's conclusion are bundled into the predicate
`Stacks.StrictHenselization.IsStrictHenselization`, and the henselization `R^h`, which the
sibling statement in `StrictHenselization.Existence` carries as a hypothesis, is produced here
by `IsLocalRing.exists_henselization` rather than assumed; so this is the source's existential
form. The separable algebraic closure is taken over `(maximalIdeal R).ResidueField`, the
spelling `IsStrictHenselization` uses, and may lie in a universe independent of `R`.",
  ega "IV 18.8.7",
  ega "IV 18.8.8", sga "4 VIII 4.4"]
public theorem exists_isStrictHenselization (R : Type u) [CommRing R] [IsLocalRing R]
    (κ : Type v) [Field κ] [Algebra (maximalIdeal R).ResidueField κ]
    [IsSepClosure (maximalIdeal R).ResidueField κ] :
    ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : IsLocalRing Rsh) (_ : Algebra R Rsh),
      Nonempty (IsStrictHenselization R κ Rsh) := by
  obtain ⟨Rsh, ringRsh, localRsh, algebraRsh, hRsh⟩ :=
    exists_isStrictHenselization_of_univ R (SeparableClosure (maximalIdeal R).ResidueField)
  let := ringRsh
  let := localRsh
  let := algebraRsh
  exact ⟨Rsh, ringRsh, localRsh, algebraRsh, hRsh.elim fun h => ⟨h.reindex
    (IsSepClosure.equiv (maximalIdeal R).ResidueField κ
      (SeparableClosure (maximalIdeal R).ResidueField))⟩⟩

end Stacks.StrictHenselization

end
