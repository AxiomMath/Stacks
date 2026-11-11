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
* `Stacks.StrictHenselization.exists_henselization_isStrictHenselization`: Stacks 04GP, the
  commutative diagram `R → R^h → R^{sh}` over `κ → κ → κ^sep`, with `R → R^h` the henselization of
  Lemma 04GN, `R^h → R^{sh}` local, and `R^{sh}` a strict henselization of `R` with respect to
  `κ ⊆ κ^sep`.
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

/-- The henselization and the strict henselization exist when the separable algebraic closure
lies in the universe of the ring: take the henselization `R → Rh` of
`IsLocalRing.exists_henselization`, feed it to `IsLocalRing.exists_strictHenselization`, and
repackage the conclusion, transporting the separable algebraic closure from `R ⧸ 𝔪` to
`Frac(R ⧸ 𝔪)`. -/
private theorem exists_henselization_isStrictHenselization_of_univ (R : Type u) [CommRing R]
    [IsLocalRing R] (κ : Type u) [Field κ] [Algebra (maximalIdeal R).ResidueField κ]
    [IsSepClosure (maximalIdeal R).ResidueField κ] :
    ∃ (Rh : Type u) (_ : CommRing Rh) (_ : Algebra R Rh) (_ : IsLocalRing Rh)
      (_ : IsLocalHom (algebraMap R Rh)),
      HenselianLocalRing Rh ∧
      (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R Rh) ∧
      (maximalIdeal R).map (algebraMap R Rh) = maximalIdeal Rh ∧
      Function.Bijective (ResidueField.map (algebraMap R Rh)) ∧
      ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : IsLocalRing Rsh) (_ : Algebra R Rsh)
        (_ : Algebra Rh Rsh) (_ : IsScalarTower R Rh Rsh) (_ : IsLocalHom (algebraMap Rh Rsh)),
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
  obtain ⟨Rh, ringRh, algebraRh, localRh, localMapRh, henselianRh, indRh, maximalRh, residueRh⟩ :=
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
  refine ⟨Rh, ringRh, algebraRh, localRh, localMapRh, henselianRh, indRh, maximalRh, residueRh,
    Rsh, ringRsh, localRsh, algebraRsh, algebraRhRsh, towerRsh, localMapRhRsh, ⟨{
    isLocalHom := inferInstance
    henselian := henselianRsh
    sepClosed := IsSepClosed.of_ringEquiv quotientEquivSh.symm.toRingEquiv
    isFilteredColimitEtale := StacksDraft.indEtale_iff.mpr indRsh
    maximalIdeal_map := maximalRsh
    residueFieldEquiv := residueEquiv.trans quotientEquivSh.toRingEquiv
    residueFieldEquiv_comp := ?_ }⟩⟩
  ext y
  change quotientEquivSh (residueEquiv (algebraMap (ResidueField R) κ (residue R y))) = _
  rw [hresidueEquiv]
  exact (Ideal.ResidueField.map_algebraMap _ _ _ _ y).symm

/-- In a tower `R → Rh → Rsh` of local ring maps with `Rsh` a strict henselization of `R` with
respect to `κ`, the square of residue fields over `Rh → Rsh` commutes: if `x : R` and `y : Rh`
have the same residue class in `Rh`, then the class of `x` in `κ` and the class of `y` in the
residue field of `Rsh` correspond under the identification `κ ≃ κ(Rsh)`. -/
private theorem IsStrictHenselization.residueFieldEquiv_algebraMap_of_residue_eq
    {R : Type u} [CommRing R] [IsLocalRing R]
    {κ : Type v} [Field κ] [Algebra (maximalIdeal R).ResidueField κ]
    [IsSepClosure (maximalIdeal R).ResidueField κ]
    {Rh : Type w} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    {Rsh : Type x} [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh] [Algebra Rh Rsh]
    [IsScalarTower R Rh Rsh] [IsLocalHom (algebraMap Rh Rsh)]
    (h : IsStrictHenselization R κ Rsh) (y : Rh) (x : R)
    (hxy : residue Rh (algebraMap R Rh x) = residue Rh y) :
    h.residueFieldEquiv (algebraMap (maximalIdeal R).ResidueField κ
        (algebraMap R (maximalIdeal R).ResidueField x)) =
      algebraMap Rsh (maximalIdeal Rsh).ResidueField (algebraMap Rh Rsh y) := by
  let := h.isLocalHom
  have hcomp : h.residueFieldEquiv (algebraMap (maximalIdeal R).ResidueField κ
      (algebraMap R (maximalIdeal R).ResidueField x)) =
      Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Rsh) (algebraMap R Rsh)
        (maximalIdeal_comap (algebraMap R Rsh)).symm
        (algebraMap R (maximalIdeal R).ResidueField x) :=
    RingHom.congr_fun h.residueFieldEquiv_comp (algebraMap R (maximalIdeal R).ResidueField x)
  have hmem : algebraMap R Rh x - y ∈ maximalIdeal Rh :=
    (residue_eq_zero_iff _).mp (by rw [map_sub, hxy, sub_self])
  rw [← maximalIdeal_comap (algebraMap Rh Rsh), Ideal.mem_comap, map_sub] at hmem
  rw [hcomp, Ideal.ResidueField.map_algebraMap, IsScalarTower.algebraMap_apply R Rh Rsh x,
    ← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero]
  exact hmem

/-- **Existence of the henselization and the strict henselization** (Stacks 04GP). Let
`(R, 𝔪, κ)` be a local ring and let `κ ⊆ κ^sep` be a separable algebraic closure. There is a
commutative diagram
```
κ  →  κ  →  κ^sep
↑     ↑      ↑
R  →  Rh  →  Rsh
```
where `R → Rh` is the henselization of `R` (Stacks 04GN: a local ring map, `Rh` henselian and a
filtered colimit of étale `R`-algebras, `𝔪 Rh` the maximal ideal of `Rh`, and `κ = Rh/𝔪 Rh`),
such that (1) `Rh → Rsh` is local, (2) `Rsh` is strictly henselian, (3) `Rsh` is a filtered
colimit of étale `R`-algebras, (4) `𝔪 Rsh` is the maximal ideal of `Rsh`, and
(5) `κ^sep = Rsh/𝔪 Rsh`. -/
@[stacks 04GP "The middle column `R → Rh` is produced, with the four properties of Lemma 04GN
(`IsLocalHom`, `HenselianLocalRing`, `(CommAlgCat.etale R).ind`, `𝔪 Rh` the maximal ideal, and
bijectivity of the residue field map, which is the vertical `κ = κ`). The map `Rh → Rsh` is the
`Algebra Rh Rsh` with `IsScalarTower R Rh Rsh`, and item (1) is `IsLocalHom (algebraMap Rh Rsh)`.
Items (2)–(5) and the outer rectangle are the predicate
`Stacks.StrictHenselization.IsStrictHenselization`: strictly henselian is `henselian` plus
`sepClosed`, the filtered colimit is `isFilteredColimitEtale`, `𝔪 Rsh` is `maximalIdeal_map`, and
`κ^sep = Rsh/𝔪 Rsh` is `residueFieldEquiv` with its compatibility `residueFieldEquiv_comp`. The
right square is the last clause: the residue class of `y : Rh` in `κ` is that of any `x : R`
with the same residue in `Rh`, and its image in `κ^sep` is the class of `y` in `Rsh`. The
residue field of `R` is spelled `(maximalIdeal R).ResidueField`, and `κ^sep` may lie in any
universe.",
  ega "IV 18.8.7", ega "IV 18.8.8", sga "4 VIII 4.4"]
public theorem exists_henselization_isStrictHenselization (R : Type u) [CommRing R]
    [IsLocalRing R] (κ : Type v) [Field κ] [Algebra (maximalIdeal R).ResidueField κ]
    [IsSepClosure (maximalIdeal R).ResidueField κ] :
    ∃ (Rh : Type u) (_ : CommRing Rh) (_ : Algebra R Rh) (_ : IsLocalRing Rh)
      (_ : IsLocalHom (algebraMap R Rh)),
      HenselianLocalRing Rh ∧
      (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R Rh) ∧
      (maximalIdeal R).map (algebraMap R Rh) = maximalIdeal Rh ∧
      Function.Bijective (ResidueField.map (algebraMap R Rh)) ∧
      ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : IsLocalRing Rsh) (_ : Algebra R Rsh)
        (_ : Algebra Rh Rsh) (_ : IsScalarTower R Rh Rsh) (_ : IsLocalHom (algebraMap Rh Rsh))
        (h : IsStrictHenselization R κ Rsh), ∀ (y : Rh) (x : R),
          residue Rh (algebraMap R Rh x) = residue Rh y →
          h.residueFieldEquiv (algebraMap (maximalIdeal R).ResidueField κ
              (algebraMap R (maximalIdeal R).ResidueField x)) =
            algebraMap Rsh (maximalIdeal Rsh).ResidueField (algebraMap Rh Rsh y) := by
  obtain ⟨Rh, ringRh, algebraRh, localRh, localMapRh, henselianRh, indRh, maximalRh, residueRh,
    Rsh, ringRsh, localRsh, algebraRsh, algebraRhRsh, towerRsh, localMapRhRsh, ⟨h⟩⟩ :=
    exists_henselization_isStrictHenselization_of_univ R
      (SeparableClosure (maximalIdeal R).ResidueField)
  let := ringRh
  let := algebraRh
  let := localRh
  let := ringRsh
  let := localRsh
  let := algebraRsh
  let := algebraRhRsh
  let := towerRsh
  let := localMapRhRsh
  let h' := h.reindex (IsSepClosure.equiv (maximalIdeal R).ResidueField κ
    (SeparableClosure (maximalIdeal R).ResidueField))
  exact ⟨Rh, ringRh, algebraRh, localRh, localMapRh, henselianRh, indRh, maximalRh, residueRh,
    Rsh, ringRsh, localRsh, algebraRsh, algebraRhRsh, towerRsh, localMapRhRsh, h',
    h'.residueFieldEquiv_algebraMap_of_residue_eq⟩

/-- **Existence of the strict henselization.** A local ring `(R, 𝔪, κ)` together
with a separable algebraic closure `κ ⊆ κ^sep` of its residue field admits a local `R`-algebra
`R^{sh}` which is a strict henselization of `R` with respect to `κ ⊆ κ^sep`, that is: it is
strictly henselian, `R → R^{sh}` is a local ring map realizing `R^{sh}` as a filtered colimit of
étale `R`-algebras, `𝔪 R^{sh}` is the maximal ideal of `R^{sh}`, and the residue field of
`R^{sh}` is identified with `κ^sep` compatibly with `κ ⊆ κ^sep`. This is the strict henselization
column of `exists_henselization_isStrictHenselization` (Stacks 04GP), without the henselization
`R → R^h` through which it factors. -/
@[ega "IV 18.8.7", ega "IV 18.8.8", sga "4 VIII 4.4"]
public theorem exists_isStrictHenselization (R : Type u) [CommRing R] [IsLocalRing R]
    (κ : Type v) [Field κ] [Algebra (maximalIdeal R).ResidueField κ]
    [IsSepClosure (maximalIdeal R).ResidueField κ] :
    ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : IsLocalRing Rsh) (_ : Algebra R Rsh),
      Nonempty (IsStrictHenselization R κ Rsh) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, Rsh, ringRsh, localRsh, algebraRsh, _, _, _, h, _⟩ :=
    exists_henselization_isStrictHenselization R κ
  exact ⟨Rsh, ringRsh, localRsh, algebraRsh, ⟨h⟩⟩

end Stacks.StrictHenselization

end
