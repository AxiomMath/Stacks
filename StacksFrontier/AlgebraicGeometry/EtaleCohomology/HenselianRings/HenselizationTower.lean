module

public import Mathlib.Algebra.Field.Shrink
public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.Henselization.Existence
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Existence
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite

/-!
# Henselizations and strict henselizations

For a local ring `R` and a chosen separable closure `κsep` of its residue field, there is a
chosen tower of canonical flat local maps `R → Rʰ → Rˢʰ`. The two rings are ind-étale over
`R`, are respectively henselian and strictly henselian, and have the prescribed residue fields.

## Main definitions

* `IsLocalRing.HenselizationTower` packages chosen representatives of the henselization and
  strict henselization, their canonical maps, and compatible residue-field identifications.
* `IsLocalRing.henselizationTower` chooses such a tower.

## Main results

* `IsLocalRing.IsHenselization.map_maximalIdeal` identifies the extended maximal ideal with the
  maximal ideal of either chosen ring.
* `HenselianLocalRing.indEtaleAlgHom_unique` characterizes the canonical map from a
  henselization to a henselian local `R`-algebra; the field
  `IsLocalRing.HenselizationTower.canonicalMap_unique` records this characterization for the
  map `Rʰ → Rˢʰ` in the chosen tower.

## Implementation notes

The `IsLocalRing.IsHenselization` fields say simultaneously that the rings are henselian,
ind-étale over `R`, and have the indicated residue fields as extensions of `κ(R)`. Explicit
ring equivalences are retained in the package so users can refer to the residue identifications
without making another choice. The separable closure may live in a universe independent of the
rings; it is replaced by an equivalent small model before the existence theorems are applied.

## References

* [Stacks Project, Tag 03QL](https://stacks.math.columbia.edu/tag/03QL)
-/

@[expose] public section

open IsLocalRing

universe u v

namespace IsLocalRing


/-- Chosen representatives of the henselization and strict henselization of a local ring,
together with their canonical flat local maps and compatible residue-field identifications. -/
public structure HenselizationTower (R : Type u) [CommRing R] [IsLocalRing R]
    (κsep : Type v) [Field κsep] [Algebra (ResidueField R) κsep]
    [IsSepClosure (ResidueField R) κsep] where
  /-- The chosen henselization. -/
  henselization : Type u
  [henselizationCommRing : CommRing henselization]
  [henselizationIsLocalRing : IsLocalRing henselization]
  [henselizationAlgebra : Algebra R henselization]
  [henselizationIsLocalHom : IsLocalHom (algebraMap R henselization)]
  [henselizationIsFlat : Module.Flat R henselization]
  [henselizationIsHenselization :
    IsLocalRing.IsHenselization R (ResidueField R) henselization]
  /-- The chosen strict henselization. -/
  strictHenselization : Type u
  [strictHenselizationCommRing : CommRing strictHenselization]
  [strictHenselizationIsLocalRing : IsLocalRing strictHenselization]
  [strictHenselizationAlgebra : Algebra R strictHenselization]
  [henselizationAlgebraStrictHenselization : Algebra henselization strictHenselization]
  [isScalarTower : IsScalarTower R henselization strictHenselization]
  [strictHenselizationIsLocalHom :
    IsLocalHom (algebraMap henselization strictHenselization)]
  [strictHenselizationIsFlat : Module.Flat henselization strictHenselization]
  [strictHenselizationIsHenselization :
    IsLocalRing.IsHenselization R κsep strictHenselization]
  [strictHenselizationIsStrictlyHenselian :
    StrictlyHenselianLocalRing strictHenselization]
  /-- The identification `κ(R) ≃ κ(Rʰ)`. -/
  henselizationResidueEquiv : ResidueField R ≃+* ResidueField henselization
  /-- The residue identification for `Rʰ` is compatible with the structure map from `R`. -/
  henselizationResidueEquiv_residue (x : R) :
    henselizationResidueEquiv (residue R x) =
      residue henselization (algebraMap R henselization x)
  /-- The identification `κsep ≃ κ(Rˢʰ)`. -/
  strictHenselizationResidueEquiv : κsep ≃+* ResidueField strictHenselization
  /-- The residue identification for `Rˢʰ` is compatible with the extension `κ(R) → κsep`. -/
  strictHenselizationResidueEquiv_residue (x : R) :
    strictHenselizationResidueEquiv
        (algebraMap (ResidueField R) κsep (residue R x)) =
      residue strictHenselization (algebraMap R strictHenselization x)
  /-- The local `R`-algebra map from the henselization to the strict henselization is uniquely
  the map induced by the displayed algebra tower. -/
  canonicalMap_unique (f : henselization →ₐ[R] strictHenselization) (hf : IsLocalHom f) :
    f = IsScalarTower.toAlgHom R henselization strictHenselization

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {κsep : Type v} [Field κsep] [Algebra (ResidueField R) κsep]
  [IsSepClosure (ResidueField R) κsep]

/-- The ring structure on the henselization in a chosen tower. -/
public instance HenselizationTower.instCommRingHenselization
    (T : HenselizationTower R κsep) : CommRing T.henselization :=
  T.henselizationCommRing

/-- The local-ring structure on the henselization in a chosen tower. -/
public instance HenselizationTower.instIsLocalRingHenselization
    (T : HenselizationTower R κsep) : IsLocalRing T.henselization :=
  T.henselizationIsLocalRing

/-- The `R`-algebra structure on the henselization in a chosen tower. -/
public instance HenselizationTower.instAlgebraHenselization
    (T : HenselizationTower R κsep) : Algebra R T.henselization :=
  T.henselizationAlgebra

/-- The structure map to the henselization in a chosen tower is local. -/
public instance HenselizationTower.instIsLocalHomHenselization
    (T : HenselizationTower R κsep) : IsLocalHom (algebraMap R T.henselization) :=
  T.henselizationIsLocalHom

/-- The henselization in a chosen tower is flat over `R`. -/
public instance HenselizationTower.instFlatHenselization
    (T : HenselizationTower R κsep) : Module.Flat R T.henselization :=
  T.henselizationIsFlat

/-- The henselization in a chosen tower has its characterizing henselization structure. -/
public instance HenselizationTower.instIsHenselizationHenselization
    (T : HenselizationTower R κsep) :
    IsLocalRing.IsHenselization R (ResidueField R) T.henselization :=
  T.henselizationIsHenselization

/-- The henselization in a chosen tower is henselian. -/
public instance HenselizationTower.instHenselianLocalRingHenselization
    (T : HenselizationTower R κsep) : HenselianLocalRing T.henselization :=
  T.henselizationIsHenselization.henselian

/-- The ring structure on the strict henselization in a chosen tower. -/
public instance HenselizationTower.instCommRingStrictHenselization
    (T : HenselizationTower R κsep) : CommRing T.strictHenselization :=
  T.strictHenselizationCommRing

/-- The local-ring structure on the strict henselization in a chosen tower. -/
public instance HenselizationTower.instIsLocalRingStrictHenselization
    (T : HenselizationTower R κsep) : IsLocalRing T.strictHenselization :=
  T.strictHenselizationIsLocalRing

/-- The `R`-algebra structure on the strict henselization in a chosen tower. -/
public instance HenselizationTower.instAlgebraStrictHenselization
    (T : HenselizationTower R κsep) : Algebra R T.strictHenselization :=
  T.strictHenselizationAlgebra

/-- The strict henselization in a chosen tower is an algebra over its henselization. -/
public instance HenselizationTower.instAlgebraHenselizationStrictHenselization
    (T : HenselizationTower R κsep) : Algebra T.henselization T.strictHenselization :=
  T.henselizationAlgebraStrictHenselization

/-- The algebra structures in a chosen henselization tower form a scalar tower. -/
public instance HenselizationTower.instIsScalarTower
    (T : HenselizationTower R κsep) :
    IsScalarTower R T.henselization T.strictHenselization :=
  T.isScalarTower

/-- The canonical map from the henselization to the strict henselization is local. -/
public instance HenselizationTower.instIsLocalHomStrictHenselization
    (T : HenselizationTower R κsep) :
    IsLocalHom (algebraMap T.henselization T.strictHenselization) :=
  T.strictHenselizationIsLocalHom

/-- The strict henselization in a chosen tower is flat over the henselization. -/
public instance HenselizationTower.instFlatStrictHenselization
    (T : HenselizationTower R κsep) : Module.Flat T.henselization T.strictHenselization :=
  T.strictHenselizationIsFlat

/-- The strict henselization in a chosen tower has its characterizing henselization structure. -/
public instance HenselizationTower.instIsHenselizationStrictHenselization
    (T : HenselizationTower R κsep) :
    IsLocalRing.IsHenselization R κsep T.strictHenselization :=
  T.strictHenselizationIsHenselization

/-- The strict henselization in a chosen tower is strictly henselian. -/
public instance HenselizationTower.instStrictlyHenselianLocalRing
    (T : HenselizationTower R κsep) :
    StrictlyHenselianLocalRing T.strictHenselization :=
  T.strictHenselizationIsStrictlyHenselian

/-- The canonical henselization/strict-henselization tower associated to a local ring and a
chosen separable closure of its residue field. -/
@[stacks 03QL "existence, flat local maps, and parts (1), (2), and (4)"]
public noncomputable def henselizationTower (R : Type u) [CommRing R] [IsLocalRing R]
    (κsep : Type v) [Field κsep] [Algebra (ResidueField R) κsep]
    [IsSepClosure (ResidueField R) κsep] : HenselizationTower R κsep := by
  letI : Small.{u} κsep := by
    let : Algebra.IsAlgebraic (ResidueField R) κsep := IsSepClosure.separable.isAlgebraic
    apply small_of_injective (β := ResidueField R ⊕ ℕ)
      (Classical.choice (Cardinal.lift_mk_le'.mp ?_)).injective
    refine (Algebra.IsAlgebraic.lift_cardinalMk_le_max (ResidueField R) κsep).trans ?_
    simp [Cardinal.mk_sum, Cardinal.lift_add]
  letI : Algebra (ResidueField R) (Shrink.{u} κsep) :=
    ((Shrink.ringEquiv κsep).symm.toRingHom.comp
      (algebraMap (ResidueField R) κsep)).toAlgebra
  have hShrinkAlg (x : ResidueField R) : algebraMap (ResidueField R) (Shrink.{u} κsep) x =
      (Shrink.ringEquiv κsep).symm (algebraMap (ResidueField R) κsep x) := rfl
  let eShrink : Shrink.{u} κsep ≃ₐ[ResidueField R] κsep :=
    { Shrink.ringEquiv κsep with commutes' := fun x => by rw [hShrinkAlg]; simp }
  letI : IsSepClosed κsep := IsSepClosure.sep_closed (ResidueField R)
  letI : IsSepClosed (Shrink.{u} κsep) := IsSepClosed.of_ringEquiv eShrink.toRingEquiv
  letI : IsSepClosure (ResidueField R) (Shrink.{u} κsep) :=
    ⟨inferInstance, AlgEquiv.Algebra.isSeparable eShrink.symm⟩
  apply Classical.choice
  obtain ⟨Rh, hRhRing, hRhAlg, hRhLocal, hRhMapLocal, hRhHens, hRhInd, -, hRhRes⟩ :=
    IsLocalRing.exists_henselization R
  let : CommRing Rh := hRhRing
  let : Algebra R Rh := hRhAlg
  let : IsLocalRing Rh := hRhLocal
  let : IsLocalHom (algebraMap R Rh) := hRhMapLocal
  let eRh : ResidueField R ≃+* ResidueField Rh :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap R Rh)) hRhRes
  have heRh (x : R) : eRh (residue R x) = residue Rh (algebraMap R Rh x) :=
    ResidueField.map_residue _ x
  let : IsLocalRing.IsHenselization R (ResidueField R) Rh :=
    IsLocalRing.IsHenselization.of_ind_etale hRhHens hRhInd ⟨eRh, heRh⟩
  obtain ⟨Rsh, hRshRing, hRshLocal, hRRshAlg, hRhRshAlg, hTower, hRhRshLocal,
      hRshHens, hRshSep, hRshInd, -, eRshSmall, heRshSmall⟩ :=
    IsLocalRing.exists_strictHenselization R Rh hRhInd hRhRes.2 (Shrink.{u} κsep)
  let : CommRing Rsh := hRshRing
  let : IsLocalRing Rsh := hRshLocal
  let : Algebra R Rsh := hRRshAlg
  let : Algebra Rh Rsh := hRhRshAlg
  let : IsScalarTower R Rh Rsh := hTower
  let : IsLocalHom (algebraMap Rh Rsh) := hRhRshLocal
  let eRsh : κsep ≃+* ResidueField Rsh := (Shrink.ringEquiv κsep).symm.trans eRshSmall
  have heRsh (x : R) :
      eRsh (algebraMap (ResidueField R) κsep (residue R x)) =
        residue Rsh (algebraMap R Rsh x) := by
    change eRshSmall ((Shrink.ringEquiv κsep).symm
      (algebraMap (ResidueField R) κsep (residue R x))) = _
    rw [← hShrinkAlg]; exact heRshSmall x
  let : IsLocalRing.IsHenselization R κsep Rsh :=
    IsLocalRing.IsHenselization.of_ind_etale hRshHens hRshInd ⟨eRsh, heRsh⟩
  let : Module.Flat R Rsh := CommAlgCat.flat_of_ind_etale hRshInd
  let : HenselianLocalRing Rsh := hRshHens
  let : IsSepClosed (ResidueField Rsh) := hRshSep
  exact ⟨
    { henselization := Rh
      henselizationCommRing := inferInstance
      henselizationIsLocalRing := inferInstance
      henselizationAlgebra := inferInstance
      henselizationIsLocalHom := inferInstance
      henselizationIsFlat := CommAlgCat.flat_of_ind_etale hRhInd
      henselizationIsHenselization := inferInstance
      strictHenselization := Rsh
      strictHenselizationCommRing := inferInstance
      strictHenselizationIsLocalRing := inferInstance
      strictHenselizationAlgebra := inferInstance
      henselizationAlgebraStrictHenselization := inferInstance
      isScalarTower := inferInstance
      strictHenselizationIsLocalHom := inferInstance
      strictHenselizationIsFlat := CommAlgCat.flat_of_ind_etale_restrictScalars hRhInd
      strictHenselizationIsHenselization := inferInstance
      strictHenselizationIsStrictlyHenselian := ⟨⟩
      henselizationResidueEquiv := eRh
      henselizationResidueEquiv_residue := heRh
      strictHenselizationResidueEquiv := eRsh
      strictHenselizationResidueEquiv_residue := heRsh
      canonicalMap_unique := fun f hf => by
        let : IsLocalHom (algebraMap R Rsh) := by
          rw [IsScalarTower.algebraMap_eq R Rh Rsh]; exact RingHom.isLocalHom_comp _ _
        have hind : (CommAlgCat.etale R).ind (CommAlgCat.of R (ULift.{u} Rh)) :=
          (CommAlgCat.etale R).ind.prop_of_iso
            (CommAlgCat.isoMk (ULift.algEquiv (R := R) (A := Rh)).symm) hRhInd
        have hg := HenselianLocalRing.indEtaleAlgHom_unique (Sh := Rsh) hind hRhRes.2
        exact (hg f hf).trans
          (hg (IsScalarTower.toAlgHom R Rh Rsh)
            ⟨fun x hx => IsLocalHom.map_nonunit (f := algebraMap Rh Rsh) x hx⟩).symm }⟩

add_to_stacks 03QL "part (3): maximal ideals"
  IsLocalRing.IsHenselization.map_maximalIdeal

end IsLocalRing
