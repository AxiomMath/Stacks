module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.Examples.Flatness.StrangeFlatModules

/-!
# A finite flat nonprojective quotient

The data of a commutative ring `R` together with an ideal `I` for which `R ⧸ I` is a finite
flat `R`-module that is not projective.

Such an ideal is automatically pure, hence idempotent, and it cannot be finitely generated,
since a pure finitely generated ideal has projective quotient. A witness is the ideal of smooth
real functions vanishing near the origin.

## Main definitions

* `Stacks.Examples.FiniteFlatNonprojectiveQuotient`: the bundle of the ring, the ideal, and
  the finiteness, flatness, non-projectivity, non-finite-generation and idempotence
  properties.
* `Stacks.Examples.FiniteFlatNonprojectiveQuotient.baseScheme`: the affine scheme `Spec R`.

## Main results

* `Stacks.Examples.nonempty_finiteFlatNonprojectiveQuotient`: such a bundle exists in every
  universe.

## References

* [Stacks Project, Tag 05FY](https://stacks.math.columbia.edu/tag/05FY)
-/

@[expose] public section

namespace Stacks.Examples

open AlgebraicGeometry

universe u

/-- A commutative ring together with an ideal whose quotient is a finite flat but not
projective module, recording also that the ideal is not finitely generated and is
idempotent. -/
structure FiniteFlatNonprojectiveQuotient where
  /-- The ambient commutative ring. -/
  R : Type u
  [commRing : CommRing R]
  /-- The ideal whose quotient is finite, flat and not projective. -/
  I : Ideal R
  /-- The quotient is a finite module. -/
  finite : Module.Finite R (R ⧸ I)
  /-- The quotient is a flat module. -/
  flat : Module.Flat R (R ⧸ I)
  /-- The quotient is not a projective module. -/
  not_projective : ¬ Module.Projective R (R ⧸ I)
  /-- The ideal is not finitely generated. -/
  not_fg : ¬ I.FG
  /-- The ideal is idempotent. -/
  idempotent : I = I * I

attribute [instance] FiniteFlatNonprojectiveQuotient.commRing

namespace FiniteFlatNonprojectiveQuotient

/-- The affine scheme `Spec R` over which the example lives. -/
noncomputable abbrev baseScheme (D : FiniteFlatNonprojectiveQuotient.{u}) : Scheme.{u} :=
  Spec (.of D.R)

end FiniteFlatNonprojectiveQuotient

/-- The forward direction of the pair of mutually inverse ring homomorphisms underlying
`ULift.ringEquiv` on smooth functions. -/
private instance vanishNearZeroLiftRingHomInvPair :
    RingHomInvPair
      (ULift.ringEquiv : ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal ≃+*
        Stacks.FiniteFlatNotProjective.SmoothFunReal).toRingHom
      (RingEquiv.symm
        (ULift.ringEquiv : ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal ≃+*
          Stacks.FiniteFlatNotProjective.SmoothFunReal)).toRingHom :=
  RingHomInvPair.of_ringEquiv
    (ULift.ringEquiv : ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal ≃+*
      Stacks.FiniteFlatNotProjective.SmoothFunReal)

/-- The backward direction of that pair. -/
private instance vanishNearZeroLiftRingHomInvPair_symm :
    RingHomInvPair
      (RingEquiv.symm
        (ULift.ringEquiv : ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal ≃+*
          Stacks.FiniteFlatNotProjective.SmoothFunReal)).toRingHom
      (ULift.ringEquiv : ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal ≃+*
        Stacks.FiniteFlatNotProjective.SmoothFunReal).toRingHom :=
  RingHomInvPair.of_ringEquiv
    (ULift.ringEquiv : ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal ≃+*
      Stacks.FiniteFlatNotProjective.SmoothFunReal).symm

/-- The transported ideal maps onto the ideal of smooth functions vanishing near the origin. -/
private theorem map_vanishNearZeroLift :
    (vanishNearZeroLift.{u}).map
      (ULift.ringEquiv : ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal ≃+*
        Stacks.FiniteFlatNotProjective.SmoothFunReal).toRingHom =
      Stacks.FiniteFlatNotProjective.vanishNearZero := by
  let e : ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal ≃+*
    Stacks.FiniteFlatNotProjective.SmoothFunReal := ULift.ringEquiv
  exact (Ideal.map_comap_of_equiv e).trans (Ideal.comap_of_equiv e.symm)

/-- The quotient by the transported ideal is semilinearly equivalent, over
`ULift.ringEquiv`, to the quotient by the ideal of smooth functions vanishing near the
origin. -/
private noncomputable def vanishNearZeroLiftQuotientEquiv :
    ((ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal) ⧸ vanishNearZeroLift.{u})
      ≃ₛₗ[(ULift.ringEquiv : ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal ≃+*
          Stacks.FiniteFlatNotProjective.SmoothFunReal).toRingHom]
    Stacks.FiniteFlatNotProjective.SmoothFunReal ⧸
      Stacks.FiniteFlatNotProjective.vanishNearZero := by
  let e : ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal ≃+*
    Stacks.FiniteFlatNotProjective.SmoothFunReal := ULift.ringEquiv
  let q := Ideal.quotientEquiv _ Stacks.FiniteFlatNotProjective.vanishNearZero e
    map_vanishNearZeroLift.symm
  exact { q with map_smul' := fun a x => q.map_mul a x }

/-- The ideal of smooth functions vanishing near the origin is not finitely generated. -/
private theorem vanishNearZero_not_fg : ¬ Stacks.FiniteFlatNotProjective.vanishNearZero.FG := by
  intro hfg
  have hpair : Stacks.FiniteFlatNotProjective.vanishNearZero.IsPure ∧
    Stacks.FiniteFlatNotProjective.vanishNearZero.FG :=
    ⟨Stacks.FiniteFlatNotProjective.vanishNearZero_pure, hfg⟩
  exact Stacks.FiniteFlatNotProjective.quotientModule_not_projective
    (((pure_fg_tfae Stacks.FiniteFlatNotProjective.SmoothFunReal
      Stacks.FiniteFlatNotProjective.vanishNearZero).out 1 4).mp hpair)

/-- A finite flat nonprojective quotient exists, with its ideal non-finitely generated and
idempotent. -/
theorem nonempty_finiteFlatNonprojectiveQuotient :
    Nonempty FiniteFlatNonprojectiveQuotient.{u} := by
  let R : Type u := ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal
  let e : R ≃+* Stacks.FiniteFlatNotProjective.SmoothFunReal := ULift.ringEquiv
  let I : Ideal R := vanishNearZeroLift
  have hpure : I.Pure := vanishNearZeroLift_pure
  exact ⟨{
    R := R
    I := I
    finite := inferInstance
    flat := hpure
    not_projective := fun _ => Stacks.FiniteFlatNotProjective.quotientModule_not_projective
      (Module.Projective.of_equiv vanishNearZeroLiftQuotientEquiv)
    not_fg := fun hfg => vanishNearZero_not_fg (map_vanishNearZeroLift ▸ hfg.map e.toRingHom)
    idempotent := by simpa using I.inf_eq_mul_of_pure I }⟩

end Stacks.Examples
