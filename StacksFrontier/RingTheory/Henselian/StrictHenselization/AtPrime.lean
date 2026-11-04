module

public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.HenselizationTower
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.HenselizationUniverse.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The strict henselization of a ring at a prime

For a commutative ring `C` and a prime `p ⊆ C`, the *strict henselization of `C` at `p`* is a
strict henselization `C^sh_p` of the local ring `C_p`, regarded as a `C`-algebra through
`C → C_p → C^sh_p`. As a `C`-algebra it is a filtered colimit of étale `C`-algebras.

## Main definitions

* `StacksDraft.strictHenselizationAtPrime`: the chosen strict henselization `C^sh_p` of `C` at
  `p`, together with its `C`-algebra structure. The separable closure of `κ(p)` used is the
  absolute one, `SeparableClosure (κ(p))`.

## Main results

* `StacksDraft.indEtale_of_isHenselization_atPrime`: a henselization of the local ring at a prime
  is ind-étale over the ring itself, for an arbitrary residue-field extension `L` of `κ(p)`:
  `L = κ(p)` gives the henselization and `L` a separable closure the strict henselization.
* `StacksDraft.indEtale_strictHenselizationAtPrime`: the colimit presentation for the chosen
  `C^sh_p`.
* `StacksDraft.indEtale_tensorProduct_strictHenselizationAtPrime`: the same presentation after
  base change, `A ⊗[C] C^sh_p` as a filtered colimit of the `A ⊗[C] C_i`.
* `StacksDraft.indEtale_iff_ind_underMk`: the colimit presentation of an ind-étale `C`-algebra `B`
  in the shape `ObjectProperty.ind CommRingCat.etale.underObj (Under.mk (algebraMap C B))`.
* `StacksDraft.flat_of_indEtale`: an ind-étale algebra is flat, with the base and the algebra in
  independent universes.
* `StacksDraft.under_maximalIdeal_strictHenselizationAtPrime`: the closed point of `C^sh_p` lies
  over `p`.

## References

* [Stacks Project, Tag 04GP](https://stacks.math.columbia.edu/tag/04GP)
* [Stacks Project, Tag 04GU](https://stacks.math.columbia.edu/tag/04GU)
* [Stacks Project, Tag 0BSI](https://stacks.math.columbia.edu/tag/0BSI)
* [Stacks Project, Tag 00QP](https://stacks.math.columbia.edu/tag/00QP)

## Tags

strict henselization, prime ideal, ind-étale, filtered colimit, étale neighbourhood
-/

@[expose] public section

open CategoryTheory IsLocalRing
open scoped TensorProduct

universe u v w

namespace StacksDraft

/-- An ind-étale algebra is flat. -/
theorem flat_of_indEtale {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (h : IndEtale A B) : Module.Flat A B :=
  have : Module.Flat A (ULift.{u} B) := CommAlgCat.flat_of_ind_etale h
  Module.Flat.of_linearEquiv (ULift.algEquiv : ULift.{u} B ≃ₐ[A] B).symm.toLinearEquiv

/-- The colimit presentation of an ind-étale algebra in the `Under` form: `B` is ind-étale over `C`
exactly when the object `Under.mk (algebraMap C B)` of `Under (CommRingCat.of C)` is a filtered
colimit of objects whose structure map is étale. -/
theorem indEtale_iff_ind_underMk {C B : Type u} [CommRing C] [CommRing B] [Algebra C B] :
    IndEtale C B ↔ ObjectProperty.ind.{u} (CommRingCat.etale.{u}).underObj
      (Under.mk (CommRingCat.ofHom (algebraMap C B))) := by
  rw [indEtale_iff, CommAlgCat.ind_etale_iff_ind_algebraMap,
    MorphismProperty.ind_iff_ind_underMk]

section Abstract

variable {C : Type u} (Cp : Type v) {Ch : Type w}
  [CommRing C] (p : Ideal C) [p.IsPrime]
  [CommRing Cp] [IsLocalRing Cp] [Algebra C Cp] [IsLocalization.AtPrime Cp p]
  (L : Type*) [Field L] [Algebra (ResidueField Cp) L]
  [CommRing Ch] [IsLocalRing Ch] [Algebra Cp Ch] [Algebra C Ch]
  [IsScalarTower C Cp Ch] [IsHenselization Cp L Ch]

include Cp p L in
/-- A henselization of the local ring at a prime is a filtered colimit of étale algebras over the
ring itself. For `L` a separable closure of `κ(p)` this is the strict henselization of `C` at `p`,
and for `L = κ(p)` the henselization. -/
theorem indEtale_of_isHenselization_atPrime : IndEtale C Ch :=
  indEtale_comp (indEtale_atPrime (B := Cp) p)
    (indEtale_of_isHenselization (R := Cp) L (Rh := Ch))

include Cp p L in
/-- A henselization of the local ring at a prime is flat over the ring itself. -/
theorem flat_of_isHenselization_atPrime : Module.Flat C Ch :=
  flat_of_indEtale (indEtale_of_isHenselization_atPrime Cp p L)

include Cp p L in
/-- The closed point of a henselization of `C_p` lies over `p`. -/
theorem under_maximalIdeal_of_isHenselization_atPrime :
    (maximalIdeal Ch).under C = p := by
  have : IsLocalHom (algebraMap Cp Ch) :=
    IsHenselization.isLocalHom (R := Cp) (L := L) (Rh := Ch)
  have hcomp : (maximalIdeal Ch).comap (algebraMap C Ch) =
      ((maximalIdeal Ch).comap (algebraMap Cp Ch)).comap (algebraMap C Cp) := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  rw [Ideal.under, hcomp, maximalIdeal_comap]
  exact IsLocalization.AtPrime.under_maximalIdeal Cp p

end Abstract

section Chosen

variable (C : Type u) [CommRing C] (p : Ideal C) [p.IsPrime]

/-- The chosen henselization tower of the local ring `C_p`, taken with respect to the absolute
separable closure of the residue field `κ(p)`. -/
noncomputable def henselizationTowerAtPrime :
    HenselizationTower (Localization.AtPrime p)
      (SeparableClosure (ResidueField (Localization.AtPrime p))) :=
  henselizationTower _ _

/-- The strict henselization of `C` at the prime `p`: the strict henselization of the local ring
`C_p` with respect to the absolute separable closure of `κ(p)`, carrying the `C`-algebra structure
of the composite `C → C_p → C^sh_p`. -/
@[ega "IV 18.8.7" "special case"]
noncomputable def strictHenselizationAtPrime : Type u :=
  (henselizationTowerAtPrime C p).strictHenselization

/-- The ring structure on `C^sh_p`. -/
noncomputable instance instCommRingStrictHenselizationAtPrime :
    CommRing (strictHenselizationAtPrime C p) :=
  inferInstanceAs (CommRing (henselizationTowerAtPrime C p).strictHenselization)

/-- `C^sh_p` is a local ring. -/
instance instIsLocalRingStrictHenselizationAtPrime :
    IsLocalRing (strictHenselizationAtPrime C p) :=
  inferInstanceAs (IsLocalRing (henselizationTowerAtPrime C p).strictHenselization)

/-- `C^sh_p` is strictly henselian. -/
@[ega "IV 18.8.8" "(i)", sga "4 VIII 4.4" "more general"]
instance instStrictlyHenselianLocalRingStrictHenselizationAtPrime :
    StrictlyHenselianLocalRing (strictHenselizationAtPrime C p) :=
  inferInstanceAs
    (StrictlyHenselianLocalRing (henselizationTowerAtPrime C p).strictHenselization)

/-- `C^sh_p` is an algebra over the local ring `C_p`. -/
noncomputable instance instAlgebraLocalizationStrictHenselizationAtPrime :
    Algebra (Localization.AtPrime p) (strictHenselizationAtPrime C p) :=
  inferInstanceAs
    (Algebra (Localization.AtPrime p) (henselizationTowerAtPrime C p).strictHenselization)

/-- `C^sh_p` is a strict henselization of `C_p`: it is henselian, it is a filtered colimit of
étale `C_p`-algebras, and its residue field is the chosen separable closure of `κ(p)`. -/
instance instIsHenselizationStrictHenselizationAtPrime :
    IsHenselization (Localization.AtPrime p)
      (SeparableClosure (ResidueField (Localization.AtPrime p)))
      (strictHenselizationAtPrime C p) :=
  inferInstanceAs (IsHenselization (Localization.AtPrime p)
    (SeparableClosure (ResidueField (Localization.AtPrime p)))
    (henselizationTowerAtPrime C p).strictHenselization)

/-- The `C`-algebra structure on `C^sh_p` is the composite `C → C_p → C^sh_p`. -/
noncomputable instance instAlgebraStrictHenselizationAtPrime :
    Algebra C (strictHenselizationAtPrime C p) :=
  ((algebraMap (Localization.AtPrime p) (strictHenselizationAtPrime C p)).comp
    (algebraMap C (Localization.AtPrime p))).toAlgebra

/-- The structure map `C → C^sh_p` factors through `C_p`. -/
instance instIsScalarTowerStrictHenselizationAtPrime :
    IsScalarTower C (Localization.AtPrime p) (strictHenselizationAtPrime C p) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The strict henselization of `C` at `p` is a filtered colimit of étale `C`-algebras. -/
theorem indEtale_strictHenselizationAtPrime : IndEtale C (strictHenselizationAtPrime C p) :=
  indEtale_of_isHenselization_atPrime (Localization.AtPrime p) p
    (SeparableClosure (ResidueField (Localization.AtPrime p)))

/-- `C^sh_p` is flat over `C`. -/
@[sga "4 VIII 4.4" "more general"]
instance instFlatStrictHenselizationAtPrime :
    Module.Flat C (strictHenselizationAtPrime C p) :=
  flat_of_indEtale (indEtale_strictHenselizationAtPrime C p)

/-- The base change `A ⊗[C] C^sh_p` of `C^sh_p` along `C → A` is a filtered colimit of étale
`A`-algebras. -/
theorem indEtale_tensorProduct_strictHenselizationAtPrime (A : Type w) [CommRing A]
    [Algebra C A] : IndEtale A (A ⊗[C] strictHenselizationAtPrime C p) :=
  indEtale_tensorProduct A (indEtale_strictHenselizationAtPrime C p)

/-- The closed point of `C^sh_p` lies over `p`. -/
theorem under_maximalIdeal_strictHenselizationAtPrime :
    (maximalIdeal (strictHenselizationAtPrime C p)).under C = p :=
  under_maximalIdeal_of_isHenselization_atPrime (Localization.AtPrime p) p
    (SeparableClosure (ResidueField (Localization.AtPrime p)))

end Chosen

end StacksDraft

end
