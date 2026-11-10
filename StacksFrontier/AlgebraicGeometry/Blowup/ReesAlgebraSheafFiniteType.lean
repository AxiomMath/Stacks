module

public import StacksFrontier.AlgebraicGeometry.Blowup.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraTotalModule
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSituationComparison
public import StacksFrontier.AlgebraicGeometry.Constructions.DirectSumQuasiCompactSections
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubalgebra.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Rees algebra sheaf of a finitely generated ideal sheaf is of finite type

Let `X` be a scheme and `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals whose ideal of sections over
every affine open is finitely generated. The Rees algebra
`⨁_{n ≥ 0} ℐⁿ = Stacks.Blowup.reesAlgebraSheaf ℐ` is an algebra sheaf of finite type in the sense
of `Stacks.RelativeSpec.AlgebraSheaf.IsFiniteType`: the structural ring map
`Γ(X, U) ⟶ Γ(U, ⨁ₙ ℐⁿ)` is of finite type over every affine open `U`.

Over an affine open `U` the ring of sections of the Rees algebra sheaf is the ordinary Rees
algebra `reesAlgebra ℐ(U) ⊆ Γ(X, U)[t]`. The `ℕ`-indexed graded section ring
`Stacks.RelativeProj.Situation.sectionRing` of a relative `Proj` situation agrees with the
`ℤ`-indexed ungraded realization `Stacks.GradedAlgebra.Total`, since the negative pieces of a
relative `Proj` situation are zero.

## Main definitions

* `Stacks.RelativeProj.Situation.sectionRingTotalEquiv`: the `ℕ`-indexed graded section ring of
  a relative `Proj` situation over an open is the `ℤ`-indexed ungraded realization there, as a
  ring isomorphism.
* `Stacks.Blowup.ReesModel.totalSectionsEquiv` and `Stacks.Blowup.reesSectionsRingEquiv`:
  `Γ(U, ⨁ₙ ℐⁿ)` is the ordinary Rees algebra `reesAlgebra ℐ(U)` over an affine open `U`.

## Main results

* `Stacks.Blowup.reesSectionsRingEquiv_algebraMap`: the identification carries `algebraMap` to the
  structural ring map of the algebra sheaf.
* `Stacks.Blowup.isFiniteType_reesAlgebraSheaf`: the Rees algebra sheaf of an ideal sheaf whose
  sections over every affine open are finitely generated is an algebra sheaf of finite type.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u}) (U : s.base.Opens)

/-- A homogeneous local section of degree `n : ℕ`, read in the `ℤ`-indexed ungraded realization:
`Stacks.GradedAlgebra.incl` at the degree `(n : ℤ)`, as an additive map. -/
def inclTotal (n : ℕ) :
    s.sectionPieces U n →+ s.algebra.toPresheafGradedAlgebra.Total (op U) where
  toFun x := s.algebra.toPresheafGradedAlgebra.incl (n : ℤ) x
  map_zero' := s.algebra.toPresheafGradedAlgebra.incl_zero (n : ℤ)
  map_add' := s.algebra.toPresheafGradedAlgebra.incl_add (n : ℤ)

/-- The comparison of the `ℕ`-indexed graded section ring with the `ℤ`-indexed ungraded
realization, as a ring homomorphism: the degree-`n` piece goes to integer degree `n`. -/
def sectionRingToTotal :
    s.sectionRing U →+* s.algebra.toPresheafGradedAlgebra.Total (op U) :=
  DirectSum.toSemiring (inclTotal s U)
    (by
      change s.algebra.toPresheafGradedAlgebra.incl 0
        (GradedMonoid.GOne.one : s.sectionPieces U 0) = 1
      rw [gradedOne_eq_algebraOne s U]
      exact (s.algebra.toPresheafGradedAlgebra.one_eq_incl (op U)).symm)
    (fun {n p} a b => by
      change s.algebra.toPresheafGradedAlgebra.incl ((n + p : ℕ) : ℤ)
          (GradedMonoid.GMul.mul a b) =
        s.algebra.toPresheafGradedAlgebra.incl (n : ℤ) a *
          s.algebra.toPresheafGradedAlgebra.incl (p : ℤ) b
      rw [gradedMul_eq_algebraMul s U n p a b]
      exact (s.algebra.toPresheafGradedAlgebra.incl_mul_incl (n : ℤ) (p : ℤ) a b).symm)

/-- The comparison on a homogeneous section. -/
theorem sectionRingToTotal_of (n : ℕ) (a : s.sectionPieces U n) :
    sectionRingToTotal s U (DirectSum.of (s.sectionPieces U) n a) =
      s.algebra.toPresheafGradedAlgebra.incl (n : ℤ) a :=
  DirectSum.toSemiring_of (inclTotal s U) _ _ n a

/-- The comparison is the inclusion of the nonnegative degrees of the direct sum of the
homogeneous pieces. -/
theorem sectionRingToTotal_eq (z : s.sectionRing U) :
    sectionRingToTotal s U z =
      Stacks.directSumNatToIntApp (fun i : ℤ => (s.algebra.piece i).val) (op U) z := by
  induction z using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]; rfl
  | of n a =>
      rw [sectionRingToTotal_of,
        Stacks.directSumNatToIntApp_of (fun i : ℤ => (s.algebra.piece i).val) (op U) n a]
      rfl
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']; rfl

/-- The comparison of the `ℕ`-indexed graded section ring with the `ℤ`-indexed ungraded
realization is bijective. -/
theorem bijective_sectionRingToTotal : Function.Bijective (sectionRingToTotal s U) :=
  (funext (sectionRingToTotal_eq s U)) ▸
    Stacks.bijective_directSumNatToIntApp (fun i : ℤ => (s.algebra.piece i).val) (op U)
      fun n hn => Stacks.subsingleton_of_isZero (s.negative_isZero n hn) (op U)

/-- The `ℕ`-indexed graded section ring of a relative `Proj` situation over an open is the
`ℤ`-indexed ungraded realization there. -/
def sectionRingTotalEquiv :
    s.sectionRing U ≃+* s.algebra.toPresheafGradedAlgebra.Total (op U) :=
  RingEquiv.ofBijective (sectionRingToTotal s U) (bijective_sectionRingToTotal s U)

/-- The comparison carries the canonical map from the structure sheaf to the structure map
`r ↦ r • 1` of the ungraded realization. -/
theorem sectionRingTotalEquiv_baseMap (r : s.base.ringCatSheaf.obj.obj (op U)) :
    sectionRingTotalEquiv s U (s.sectionRingBaseMap U r) =
      s.algebra.toPresheafGradedAlgebra.structureMap (op U) r := by
  change sectionRingToTotal s U (s.sectionRingBaseMap U r) = _
  rw [sectionRingBaseMap_eq_of_smul_one s U r,
    sectionRingToTotal_of s U 0 (r • s.algebra.one.eval (op U))]
  exact (s.algebra.toPresheafGradedAlgebra.incl_smul _ r _).trans
    (congrArg (fun z => r • z)
      (s.algebra.toPresheafGradedAlgebra.one_eq_incl (op U)).symm)

end Stacks.RelativeProj.Situation

open Stacks.RelativeProj Stacks.RelativeSpec

namespace Stacks.Blowup

/-- The comparison of the graded section ring of the chosen Rees algebra with the ordinary Rees
algebra carries the canonical map from the structure sheaf to `algebraMap`. -/
theorem reesSectionRingEquiv_baseMap {X : Scheme.{u}} (J : X.IdealSheafData)
    (U : X.affineOpens) (r : X.ringCatSheaf.obj.obj (op U.1)) :
    AlgebraicGeometry.reesSectionRingEquiv J U
        ((AlgebraicGeometry.reesSituation J).sectionRingBaseMap U.1 r) =
      algebraMap Γ(X, U.1) ↥(reesAlgebra (J.ideal U)) r :=
  Subtype.ext (AlgebraicGeometry.coe_reesSectionGradedHom_baseMap J U r)

/-- The sections of the ungraded realization of a Rees model over an affine open are the
ordinary Rees algebra of the ideal there. -/
def ReesModel.totalSectionsEquiv {s : Situation.{u}} {J : s.base.IdealSheafData}
    (m : ReesModel s J) (U : s.base.affineOpens) :
    ↥(reesAlgebra (J.ideal U)) ≃+*
      ((s.algebra.toPresheafGradedAlgebra.totalSheaf
        (Opens.grothendieckTopology (s.base : TopCat))).obj.obj (op U.1)) :=
  (AlgebraicGeometry.reesSectionRingEquiv J U).symm.trans
    ((m.sectionRingEquiv U).symm.trans
      ((Situation.sectionRingTotalEquiv s U.1).trans
        (Stacks.RelativeSpec.totalSectionsRingEquiv s.base s.algebra s.mul_comm U.2)))

/-- The identification `Stacks.Blowup.ReesModel.totalSectionsEquiv` carries `algebraMap` to the
structural ring map of the ungraded realization. -/
theorem ReesModel.totalSectionsEquiv_algebraMap {s : Situation.{u}}
    {J : s.base.IdealSheafData} (m : ReesModel s J) (U : s.base.affineOpens)
    (r : Γ(s.base, U.1)) :
    m.totalSectionsEquiv U (algebraMap Γ(s.base, U.1) ↥(reesAlgebra (J.ideal U)) r) =
      s.algebra.toPresheafGradedAlgebra.totalUnit
        (Opens.grothendieckTopology (s.base : TopCat)) (op U.1)
        (s.algebra.toPresheafGradedAlgebra.structureMap (op U.1) r) := by
  have h1 : (AlgebraicGeometry.reesSectionRingEquiv J U).symm
      (algebraMap Γ(s.base, U.1) ↥(reesAlgebra (J.ideal U)) r) =
      (AlgebraicGeometry.reesSituation J).sectionRingBaseMap U.1 r := by
    rw [← reesSectionRingEquiv_baseMap J U r, RingEquiv.symm_apply_apply]
  have h2 : (m.sectionRingEquiv U).symm
      ((AlgebraicGeometry.reesSituation J).sectionRingBaseMap U.1 r) =
      s.sectionRingBaseMap U.1 r := by
    rw [← m.sectionHom_sectionRingBaseMap U r]
    exact (m.sectionRingEquiv U).symm_apply_apply _
  change Stacks.RelativeSpec.totalSectionsRingEquiv s.base s.algebra s.mul_comm U.2
      (Situation.sectionRingTotalEquiv s U.1 ((m.sectionRingEquiv U).symm
        ((AlgebraicGeometry.reesSectionRingEquiv J U).symm
          (algebraMap Γ(s.base, U.1) ↥(reesAlgebra (J.ideal U)) r)))) = _
  rw [h1, h2, Situation.sectionRingTotalEquiv_baseMap s U.1 r]
  rfl

/-- `Γ(U, ⨁ₙ ℐⁿ)` is the ordinary Rees algebra of `ℐ(U)` over an affine open `U`, as a ring
isomorphism onto the sections of the algebra sheaf `Stacks.Blowup.reesAlgebraSheaf`. -/
def reesSectionsRingEquiv {X : Scheme.{u}} (J : X.IdealSheafData) (U : X.affineOpens) :
    ↥(reesAlgebra (J.ideal U)) ≃+* AlgebraSheaf.sections (reesAlgebraSheaf J) U.1 :=
  (reesSituationModel J).totalSectionsEquiv U

/-- The identification of `Γ(U, ⨁ₙ ℐⁿ)` with `reesAlgebra ℐ(U)` carries `algebraMap` to the
structural ring map of the algebra sheaf. -/
theorem reesSectionsRingEquiv_algebraMap {X : Scheme.{u}} (J : X.IdealSheafData)
    (U : X.affineOpens) (r : Γ(X, U.1)) :
    reesSectionsRingEquiv J U (algebraMap Γ(X, U.1) ↥(reesAlgebra (J.ideal U)) r) =
      ((reesAlgebraSheaf J).hom.hom.app (op U.1)).hom r :=
  (reesSituationModel J).totalSectionsEquiv_algebraMap U r

/-- The Rees algebra sheaf of an ideal sheaf whose sections over every affine open are finitely
generated is an algebra sheaf of finite type. -/
theorem isFiniteType_reesAlgebraSheaf {X : Scheme.{u}} (J : X.IdealSheafData)
    (hfg : ∀ U : X.affineOpens, (J.ideal U).FG) :
    AlgebraSheaf.IsFiniteType (reesAlgebraSheaf J) := by
  intro U hU
  have halg : RingHom.FiniteType
      (algebraMap Γ(X, U) ↥(reesAlgebra (J.ideal ⟨U, hU⟩))) :=
    RingHom.finiteType_algebraMap.2 (finiteType_reesAlgebra_of_fg _ (hfg ⟨U, hU⟩))
  have htr := RingHom.finiteType_respectsIso.1 _ (reesSectionsRingEquiv J ⟨U, hU⟩) halg
  refine (show (reesSectionsRingEquiv J ⟨U, hU⟩).toRingHom.comp
    (algebraMap Γ(X, U) ↥(reesAlgebra (J.ideal ⟨U, hU⟩))) =
      ((reesAlgebraSheaf J).hom.hom.app (op U)).hom from ?_) ▸ htr
  exact RingHom.ext fun r => reesSectionsRingEquiv_algebraMap J ⟨U, hU⟩ r

/-- The Rees algebra sheaf of an ideal sheaf on a locally Noetherian scheme is of finite
type. -/
@[ega "IV 19.4.10" "more general"]
theorem isFiniteType_reesAlgebraSheaf_of_isLocallyNoetherian {X : Scheme.{u}}
    [IsLocallyNoetherian X] (J : X.IdealSheafData) :
    AlgebraSheaf.IsFiniteType (reesAlgebraSheaf J) :=
  isFiniteType_reesAlgebraSheaf J fun U =>
    have := IsLocallyNoetherian.component_noetherian (X := X) U
    IsNoetherian.noetherian (J.ideal U)

end Stacks.Blowup

end
