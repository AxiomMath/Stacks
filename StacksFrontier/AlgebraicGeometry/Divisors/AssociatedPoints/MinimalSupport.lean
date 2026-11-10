module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Embedded
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociated

/-!
# Minimal points of the support are associated

A point of the support of a quasi-coherent module which is minimal there under specialization
is weakly associated to the module, and — on a locally Noetherian scheme — associated to it. In
particular the generic points of the irreducible components of a scheme are (weakly) associated
to its structure sheaf.

## Main results

* `AlgebraicGeometry.mem_supp_structureSheaf`: every point of a scheme lies in the support of
  its structure sheaf.
* `AlgebraicGeometry.mem_weaklyAssociatedPoints_of_mem_supp_of_specializes` and
  `AlgebraicGeometry.mem_associatedPoints_of_mem_supp_of_specialization`: the minimal-support
  assertions, for weakly associated and for associated points.
* `AlgebraicGeometry.mem_weaklyAssociatedPointsOfScheme_of_isGenericPoint_irreducibleComponent`
  and `AlgebraicGeometry.mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent`:
  their consequences for the generic points of the irreducible components of a scheme.

## Implementation notes

Support is the stalkwise support `SheafOfModules.supp`. Minimality is read through an affine open:
the prime corresponding to `x` is minimal in `Module.support Γ(X, U) Γ(F, U)`, and the
module-theoretic statement that a minimal point of the support is (weakly) associated then
applies. The specialization relation is Mathlib's `Specializes`.

## References

* [Stacks Project, Tag 05AH](https://stacks.math.columbia.edu/tag/05AH)
* [Stacks Project, Tag 05AQ](https://stacks.math.columbia.edu/tag/05AQ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Every point of a scheme lies in the support of its structure sheaf: the germ of `1` is
nonzero because the local ring is nontrivial. -/
theorem mem_supp_structureSheaf (X : Scheme.{u}) (x : X) :
    x ∈ SheafOfModules.supp (SheafOfModules.unit X.ringCatSheaf) := by
  rw [SheafOfModules.mem_supp_iff_nontrivial_stalk]
  let F := SheafOfModules.unit X.ringCatSheaf
  let P : TopCat.Presheaf Ab X := F.val.presheaf
  refine ⟨P.germ ⊤ x trivial (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤)), 0, ?_⟩
  intro hg
  obtain ⟨W, hxW, iWtop, iWbot, hsec⟩ :=
    P.germ_eq (U := ⊤) (V := ⊤) x trivial trivial
      (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤)) 0 (by simpa using hg)
  have hsecComm : X.presheaf.map iWtop.op (1 : X.presheaf.obj (Opposite.op ⊤)) = 0 := by
    change P.map iWtop.op (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤)) = 0
    simpa using hsec
  have hzero : (X.presheaf.germ ⊤ x trivial) 1 = 0 := by
    rw [← X.presheaf.germ_res iWtop x hxW]
    simpa using congrArg (X.presheaf.germ W x hxW) hsecComm
  simp only [map_one] at hzero
  exact one_ne_zero hzero

/-- Some affine open neighbourhood `U` of a point `x` of the support of `F` which is minimal
there under specialization is such that the prime of `Γ(X, U)` corresponding to `x` is minimal in
the support of the module of sections. -/
private theorem exists_affineOpen_minimal_mem_support_sections {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (x : X) (hx : x ∈ SheafOfModules.supp F)
    (hmin : ∀ y : X, y ∈ SheafOfModules.supp F → y ⤳ x → y = x) :
    ∃ (U : X.affineOpens) (hxU : x ∈ U.1),
      Minimal (· ∈ Module.support Γ(X, U.1) Γ(F, U.1)) (U.2.primeIdealOf ⟨x, hxU⟩) := by
  obtain ⟨W, hW, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) (by trivial)
  let U : X.affineOpens := ⟨W, hW⟩
  refine ⟨U, hxU, (Scheme.Modules.mem_support_sections_iff_mem_supp F U x hxU).2 hx,
    fun q hq hqp => ?_⟩
  let z : U.1 := U.2.isoSpec.inv q
  have hyU : (z : X) ∈ U.1 := z.2
  have hpy : U.2.primeIdealOf z = q := by
    change (U.2.isoSpec.inv ≫ U.2.isoSpec.hom) q = q
    rw [U.2.isoSpec.inv_hom_id]
    rfl
  have hy' : (z : X) ∈ SheafOfModules.supp F :=
    (AlgebraicGeometry.Scheme.Modules.mem_support_sections_iff_mem_supp F U z hyU).1
      (hpy ▸ hq)
  have hspec : (z : X) ⤳ x := by
    have hqp' : q ⤳ U.2.primeIdealOf ⟨x, hxU⟩ :=
      (PrimeSpectrum.le_iff_specializes q (U.2.primeIdealOf ⟨x, hxU⟩)).mp hqp
    have hmap := hqp'.map U.2.fromSpec.continuous
    rwa [U.2.fromSpec_primeIdealOf] at hmap
  have hzx : z = ⟨x, hxU⟩ := Subtype.ext (hmin _ hy' hspec)
  rw [show q = U.2.primeIdealOf ⟨x, hxU⟩ by simpa [hpy] using congrArg U.2.primeIdealOf hzx]

/-- **Stacks Project, Tag 05AQ.** A point of the support of a quasi-coherent module which is not
a specialization of another point of the support is weakly associated to the module. -/
@[stacks 05AQ "minimal point of the support"]
theorem mem_weaklyAssociatedPoints_of_mem_supp_of_specializes (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] (x : X) (hx : x ∈ SheafOfModules.supp F)
    (hmin : ∀ y : X, y ∈ SheafOfModules.supp F → Specializes y x → y = x) :
    x ∈ Stacks.Divisors.weaklyAssociatedPoints F := by
  obtain ⟨⟨W, hW⟩, hxW, hminp⟩ :=
    exists_affineOpen_minimal_mem_support_sections F x hx hmin
  exact (isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint F W hW x hxW).mp
    (Module.exists_mem_minimalPrimes_annihilator_span_singleton_of_minimal_mem_support hminp)

/-- **Stacks Project, Tag 05AQ.** Every generic point of an irreducible component of a scheme is
weakly associated to its structure sheaf. -/
@[stacks 05AQ "generic points of irreducible components"]
theorem mem_weaklyAssociatedPointsOfScheme_of_isGenericPoint_irreducibleComponent
    (X : Scheme.{u}) {Z : Set X} (hZ : Z ∈ irreducibleComponents X) {x : X}
    (hx : IsGenericPoint x Z) :
    x ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints X := by
  rw [Stacks.Divisors.mem_schemeWeaklyAssociatedPoints_iff]
  exact mem_weaklyAssociatedPoints_of_mem_supp_of_specializes X
    (SheafOfModules.unit X.ringCatSheaf) x (mem_supp_structureSheaf X x)
    fun y _ hyx => Topology.eq_of_specializes_isGenericPoint hZ hx hyx

/-- **Stacks Project, Tag 05AH.** A point of the support of a quasi-coherent module on a locally
Noetherian scheme which is not a specialization of another point of the support is associated to
the module. -/
@[stacks 05AH "minimal point of the support"]
theorem mem_associatedPoints_of_mem_supp_of_specialization (X : Scheme.{u})
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsQuasicoherent] (x : X)
    (hx : x ∈ SheafOfModules.supp F)
    (hmin : ∀ y : X, y ∈ SheafOfModules.supp F → y ⤳ x → y = x) :
    x ∈ Stacks.Divisors.associatedPoints F := by
  rw [Stacks.Divisors.mem_associatedPoints_iff]
  obtain ⟨⟨W, hW⟩, hxW, hminp⟩ := exists_affineOpen_minimal_mem_support_sections F x hx hmin
  have hnoeth : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hstack : IsAssociatedPrimeStacks Γ(X, W) Γ(F, W)
      (hW.primeIdealOf ⟨x, hxW⟩).asIdeal := by
    change (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.IsPrime ∧ ∃ m : Γ(F, W),
      (⊥ : Submodule Γ(X, W) Γ(F, W)).colon (Submodule.span Γ(X, W) {m}) =
        (hW.primeIdealOf ⟨x, hxW⟩).asIdeal
    obtain ⟨hprime, m, hm⟩ := isAssociatedPrime_iff.mp
      (show IsAssociatedPrime (hW.primeIdealOf ⟨x, hxW⟩).asIdeal Γ(F, W) from
        Module.mem_associatedPrimes_of_minimal_mem_support hminp)
    exact ⟨hprime, m, by simpa using hm.symm⟩
  exact isAssociatedPoint_of_isAssociatedPrime_sections F W hW hxW hstack

/-- **Stacks Project, Tag 05AH.** Every generic point of an irreducible component of a locally
Noetherian scheme is an associated point of the scheme. -/
@[stacks 05AH "generic points of irreducible components"]
theorem mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent (X : Scheme.{u})
    [IsLocallyNoetherian X] {Z : Set X} (hZ : Z ∈ irreducibleComponents X) {x : X}
    (hx : IsGenericPoint x Z) :
    x ∈ Stacks.Divisors.schemeAssociatedPoints X := by
  rw [Stacks.Divisors.mem_schemeAssociatedPoints_iff]
  exact mem_associatedPoints_of_mem_supp_of_specialization X
    (SheafOfModules.unit X.ringCatSheaf) x (mem_supp_structureSheaf X x)
    fun y _ hyx => Topology.eq_of_specializes_isGenericPoint hZ hx hyx

end AlgebraicGeometry
