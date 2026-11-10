module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.StructureSheaf
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.PowerSeries.Inverse
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.MinimalSupport
public import StacksFrontier.AlgebraicGeometry.Flatness.Impurity.HenselizationAscent
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange
public import StacksFrontier.Topology.OpensMapFinal
import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Rank
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

/-!
# A module of finite presentation which is pure but not universally pure

There is a morphism of affine schemes of finite presentation together with a finitely presented
module on its source which is pure relative to the base but not universally pure relative to it.

Let `K = k(y)` be a rational function field and let `R = k + x K[[x]]` be the subring of `K[[x]]`
of power series whose constant coefficient lies in `k`. The ring `R` is local and henselian, it
is a domain, and its only primes are `(0)` and its maximal ideal. The example is the structure
sheaf of `X = Spec A` for the finitely presented `R`-algebra `A = R[t]/(xt - xy)`, over
`S = Spec R`.

Purity holds because `R` is henselian, so an impurity over an elementary étale neighbourhood of
a point of `S` is an impurity over the henselization: over the maximal ideal the henselization
is `S` itself, and every point of `X` specializes into the closed fibre; over the generic point
`x` becomes invertible, so the base change of `X` is an isomorphism. Universal purity fails
after the base change to `Spec O` with `O = R[c]/(xc - xy⁻¹)`: evaluating `t ↦ y` and
`c ↦ y⁻¹` in `K[[x]]` gives a point of `X ×_S Spec O` in the relative assassin whose closure
lies in the locus `ct = 1` and therefore misses the fibre over the point of `Spec O` at which
`c` vanishes.

## Main results

* `Stacks.Examples.exists_isPureRelative_not_isUniversallyPureRelative`: there is a morphism of
  affine schemes of finite presentation and a finitely presented module on its source which is
  pure but not universally pure relative to the base.

## References

* [Stacks Project, Tag 05JK](https://stacks.math.columbia.edu/tag/05JK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Examples

open IsLocalRing

/-- A subring of a henselian local ring which contains the maximal ideal and is local with a
local inclusion is itself henselian. -/
private theorem henselianLocalRing_subring_of_maximalIdeal_le
    {A : Type*} [CommRing A] [HenselianLocalRing A]
    (S : Subring A) [IsLocalRing S] [IsLocalHom S.subtype]
    (hS : (maximalIdeal A : Set A) ⊆ S) : HenselianLocalRing S := by
  constructor
  intro f hf a₀ ha₀ ha₀'
  have hmem : S.subtype (f.eval a₀) ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_nonunits_iff] at ha₀ ⊢
    exact fun h => ha₀ (IsLocalHom.map_nonunit _ h)
  obtain ⟨a, ha, hdiff⟩ := HenselianLocalRing.is_henselian
    (f.map S.subtype) (hf.map S.subtype) (a₀ : A) (by
      rw [Polynomial.eval_map]
      change Polynomial.eval₂ S.subtype (S.subtype a₀) f ∈ _
      rw [Polynomial.eval₂_at_apply]
      exact hmem) (by
      rw [Polynomial.derivative_map, Polynomial.eval_map]
      change IsUnit (Polynomial.eval₂ S.subtype (S.subtype a₀) f.derivative)
      rw [Polynomial.eval₂_at_apply]
      exact ha₀'.map S.subtype)
  have haS : a ∈ S := by
    convert S.add_mem (hS hdiff) a₀.property using 1
    exact (sub_add_cancel a a₀).symm
  refine ⟨⟨a, haS⟩, ?_, ?_⟩
  · change f.eval ⟨a, haS⟩ = 0
    apply Subtype.val_injective
    change S.subtype (f.eval ⟨a, haS⟩) = 0
    rw [← Polynomial.eval₂_at_apply]
    change Polynomial.eval₂ S.subtype a f = 0
    simpa only [Polynomial.IsRoot, Polynomial.eval_map] using ha
  · change (⟨a, haS⟩ : S) - a₀ ∈ maximalIdeal S
    rw [mem_maximalIdeal, mem_nonunits_iff] at hdiff ⊢
    exact fun hu => hdiff (hu.map S.subtype)

/-- The subring `k + x K[[x]]` of power series whose constant coefficient lies in a subfield. -/
private noncomputable abbrev constantCoeffSubring {K : Type*} [Field K] (k : Subfield K) :
    Subring (PowerSeries K) := k.toSubring.comap PowerSeries.constantCoeff

/-- An element of `k + x K[[x]]` is a unit exactly when its constant coefficient is nonzero. -/
private theorem constantCoeffSubring_isUnit_iff {K : Type*} [Field K]
    (k : Subfield K) (f : constantCoeffSubring k) :
    IsUnit f ↔ PowerSeries.constantCoeff f.val ≠ 0 := by
  constructor
  · intro h
    exact isUnit_iff_ne_zero.mp ((h.map (constantCoeffSubring k).subtype).map
      PowerSeries.constantCoeff)
  · intro h
    refine isUnit_iff_exists_inv.mpr ⟨⟨f.val⁻¹, ?_⟩, ?_⟩
    · change PowerSeries.constantCoeff f.val⁻¹ ∈ k
      rw [PowerSeries.constantCoeff_inv]
      exact k.inv_mem f.property
    · exact Subtype.ext (PowerSeries.mul_inv_cancel f.val h)

/-- The ring `k + x K[[x]]` is local. -/
private theorem constantCoeffSubring_isLocalRing {K : Type*} [Field K]
    (k : Subfield K) : IsLocalRing (constantCoeffSubring k) := by
  apply Subring.isLocalRing_of_unit
  intro f hf hu
  exact (constantCoeffSubring_isUnit_iff k ⟨f, hf⟩).mpr
    (isUnit_iff_ne_zero.mp (hu.map PowerSeries.constantCoeff))

/-- The ring `k + x K[[x]]` is henselian: it contains the maximal ideal of the complete local
ring `K[[x]]`. -/
private theorem constantCoeffSubring_isHenselian {K : Type*} [Field K]
    (k : Subfield K) : HenselianLocalRing (constantCoeffSubring k) := by
  let := constantCoeffSubring_isLocalRing k
  let : IsLocalHom (constantCoeffSubring k).subtype := ⟨fun f hf =>
    (constantCoeffSubring_isUnit_iff k f).mpr
      (isUnit_iff_ne_zero.mp (hf.map PowerSeries.constantCoeff))⟩
  let : IsAdicComplete (maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  let := henselianLocalRing_of_isAdicComplete_maximalIdeal (PowerSeries K)
  apply henselianLocalRing_subring_of_maximalIdeal_le
  intro f hf
  change PowerSeries.constantCoeff f ∈ k
  change f ∈ maximalIdeal (PowerSeries K) at hf
  have hzero : PowerSeries.constantCoeff f = 0 := by
    simpa only [mem_maximalIdeal, mem_nonunits_iff,
      PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not] using hf
  exact hzero ▸ k.zero_mem

/-- The element `x` of `k + x K[[x]]`. -/
private noncomputable abbrev constantCoeffSubringX {K : Type*} [Field K] (k : Subfield K) :
    constantCoeffSubring k :=
  ⟨PowerSeries.X, by change PowerSeries.constantCoeff PowerSeries.X ∈ k; simp⟩

/-- Every nonzero element of `k + x K[[x]]` divides a power of `x`. -/
private theorem constantCoeffSubring_dvd_X_pow {K : Type*} [Field K]
    (k : Subfield K) {f : constantCoeffSubring k} (hf : f ≠ 0) :
    ∃ n : ℕ, f ∣ constantCoeffSubringX k ^ n := by
  have hf' : f.val ≠ 0 := fun h => hf (Subtype.ext h)
  let u := f.val.divXPowOrder
  have hu : PowerSeries.constantCoeff u ≠ 0 :=
    mt PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.mp hf'
  let g : constantCoeffSubring k := ⟨PowerSeries.X * u⁻¹, by
    change PowerSeries.constantCoeff (PowerSeries.X * u⁻¹) ∈ k
    simp⟩
  refine ⟨f.val.order.toNat + 1, g, ?_⟩
  apply Subtype.ext
  change PowerSeries.X ^ (f.val.order.toNat + 1) = f.val * (PowerSeries.X * u⁻¹)
  calc
    PowerSeries.X ^ (f.val.order.toNat + 1) =
        PowerSeries.X ^ f.val.order.toNat * (u * u⁻¹) * PowerSeries.X := by
      rw [PowerSeries.mul_inv_cancel u hu, mul_one, pow_succ]
    _ = (PowerSeries.X ^ f.val.order.toNat * u) * (PowerSeries.X * u⁻¹) := by ring
    _ = f.val * (PowerSeries.X * u⁻¹) := by
      rw [PowerSeries.X_pow_order_mul_divXPowOrder]

/-- In `k + x K[[x]]`, the element `x` divides the square of any element of the maximal ideal. -/
private theorem constantCoeffSubring_X_dvd_sq {K : Type*} [Field K]
    (k : Subfield K) {f : constantCoeffSubring k} (hf : PowerSeries.constantCoeff f.val = 0) :
    constantCoeffSubringX k ∣ f ^ 2 := by
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr hf
  refine ⟨⟨PowerSeries.X * g ^ 2, ?_⟩, ?_⟩
  · change PowerSeries.constantCoeff (PowerSeries.X * g ^ 2) ∈ k
    simp
  · apply Subtype.ext
    change f.val ^ 2 = PowerSeries.X * (PowerSeries.X * g ^ 2)
    rw [hg]
    ring

/-- The spectrum of `k + x K[[x]]` has exactly two points: the primes are the zero ideal and the
maximal ideal. -/
private theorem constantCoeffSubring_prime_eq_bot_or_maximal {K : Type*} [Field K]
    (k : Subfield K) (p : Ideal (constantCoeffSubring k)) [p.IsPrime] :
    letI := constantCoeffSubring_isLocalRing k
    p = ⊥ ∨ p = maximalIdeal (constantCoeffSubring k) := by
  let := constantCoeffSubring_isLocalRing k
  by_cases hp : p = ⊥
  · exact Or.inl hp
  right
  apply le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
  obtain ⟨f, hfp, hf⟩ := (Submodule.ne_bot_iff p).mp hp
  obtain ⟨n, g, hg⟩ := constantCoeffSubring_dvd_X_pow k hf
  have hx : constantCoeffSubringX k ∈ p := Ideal.IsPrime.mem_of_pow_mem inferInstance n (by
    rw [hg]
    exact p.mul_mem_right g hfp)
  intro f hf
  have hf0 : PowerSeries.constantCoeff f.val = 0 := by
    simpa only [mem_maximalIdeal, mem_nonunits_iff, constantCoeffSubring_isUnit_iff,
      not_not] using hf
  obtain ⟨g, hg⟩ := constantCoeffSubring_X_dvd_sq k hf0
  exact Ideal.IsPrime.mem_of_pow_mem inferInstance 2 (by
    rw [hg]
    exact p.mul_mem_right g hx)

/-- A henselization of a henselian local ring is isomorphic to it. -/
private theorem bijective_algebraMap_of_isHenselization
    (R A : Type*) [CommRing R] [HenselianLocalRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A]
    [IsHenselization R (ResidueField R) A] :
    Function.Bijective (algebraMap R A) := by
  have : IsLocalHom (algebraMap R A) := IsHenselization.isLocalHom (L := ResidueField R)
  have : HenselianLocalRing A := IsHenselization.henselian R (ResidueField R)
  have hind := IsHenselization.ind_etale (R := R) (L := ResidueField R) (Rh := A)
  have hres := (IsHenselization.residueField_map_bijective (R := R) (Rh := A)).surjective
  obtain ⟨f, hf, _⟩ := HenselianLocalRing.existsUnique_isLocalHom_of_ind_etale
    (R := R) (Rh := A) (Sh := R) hind hres
  have : IsLocalHom f := hf
  obtain ⟨g, hg, hu⟩ := HenselianLocalRing.existsUnique_isLocalHom_of_ind_etale
    (R := R) (Rh := A) (Sh := A) hind hres
  let i := Algebra.ofId R A
  have hcomp : IsLocalHom (i.comp f) := ⟨fun x hx =>
    IsLocalHom.map_nonunit (f := f) x
      (IsLocalHom.map_nonunit (f := algebraMap R A) (f x) hx)⟩
  have hidlocal : IsLocalHom (AlgHom.id R A) := ⟨fun _ hx => hx⟩
  have hid : i.comp f = AlgHom.id R A := (hu _ hcomp).trans (hu _ hidlocal).symm
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · simpa using congrArg f hxy
  · exact ⟨f x, DFunLike.congr_fun hid x⟩

/-- The henselization of the spectrum of a henselian local ring at its closed point is the
spectrum itself. -/
private theorem isIso_henselizationToBase_of_henselian (R : CommRingCat)
    [HenselianLocalRing R] : IsIso (henselizationToBase (Spec R) (closedPoint R)) := by
  have : HenselianLocalRing ((Spec R).presheaf.stalk (closedPoint R)) :=
    HenselianLocalRing.of_ringEquiv (stalkClosedPointIso R).commRingCatIsoToRingEquiv.symm
  have : IsIso (CommRingCat.ofHom (algebraMap
      ((Spec R).presheaf.stalk (closedPoint R))
      (henselizationRing (Spec R) (closedPoint R)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_algebraMap_of_isHenselization _ _)
  have : IsIso ((Spec R).fromSpecStalk (closedPoint R)) := by
    rw [← Spec_stalkClosedPointIso]
    infer_instance
  unfold henselizationToBase
  infer_instance

/-- The structure sheaf is of finite presentation as a module over itself. -/
private theorem structureSheaf_isFinitePresentation (X : Scheme.{u}) :
    SheafOfModules.IsFinitePresentation.{u, u, u}
      (SheafOfModules.unit.{u} X.ringCatSheaf) := by
  let G := SheafOfModules.free.generatingSections (R := X.ringCatSheaf) PUnit.{u + 1}
  let q := G.localGeneratorsData
  let : q.IsLocallyFreeData := by infer_instance
  let : SheafOfModules.LocalGeneratorsData.IsFiniteType.{u, u, u, u} q := by
    constructor
    intro i
    constructor
    change Finite PUnit.{u + 1}
    infer_instance
  let qc := q.quasiCoherentData
  have hqc : SheafOfModules.QuasicoherentData.IsFinitePresentation.{u, u, u, u} qc := by
    constructor
    intro i
    exact {
      isFiniteType_generators := ⟨by change Finite PUnit.{u + 1}; infer_instance⟩
      isFiniteType_relations := ⟨by change Finite (ULift Empty); infer_instance⟩ }
  have hfree : SheafOfModules.IsFinitePresentation.{u, u, u}
      (SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1}) :=
    SheafOfModules.IsFinitePresentation.mk.{u, u, u} ⟨qc, hqc⟩
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (structureSheafFreeIso X) hfree

open Polynomial CategoryTheory.Limits
open scoped TensorProduct

/-- In `R[t]/(at - b)`, the image of `a` times the class of `t` is the image of `b`. -/
private theorem adjoinRoot_of_mul_root_eq {R : Type*} [CommRing R] (a b : R) :
    AdjoinRoot.of (C a * X - C b) a * AdjoinRoot.root (C a * X - C b) =
      AdjoinRoot.of (C a * X - C b) b := by
  have h := AdjoinRoot.eval₂_root (C a * X - C b)
  simpa only [eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, sub_eq_zero] using h

/-- A ring map with a left inverse ring equivalence is an isomorphism of affine schemes. -/
private theorem isIso_ofHom_of_ringEquiv_apply {B C : Type u} [CommRing B] [CommRing C]
    (f : B →+* C) (E : C ≃+* B) (h : ∀ b, E (f b) = b) : IsIso (CommRingCat.ofHom f) := by
  have hbij : Function.Bijective f :=
    ⟨fun x y hxy => by simpa only [h] using congrArg E hxy, fun x => ⟨E x, E.injective (h _)⟩⟩
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij

/-- If `a` is a unit then `R[t]/(at - b)` is `R`. -/
private noncomputable def adjoinRootLinearEquiv {R : Type*} [CommRing R]
    (a b : R) (ha : IsUnit a) : AdjoinRoot (C a * X - C b) ≃ₐ[R] R := by
  let u := ha.unit
  have hu : (u : R) = a := ha.unit_spec
  rw [← hu]
  let p : Polynomial R := C (u : R) * X - C b
  have hroot : Polynomial.eval₂ (AlgHom.id R R).toRingHom ((↑u⁻¹ : R) * b) p = 0 := by
    simp [p, ← mul_assoc]
  let g := AdjoinRoot.liftAlgHom p (AlgHom.id R R) ((↑u⁻¹ : R) * b) hroot
  refine AlgEquiv.ofAlgHom g (Algebra.ofId R (AdjoinRoot p)) (by ext) ?_
  apply AdjoinRoot.algHom_ext
  change algebraMap R (AdjoinRoot p) (g (AdjoinRoot.root p)) = AdjoinRoot.root p
  have hgroot : g (AdjoinRoot.root p) = (↑u⁻¹ : R) * b :=
    AdjoinRoot.liftAlgHom_root p (AlgHom.id R R) _ hroot
  rw [hgroot, map_mul]
  have hrel : AdjoinRoot.of p (u : R) * AdjoinRoot.root p = AdjoinRoot.of p b :=
    adjoinRoot_of_mul_root_eq (u : R) b
  change AdjoinRoot.of p (↑u⁻¹ : R) * AdjoinRoot.of p b = AdjoinRoot.root p
  rw [← hrel, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

/-- Base changing `R[t]/(at - b)` to a ring in which `a` becomes a unit gives that ring. -/
private noncomputable def adjoinRootLinearBaseChangeEquiv
    {R K : Type*} [CommRing R] [CommRing K] [Algebra R K]
    (a b : R) (ha : IsUnit (algebraMap R K a)) :
    K ⊗[R] AdjoinRoot (C a * X - C b) ≃ₐ[K] K := by
  let p := C a * X - C b
  let e := Algebra.TensorProduct.rid R K K
  refine (AdjoinRoot.tensorAlgEquiv p _ rfl).trans
    ((AdjoinRoot.mapAlgEquiv e _ (C (algebraMap R K a) * X - C (algebraMap R K b)) ?_).trans
      (adjoinRootLinearEquiv _ _ ha))
  apply Associated.of_eq
  simp [p, e, Algebra.TensorProduct.includeRight, Algebra.smul_def]

/-- Every element of `R[t]/(at - b)` becomes an element of `R` after multiplying by a power of
`a`. -/
private theorem adjoinRootLinear_exists_pow_mul_eq
    {R : Type*} [CommRing R] (a b : R) (z : AdjoinRoot (C a * X - C b)) :
    ∃ (n : ℕ) (r : R), AdjoinRoot.of _ a ^ n * z = AdjoinRoot.of _ r := by
  let p := C a * X - C b
  have hrel : AdjoinRoot.of p a * AdjoinRoot.root p = AdjoinRoot.of p b :=
    adjoinRoot_of_mul_root_eq a b
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective z
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      obtain ⟨n, r, hr⟩ := hf
      obtain ⟨m, s, hs⟩ := hg
      refine ⟨n + m, a ^ m * r + a ^ n * s, ?_⟩
      rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow]
      calc
        AdjoinRoot.of p a ^ (n + m) * (AdjoinRoot.mk p f + AdjoinRoot.mk p g) =
          AdjoinRoot.of p a ^ m * (AdjoinRoot.of p a ^ n * AdjoinRoot.mk p f) +
          AdjoinRoot.of p a ^ n * (AdjoinRoot.of p a ^ m * AdjoinRoot.mk p g) := by
            rw [pow_add]
            ring
        _ = _ := by rw [hr, hs]
  | monomial n r =>
      refine ⟨n, r * b ^ n, ?_⟩
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      change AdjoinRoot.of p a ^ n * (AdjoinRoot.of p r * AdjoinRoot.root p ^ n) =
        AdjoinRoot.of p (r * b ^ n)
      rw [map_mul, map_pow, ← hrel, mul_pow]
      ring

/-- An ideal of `R[t]/(at - b)` which meets `R` only in zero is contained in the kernel of any
map to a domain which does not kill `a`. -/
private theorem adjoinRootLinear_le_ker_of_comap_eq_bot
    {R B : Type*} [CommRing R] [CommRing B] [IsDomain B]
    (a b : R) (g : AdjoinRoot (C a * X - C b) →+* B)
    (ha : g (AdjoinRoot.of _ a) ≠ 0)
    (q : Ideal (AdjoinRoot (C a * X - C b)))
    (hq : q.comap (AdjoinRoot.of _) = ⊥) : q ≤ RingHom.ker g := by
  intro z hz
  obtain ⟨n, r, hr⟩ := adjoinRootLinear_exists_pow_mul_eq a b z
  have hmem : r ∈ q.comap (AdjoinRoot.of _) := by
    change AdjoinRoot.of _ r ∈ q
    rw [← hr]
    exact q.mul_mem_left _ hz
  have hr0 : r = 0 := by simpa only [hq, Ideal.mem_bot] using hmem
  have heq := congrArg g hr
  rw [map_mul, map_pow, hr0, map_zero, map_zero] at heq
  exact (mul_eq_zero.mp heq).resolve_left (pow_ne_zero _ ha)

/-- If `c` vanishes at `p` while `ct` is inverted along a ring map to a domain, then the closure
of the corresponding point misses the fibre over `p`. -/
private theorem closure_ker_inter_fiber_eq_empty
    {R A K : Type*} [CommRing R] [CommRing A] [CommRing K] [IsDomain K]
    (i : R →+* A) (g : A →+* K) (p : PrimeSpectrum R)
    (c : R) (t : A) (hc : c ∈ p.asIdeal) (hct : g (i c * t) = 1) :
    closure {⟨RingHom.ker g, RingHom.ker_isPrime g⟩} ∩
      (PrimeSpectrum.comap i) ⁻¹' {p} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro q ⟨hq, hqp⟩
  have hle : RingHom.ker g ≤ q.asIdeal := (PrimeSpectrum.le_iff_mem_closure _ _).mpr hq
  have hcq : i c ∈ q.asIdeal := by
    change c ∈ (PrimeSpectrum.comap i q).asIdeal
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hqp ▸ hc
  have hrel : i c * t - 1 ∈ q.asIdeal := hle (by
    change g (i c * t - 1) = 0
    rw [map_sub, map_one, hct, sub_self])
  have hone : (1 : A) ∈ q.asIdeal := by
    have := q.asIdeal.sub_mem (q.asIdeal.mul_mem_right t hcq) hrel
    simpa only [sub_sub_cancel] using this
  exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

/-- Taking constant coefficients maps `k + x K[[x]]` onto `k`. -/
private noncomputable abbrev constantCoeffToSubfield {K : Type*} [Field K] (k : Subfield K) :
    constantCoeffSubring k →+* k :=
  (PowerSeries.constantCoeff.comp (constantCoeffSubring k).subtype).codRestrict k
    (fun f => f.property)

/-- The element `xy` of `k + x K[[x]]`. -/
private noncomputable abbrev constantCoeffSubringXY {K : Type*} [Field K] (k : Subfield K)
    (y : K) : constantCoeffSubring k := ⟨PowerSeries.X * PowerSeries.C y, by
      change PowerSeries.constantCoeff (PowerSeries.X * PowerSeries.C y) ∈ k
      simp⟩

/-- The algebra `R[t]/(xt - xy)` over `R = k + x K[[x]]`. -/
private noncomputable abbrev exampleAlgebra {K : Type*} [Field K] (k : Subfield K) (y : K) :=
  AdjoinRoot (Polynomial.C (constantCoeffSubringX k) * Polynomial.X -
    Polynomial.C (constantCoeffSubringXY k y))

/-- Evaluation of `R[t]/(xt - xy)` at `t = y`. -/
private noncomputable def exampleEval {K : Type*} [Field K] (k : Subfield K) (y : K) :
    exampleAlgebra k y →+* PowerSeries K :=
  AdjoinRoot.lift (constantCoeffSubring k).subtype (PowerSeries.C y) (by
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X]
    change PowerSeries.X * PowerSeries.C y - PowerSeries.X * PowerSeries.C y = 0
    exact sub_self _)

/-- Evaluation of `R[t]/(xt - xy)` at `t = 0` composed with taking constant coefficients. -/
private noncomputable def exampleClosedPoint {K : Type*} [Field K]
    (k : Subfield K) (y : K) : exampleAlgebra k y →+* k :=
  AdjoinRoot.lift (constantCoeffToSubfield k) 0 (by
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X, mul_zero, zero_sub, neg_eq_zero]
    apply Subtype.ext
    change PowerSeries.constantCoeff (PowerSeries.X * PowerSeries.C y) = 0
    simp)

/-- When `y` is transcendental, the point `t = y` specializes to the point `t = 0`. -/
private theorem exampleEval_ker_le_closedPoint_ker {K : Type*} [Field K]
    (k : Subfield K) (y : K)
    (hy : Function.Injective (Polynomial.eval₂RingHom k.subtype y)) :
    RingHom.ker (exampleEval k y) ≤ RingHom.ker (exampleClosedPoint k y) := by
  intro z hz
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  change (exampleEval k y) (AdjoinRoot.mk _ p) = 0 at hz
  rw [exampleEval, AdjoinRoot.lift_mk] at hz
  have hc := congrArg PowerSeries.constantCoeff hz
  rw [Polynomial.hom_eval₂, map_zero, PowerSeries.constantCoeff_C] at hc
  have heval : Polynomial.eval₂RingHom k.subtype y
      (p.map (constantCoeffToSubfield k)) = 0 := by
    change Polynomial.eval₂ k.subtype y (p.map (constantCoeffToSubfield k)) = 0
    rw [Polynomial.eval₂_map]
    exact hc
  have hp : p.map (constantCoeffToSubfield k) = 0 := hy (heval.trans (map_zero _).symm)
  change exampleClosedPoint k y (AdjoinRoot.mk _ p) = 0
  rw [exampleClosedPoint, AdjoinRoot.lift_mk, ← Polynomial.eval_map, hp, Polynomial.eval_zero]

/-- The point `t = 0` of `Spec R[t]/(xt - xy)` lies over the closed point of `Spec R`. -/
private theorem exampleClosedPoint_comap_ker {K : Type*} [Field K] (k : Subfield K) (y : K) :
    letI := constantCoeffSubring_isLocalRing k
    (RingHom.ker (exampleClosedPoint k y)).comap (AdjoinRoot.of _) =
      maximalIdeal (constantCoeffSubring k) := by
  let := constantCoeffSubring_isLocalRing k
  ext r
  change exampleClosedPoint k y (AdjoinRoot.of _ r) = 0 ↔ _
  rw [exampleClosedPoint, AdjoinRoot.lift_of, mem_maximalIdeal, mem_nonunits_iff,
    constantCoeffSubring_isUnit_iff, not_not]
  exact Subtype.ext_iff

/-- Every point of `Spec R[t]/(xt - xy)` specializes to a point over the closed point of
`Spec R`. -/
private theorem example_specializes_to_closed_fiber {K : Type*} [Field K]
    (k : Subfield K) (y : K)
    (hy : Function.Injective (Polynomial.eval₂RingHom k.subtype y))
    (q : PrimeSpectrum (exampleAlgebra k y)) :
    letI := constantCoeffSubring_isLocalRing k
    ∃ z : PrimeSpectrum (exampleAlgebra k y), q ⤳ z ∧
      PrimeSpectrum.comap (AdjoinRoot.of _) z = closedPoint (constantCoeffSubring k) := by
  let := constantCoeffSubring_isLocalRing k
  obtain hp | hp := constantCoeffSubring_prime_eq_bot_or_maximal k
    (q.asIdeal.comap (AdjoinRoot.of _))
  · let z : PrimeSpectrum (exampleAlgebra k y) :=
      ⟨RingHom.ker (exampleClosedPoint k y), RingHom.ker_isPrime _⟩
    refine ⟨z, specializes_iff_mem_closure.mpr ((PrimeSpectrum.le_iff_mem_closure q z).mp
      ((adjoinRootLinear_le_ker_of_comap_eq_bot _ _ (exampleEval k y) ?_ _ hp).trans
        (exampleEval_ker_le_closedPoint_ker k y hy))),
      PrimeSpectrum.ext (exampleClosedPoint_comap_ker k y)⟩
    rw [exampleEval, AdjoinRoot.lift_of]
    change PowerSeries.X ≠ (0 : PowerSeries K)
    exact PowerSeries.X_ne_zero
  · exact ⟨q, specializes_rfl, PrimeSpectrum.ext hp⟩

/-- There is no impurity if a point of the fibre over the chosen point is a specialization of
the generic point of the impurity. -/
private theorem not_isImpurity_of_specializes
    (P : PrePureSituation) (D : ImpurityDiagram P) (z : D.X_T) (hz : D.xi ⤳ z)
    (hz' : D.toT z = D.t) : ¬ IsImpurity P D := by
  intro hD
  have hm : z ∈ closure {D.xi} ∩ Set.range (D.toT.fiberι D.t) :=
    ⟨specializes_iff_mem_closure.mp hz, by rw [D.toT.range_fiberι]; exact hz'⟩
  rw [hD.2] at hm
  exact hm

/-- There is no impurity over an isomorphism when every point of the source specializing over the
chosen point specializes into its fibre. -/
private theorem not_isImpurity_of_isIso
    (P : PrePureSituation) (D : ImpurityDiagram P) [IsIso D.g]
    (h : ∀ x : P.X, P.f x ⤳ P.s → ∃ y, x ⤳ y ∧ P.f y = P.s) : ¬ IsImpurity P D := by
  have : IsIso D.toX := D.isPullback.isIso_fst_of_isIso
  have hcomm (x : D.X_T) : P.f (D.toX x) = D.g (D.toT x) :=
    congrArg (fun f : D.X_T ⟶ P.S => f x) D.isPullback.w
  have hspec : P.f (D.toX D.xi) ⤳ P.s := by
    rw [hcomm, D.xi_liesOver, ← D.mapsToChosenPoint]
    exact D.specializes.map D.g.continuous
  obtain ⟨y, hxy, hy⟩ := h (D.toX D.xi) hspec
  refine not_isImpurity_of_specializes P D (D.toX.homeomorph.symm y) ?_ ?_
  · have hxy₀ : D.toX.homeomorph D.xi ⤳ y := hxy
    simpa only [Homeomorph.symm_apply_apply] using hxy₀.map D.toX.homeomorph.symm.continuous
  · apply D.g.homeomorph.injective
    change D.g (D.toT (D.toX.homeomorph.symm y)) = D.g D.t
    rw [← hcomm, D.mapsToChosenPoint]
    simpa [← Scheme.Hom.homeomorph_apply] using hy

/-- Purity along a fibre over a point whose henselization is the base itself. -/
private theorem isPureAlong_of_henselization_isIso
    (P : PrePureSituation) [IsIso (henselizationToBase P.S P.s)]
    (h : ∀ x : P.X, P.f x ⤳ P.s → ∃ y, x ⤳ y ∧ P.f y = P.s) : IsPureAlong P := by
  intro D hD hEl hImp
  obtain ⟨E, e, he, hE⟩ :=
    (exists_isImpurity_henselization_iff_elementaryEtaleNeighborhood P).mpr ⟨D, hD, hImp, hEl⟩
  have : IsIso E.g := by rw [he]; infer_instance
  exact not_isImpurity_of_isIso P E h hE

/-- There is no impurity whose projection to the test family is an isomorphism. -/
private theorem not_isImpurity_of_projection_isIso
    (P : PrePureSituation) (D : ImpurityDiagram P) [IsIso D.toT] : ¬ IsImpurity P D := by
  refine not_isImpurity_of_specializes P D (D.toT.homeomorph.symm D.t) ?_
    (D.toT.homeomorph.apply_symm_apply D.t)
  have hs : D.toT.homeomorph D.xi ⤳ D.t := by
    change D.toT D.xi ⤳ D.t
    rw [D.xi_liesOver]
    exact D.specializes
  simpa only [Homeomorph.symm_apply_apply] using hs.map D.toT.homeomorph.symm.continuous

/-- Purity along a fibre over a point along whose henselization the morphism becomes an
isomorphism. -/
private theorem isPureAlong_of_henselization_pullback_isIso
    (P : PrePureSituation) [IsIso (pullback.snd P.f (henselizationToBase P.S P.s))] :
    IsPureAlong P := by
  intro D hD hEl hImp
  obtain ⟨E, e, he, hE⟩ :=
    (exists_isImpurity_henselization_iff_elementaryEtaleNeighborhood P).mpr ⟨D, hD, hImp, hEl⟩
  have hpb : IsPullback E.toX (E.toT ≫ e.hom) P.f (henselizationToBase P.S P.s) :=
    E.isPullback.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _)
      (by simp) (by simp) (by simp) (by simpa using he)
  have : IsIso (E.toT ≫ e.hom) := by
    rw [← hpb.isoPullback_hom_snd]
    infer_instance
  have : IsIso E.toT := IsIso.of_isIso_comp_right E.toT e.hom
  exact not_isImpurity_of_projection_isIso P E hE

/-- After base change along a ring in which `a` becomes a unit, `Spec R[t]/(at - b)` becomes the
base. -/
private theorem isIso_pullback_snd_linearSpec
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (a b : R) (ha : IsUnit (algebraMap R B a)) :
    IsIso (pullback.snd (Spec.map (CommRingCat.ofHom (AdjoinRoot.of (C a * X - C b))))
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))) := by
  let A := AdjoinRoot (C a * X - C b)
  let e := adjoinRootLinearBaseChangeEquiv (K := B) a b ha
  let E : A ⊗[R] B ≃+* B :=
    (Algebra.TensorProduct.comm R A B).toRingEquiv.trans e.toRingEquiv
  have hE (b : B) : E (Algebra.TensorProduct.includeRight b) = b := by
    change e (b ⊗ₜ[R] (1 : A)) = b
    exact e.commutes b
  have : IsIso (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) :=
    isIso_ofHom_of_ringEquiv_apply _ E hE
  change IsIso (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap R B))))
  rw [← pullbackSpecIso_hom_snd R A B]
  change IsIso ((pullbackSpecIso R A B).hom ≫ Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom))
  infer_instance

/-- Over a point at which `a` does not vanish, the base change of `Spec R[t]/(at - b)` to the
henselization is an isomorphism. -/
private theorem isIso_henselization_pullback_snd_linearSpec
    (R : CommRingCat.{u}) (a b : R) (s : Spec R) (ha : a ∉ s.asIdeal) :
    IsIso (pullback.snd (Spec.map (CommRingCat.ofHom (AdjoinRoot.of (C a * X - C b))))
      (henselizationToBase (Spec R) s)) := by
  let B := henselizationRing (Spec R) s
  let : s.asIdeal.IsPrime := s.isPrime
  let : Algebra R ((Spec R).presheaf.stalk s) := StructureSheaf.stalkAlgebra R s
  let : IsLocalization.AtPrime ((Spec R).presheaf.stalk s) s.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R s
  let φ : R →+* B := (algebraMap ((Spec R).presheaf.stalk s) B).comp
    (StructureSheaf.toStalk R s).hom
  let : Algebra R B := φ.toAlgebra
  have heq : henselizationToBase (Spec R) s =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    unfold henselizationToBase
    rw [Spec.fromSpecStalk_eq' R s]
    exact (Spec.map_comp (StructureSheaf.toStalk R s)
      (CommRingCat.ofHom (algebraMap ((Spec R).presheaf.stalk s) B))).symm
  rw [heq]
  apply isIso_pullback_snd_linearSpec
  have hunit : IsUnit (algebraMap R ((Spec R).presheaf.stalk s) a) :=
    IsLocalization.map_units (M := s.asIdeal.primeCompl) ((Spec R).presheaf.stalk s) ⟨a, ha⟩
  exact hunit.map (algebraMap ((Spec R).presheaf.stalk s) B)

/-- The example is pure along the fibre over the closed point of `Spec R`. -/
private theorem example_isPureAlong_closed
    {K : Type u} [Field K] (k : Subfield K) (y : K)
    (hy : Function.Injective (Polynomial.eval₂RingHom k.subtype y))
    (F : (Spec (.of (exampleAlgebra k y))).Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] :
    letI := constantCoeffSubring_isLocalRing k
    let f := Spec.map (CommRingCat.ofHom (AdjoinRoot.of
      (Polynomial.C (constantCoeffSubringX k) * Polynomial.X -
        Polynomial.C (constantCoeffSubringXY k y))))
    letI : LocallyOfFinitePresentation f :=
      (LocallyOfFinitePresentation.SpecMap_iff _).mpr
        (RingHom.finitePresentation_algebraMap.mpr inferInstance)
    IsPureAlong
      ({ S := Spec (.of (constantCoeffSubring k)), X := Spec (.of (exampleAlgebra k y)),
         f := f, F := F, s := closedPoint (constantCoeffSubring k) } : PrePureSituation) := by
  let := constantCoeffSubring_isHenselian k
  have := isIso_henselizationToBase_of_henselian (.of (constantCoeffSubring k))
  apply isPureAlong_of_henselization_isIso
  exact fun q _ => example_specializes_to_closed_fiber k y hy q

/-- The example is pure relative to `Spec R`. -/
private theorem example_isPureRelative
    {K : Type u} [Field K] (k : Subfield K) (y : K)
    (hy : Function.Injective (Polynomial.eval₂RingHom k.subtype y))
    (F : (Spec (.of (exampleAlgebra k y))).Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] :
    let f := Spec.map (CommRingCat.ofHom (AdjoinRoot.of
      (Polynomial.C (constantCoeffSubringX k) * Polynomial.X -
        Polynomial.C (constantCoeffSubringXY k y))))
    letI : LocallyOfFinitePresentation f :=
      (LocallyOfFinitePresentation.SpecMap_iff _).mpr
        (RingHom.finitePresentation_algebraMap.mpr inferInstance)
    IsPureRelative f F := by
  dsimp only
  let := constantCoeffSubring_isLocalRing k
  intro s
  have : s.asIdeal.IsPrime := s.isPrime
  obtain hs | hs := constantCoeffSubring_prime_eq_bot_or_maximal k s.asIdeal
  · have ha : constantCoeffSubringX k ∉ s.asIdeal := by
      rw [hs, Ideal.mem_bot]
      exact fun h => PowerSeries.X_ne_zero (congrArg Subtype.val h)
    have := isIso_henselization_pullback_snd_linearSpec
      (.of (constantCoeffSubring k)) (constantCoeffSubringX k)
      (constantCoeffSubringXY k y) s ha
    exact isPureAlong_of_henselization_pullback_isIso _
  · obtain rfl : s = closedPoint (constantCoeffSubring k) := PrimeSpectrum.ext hs
    exact example_isPureAlong_closed k y hy F

open TopologicalSpace

/-- Associated points are invariant under an isomorphism of modules. -/
private lemma isAssociatedPoint_of_iso {X : Scheme.{u}} {F G : X.Modules}
    (e : F ≅ G) (x : X) (hx : Stacks.Divisors.IsAssociatedPoint F x) :
    Stacks.Divisors.IsAssociatedPoint G x :=
  associatedPoints_subset_of_mono e.hom hx

/-- A point of a one-point fibre lies in the relative assassin of the structure sheaf. -/
theorem mem_relativeAssassin_of_fiberToSpecResidueField_isIso
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (e : F ≅ SheafOfModules.unit X.ringCatSheaf) (s : S)
    [IsIso (f.fiberToSpecResidueField s)] (x : X) (hx : f x = s) :
    x ∈ Stacks.Divisors.relativeAssassin f F := by
  have : IsLocallyNoetherian (f.fiber s) :=
    isLocallyNoetherian_of_isOpenImmersion (f.fiberToSpecResidueField s)
  have : Subsingleton (f.fiber s) :=
    Function.Injective.subsingleton (f.fiberToSpecResidueField s).homeomorph.injective
  obtain ⟨z, hz⟩ : x ∈ Set.range (f.fiberι s) := by
    rw [f.range_fiberι]
    exact hx
  have : Nonempty (f.fiber s) := ⟨z⟩
  have hgen : IsGenericPoint z (Set.univ : Set (f.fiber s)) := by
    change closure {z} = Set.univ
    have hsingleton : ({z} : Set (f.fiber s)) = Set.univ := by
      ext y
      simp [Subsingleton.elim y z]
    rw [hsingleton, closure_univ]
  have : IrreducibleSpace (f.fiber s) := (irreducibleSpace_def _).mpr hgen.isIrreducible
  have hass := mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent
    (f.fiber s) (by rw [irreducibleComponents_eq_singleton]; exact Set.mem_singleton _) hgen
  apply (Stacks.Divisors.mem_relativeAssassin f F x).mpr
  refine ⟨s, z, ?_, hz⟩
  exact isAssociatedPoint_of_iso
    (((Scheme.Modules.pullback (f.fiberι s)).mapIso e) ≪≫
      AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (f.fiberι s)).symm z hass

/-- Over a point at which `a` does not vanish, the fibre of `Spec R[t]/(at - b)` is a single
point. -/
private theorem isIso_fiberToSpecResidueField_linearSpec
    {R : Type u} [CommRing R] (a b : R) (s : PrimeSpectrum R) (ha : a ∉ s.asIdeal) :
    IsIso ((Spec.map (CommRingCat.ofHom
      (AdjoinRoot.of (C a * X - C b)))).fiberToSpecResidueField s) := by
  let A := AdjoinRoot (C a * X - C b)
  let B := s.asIdeal.ResidueField
  have hau : IsUnit (algebraMap R B a) :=
    isUnit_iff_ne_zero.mpr fun h => ha (Ideal.algebraMap_residueField_eq_zero.mp h)
  let e := adjoinRootLinearBaseChangeEquiv (K := B) a b hau
  have : IsIso (CommRingCat.ofHom (algebraMap B (B ⊗[R] A))) :=
    isIso_ofHom_of_ringEquiv_apply _ e.toRingEquiv e.commutes
  let i := Spec.fiberToSpecResidueFieldIso R A s
  exact (Arrow.isIso_iff_isIso_of_isIso i.hom).mpr inferInstance

/-- The example is not universally pure relative to `Spec R`: an impurity appears after the base
change to `Spec R[c]/(xc - xy⁻¹)`. -/
private theorem example_not_isUniversallyPureRelative
    {K : Type u} [Field K] (k : Subfield K) (y : K) (hy0 : y ≠ 0)
    (hyi : Function.Injective (Polynomial.eval₂RingHom k.subtype y⁻¹)) :
    let f := Spec.map (CommRingCat.ofHom (AdjoinRoot.of
      (Polynomial.C (constantCoeffSubringX k) * Polynomial.X -
        Polynomial.C (constantCoeffSubringXY k y))))
    letI : LocallyOfFinitePresentation f :=
      (LocallyOfFinitePresentation.SpecMap_iff _).mpr
        (RingHom.finitePresentation_algebraMap.mpr inferInstance)
    letI := structureSheaf_isFiniteType (Spec (.of (exampleAlgebra k y)))
    letI :=
      Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit
        (Spec (.of (exampleAlgebra k y)))
    ¬ IsUniversallyPureRelative f
      (SheafOfModules.unit (Spec (.of (exampleAlgebra k y))).ringCatSheaf) := by
  dsimp only
  let R := constantCoeffSubring k
  let A := exampleAlgebra k y
  let O := exampleAlgebra k y⁻¹
  let : Algebra R (PowerSeries K) := (constantCoeffSubring k).subtype.toAlgebra
  let ea : A →ₐ[R] PowerSeries K :=
    { toRingHom := exampleEval k y
      commutes' := fun r => AdjoinRoot.lift_of _ }
  let eo : O →ₐ[R] PowerSeries K :=
    { toRingHom := exampleEval k y⁻¹
      commutes' := fun r => AdjoinRoot.lift_of _ }
  let ev : A ⊗[R] O →ₐ[R] PowerSeries K :=
    Algebra.TensorProduct.lift ea eo (fun _ _ => Commute.all _ _)
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let g := Spec.map (CommRingCat.ofHom (algebraMap R O))
  let toX := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] O).toRingHom)
  let toT := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : O →ₐ[R] A ⊗[R] O).toRingHom)
  have : LocallyOfFinitePresentation f :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have hpb : IsPullback toX toT f g := by
    apply isPullback_SpecMap_of_isPushout
    exact IsPushout.of_isColimit (CommRingCat.pushoutCoconeIsColimit R A O)
  let t : ↥(Spec (CommRingCat.of O)) :=
    ⟨RingHom.ker (exampleClosedPoint k y⁻¹), RingHom.ker_isPrime _⟩
  let t' : ↥(Spec (CommRingCat.of O)) := ⟨RingHom.ker eo.toRingHom, RingHom.ker_isPrime _⟩
  let xi : ↥(Spec (CommRingCat.of (A ⊗[R] O))) :=
    ⟨RingHom.ker ev.toRingHom, RingHom.ker_isPrime _⟩
  have hspec : t' ⤳ t := specializes_iff_mem_closure.mpr
    ((PrimeSpectrum.le_iff_mem_closure t' t).mp (exampleEval_ker_le_closedPoint_ker k y⁻¹ hyi))
  have hxi : toT xi = t' := by
    apply PrimeSpectrum.ext
    ext r
    change ev (Algebra.TensorProduct.includeRight r) = 0 ↔ eo r = 0
    simp [ev]
  have hempty : closure {xi} ∩ Set.range (toT.fiberι t) = ∅ := by
    rw [Scheme.Hom.range_fiberι]
    apply closure_ker_inter_fiber_eq_empty
      (Algebra.TensorProduct.includeRight : O →ₐ[R] A ⊗[R] O).toRingHom
      ev.toRingHom t (AdjoinRoot.root _)
      ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] O) (AdjoinRoot.root _))
    · change exampleClosedPoint k y⁻¹ (AdjoinRoot.root _) = 0
      exact AdjoinRoot.lift_root _
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul]
      change ev ((1 : A) ⊗ₜ[R] AdjoinRoot.root _) *
        ev (AdjoinRoot.root _ ⊗ₜ[R] (1 : O)) = 1
      simp only [ev, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one]
      change exampleEval k y⁻¹ (AdjoinRoot.root _) * exampleEval k y (AdjoinRoot.root _) = 1
      rw [exampleEval, AdjoinRoot.lift_root, exampleEval, AdjoinRoot.lift_root,
        ← map_mul, inv_mul_cancel₀ hy0, map_one]
  have ha : constantCoeffSubringX k ∉ (g t').asIdeal := by
    change ¬ eo (algebraMap R O (constantCoeffSubringX k)) = 0
    rw [eo.commutes]
    exact PowerSeries.X_ne_zero
  have : IsIso (toT.fiberToSpecResidueField t') :=
    (isPullback_fiberToSpecResidueField_of_isPullback hpb t').isIso_snd_of_isIso
      (isIso_fiberToSpecResidueField_linearSpec
        (constantCoeffSubringX k) (constantCoeffSubringXY k y) (g t') ha)
  let P : PrePureSituation :=
    { S := Spec (.of R), X := Spec (.of A), f := f,
      F := SheafOfModules.unit (Spec (.of A)).ringCatSheaf, s := g t,
      isFiniteType := structureSheaf_isFiniteType _,
      isQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _ }
  let D : ImpurityDiagram P :=
    { T := Spec (.of O), g := g, t' := t', t := t, specializes := hspec,
      mapsToChosenPoint := rfl, X_T := Spec (.of (A ⊗[R] O)),
      toX := toX, toT := toT, isPullback := hpb, xi := xi, xi_liesOver := hxi }
  exact fun hpure => hpure (g t) D ⟨mem_relativeAssassin_of_fiberToSpecResidueField_isIso toT _
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso toX) t' xi hxi, hempty⟩

/-- Evaluating at a transcendental element is injective on polynomials over the range of a field
embedding. -/
private theorem eval₂RingHom_subtype_fieldRange_injective
    {k K : Type*} [Field k] [Field K] (f : k →+* K) (y : K)
    (h : Function.Injective (Polynomial.eval₂RingHom f y)) :
    Function.Injective (Polynomial.eval₂RingHom f.fieldRange.subtype y) := by
  let e := f.rangeRestrictFieldEquiv
  intro p q hpq
  obtain ⟨p, rfl⟩ := Polynomial.map_surjective e.toRingHom e.surjective p
  obtain ⟨q, rfl⟩ := Polynomial.map_surjective e.toRingHom e.surjective q
  apply congrArg (Polynomial.map e.toRingHom)
  apply h
  change Polynomial.eval₂ f y p = Polynomial.eval₂ f y q
  change Polynomial.eval₂ f.fieldRange.subtype y (p.map e.toRingHom) =
    Polynomial.eval₂ f.fieldRange.subtype y (q.map e.toRingHom) at hpq
  have he : f.fieldRange.subtype.comp e.toRingHom = f := by
    ext r
    exact f.rangeRestrictFieldEquiv_apply_coe r
  simpa only [Polynomial.eval₂_map, he] using hpq

/-- There is a morphism of affine schemes of finite presentation and a module of finite
presentation on its source which is pure relative to the base, but not universally pure relative
to it. -/
@[stacks 05JK]
theorem exists_isPureRelative_not_isUniversallyPureRelative :
    ∃ (X S : Scheme.{u}) (_ : IsAffine X) (_ : IsAffine S) (f : X ⟶ S)
      (hf : FinitePresentation f) (F : X.Modules)
      (hF : SheafOfModules.IsFinitePresentation.{u, u, u} F)
      (hFT : SheafOfModules.IsFiniteType.{u, u, u} F)
      (hQC : SheafOfModules.IsQuasicoherent.{u, u, u} F),
      letI : LocallyOfFinitePresentation f := hf.1
      letI : LocallyOfFiniteType f := inferInstance
      letI : QuasiCompact f := hf.2.1
      letI : SheafOfModules.IsFinitePresentation.{u, u, u} F := hF
      letI : SheafOfModules.IsFiniteType.{u, u, u} F := hFT
      letI : SheafOfModules.IsQuasicoherent.{u, u, u} F := hQC
      IsPureRelative f F ∧ ¬ IsUniversallyPureRelative f F := by
  classical
  let k₀ := ULift.{u} ℚ
  let K := RatFunc k₀
  let i := algebraMap k₀ K
  let k : Subfield K := i.fieldRange
  let y : K := RatFunc.X
  have hyt : Transcendental k₀ y := RatFunc.transcendental_X
  have hyit : Transcendental k₀ y⁻¹ := fun h => hyt (IsAlgebraic.inv_iff.mp h)
  have hy := eval₂RingHom_subtype_fieldRange_injective i y
    (transcendental_iff_injective.mp hyt)
  have hyi := eval₂RingHom_subtype_fieldRange_injective i y⁻¹
    (transcendental_iff_injective.mp hyit)
  let R := constantCoeffSubring k
  let A := exampleAlgebra k y
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let F := SheafOfModules.unit.{u} (Spec (.of A)).ringCatSheaf
  have : LocallyOfFinitePresentation f :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have : F.IsFinitePresentation := structureSheaf_isFinitePresentation _
  have : F.IsFiniteType := structureSheaf_isFiniteType _
  have : F.IsQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _
  let hf : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  refine ⟨Spec (.of A), Spec (.of R), inferInstance, inferInstance,
    f, hf, F, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact example_isPureRelative k y hy F
  · exact example_not_isUniversallyPureRelative k y RatFunc.X_ne_zero hyi

end Stacks.Examples

end
