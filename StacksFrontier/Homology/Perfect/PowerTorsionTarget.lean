module

public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.Homology.Perfect.Characterizing
public import StacksFrontier.RingTheory.Koszul.PowerLift.SingleTorsion

/-!
# Morphisms from a perfect complex into a complex with power-torsion cohomology

Let `A` be a commutative ring, let `f ∈ A`, and let `E` and `E'` be objects of the derived
category `D(A)`. If `E` is perfect and the cohomology modules of `E'` are all `f`-power torsion,
then every morphism `α : E ⟶ E'` is annihilated by a power of `f`.

## Main results

* `StacksDraft.Perfect.homPowerTorsion_of_isPerfect`: for a perfect source, the group of
  morphisms into a complex whose cohomology is `f`-power torsion is `f`-power torsion.
* `StacksDraft.Perfect.exists_pow_smul_eq_zero_of_isPerfect`: the same conclusion written out as
  `∃ n, f ^ n • α = 0`.
* `StacksDraft.Perfect.exists_pow_smul_eq_zero_of_isPerfect_of_support_subset_zeroLocus`:
  the same conclusion when every cohomology module of `E'` has support in `V(f)`.

## References

* [Stacks Project, Lemma 36.10.12 (Tag 08EJ)](https://stacks.math.columbia.edu/tag/08EJ)
* [Stacks Project, Lemma 15.76.3 (Tag 0ATI)](https://stacks.math.columbia.edu/tag/0ATI)
* [Stacks Project, Lemma 36.3.5 (Tag 06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Lemma 15.90.6 (Tag 0953)](https://stacks.math.columbia.edu/tag/0953)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty
open scoped ZeroObject

universe u v w

namespace Stacks.Koszul.PowerLift

variable {R : Type*} [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- If every morphism `Y ⟶ E` is killed by a power of `g`, then so is every morphism `X ⟶ E`
for a retract `X` of `Y`. -/
public theorem HomPowerTorsion.of_retract {g : R} {X Y E : C} (r : Retract X Y)
    (h : HomPowerTorsion g Y E) : HomPowerTorsion g X E := by
  intro φ
  obtain ⟨k, hk⟩ := h (r.r ≫ φ)
  refine ⟨k, ?_⟩
  rw [← Category.id_comp (g ^ k • φ), ← r.retract, Category.assoc, Linear.comp_smul, hk,
    comp_zero]

end Stacks.Koszul.PowerLift

namespace StacksDraft.Perfect

open Stacks.Koszul.PowerLift

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]

/-- The objects `X` of `D(A)` such that every shift `X⟦n⟧` has `f`-power torsion morphism group
into a fixed object `E`. -/
private def homPowerTorsionShifts (g : A) (E : DerivedCategory (ModuleCat.{u} A)) :
    ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
  fun X => ∀ n : ℤ, HomPowerTorsion g (X⟦n⟧) E

private theorem homPowerTorsionShifts_isClosedUnderIsomorphisms
    (g : A) (E : DerivedCategory (ModuleCat.{u} A)) :
    (homPowerTorsionShifts g E).IsClosedUnderIsomorphisms where
  of_iso e h n := HomPowerTorsion.of_iso ((shiftFunctor _ n).mapIso e) (h n)

private theorem homPowerTorsionShifts_isStableUnderRetracts
    (g : A) (E : DerivedCategory (ModuleCat.{u} A)) :
    (homPowerTorsionShifts g E).IsStableUnderRetracts where
  of_retract r h n :=
    HomPowerTorsion.of_retract
      { i := r.i⟦n⟧'
        r := r.r⟦n⟧'
        retract := by
          rw [← CategoryTheory.Functor.map_comp, r.retract, CategoryTheory.Functor.map_id] }
      (h n)

private theorem homPowerTorsionShifts_containsZero
    (g : A) (E : DerivedCategory (ModuleCat.{u} A)) :
    (homPowerTorsionShifts g E).ContainsZero where
  exists_zero :=
    ⟨0, isZero_zero _, fun n => HomPowerTorsion.of_isZero
      (IsZero.of_iso (isZero_zero _) (shiftFunctor _ n).mapZeroObject) E⟩

private theorem homPowerTorsionShifts_isStableUnderShift
    (g : A) (E : DerivedCategory (ModuleCat.{u} A)) :
    (homPowerTorsionShifts g E).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun X h n =>
    HomPowerTorsion.of_iso
      ((shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} A)) a n (a + n) rfl).app X)
      (h (a + n))⟩

private theorem homPowerTorsionShifts_isTriangulatedClosed₂
    (g : A) (E : DerivedCategory (ModuleCat.{u} A)) :
    (homPowerTorsionShifts g E).IsTriangulatedClosed₂ :=
  have := homPowerTorsionShifts_isClosedUnderIsomorphisms g E
  IsTriangulatedClosed₂.mk' fun T hT h₁ h₃ n =>
    HomPowerTorsion.of_distTriang₂
      ((Triangle.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) n).obj T)
      (Triangle.shift_distinguished T hT n) (h₁ n) (h₃ n)

private theorem homPowerTorsionShifts_isTriangulated
    (g : A) (E : DerivedCategory (ModuleCat.{u} A)) :
    (homPowerTorsionShifts g E).IsTriangulated :=
  have := homPowerTorsionShifts_containsZero g E
  have := homPowerTorsionShifts_isStableUnderShift g E
  have := homPowerTorsionShifts_isTriangulatedClosed₂ g E
  { }

/-- If every cohomology module of `E` is `g`-power torsion, then every perfect object `X` of
`D(A)` satisfies `homPowerTorsionShifts g E`. -/
private theorem isPerfect_le_homPowerTorsionShifts (g : A)
    (E : DerivedCategory (ModuleCat.{u} A))
    (hE : ∀ (p : ℤ) (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj E),
      ∃ k : ℕ, g ^ k • x = 0) :
    (IsPerfect : ObjectProperty (DerivedCategory (ModuleCat.{u} A))) ≤
      homPowerTorsionShifts g E := by
  have := homPowerTorsionShifts_isClosedUnderIsomorphisms g E
  have := homPowerTorsionShifts_isStableUnderRetracts g E
  have := homPowerTorsionShifts_isTriangulated g E
  rw [isPerfect_eq_triangEnvelope_singleton_regularModule, triangEnvelope_le_iff,
    singleton_le_iff]
  intro n
  exact HomPowerTorsion.of_iso
    (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso n (-n) 0
      (by lia)).app (ModuleCat.of A A)).symm
    (homPowerTorsion_singleRing g (-n) E (hE (-n)))

/-- Let `A` be a commutative ring, `g : A`, and `E` an object of `D(A)` all of whose
cohomology modules are `g`-power torsion. Then for every perfect object `K` of `D(A)` every
morphism `K ⟶ E` is annihilated by a power of `g`. -/
public theorem homPowerTorsion_of_isPerfect (g : A) (E : DerivedCategory (ModuleCat.{u} A))
    (hE : ∀ (p : ℤ) (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj E),
      ∃ k : ℕ, g ^ k • x = 0)
    {K : DerivedCategory (ModuleCat.{u} A)} (hK : IsPerfect K) :
    HomPowerTorsion g K E :=
  HomPowerTorsion.of_iso
    ((shiftFunctorZero (DerivedCategory (ModuleCat.{u} A)) ℤ).app K)
    (isPerfect_le_homPowerTorsionShifts g E hE K hK 0)

/-- Every element of an `f`-power torsion module, in the sense of `IsElementPowerTorsion`, is
killed by a power of `f`. -/
private theorem exists_pow_smul_eq_zero_of_isElementPowerTorsion {M : Type*} [AddCommGroup M]
    [Module A M] {f : A} (h : IsElementPowerTorsion A M f) (x : M) : ∃ k : ℕ, f ^ k • x = 0 :=
  (h x).imp fun _ hk => hk.2

/-- Let `A` be a commutative ring and `f : A`. Let `α : E ⟶ E'` be a morphism of `D(A)` with `E`
perfect and every cohomology module of `E'` `f`-power torsion. Then `f ^ n • α = 0` for some
`n`. -/
public theorem exists_pow_smul_eq_zero_of_isPerfect (f : A)
    {E E' : DerivedCategory (ModuleCat.{u} A)} (hE : IsPerfect E)
    (hE' : ∀ p : ℤ, IsElementPowerTorsion A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj E' : Type u) f)
    (α : E ⟶ E') : ∃ n : ℕ, f ^ n • α = 0 :=
  homPowerTorsion_of_isPerfect f E'
    (fun p => exists_pow_smul_eq_zero_of_isElementPowerTorsion (hE' p)) hE α

/-- A module whose support lies in the zero locus `V(f)` is `f`-power torsion. -/
public theorem isElementPowerTorsion_of_support_subset_zeroLocus {M : Type*} [AddCommGroup M]
    [Module A M] {f : A} (h : Module.support A M ⊆ PrimeSpectrum.zeroLocus {f}) :
    IsElementPowerTorsion A M f := by
  have hFG : (Ideal.span {f}).FG := Submodule.fg_span_singleton f
  have hsub : Module.support A M ⊆
      PrimeSpectrum.zeroLocus ((Ideal.span {f} : Ideal A) : Set A) := by
    rwa [PrimeSpectrum.zeroLocus_span]
  intro m
  obtain ⟨n, hn, hkill⟩ := isIPowerTorsion_of_support_subset hFG hsub m
  exact ⟨n, hn, hkill _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self f) n)⟩

/-- Let `A` be a commutative ring and let `f : A`. Let `α : E ⟶ E'` be a morphism in `D(A)` such
that `E` is perfect and `E'` is supported on `T = V(f)`, that is, every cohomology module of `E'`
has support contained in the zero locus of `f`. Then there is an `n ≥ 0` with `f ^ n • α = 0`. -/
@[stacks 08EJ "affine case, in D(A); the geometric form on an affine scheme, and the \
quasi-compact quasi-separated case, are in the AlgebraicGeometry directory"]
public theorem exists_pow_smul_eq_zero_of_isPerfect_of_support_subset_zeroLocus (f : A)
    {E E' : DerivedCategory (ModuleCat.{u} A)} (hE : IsPerfect E)
    (hE' : ∀ p : ℤ, Module.support A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj E' : Type u) ⊆
      PrimeSpectrum.zeroLocus {f})
    (α : E ⟶ E') : ∃ n : ℕ, f ^ n • α = 0 :=
  exists_pow_smul_eq_zero_of_isPerfect f hE
    (fun p => isElementPowerTorsion_of_support_subset_zeroLocus (hE' p)) α

end StacksDraft.Perfect

end
