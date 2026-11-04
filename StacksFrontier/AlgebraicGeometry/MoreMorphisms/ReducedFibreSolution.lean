module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.StalkBaseAlgebra
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.GenericPointCoheight
public import StacksFrontier.AlgebraicGeometry.Properties.NormalStalkDvr
public import StacksFrontier.FieldTheory.CommonFiniteExtension
public import StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationTheorem
public import StacksFrontier.RingTheory.DiscreteValuationRing.SolutionTower

/-!
# Solutions at the generic points of the fibres of a flat morphism over a Dedekind base

Let `A` be a Dedekind domain with fraction field `K` and let `X` be normal, flat and locally of
finite type over `A`. Let `x : X` be a generic point of an irreducible component of its own
fibre, and assume that fibre is not the generic one. Then the localization `A_x` of `A` at the
prime under `x` and the local ring `𝒪_{X, x}` are discrete valuation rings, the second an
extension of the first which is essentially of finite type, with fraction fields `K` and
`Frac 𝒪_{X, x}`. Elimination of ramification therefore provides a finite extension `K₁/K` which
is a solution for `A_x → 𝒪_{X, x}`, and for finitely many such points a single finite extension
serves all of them: embed the individual solutions into a common finite extension and use that
a finite extension of a solution is again a solution.

## Main results

* `AlgebraicGeometry.IsSolutionForStalk`: the property that a finite extension of `K` is a
  solution for the extension of discrete valuation rings `A_x → 𝒪_{X, x}`.
* `AlgebraicGeometry.exists_finite_extension_isSolution_stalk`: such a finite extension exists
  for a single point.
* `AlgebraicGeometry.exists_finite_extension_forall_isSolution_stalk`: one finite extension
  serves finitely many points at once.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 09II](https://stacks.math.columbia.edu/tag/09II)
* [Stacks Project, Tag 0GLR](https://stacks.math.columbia.edu/tag/0GLR)
-/

public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section Plumbing

variable {A : Type u} [CommRing A] [IsDedekindDomain A]
  (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (x : X) [(f.base x).asIdeal.IsPrime]

/-- The fraction field `K` of `A` as an algebra over the localization of `A` at the prime under
`x`, through the factorization of the structure map of `K` over this localization. -/
@[instance_reducible]
def algebraLocalizationAtPrimeBase :
    Algebra (Localization.AtPrime (f.base x).asIdeal) K :=
  (IsLocalization.lift (M := (f.base x).asIdeal.primeCompl)
    (S := Localization.AtPrime (f.base x).asIdeal) (g := algebraMap A K)
    (fun y => IsLocalization.map_units K
      ⟨y.1, Ideal.primeCompl_le_nonZeroDivisors _ y.2⟩)).toAlgebra

/-- The structure map of `K` over `A` factors through the localization of `A` at the prime
under `x`. -/
lemma isScalarTower_localizationAtPrimeBase :
    letI := algebraLocalizationAtPrimeBase K f x
    IsScalarTower A (Localization.AtPrime (f.base x).asIdeal) K :=
  let := algebraLocalizationAtPrimeBase K f x
  IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.lift_eq _ r).symm

/-- `K` is the fraction field of the localization of `A` at the prime under `x`. -/
lemma isFractionRing_localizationAtPrimeBase :
    letI := algebraLocalizationAtPrimeBase K f x
    IsFractionRing (Localization.AtPrime (f.base x).asIdeal) K :=
  let := algebraLocalizationAtPrimeBase K f x
  let := isScalarTower_localizationAtPrimeBase K f x
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (f.base x).asIdeal.primeCompl _ K

/-- The localization of a Dedekind domain at a nonzero prime is a discrete valuation ring. -/
lemma isDiscreteValuationRing_localizationAtPrimeBase (hs : (f.base x).asIdeal ≠ ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime (f.base x).asIdeal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (A := CommRingCat.of A) hs _

omit [(f.base x).asIdeal.IsPrime] in
/-- **The local ring at a generic point of a non-generic fibre is a discrete valuation ring.**
For `X` normal, flat and locally of finite type over a Dedekind domain `A`, and `x` a generic
point of an irreducible component of its own fibre over a nonzero prime of `A`, the local ring
`𝒪_{X, x}` is a discrete valuation ring. -/
lemma isDiscreteValuationRing_stalk_of_mem_genericPoints [Flat f] [LocallyOfFiniteType f]
    [IsNormal X] (hs : (f.base x).asIdeal ≠ ⊥)
    (hg : f.asFiber x ∈ genericPoints (f.fiber (f.base x))) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  have : IsNoetherianRing (CommRingCat.of A) := inferInstanceAs (IsNoetherianRing A)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have h := coheight_fiberι_eq_one_of_isDedekindDomain f hs hg
  rw [f.fiberι_asFiber x] at h
  exact isDiscreteValuationRing_stalk_of_coheight_eq_one h

omit [IsDedekindDomain A] in
/-- **The local ring of `X` at `x` is essentially of finite type over the localization of the
base**, for `f` locally of finite type. -/
lemma essFiniteType_stalkAlgebraOfSpecHom [LocallyOfFiniteType f] :
    letI := stalkAlgebraOfSpecHom f x
    Algebra.EssFiniteType (Localization.AtPrime (f.base x).asIdeal) (X.presheaf.stalk x) := by
  show RingHom.EssFiniteType (localizationAtPrimeToStalk f x).hom
  rw [localizationAtPrimeToStalk, CommRingCat.hom_comp]
  exact (RingHom.EssFiniteType.respectsIso.cancel_left_isIso
    (Spec.stalkIso (.of A) (f.base x)).inv (f.stalkMap x)).mpr
      (LocallyOfFiniteType.stalkMap f x)

omit [IsDedekindDomain A] in
/-- For `f` flat the composite of the structure map `A_x → 𝒪_{X, x}` with the map of
`𝒪_{X, x}` into its fraction field is injective. -/
lemma injective_algebraMap_stalkFractionRing [Flat f] [IsNormal X] :
    letI := stalkAlgebraOfSpecHom f x
    Function.Injective
      (algebraMap (Localization.AtPrime (f.base x).asIdeal)
        (FractionRing (X.presheaf.stalk x))) := by
  let := stalkAlgebraOfSpecHom f x
  have := faithfulSMul_stalkAlgebraOfSpecHom f x
  rw [IsScalarTower.algebraMap_eq (Localization.AtPrime (f.base x).asIdeal)
    (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))]
  exact (IsFractionRing.injective (X.presheaf.stalk x)
    (FractionRing (X.presheaf.stalk x))).comp
      (FaithfulSMul.algebraMap_injective _ _)

/-- The fraction field of `𝒪_{X, x}` is an algebra over `K`: the injection of `A_x` into it
extends to the fraction field `K` of `A_x`. -/
@[instance_reducible]
def algebraStalkFractionRing [Flat f] [IsNormal X] :
    Algebra K (FractionRing (X.presheaf.stalk x)) :=
  letI := stalkAlgebraOfSpecHom f x
  letI := algebraLocalizationAtPrimeBase K f x
  letI := isFractionRing_localizationAtPrimeBase K f x
  (IsFractionRing.lift (injective_algebraMap_stalkFractionRing f x)).toAlgebra

/-- The map of `A_x` into the fraction field of `𝒪_{X, x}` factors through `K`. -/
lemma isScalarTower_stalkFractionRing [Flat f] [IsNormal X] :
    letI := stalkAlgebraOfSpecHom f x
    letI := algebraLocalizationAtPrimeBase K f x
    letI := algebraStalkFractionRing K f x
    IsScalarTower (Localization.AtPrime (f.base x).asIdeal) K
      (FractionRing (X.presheaf.stalk x)) :=
  let := stalkAlgebraOfSpecHom f x
  let := algebraLocalizationAtPrimeBase K f x
  let := isFractionRing_localizationAtPrimeBase K f x
  let := algebraStalkFractionRing K f x
  IsScalarTower.of_algebraMap_eq fun r =>
    (IsFractionRing.lift_algebraMap (injective_algebraMap_stalkFractionRing f x) r).symm

end Plumbing

variable {A : Type u} [CommRing A] [IsDedekindDomain A]
  (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f] [LocallyOfFiniteType f] [IsNormal X]

/-- **`K₁` is a solution for the extension of discrete valuation rings at `x`.** For `x` a
generic point of an irreducible component of its own fibre, that fibre not the generic one, the
localization `A_x` of `A` at the prime under `x` and the local ring `𝒪_{X, x}` are discrete
valuation rings with fraction fields `K` and `Frac 𝒪_{X, x}`, the second an extension of the
first; this is the base-change package of Tag 09EM for the finite extension `K₁/K`, together
with the formal smoothness of Tag 09EN(2). -/
@[expose]
def IsSolutionForStalk (x : X) (hs : (f.base x).asIdeal ≠ ⊥)
    (hg : f.asFiber x ∈ genericPoints (f.fiber (f.base x)))
    (K₁ : Type u) [Field K₁] [Algebra K K₁] [Module.Finite K K₁] : Prop :=
  letI : (f.base x).asIdeal.IsPrime := (f.base x).isPrime
  letI := stalkAlgebraOfSpecHom f x
  haveI := isDiscreteValuationRing_localizationAtPrimeBase f x hs
  haveI := isDiscreteValuationRing_stalk_of_mem_genericPoints f x hs hg
  haveI := isExtension_stalkAlgebraOfSpecHom f x
  letI := algebraLocalizationAtPrimeBase K f x
  haveI := isFractionRing_localizationAtPrimeBase K f x
  letI := algebraStalkFractionRing K f x
  haveI := isScalarTower_stalkFractionRing K f x
  letI : Algebra (Localization.AtPrime (f.base x).asIdeal) K₁ :=
    ((algebraMap K K₁).comp
      (algebraMap (Localization.AtPrime (f.base x).asIdeal) K)).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime (f.base x).asIdeal) K K₁ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u, u, u, u, u, u, u, u}
      (Localization.AtPrime (f.base x).asIdeal) (X.presheaf.stalk x) K
      (FractionRing (X.presheaf.stalk x)) K₁,
    D.IsSolution.{u, u, u, u, u, u, u, u, u}

/-- **A solution at a generic point of a non-generic fibre.** For `X` normal, flat and locally of
finite type over a Dedekind domain `A` with fraction field `K`, and `x : X` a generic point of an
irreducible component of its own fibre, that fibre not the generic one, there is a finite
extension `K₁/K` which is a solution for the extension of discrete valuation rings
`A_x → 𝒪_{X, x}`. -/
theorem exists_finite_extension_isSolution_stalk (x : X)
    (hs : (f.base x).asIdeal ≠ ⊥)
    (hg : f.asFiber x ∈ genericPoints (f.fiber (f.base x))) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Module.Finite K K₁),
      IsSolutionForStalk K f x hs hg K₁ := by
  let : (f.base x).asIdeal.IsPrime := (f.base x).isPrime
  let := stalkAlgebraOfSpecHom f x
  have := isDiscreteValuationRing_localizationAtPrimeBase f x hs
  have := isDiscreteValuationRing_stalk_of_mem_genericPoints f x hs hg
  have := isExtension_stalkAlgebraOfSpecHom f x
  have := essFiniteType_stalkAlgebraOfSpecHom f x
  let := algebraLocalizationAtPrimeBase K f x
  have := isFractionRing_localizationAtPrimeBase K f x
  let := algebraStalkFractionRing K f x
  have := isScalarTower_stalkFractionRing K f x
  obtain ⟨K₁, hfield, halgK, halgA, htower, hfin, D, hD⟩ :=
    Stacks.EliminateRamification.exists_finite_extension_isSolution.{u, u, u, u, u}
      (Localization.AtPrime (f.base x).asIdeal) (X.presheaf.stalk x) K
      (FractionRing (X.presheaf.stalk x))
  let := hfield
  let := halgK
  let := halgA
  have := htower
  have := hfin
  refine ⟨K₁, hfield, halgK, hfin, ?_⟩
  have hext : halgA = ((algebraMap K K₁).comp
      (algebraMap (Localization.AtPrime (f.base x).asIdeal) K)).toAlgebra :=
    Algebra.algebra_ext _ _ fun r =>
      IsScalarTower.algebraMap_apply (Localization.AtPrime (f.base x).asIdeal) K K₁ r
  subst hext
  exact ⟨D, hD⟩

/-- **One finite extension solving finitely many points at once.** With `X` normal, flat and
locally of finite type over a Dedekind domain `A` with fraction field `K`, let `x i` be finitely
many points, each a generic point of an irreducible component of its own fibre, none of those
fibres the generic one. Then a single finite extension `K₁/K` is a solution for every extension
of discrete valuation rings `A_{x i} → 𝒪_{X, x i}`. -/
theorem exists_finite_extension_forall_isSolution_stalk {ι : Type} [Finite ι] (x : ι → X)
    (hs : ∀ i, (f.base (x i)).asIdeal ≠ ⊥)
    (hg : ∀ i, f.asFiber (x i) ∈ genericPoints (f.fiber (f.base (x i)))) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Module.Finite K K₁),
      ∀ i, IsSolutionForStalk K f (x i) (hs i) (hg i) K₁ := by
  classical
  choose F hfield halg hfin hsol using fun i =>
    exists_finite_extension_isSolution_stalk K f (x i) (hs i) (hg i)
  let := hfield
  let := halg
  have := hfin
  obtain ⟨E, hEfield, hEalg, hEfin, ⟨φ⟩⟩ := exists_finiteDimensional_algHom_forall (K := K) F
  let := hEfield
  let := hEalg
  have := hEfin
  refine ⟨E, hEfield, hEalg, hEfin, fun i => ?_⟩
  let : (f.base (x i)).asIdeal.IsPrime := (f.base (x i)).isPrime
  let := stalkAlgebraOfSpecHom f (x i)
  have := isDiscreteValuationRing_localizationAtPrimeBase f (x i) (hs i)
  have := isDiscreteValuationRing_stalk_of_mem_genericPoints f (x i) (hs i) (hg i)
  have := isExtension_stalkAlgebraOfSpecHom f (x i)
  let := algebraLocalizationAtPrimeBase K f (x i)
  have := isFractionRing_localizationAtPrimeBase K f (x i)
  let := algebraStalkFractionRing K f (x i)
  have := isScalarTower_stalkFractionRing K f (x i)
  let : Algebra (Localization.AtPrime (f.base (x i)).asIdeal) (F i) :=
    ((algebraMap K (F i)).comp
      (algebraMap (Localization.AtPrime (f.base (x i)).asIdeal) K)).toAlgebra
  have : IsScalarTower (Localization.AtPrime (f.base (x i)).asIdeal) K (F i) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra (Localization.AtPrime (f.base (x i)).asIdeal) E :=
    ((algebraMap K E).comp
      (algebraMap (Localization.AtPrime (f.base (x i)).asIdeal) K)).toAlgebra
  have : IsScalarTower (Localization.AtPrime (f.base (x i)).asIdeal) K E :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra (F i) E := (φ i).toRingHom.toAlgebra
  have : IsScalarTower K (F i) E :=
    IsScalarTower.of_algebraMap_eq fun k => ((φ i).commutes k).symm
  have : IsScalarTower (Localization.AtPrime (f.base (x i)).asIdeal) (F i) E :=
    IsScalarTower.of_algebraMap_eq fun _ => ((φ i).commutes _).symm
  have : Module.Finite (F i) E := Module.Finite.of_restrictScalars_finite K (F i) E
  exact IsDiscreteValuationRing.exists_isSolution_of_tower
    (Localization.AtPrime (f.base (x i)).asIdeal) (X.presheaf.stalk (x i)) K
    (FractionRing (X.presheaf.stalk (x i))) (F i) E (hsol i)

end AlgebraicGeometry

end
