module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreSolution
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSeparableSolutionII
public import StacksFrontier.RingTheory.Nagata.Japanese

/-!
# Separable solutions at the generic points of the fibres of a flat morphism over a Dedekind base

Let `A` be a Nagata Dedekind domain with fraction field `K` and let `X` be normal, flat and
locally of finite type over `A`. Let `x : X` be a generic point of an irreducible component of
its own fibre, that fibre not the generic one. Then the localization `A_x` of `A` at the prime
under `x` and the local ring `𝒪_{X, x}` are discrete valuation rings, the second an extension of
the first which is essentially of finite type, with fraction fields `K` and `Frac 𝒪_{X, x}`. If
that second fraction field is separable over `K`, the separable form of elimination of
ramification provides a finite **separable** extension `K₁ / K` which is a solution for
`A_x → 𝒪_{X, x}`, and for finitely many such points a single finite separable extension serves
all of them: embed the individual solutions into a common finite separable extension and use that
a finite extension of a solution is again a solution.

This is the second and third paragraphs of the proof of the variant of the reduced fibre theorem
with a separable extension, the substitution of the separable statement of Tag 0BRP for Tag 09II
being the only change from the main theorem.

The separability hypothesis is `Frac 𝒪_{X, x} / K` separable. On a normal — in particular
reduced — scheme the local ring at `x` is a domain whose fraction field is the residue field at
the generic point of the irreducible component containing `x`, so this is what the hypothesis of
the source, separability of `κ(η) / K` at every generic point `η` of `X`, supplies at `x`.

## Main definitions

* `AlgebraicGeometry.IsSeparableSolutionForStalk`: the property that a finite extension of `K` is
  a separable solution for the extension of discrete valuation rings `A_x → 𝒪_{X, x}`.

## Main results

* `AlgebraicGeometry.exists_finite_extension_isSeparableSolution_stalk`: such a finite separable
  extension exists for a single point.
* `AlgebraicGeometry.exists_finite_extension_forall_isSeparableSolution_stalk`: one finite
  separable extension serves finitely many points at once.
* `AlgebraicGeometry.IsSeparableSolutionForStalk.isSolutionForStalk`: a separable solution is a
  solution.

## Implementation notes

The Nagata hypothesis is needed on `A_x` rather than on `A`, and passes from `A` to its
localization by Tag 032U. Tag 0BRP takes the Nagata condition on either end of the extension, so
only the disjunct for the base is used.

The individual separable solutions are amalgamated inside an algebraic closure of `K`: the
compositum of finitely many finite separable subextensions is again finite and separable, and the
tower statement Tag 0GLR then transports the solution property from each member to the
compositum. Separability of the compositum is not part of what Tag 0GLR transports; it is carried
alongside, which is why it appears as a separate conjunct.

## References

* [Stacks Project, Tag 0BRR](https://stacks.math.columbia.edu/tag/0BRR)
* [Stacks Project, Tag 0BRP](https://stacks.math.columbia.edu/tag/0BRP)
* [Stacks Project, Tag 0GLR](https://stacks.math.columbia.edu/tag/0GLR)
* [Stacks Project, Tag 032U](https://stacks.math.columbia.edu/tag/032U)
-/

public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] [IsDedekindDomain A]
  (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f] [LocallyOfFiniteType f] [IsNormal X]

/-- **`K₁` is a separable solution for the extension of discrete valuation rings at `x`.** For
`x` a generic point of an irreducible component of its own fibre, that fibre not the generic one,
the localization `A_x` of `A` at the prime under `x` and the local ring `𝒪_{X, x}` are discrete
valuation rings with fraction fields `K` and `Frac 𝒪_{X, x}`, the second an extension of the
first; this is the base-change package of Tag 09EM for the finite extension `K₁ / K`, together
with the formal smoothness of Tag 09EN(2) and separability of `K₁ / K`. -/
def IsSeparableSolutionForStalk (x : X) (hs : (f.base x).asIdeal ≠ ⊥)
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
    D.IsSeparableSolution.{u, u, u, u, u, u, u, u, u}

/-- **A separable solution is a solution.** -/
theorem IsSeparableSolutionForStalk.isSolutionForStalk {x : X} {hs : (f.base x).asIdeal ≠ ⊥}
    {hg : f.asFiber x ∈ genericPoints (f.fiber (f.base x))}
    {K₁ : Type u} [Field K₁] [Algebra K K₁] [Module.Finite K K₁]
    (h : IsSeparableSolutionForStalk K f x hs hg K₁) : IsSolutionForStalk K f x hs hg K₁ := by
  obtain ⟨D, hD, -⟩ := h
  exact ⟨D, hD⟩

/-- **The separable solution property only depends on the point.** The two hypotheses of
`AlgebraicGeometry.IsSeparableSolutionForStalk` are propositions, so for equal points the
predicate transports along the equality by proof irrelevance. -/
theorem isSeparableSolutionForStalk_congr {x y : X} (h : x = y)
    (hsx : (f.base x).asIdeal ≠ ⊥)
    (hgx : f.asFiber x ∈ genericPoints (f.fiber (f.base x)))
    (hsy : (f.base y).asIdeal ≠ ⊥)
    (hgy : f.asFiber y ∈ genericPoints (f.fiber (f.base y)))
    (K₁ : Type u) [Field K₁] [Algebra K K₁] [Module.Finite K K₁]
    (H : IsSeparableSolutionForStalk K f x hsx hgx K₁) :
    IsSeparableSolutionForStalk K f y hsy hgy K₁ := by
  subst h
  exact H

/-- **A separable solution at a generic point of a non-generic fibre.** For `X` normal, flat and
locally of finite type over a Nagata Dedekind domain `A` with fraction field `K`, and `x : X` a
generic point of an irreducible component of its own fibre, that fibre not the generic one, whose
local ring has fraction field separable over `K`, there is a finite separable extension `K₁ / K`
which is a solution for the extension of discrete valuation rings `A_x → 𝒪_{X, x}`. This is Tag
0BRP applied to that extension, which is essentially of finite type because `f` is locally of
finite type and whose base is Nagata because `A` is and localization preserves that (Tag 032U). -/
theorem exists_finite_extension_isSeparableSolution_stalk (hA : IsNagataRing A) (x : X)
    (hs : (f.base x).asIdeal ≠ ⊥)
    (hg : f.asFiber x ∈ genericPoints (f.fiber (f.base x)))
    (hsep : letI : (f.base x).asIdeal.IsPrime := (f.base x).isPrime
      letI := algebraStalkFractionRing K f x
      Algebra.IsSeparableExtension K (FractionRing (X.presheaf.stalk x))) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Module.Finite K K₁),
      IsSeparableSolutionForStalk K f x hs hg K₁ := by
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
  have hnagata : IsNagataRing (Localization.AtPrime (f.base x).asIdeal) :=
    isNagata_of_isLocalization A (f.base x).asIdeal.primeCompl _ hA
  obtain ⟨K₁, hfield, halgK, halgA, htower, hfin, D, hD⟩ :=
    IsDiscreteValuationRing.exists_isSeparableSolution_of_essFiniteType.{u, u, u, u}
      (Localization.AtPrime (f.base x).asIdeal) (X.presheaf.stalk x) K
      (FractionRing (X.presheaf.stalk x)) (.inl hnagata) hsep
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

/-- **One finite separable extension solving finitely many points at once.** With `X` normal,
flat and locally of finite type over a Nagata Dedekind domain `A` with fraction field `K`, let
`x i` be finitely many points, each a generic point of an irreducible component of its own fibre,
none of those fibres the generic one, and each with `Frac 𝒪_{X, x i}` separable over `K`. Then a
single finite **separable** extension `K₁ / K` is a separable solution for every extension of
discrete valuation rings `A_{x i} → 𝒪_{X, x i}`: take a finite separable extension of `K` into
which all the individual separable solutions of Tag 0BRP embed, and apply Tag 0GLR to each of
them. The separability of the common extension is part of the conclusion, so that it is available
even for an empty family. -/
theorem exists_finite_extension_forall_isSeparableSolution_stalk (hA : IsNagataRing A)
    {ι : Type} [Finite ι] (x : ι → X)
    (hs : ∀ i, (f.base (x i)).asIdeal ≠ ⊥)
    (hg : ∀ i, f.asFiber (x i) ∈ genericPoints (f.fiber (f.base (x i))))
    (hsep : ∀ i, letI : (f.base (x i)).asIdeal.IsPrime := (f.base (x i)).isPrime
      letI := algebraStalkFractionRing K f (x i)
      Algebra.IsSeparableExtension K (FractionRing (X.presheaf.stalk (x i)))) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Module.Finite K K₁)
      (_ : Algebra.IsSeparable K K₁),
      ∀ i, IsSeparableSolutionForStalk K f (x i) (hs i) (hg i) K₁ := by
  classical
  choose F hfield halg hfin hsol using fun i =>
    exists_finite_extension_isSeparableSolution_stalk K f hA (x i) (hs i) (hg i) (hsep i)
  let := hfield
  let := halg
  have := hfin
  have hsepF : ∀ i, Algebra.IsSeparable K (F i) := fun i => by
    obtain ⟨-, -, hsepi⟩ := hsol i
    exact hsepi
  have := hsepF
  obtain ⟨E, hEfield, hEalg, hEfin, hEsep, ⟨φ⟩⟩ :=
    exists_finiteDimensional_isSeparable_algHom_forall (K := K) F
  let := hEfield
  let := hEalg
  have := hEfin
  have := hEsep
  refine ⟨E, hEfield, hEalg, hEfin, hEsep, fun i => ?_⟩
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
  obtain ⟨D, hD⟩ := IsDiscreteValuationRing.exists_isSolution_of_tower
    (Localization.AtPrime (f.base (x i)).asIdeal) (X.presheaf.stalk (x i)) K
    (FractionRing (X.presheaf.stalk (x i))) (F i) E
    (hsol i).isSolutionForStalk
  exact ⟨D, hD, hEsep⟩

end AlgebraicGeometry

end
