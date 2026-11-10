module

public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreSolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Solutions at the generic points of the fibres of a flat morphism over a regular curve

Let `S` be an integral scheme, regular of dimension one, and let `X` be normal, flat and locally
of finite type over `S`. Let `x : X` be a generic point of an irreducible component of its own
fibre, that fibre not the generic one. Then the local ring `𝒪_{S, f x}` of the base and the local
ring `𝒪_{X, x}` are discrete valuation rings, the second an extension of the first which is
essentially of finite type, with fraction fields the function field `R(S)` of `S` and
`Frac 𝒪_{X, x}`. Elimination of ramification therefore provides a finite extension `L/R(S)` which
is a solution for `𝒪_{S, f x} → 𝒪_{X, x}`, and for finitely many such points a single finite
extension serves all of them.

## Main definitions

* `AlgebraicGeometry.IsSolutionForStalkOverBase`: the property that a finite extension of the
  function field of `S` is a solution for the extension of discrete valuation rings
  `𝒪_{S, f x} → 𝒪_{X, x}`.

## Main results

* `AlgebraicGeometry.coheight_eq_one_of_ne_genericPoint`: every point other than the generic
  point of an integral scheme of dimension one has codimension one.
* `AlgebraicGeometry.exists_finite_extension_isSolutionForStalkOverBase`: such a finite extension
  of the function field exists for a single point.
* `AlgebraicGeometry.exists_finite_extension_forall_isSolutionForStalkOverBase`: one finite
  extension of the function field serves finitely many points at once.

## Implementation notes

The structure map of `𝒪_{X, x}` over `𝒪_{S, f x}` is the stalk map `f.stalkMap x`. For `S`
integral the fraction field of every local ring `𝒪_{S, s}` is the function field of `S`, so one
field `R(S)` serves every point.

The hypothesis that the fibre through `x` is not the generic fibre is `f.base x ≠ genericPoint S`.

The base is asked to be normal and locally Noetherian of dimension one. For a locally Noetherian
scheme of dimension at most one this is equivalent to being regular, by
`AlgebraicGeometry.isRegular_iff_isNormal_of_topologicalKrullDim_le_one`.

The scheme `X` is assumed normal and locally Noetherian.

## References

* [Stacks Project, Tag 0BRQ](https://stacks.math.columbia.edu/tag/0BRQ)
* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 09II](https://stacks.math.columbia.edu/tag/09II)
* [Stacks Project, Tag 0GLR](https://stacks.math.columbia.edu/tag/0GLR)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
-/

public noncomputable section

open CategoryTheory Order

universe u

namespace AlgebraicGeometry

/-- **Every point other than the generic point of an integral scheme of dimension one has
codimension one.** -/
theorem coheight_eq_one_of_ne_genericPoint (S : Scheme.{u}) [IsIntegral S]
    (hdim : topologicalKrullDim S = 1) {s : S} (hs : s ≠ genericPoint S) :
    coheight s = 1 := by
  have h : (coheight s : WithBot ℕ∞) = 1 :=
    (ringKrullDim_stalk_eq_coheight s).symm.trans
      (Stacks.AlgebraicGeometry.AmpleDimensionOne.ringKrullDim_stalk_eq_one_of_ne_genericPoint
        S hdim hs)
  exact_mod_cast h

section Plumbing

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- The local ring of `X` at `x` is an algebra over the local ring of `S` at the image of `x`, by
the stalk map of `f`. -/
@[instance_reducible]
def stalkAlgebraOfHom : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
  (f.stalkMap x).hom.toAlgebra

/-- The stalk map of a morphism of schemes is a local ring homomorphism. -/
lemma isLocalHom_algebraMap_stalkAlgebraOfHom :
    letI := stalkAlgebraOfHom f x
    IsLocalHom (algebraMap (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) :=
  inferInstanceAs (IsLocalHom (f.stalkMap x).hom)

/-- **The local ring of `X` at `x` is faithfully flat over the local ring of `S` below it when `f`
is flat.** -/
lemma faithfullyFlat_stalkAlgebraOfHom [Flat f] :
    letI := stalkAlgebraOfHom f x
    Module.FaithfullyFlat (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
  let := stalkAlgebraOfHom f x
  have : Module.Flat (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  have : IsLocalHom (algebraMap (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) :=
    isLocalHom_algebraMap_stalkAlgebraOfHom f x
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- For `f` flat the structure map of the local ring of `X` at `x` over the local ring of `S`
below it is injective. -/
lemma faithfulSMul_stalkAlgebraOfHom [Flat f] :
    letI := stalkAlgebraOfHom f x
    FaithfulSMul (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
  let := stalkAlgebraOfHom f x
  have := faithfullyFlat_stalkAlgebraOfHom f x
  infer_instance

/-- **The two local rings form an extension of discrete valuation rings** when `f` is flat and
both local rings are discrete valuation rings. -/
lemma isExtension_stalkAlgebraOfHom [Flat f]
    [IsDomain (S.presheaf.stalk (f.base x))]
    [IsDiscreteValuationRing (S.presheaf.stalk (f.base x))]
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    letI := stalkAlgebraOfHom f x
    IsDiscreteValuationRing.IsExtension (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
  let := stalkAlgebraOfHom f x
  have := faithfulSMul_stalkAlgebraOfHom f x
  have := isLocalHom_algebraMap_stalkAlgebraOfHom f x
  exact ⟨⟩

/-- **The local ring of `X` at `x` is essentially of finite type over the local ring of `S` below
it** when `f` is locally of finite type. -/
lemma essFiniteType_stalkAlgebraOfHom [LocallyOfFiniteType f] :
    letI := stalkAlgebraOfHom f x
    Algebra.EssFiniteType (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
  let := stalkAlgebraOfHom f x
  change RingHom.EssFiniteType (f.stalkMap x).hom
  exact LocallyOfFiniteType.stalkMap f x

/-- For `f` flat the composite of the stalk map with the map of `𝒪_{X, x}` into its fraction
field is injective. -/
lemma injective_algebraMap_stalkFractionRingOverBase [Flat f] [IsDomain (X.presheaf.stalk x)] :
    letI := stalkAlgebraOfHom f x
    Function.Injective
      (algebraMap (S.presheaf.stalk (f.base x)) (FractionRing (X.presheaf.stalk x))) := by
  let := stalkAlgebraOfHom f x
  have := faithfulSMul_stalkAlgebraOfHom f x
  rw [IsScalarTower.algebraMap_eq (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x)
    (FractionRing (X.presheaf.stalk x))]
  exact (IsFractionRing.injective (X.presheaf.stalk x)
    (FractionRing (X.presheaf.stalk x))).comp (FaithfulSMul.algebraMap_injective _ _)

/-- The fraction field of `𝒪_{X, x}` is an algebra over the function field of `S`: the injection
of `𝒪_{S, f x}` into it extends to the fraction field of `𝒪_{S, f x}`, which for `S` integral is
the function field of `S`. -/
@[instance_reducible]
def algebraFunctionFieldStalkFractionRing [IsIntegral S] [Flat f]
    [IsDomain (X.presheaf.stalk x)] :
    Algebra S.functionField (FractionRing (X.presheaf.stalk x)) :=
  let := stalkAlgebraOfHom f x
  (IsFractionRing.lift (injective_algebraMap_stalkFractionRingOverBase f x)).toAlgebra

/-- The map of `𝒪_{S, f x}` into the fraction field of `𝒪_{X, x}` factors through the function
field of `S`. -/
lemma isScalarTower_functionFieldStalkFractionRing [IsIntegral S] [Flat f]
    [IsDomain (X.presheaf.stalk x)] :
    letI := stalkAlgebraOfHom f x
    letI := algebraFunctionFieldStalkFractionRing f x
    IsScalarTower (S.presheaf.stalk (f.base x)) S.functionField
      (FractionRing (X.presheaf.stalk x)) :=
  let := stalkAlgebraOfHom f x
  let := algebraFunctionFieldStalkFractionRing f x
  IsScalarTower.of_algebraMap_eq fun r =>
    (IsFractionRing.lift_algebraMap
      (injective_algebraMap_stalkFractionRingOverBase f x) r).symm

end Plumbing

variable {X S : Scheme.{u}} [IsIntegral S] (f : X ⟶ S) [Flat f] [LocallyOfFiniteType f]
  [IsNormal X] [IsLocallyNoetherian X]

omit [LocallyOfFiniteType f] in
/-- **The local ring at a generic point of a non-generic fibre is a discrete valuation ring.**
Here `f` is flat, `X` is normal and locally Noetherian, and `S` is integral, locally Noetherian
and of dimension one. -/
@[ega "II 7.1.6" "special case"]
lemma isDiscreteValuationRing_stalk_of_mem_genericPoints_over_base [IsLocallyNoetherian S]
    (hdim : topologicalKrullDim S = 1) (x : X) (hs : f.base x ≠ genericPoint S)
    (hg : f.asFiber x ∈ genericPoints (f.fiber (f.base x))) :
    IsDiscreteValuationRing (X.presheaf.stalk x) :=
  isDiscreteValuationRing_stalk_of_coheight_eq_one
    ((coheight_eq_coheight_base_of_asFiber_mem_genericPoints f hg).trans
      (coheight_eq_one_of_ne_genericPoint S hdim hs))

/-- The local ring at a point other than the generic point of a one-dimensional base is a
discrete valuation ring. -/
private lemma isDiscreteValuationRing_stalk_of_ne_genericPoint [IsNormal S]
    [IsLocallyNoetherian S] (hdim : topologicalKrullDim S = 1) {s : S}
    (hs : s ≠ genericPoint S) : IsDiscreteValuationRing (S.presheaf.stalk s) :=
  isDiscreteValuationRing_stalk_of_coheight_eq_one (X := S)
    (coheight_eq_one_of_ne_genericPoint S hdim hs)

/-- **`L` is a solution for the extension of discrete valuation rings at `x`.** For `x` a generic
point of an irreducible component of its own fibre, that fibre not the generic one, the local
ring `𝒪_{S, f x}` of the base and the local ring `𝒪_{X, x}` are discrete valuation rings with
fraction fields the function field of `S` and `Frac 𝒪_{X, x}`, the second an extension of the
first; this is the base-change package of Tag 09EM for the finite extension `L` of the function
field, together with the formal smoothness of Tag 09EN(2). -/
def IsSolutionForStalkOverBase [IsNormal S] [IsLocallyNoetherian S]
    (hdim : topologicalKrullDim S = 1) (x : X) (hs : f.base x ≠ genericPoint S)
    (hg : f.asFiber x ∈ genericPoints (f.fiber (f.base x)))
    (L : Type u) [Field L] [Algebra S.functionField L]
    [Module.Finite S.functionField L] : Prop :=
  let := stalkAlgebraOfHom f x
  have := isDiscreteValuationRing_stalk_of_coheight_eq_one (X := S)
    (coheight_eq_one_of_ne_genericPoint S hdim hs)
  have := isDiscreteValuationRing_stalk_of_mem_genericPoints_over_base f hdim x hs hg
  have := isExtension_stalkAlgebraOfHom f x
  let := algebraFunctionFieldStalkFractionRing f x
  have := isScalarTower_functionFieldStalkFractionRing f x
  let : Algebra (S.presheaf.stalk (f.base x)) L :=
    ((algebraMap S.functionField L).comp
      (algebraMap (S.presheaf.stalk (f.base x)) S.functionField)).toAlgebra
  have : IsScalarTower (S.presheaf.stalk (f.base x)) S.functionField L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u, u, u, u, u, u, u, u}
      (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) S.functionField
      (FractionRing (X.presheaf.stalk x)) L,
    D.IsSolution.{u, u, u, u, u, u, u, u, u}

/-- **A solution at a generic point of a non-generic fibre, over a regular curve.** For `X` normal
and locally Noetherian, flat and locally of finite type over an integral, normal, locally
Noetherian scheme `S` of dimension one, and `x : X` a generic point of an irreducible component of
its own fibre, that fibre not the generic one, there is a finite extension `L` of the function
field of `S` which is a solution for the extension of discrete valuation rings
`𝒪_{S, f x} → 𝒪_{X, x}`. -/
theorem exists_finite_extension_isSolutionForStalkOverBase [IsNormal S] [IsLocallyNoetherian S]
    (hdim : topologicalKrullDim S = 1) (x : X) (hs : f.base x ≠ genericPoint S)
    (hg : f.asFiber x ∈ genericPoints (f.fiber (f.base x))) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra S.functionField L)
      (_ : Module.Finite S.functionField L),
      IsSolutionForStalkOverBase f hdim x hs hg L := by
  let := stalkAlgebraOfHom f x
  have := isDiscreteValuationRing_stalk_of_ne_genericPoint hdim hs
  have := isDiscreteValuationRing_stalk_of_mem_genericPoints_over_base f hdim x hs hg
  have := isExtension_stalkAlgebraOfHom f x
  have := essFiniteType_stalkAlgebraOfHom f x
  let := algebraFunctionFieldStalkFractionRing f x
  have := isScalarTower_functionFieldStalkFractionRing f x
  obtain ⟨L, hfield, halgK, halgA, htower, hfin, D, hD⟩ :=
    Stacks.EliminateRamification.exists_finite_extension_isSolution.{u, u, u, u, u}
      (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) S.functionField
      (FractionRing (X.presheaf.stalk x))
  let := hfield
  let := halgK
  let := halgA
  have := htower
  have := hfin
  refine ⟨L, hfield, halgK, hfin, ?_⟩
  have hext : halgA = ((algebraMap S.functionField L).comp
      (algebraMap (S.presheaf.stalk (f.base x)) S.functionField)).toAlgebra :=
    Algebra.algebra_ext _ _ fun r =>
      IsScalarTower.algebraMap_apply (S.presheaf.stalk (f.base x)) S.functionField L r
  subst hext
  exact ⟨D, hD⟩

/-- **One finite extension of the function field solving finitely many points at once.** With `X`
normal and locally Noetherian, flat and locally of finite type over an integral, normal, locally
Noetherian scheme `S` of dimension one, let `x i` be finitely many points, each a generic point of
an irreducible component of its own fibre, none of those fibres the generic one. Then a single
finite extension `L` of the function field of `S` is a solution for every extension of discrete
valuation rings `𝒪_{S, f (x i)} → 𝒪_{X, x i}`. -/
theorem exists_finite_extension_forall_isSolutionForStalkOverBase [IsNormal S]
    [IsLocallyNoetherian S] (hdim : topologicalKrullDim S = 1)
    {ι : Type} [Finite ι] (x : ι → X)
    (hs : ∀ i, f.base (x i) ≠ genericPoint S)
    (hg : ∀ i, f.asFiber (x i) ∈ genericPoints (f.fiber (f.base (x i)))) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra S.functionField L)
      (_ : Module.Finite S.functionField L),
      ∀ i, IsSolutionForStalkOverBase f hdim (x i) (hs i) (hg i) L := by
  classical
  choose F hfield halg hfin hsol using fun i =>
    exists_finite_extension_isSolutionForStalkOverBase f hdim (x i) (hs i) (hg i)
  let := hfield
  let := halg
  have := hfin
  obtain ⟨E, hEfield, hEalg, hEfin, ⟨φ⟩⟩ :=
    exists_finiteDimensional_algHom_forall (K := S.functionField) F
  let := hEfield
  let := hEalg
  have := hEfin
  refine ⟨E, hEfield, hEalg, hEfin, fun i => ?_⟩
  let := stalkAlgebraOfHom f (x i)
  have := isDiscreteValuationRing_stalk_of_ne_genericPoint hdim (hs i)
  have := isDiscreteValuationRing_stalk_of_mem_genericPoints_over_base f hdim (x i) (hs i) (hg i)
  have := isExtension_stalkAlgebraOfHom f (x i)
  let := algebraFunctionFieldStalkFractionRing f (x i)
  have := isScalarTower_functionFieldStalkFractionRing f (x i)
  let : Algebra (S.presheaf.stalk (f.base (x i))) (F i) :=
    ((algebraMap S.functionField (F i)).comp
      (algebraMap (S.presheaf.stalk (f.base (x i))) S.functionField)).toAlgebra
  have : IsScalarTower (S.presheaf.stalk (f.base (x i))) S.functionField (F i) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra (S.presheaf.stalk (f.base (x i))) E :=
    ((algebraMap S.functionField E).comp
      (algebraMap (S.presheaf.stalk (f.base (x i))) S.functionField)).toAlgebra
  have : IsScalarTower (S.presheaf.stalk (f.base (x i))) S.functionField E :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra (F i) E := (φ i).toRingHom.toAlgebra
  have : IsScalarTower S.functionField (F i) E :=
    IsScalarTower.of_algebraMap_eq fun k => ((φ i).commutes k).symm
  have := IsScalarTower.to₁₃₄ (S.presheaf.stalk (f.base (x i))) S.functionField (F i) E
  have : Module.Finite (F i) E := Module.Finite.of_restrictScalars_finite S.functionField (F i) E
  exact IsDiscreteValuationRing.exists_isSolution_of_tower
    (S.presheaf.stalk (f.base (x i))) (X.presheaf.stalk (x i)) S.functionField
    (FractionRing (X.presheaf.stalk (x i))) (F i) E (hsol i)

end AlgebraicGeometry

end
