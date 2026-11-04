module

public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass.PrimeDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ExtendedIntegers
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.Codimension
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksCore.Tactic.StacksAttribute

/-!
# Prime divisors, codimension one and delta-dimension

Let `X` be an integral scheme locally of finite type over the base scheme `S` of chapter 42 of
the Stacks Project. Stacks 02RK says that for an integral closed subscheme `Z ⊆ X` the three
conditions

* `Z` is a prime divisor,
* `Z` has codimension one in `X`,
* `dim_δ(Z) = dim_δ(X) - 1`,

are equivalent, and that every irreducible component of an effective Cartier divisor on `X`
satisfies them.

The first equivalence is the definition of a prime divisor, read through the bijection between
integral closed subschemes of `X` and points of `X` that sends an integral closed subscheme to
its generic point. The second is the defining property of a dimension function: the relative
dimension of Stacks 02JW takes the value `dim_δ(X)` at the generic point of `X` and drops by
exactly one along an immediate specialization, so it equals `dim_δ(X) - 1` exactly at the points
of coheight one. That statement is
`Stacks.Chow.relativeDimension_eq_sub_one_iff_coheight_eq_one`, and all that is added here is
the passage from a point to the integral closed subscheme it is the generic point of, and the
embedding of the resulting integer identity into `EInt`.

## Main results

* `Stacks.Chow.exists_primeDivisor_iff_codimension_one` — **Stacks 02RK**: an integral closed
  subscheme is a prime divisor exactly when it has codimension one.
* `Stacks.Chow.codimension_one_iff_schemeDeltaDimension` — **Stacks 02RK**: it has codimension
  one exactly when its delta-dimension is one less than that of the ambient scheme.
* `Stacks.Chow.deltaDimension_irreducibleComponent_of_coheight_eq_one` — an irreducible
  component of a closed subscheme whose generic point has coheight one has delta-dimension one
  less than the ambient scheme. This is the step that computes the delta-dimension of a
  component of an effective Cartier divisor, once the component's generic point is known to
  have coheight one.
* `Stacks.Chow.deltaDimension_irreducibleComponent_isEffectiveCartierDivisor` — **Stacks 02RK**:
  every irreducible component of an effective Cartier divisor has delta-dimension one less than
  the ambient scheme.

## References

* [Stacks Project, Tag 02RK](https://stacks.math.columbia.edu/tag/02RK)
* [Stacks Project, Tag 0BE2](https://stacks.math.columbia.edu/tag/0BE2)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

/-- **Stacks 02RK.** An integral closed subscheme of `X` is a prime divisor exactly when the
closure of its generic point has codimension one in `X`. This is the definition of a prime
divisor, read through the presentation of an integral closed subscheme by its ideal sheaf. -/
@[stacks 02RK "prime_divisor_iff_delta_dimension"]
theorem exists_primeDivisor_iff_codimension_one {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : IsIntegral I.subscheme) :
    (∃ D : Stacks.Divisors.PrimeDivisor X, D.idealSheaf = I) ↔
      codimension (IrreducibleCloseds.closureSingleton (genericPointOf I hI)) = 1 := by
  refine ⟨?_, fun h ↦ ⟨⟨I, hI, h⟩, rfl⟩⟩
  rintro ⟨D, rfl⟩
  exact D.codimension_one

/-- The delta-dimension of an integral closed subscheme of a scheme locally of finite type over
the base is the relative dimension of its generic point, read on the ambient scheme. -/
theorem schemeDeltaDimension_subschemeι_comp (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (I : X.IdealSheafData)
    (hI : IsIntegral I.subscheme) :
    schemeDeltaDimension C (I.subschemeι ≫ f) =
      ((relativeDimension C.dimensionFunction f (genericPointOf I hI) : ℤ) : EInt) := by
  let _ := hI
  rw [schemeDeltaDimension_eq_genericPoint C (I.subschemeι ≫ f), genericPointOf,
    relativeDimension_comp_closedImmersion]

/-- On an integral scheme, one less than the delta-dimension is the relative dimension of the
generic point minus one. -/
private theorem schemeDeltaDimension_add_neg_one_eq (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsIntegral X] :
    schemeDeltaDimension C f + (-1 : ℤ) =
      ((relativeDimension C.dimensionFunction f (genericPoint X) - 1 : ℤ) : EInt) := by
  rw [schemeDeltaDimension_eq_genericPoint C f, ← coe_add_coe_eq_coe_add, sub_eq_add_neg]

/-- **Stacks 02RK.** An integral closed subscheme of an integral scheme `X` locally of finite
type over the base has codimension one exactly when its delta-dimension is one less than that
of `X`. -/
@[stacks 02RK "prime_divisor_iff_delta_dimension"]
theorem codimension_one_iff_schemeDeltaDimension (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsIntegral X] (I : X.IdealSheafData)
    (hI : IsIntegral I.subscheme) :
    codimension (IrreducibleCloseds.closureSingleton (genericPointOf I hI)) = 1 ↔
      schemeDeltaDimension C (I.subschemeι ≫ f) = schemeDeltaDimension C f + (-1 : ℤ) := by
  rw [Stacks.Divisors.PrimeDivisor.codimension_closureSingleton,
    schemeDeltaDimension_subschemeι_comp C f I hI, schemeDeltaDimension_add_neg_one_eq C f,
    ← relativeDimension_eq_sub_one_iff_coheight_eq_one C f
      (schemeDeltaDimension_eq_genericPoint C f) (genericPointOf I hI)]
  exact WithBotTop.coe_injective.eq_iff.symm

/-- An irreducible component of a closed subscheme of an integral scheme `X` locally of finite
type over the base, whose generic point has coheight one in `X`, has delta-dimension one less
than `X`.

Combined with the fact that the generic point of an irreducible component of an effective
Cartier divisor has ambient local ring of Krull dimension one, this is the second half of
Stacks 02RK. -/
theorem deltaDimension_irreducibleComponent_of_coheight_eq_one (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsIntegral X]
    (D : X.IdealSheafData) (Z : irreducibleComponents D.subscheme)
    (hZ : coheight (D.subschemeι.base Z.2.1.genericPoint) = 1) :
    (deltaDimension C (D.subschemeι ≫ f)
        ⟨Z, Z.2.1, isClosed_of_mem_irreducibleComponents (Z : Set D.subscheme) Z.2⟩ : EInt) =
      schemeDeltaDimension C f + (-1 : ℤ) := by
  have hval : deltaDimension C (D.subschemeι ≫ f)
      ⟨Z, Z.2.1, isClosed_of_mem_irreducibleComponents (Z : Set D.subscheme) Z.2⟩ =
      relativeDimension C.dimensionFunction f (D.subschemeι.base Z.2.1.genericPoint) := by
    rw [deltaDimension_eq_of_isGenericPoint C (D.subschemeι ≫ f) _ Z.2.1.genericPoint
      (Z.2.1.isGenericPoint_genericPoint
        (isClosed_of_mem_irreducibleComponents (Z : Set D.subscheme) Z.2)),
      relativeDimension_comp_closedImmersion]
  rw [hval, relativeDimension_eq_sub_one_of_coheight_eq_one C f
    (schemeDeltaDimension_eq_genericPoint C f) hZ, schemeDeltaDimension_add_neg_one_eq]

/-- **Stacks 02RK.** Every irreducible component of an effective Cartier divisor on an integral
scheme locally of finite type over the base has delta-dimension one less than the ambient
scheme.

The generic point of such a component has ambient local ring of Krull dimension one, hence
coheight one, which is exactly the hypothesis of
`Stacks.Chow.deltaDimension_irreducibleComponent_of_coheight_eq_one`. -/
@[stacks 02RK "cartier_component_delta_dimension"]
theorem deltaDimension_irreducibleComponent_isEffectiveCartierDivisor (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsIntegral X]
    (D : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (Z : irreducibleComponents D.subscheme) :
    (deltaDimension C (D.subschemeι ≫ f)
        ⟨Z, Z.2.1, isClosed_of_mem_irreducibleComponents (Z : Set D.subscheme) Z.2⟩ : EInt) =
      schemeDeltaDimension C f + (-1 : ℤ) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine deltaDimension_irreducibleComponent_of_coheight_eq_one C f D Z ?_
  exact_mod_cast
    (ringKrullDim_stalk_eq_coheight (D.subschemeι.base Z.2.1.genericPoint)).symm.trans
      (ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor D hD Z.2.1.genericPoint
        ⟨Z, Z.2.1.isGenericPoint_genericPoint
          (isClosed_of_mem_irreducibleComponents (Z : Set D.subscheme) Z.2)⟩)

end Stacks.Chow

end
