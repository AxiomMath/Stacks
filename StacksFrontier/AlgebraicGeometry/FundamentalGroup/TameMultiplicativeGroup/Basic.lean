module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOnePullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tame fundamental group of `𝐆_m` over a field

Let `k` be a field and `𝐆_{m,k} = Spec k[x]_x`, the complement of the two points `0` and `∞` of
`𝐏¹_k`. The boundary of `𝐆_m ⊂ 𝐏¹` is covered by the two affine charts
`j₀ : 𝐆_m ⟶ Spec k[x] = 𝐀¹` (containing `0`) and `j_∞ : 𝐆_m ⟶ Spec k[y]` (containing `∞`),
`y = 1/x`. A finite étale cover of `𝐆_m` is *tame* if it is tamely ramified in codimension one
along both charts (`Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne`, the notion of
[Stacks, Tag 0EYD]), that is, tamely ramified at `0` and at `∞`. The *tame fundamental group*
`π₁ᵗ(𝐆_{m,k}, η̄)` at the geometric generic point `η̄` is the automorphism group of the fibre
functor at `η̄` restricted to tame covers, with the topology of pointwise convergence on fibres.

## Main definitions

* `AlgebraicGeometry.TameMultiplicativeGroup.Gm k`: the scheme `𝐆_{m,k}`.
* `AlgebraicGeometry.TameMultiplicativeGroup.chartZero`, `chartInfty`: the two charts.
* `AlgebraicGeometry.TameMultiplicativeGroup.IsTameCover`: tameness at `0` and `∞`.
* `AlgebraicGeometry.TameMultiplicativeGroup.tameFundamentalGroup k`: `π₁ᵗ(𝐆_{m,k}, η̄)`.

## References

* [Stacks Project, Tag 03VQ](https://stacks.math.columbia.edu/tag/03VQ)
* [Stacks Project, Tag 0EYD](https://stacks.math.columbia.edu/tag/0EYD)
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial

universe u

namespace AlgebraicGeometry.TameMultiplicativeGroup

variable (k : Type u) [Field k]

/-- The coordinate ring `k[x]_x` of `𝐆_{m,k}`. -/
public abbrev Ring : Type u := Localization.Away (X : k[X])

/-- **The multiplicative group** `𝐆_{m,k} = Spec k[x]_x`. -/
public abbrev Gm : Scheme.{u} := Spec (.of (Ring k))

/-- The inverse coordinate `y ↦ x⁻¹`, as a ring map `k[y] → k[x]_x`. -/
public def inverseCoordinate : k[X] →+* Ring k :=
  Polynomial.eval₂RingHom (algebraMap k (Ring k))
    ((IsLocalization.Away.invSelf (X : k[X]) : Ring k))

/-- **The chart at `0`**: `𝐆_m ⟶ Spec k[x] = 𝐀¹`. -/
public def chartZero : Gm k ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap k[X] (Ring k)))

/-- **The chart at `∞`**: `𝐆_m ⟶ Spec k[y]`, `y = 1/x`. -/
public def chartInfty : Gm k ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (inverseCoordinate k))

variable {k}

/-- **A tame cover** of `𝐆_{m,k}`: a finite étale cover tamely ramified at `0` and at `∞`. -/
@[sga "1 XIII 2.1.3" "special case"]
public def IsTameCover (Y : FiniteEtaleOver (Gm k)) : Prop :=
  Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (chartZero k) Y.hom ∧
    Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (chartInfty k) Y.hom

variable (k)

/-- The category of tame covers of `𝐆_{m,k}`. -/
public abbrev TameCover : Type (u + 1) := ObjectProperty.FullSubcategory (IsTameCover (k := k))

/-- The coordinate ring `k[x]_x` of `𝐆_{m,k}` is a domain. -/
public instance : IsDomain (Ring k) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors X_ne_zero)

/-- The scheme `𝐆_{m,k}` is irreducible. -/
public instance : IrreducibleSpace (Gm k) := inferInstance

/-- **The geometric generic point** `η̄` of `𝐆_{m,k}`. -/
public def genericGeometricPoint : GeometricPoint (Gm k) :=
  GeometricPoint.ofPoint (Gm k) (genericPoint (Gm k))

/-- The fibre functor at `η̄` on tame covers. -/
public def tameFiberFunctor : TameCover k ⥤ Type u :=
  ObjectProperty.ι _ ⋙ finiteEtaleFiberFunctor (genericGeometricPoint k)

/-- **The tame fundamental group** `π₁ᵗ(𝐆_{m,k}, η̄)`: the automorphisms of the fibre functor at
the geometric generic point on tame covers. -/
@[sga "1 XIII 2.1.3" "special case"]
public def tameFundamentalGroup : Type (u + 1) := Aut (tameFiberFunctor k)

/-- The group structure on `π₁ᵗ(𝐆_{m,k}, η̄)` given by composition of automorphisms. -/
public instance : Group (tameFundamentalGroup k) :=
  inferInstanceAs (Group (Aut (tameFiberFunctor k)))

/-- The topology of pointwise convergence on the fibres. -/
public instance : TopologicalSpace (tameFundamentalGroup k) :=
  Stacks.FundamentalGroup.functorAutomorphismTopology (tameFiberFunctor k)

/-- With the topology of pointwise convergence, `π₁ᵗ(𝐆_{m,k}, η̄)` is a topological group. -/
public instance : IsTopologicalGroup (tameFundamentalGroup k) :=
  Stacks.FundamentalGroup.functorAutomorphismIsTopologicalGroup (tameFiberFunctor k)

end AlgebraicGeometry.TameMultiplicativeGroup

end
