module

public import StacksFrontier.AlgebraicGeometry.Stacks.DecentStackSoberInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralAlgebraicStack

/-!
# Points, irreducible closed subsets and integral closed substacks (Stacks 0GWE)

Let `𝒳` be a decent algebraic stack over `S` whose inertia projection `I_𝒳 ⟶ 𝒳` is quasi-compact.
**Stacks 0GWE** asserts that there are canonical bijections between

1. the set of points `|𝒳|`,
2. the set of irreducible closed subsets of `|𝒳|`,
3. the set of integral closed substacks of `𝒳`,

the map from (1) to (2) sending `x` to `closure {x}` and the map from (3) to (2) sending `𝒵` to
`|𝒵|`.

## Main definitions

* `AlgebraicGeometry.Stack.IntegralClosedSubstack`: the integral closed substacks of `𝒳`
  (**Stacks 04YM**, part (2), and **Stacks 0GWB**).
* `AlgebraicGeometry.Stack.IntegralClosedSubstack.support`: the irreducible closed subset `|𝒵|`
  of `|𝒳|`.
* `AlgebraicGeometry.Stack.pointClosure`: the irreducible closed subset `closure {x}`.

## Main results

* `AlgebraicGeometry.Stack.bijective_pointClosure_and_bijective_support`: **Stacks 0GWE**, both
  maps are bijective.
* `AlgebraicGeometry.Stack.integralClosedSubstackEquiv`: the resulting equivalence between
  integral closed substacks and irreducible closed subsets, which is the support map.

## Implementation notes

The proof is the source's. The map from points is bijective because `|𝒳|` is sober
(**Stacks 0GW9**). An integral closed substack is reduced, so two with the same support are equal
by the uniqueness half of **Stacks 0509**. Conversely the reduced closed substack on an
irreducible closed `T` (the existence half of **Stacks 0509**) is integral: it is decent
(**Stacks 0GW3**), its inertia is the base change of that of `𝒳` (**Stacks 06R5**) hence
quasi-compact (**Stacks 050V**), it is reduced, and `|𝒵| ≅ T` is irreducible.

An integral closed substack is recorded by its strictly full subcategory, as in **Stacks 04YM**;
the support is read through the algebraicity witness the closed-substack condition carries, and
does not depend on it.

## References

* [Stacks Project, Tag 0GWE](https://stacks.math.columbia.edu/tag/0GWE)
* [Stacks Project, Tag 0GW9](https://stacks.math.columbia.edu/tag/0GW9)
* [Stacks Project, Tag 0GWB](https://stacks.math.columbia.edu/tag/0GWB)
* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **An integral closed substack** of an algebraic stack `𝒳` over `S`: a strictly full
subcategory of `𝒳` which is a closed substack (**Stacks 04YM**, part (2)) and an integral
algebraic stack (**Stacks 0GWB**). -/
abbrev IntegralClosedSubstack : Type _ :=
  {P : ObjectProperty 𝒳.val.val.obj // ∃ hP : IsClosedSubstack 𝒳 P,
    IsIntegral B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP.2.choose)}

variable {B S hS 𝒳}

/-- **The support of an integral closed substack**: the image `|𝒵|` of its points in `|𝒳|`,
which is closed (the inclusion is a closed embedding on points) and irreducible (`|𝒵|` is). -/
noncomputable def IntegralClosedSubstack.support (Z : IntegralClosedSubstack B S hS 𝒳) :
    @IrreducibleCloseds (AlgebraicStacks.points B S hS 𝒳) (pointTopology B S hS 𝒳.val) :=
  letI := pointTopology B S hS 𝒳.val
  letI := pointTopology B S hS
    (fullSubcategoryAlgebraicStack 𝒳 Z.val Z.property.choose.2.choose).val
  have hφ := AlgebraicStacks.isClosedEmbedding_pointsMap_of_isClosedSubstack
    Z.property.choose Z.property.choose.2.choose
  have hirr := Z.property.choose_spec.2.2.2
  { carrier := Set.range (AlgebraicStacks.pointsMap B S hS
      (fullSubcategoryInclusion 𝒳 Z.val Z.property.choose.2.choose))
    isIrreducible' := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ hφ.continuous.continuousOn
    isClosed' := hφ.isClosed_range }

/-- The support of an integral closed substack is the range of the map on points of its
inclusion. -/
theorem IntegralClosedSubstack.coe_support (Z : IntegralClosedSubstack B S hS 𝒳) :
    ((Z.support : @IrreducibleCloseds _ (pointTopology B S hS 𝒳.val)) :
        Set (AlgebraicStacks.points B S hS 𝒳)) =
      Set.range (AlgebraicStacks.pointsMap B S hS
        (fullSubcategoryInclusion 𝒳 Z.val Z.property.choose.2.choose)) :=
  rfl

variable (B S hS 𝒳) in
/-- **The irreducible closed subset of a point**: the closure `closure {x}` of a point of
`|𝒳|`. -/
def pointClosure (x : AlgebraicStacks.points B S hS 𝒳) :
    @IrreducibleCloseds (AlgebraicStacks.points B S hS 𝒳) (pointTopology B S hS 𝒳.val) :=
  letI := pointTopology B S hS 𝒳.val
  ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- **Stacks 0GWE.** Let `𝒳` be a decent algebraic stack over `S` whose inertia projection
`I_𝒳 ⟶ 𝒳` is quasi-compact. Then the map `x ↦ closure {x}` from the points of `𝒳` to the
irreducible closed subsets of `|𝒳|` is bijective, and so is the map `𝒵 ↦ |𝒵|` from the integral
closed substacks of `𝒳` to the irreducible closed subsets of `|𝒳|`. -/
@[stacks 0GWE]
theorem bijective_pointClosure_and_bijective_support
    (hd : IsDecent B S hS 𝒳.val)
    (hqc : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    Function.Bijective (pointClosure B S hS 𝒳) ∧
      Function.Bijective (IntegralClosedSubstack.support (𝒳 := 𝒳)) := by
  let := pointTopology B S hS 𝒳.val
  have hsober := AlgebraicStacks.stacksSober_points_of_isDecent 𝒳 hd hqc
  obtain ⟨_, _⟩ := stacksSober_iff_t0_and_quasiSober.mp hsober
  let := specializationOrder (AlgebraicStacks.points B S hS 𝒳)
  refine ⟨(irreducibleSetEquivPoints (α := AlgebraicStacks.points B S hS 𝒳)).symm.bijective,
    ⟨?_, ?_⟩⟩
  · -- two integral closed substacks with the same support are equal (Stacks 0509, uniqueness)
    intro Z₁ Z₂ h
    exact Subtype.ext <| eq_of_isReducedStack_of_range_pointsMap_eq B S hS Z₁.property.choose
      Z₂.property.choose _ _ Z₁.property.choose_spec.1 Z₂.property.choose_spec.1
      (congrArg (fun s : IrreducibleCloseds (AlgebraicStacks.points B S hS 𝒳) => s.carrier) h)
  · -- the reduced closed substack on an irreducible closed set is integral
    intro T
    obtain ⟨P, hP, hPT⟩ := exists_isClosedSubstack_isReducedStack_range_pointsMap_eq 𝒳
      (T : Set _) T.isClosed
    have hA := hP.2.choose
    obtain ⟨hrange, hred⟩ := hPT hA
    let := pointTopology B S hS (fullSubcategoryAlgebraicStack 𝒳 P hA).val
    have hφ := AlgebraicStacks.isClosedEmbedding_pointsMap_of_isClosedSubstack hP hA
    have hirr : IrreducibleSpace (AlgebraicStacks.points B S hS
        (fullSubcategoryAlgebraicStack 𝒳 P hA)) := by
      have hT' : IrreducibleSpace (Set.range (AlgebraicStacks.pointsMap B S hS
          (fullSubcategoryInclusion 𝒳 P hA))) := by
        rw [hrange]
        exact isIrreducible_iff_irreducibleSpace.mp T.isIrreducible
      exact (hφ.toHomeomorph.irreducibleSpace_iff).2 hT'
    have hint : IsIntegral B S hS (fullSubcategoryAlgebraicStack 𝒳 P hA) :=
      ⟨hred, AlgebraicStacks.isDecent_of_isClosedSubstack hd hP hA,
        AlgebraicStacks.isQuasiCompactMorphism_inertia_of_fullyFaithful
          (fullSubcategoryInclusion 𝒳 P hA) (Functor.FullyFaithful.ofFullyFaithful _) hqc,
        hirr⟩
    exact ⟨⟨P, hP, hint⟩,
      IrreducibleCloseds.ext ((IntegralClosedSubstack.coe_support _).trans hrange)⟩

/-- **The equivalence of Stacks 0GWE between integral closed substacks and irreducible closed
subsets**, under its hypotheses: the support map, bijective by
`AlgebraicGeometry.Stack.bijective_pointClosure_and_bijective_support`. -/
noncomputable def integralClosedSubstackEquiv (hd : IsDecent B S hS 𝒳.val)
    (hqc : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    IntegralClosedSubstack B S hS 𝒳 ≃
      @IrreducibleCloseds (AlgebraicStacks.points B S hS 𝒳) (pointTopology B S hS 𝒳.val) :=
  Equiv.ofBijective _ (bijective_pointClosure_and_bijective_support hd hqc).2

/-- The equivalence of Stacks 0GWE sends an integral closed substack to its support. -/
theorem integralClosedSubstackEquiv_apply (hd : IsDecent B S hS 𝒳.val)
    (hqc : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳))
    (Z : IntegralClosedSubstack B S hS 𝒳) :
    integralClosedSubstackEquiv hd hqc Z = Z.support :=
  rfl

end AlgebraicGeometry.Stack

end
