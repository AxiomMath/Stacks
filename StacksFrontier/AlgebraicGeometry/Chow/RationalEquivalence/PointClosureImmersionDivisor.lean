module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointClosureImmersionBoundary
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwiseDivisorOrder
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.OpenImmersion

/-!
# The local coefficient of the divisor differential of Stacks 0GU3 along an immersion

Let `f : Z ⟶ X` be a morphism inducing an isomorphism on every residue field — a closed or an
open immersion — and let `x` be a point of `Z`. Stacks 0GUA needs that the summand
`ord_{closure {x}}` of the *second* differential of Stacks 0GU9, the divisor differential of
Stacks 0GU3, is the same computed in `Z` and computed in `X`, under the identification of the
residue field at `x`.

That is what this file proves, by the same device as
`StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/PointClosureImmersionBoundary.lean`: the
whole content is a comparison morphism `ψ` of the two reduced closures over `f`, which is an open
immersion. The coefficient of a pushed-forward principal divisor at a point of the subscheme is
the coefficient of the principal divisor there
(`Stacks.Chow.principalDivisorPushforward_apply_subschemeι`), and an open immersion of integral
schemes changes neither the order of vanishing nor the principal divisor
(`Stacks.Chow.principalCycle_functionFieldEquiv_openImmersion_apply`). What remains is that the
two rational functions correspond under the induced isomorphism of function fields, which is the
fraction-field compatibility `Stacks.Chow.pointClosureFunctionFieldEquiv_comparison` of the
comparison, read at the generic point and extended to the whole function field by writing an
element of it as a quotient of two germs.

## Main results

* `Stacks.Chow.rationalFunctionsEquivFunctionField_integralComponentFunction` — the rational
  function on `closure {x}` with a prescribed value at `x`, read in the function field.
* `Stacks.Chow.pointClosureFunctionFieldEquiv_comparison_functionField` — the fraction-field
  compatibility of the comparison, on the whole function field.
* `Stacks.Chow.pointClosureOrd_comparison` — **the summand `ord_{closure {x}}` of the divisor
  differential of Stacks 0GU3 is natural along a morphism admitting such a comparison.**
* `Stacks.Chow.pointClosureOrd_isOpenImmersion`,
  `Stacks.Chow.pointClosureOrd_isClosedImmersion` — the two immersions supply the comparison.

## References

* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
* [Stacks Project, Tag 0BE3](https://stacks.math.columbia.edu/tag/0BE3)
* [Stacks Project, Tag 0GU3](https://stacks.math.columbia.edu/tag/0GU3)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

/-! ### The coefficient of a pushed-forward principal divisor on the subscheme -/

/-- **The coefficient of a pushed-forward principal divisor at a point of the subscheme is the
coefficient of the principal divisor there.** Pushforward along a closed immersion transports a
coefficient from a point to its image. -/
theorem principalDivisorPushforward_apply_subschemeι (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (W : X.IdealSheafData) [hW : IsIntegral W.subscheme]
    [IsLocallyNoetherian W.subscheme] (g : (rationalFunctions W.subscheme)ˣ)
    (z : W.subscheme) :
    principalDivisorPushforward C p W hW g (W.subschemeι.base z) =
      principalCycle W.subscheme
        ((rationalFunctionsEquivFunctionField W.subscheme).1
          (g : rationalFunctions W.subscheme)) z := by
  show closedSubschemeCyclePushforward C p W
      (principalCycle W.subscheme ((rationalFunctionsEquivFunctionField W.subscheme).1
        (g : rationalFunctions W.subscheme))) (W.subschemeι.base z) = _
  rw [closedSubschemeCyclePushforward_apply]

/-- **The coefficient at a point of `closure {x'}` of the principal divisor attached to a
degree-one Milnor K-class at `x'`.** This removes the pushforward from
`Stacks.Chow.pointClosureOrd` at a point of the closure. -/
theorem pointClosureOrd_subschemeι (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (x' : X) (u : MilnorKTheory (X.residueField x') 1)
    (z : (integralComponentAt x').subscheme) :
    pointClosureOrd C p x' u ((integralComponentAt x').subschemeι.base z) =
      letI : IsLocallyNoetherian (integralComponentAt x').subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x').subschemeι ≫ p)
      principalCycle (integralComponentAt x').subscheme
        ((rationalFunctionsEquivFunctionField (integralComponentAt x').subscheme).1
          (integralComponentFunction x'
              (Additive.toMul (milnorKTheoryOneAddEquiv (X.residueField x') u)) :
            rationalFunctions (integralComponentAt x').subscheme)) z := by
  let : IsLocallyNoetherian (integralComponentAt x').subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x').subschemeι ≫ p)
  exact principalDivisorPushforward_apply_subschemeι C p (integralComponentAt x') _ z

/-! ### The rational function attached to a Milnor K-class, in the function field -/

/-- **The rational function on `closure {x}` with a prescribed value at `x`, read in the function
field of `closure {x}`.** The identification of Stacks 01RV of that function field with `κ(x)`
carries it back to the prescribed value, so it is the inverse image of that value. -/
theorem rationalFunctionsEquivFunctionField_integralComponentFunction {X : Scheme.{u}} (x : X)
    (v : (X.residueField x)ˣ) :
    (rationalFunctionsEquivFunctionField (integralComponentAt x).subscheme).1
        (integralComponentFunction x v : rationalFunctions (integralComponentAt x).subscheme) =
      (pointClosureFunctionFieldEquiv x).symm (v : X.residueField x) := by
  refine (pointClosureFunctionFieldEquiv x).injective ?_
  rw [RingEquiv.apply_symm_apply]
  show rationalFunctionsEquivResidueFieldOfGenericPoint (integralComponentAt x)
      (isIntegral_integralComponentAt x) (genericPointOf_integralComponentAt x)
      ((rationalFunctionsEquivFunctionField (integralComponentAt x).subscheme).1.symm
        ((rationalFunctionsEquivFunctionField (integralComponentAt x).subscheme).1
          (integralComponentFunction x v :
            rationalFunctions (integralComponentAt x).subscheme))) = _
  rw [RingEquiv.symm_apply_apply]
  exact congrArg Units.val (integralComponentFunction_value x v)

/-! ### The comparison of reduced closures on the whole function field -/

section Comparison

variable {X Z : Scheme.{u}} (f : Z ⟶ X) (x : Z)
  (ψ : (integralComponentAt x).subscheme ⟶ (integralComponentAt (f.base x)).subscheme)
  (hψ : ψ ≫ (integralComponentAt (f.base x)).subschemeι =
    (integralComponentAt x).subschemeι ≫ f)

include hψ

/-- **The fraction-field compatibility of the comparison, on the whole function field.** The
identification of Stacks 01RV of the function field of a reduced closure with the residue field at
its generic point turns the function-field map of the comparison into the residue-field map of
`f`.

`Stacks.Chow.pointClosureFunctionFieldEquiv_comparison` is this statement for a germ pulled back
from the ambient scheme; every element of the function field is a quotient of two such germs
(`Stacks.Chow.exists_div_algebraMap_stalk_eq`), and both sides of the square are ring
homomorphisms. -/
theorem pointClosureFunctionFieldEquiv_comparison_functionField
    (hbij : ∀ t : Z, Function.Bijective (f.residueFieldMap t).hom) [IsOpenImmersion ψ]
    [IsDominant ψ] (b : ↥((integralComponentAt (f.base x)).subscheme.functionField)) :
    immersionResidueFieldEquiv f hbij x (pointClosureFunctionFieldEquiv (f.base x) b) =
      pointClosureFunctionFieldEquiv x (functionFieldEquiv_openImmersion ψ b) := by
  set v : (integralComponentAt x).subscheme :=
    genericPoint (integralComponentAt x).subscheme with hv
  have hvx : (integralComponentAt x).subschemeι.base v = x :=
    genericPointOf_integralComponentAt x
  have hspec : x ⤳ (integralComponentAt x).subschemeι.base v := by rw [hvx]
  have hpt : (integralComponentAt (f.base x)).subschemeι.base (ψ.base v) =
      f.base ((integralComponentAt x).subschemeι.base v) :=
    subschemeι_pointClosureComparison f x ψ hψ v
  have hspec' : f.base x ⤳
      (integralComponentAt (f.base x)).subschemeι.base (ψ.base v) := by
    rw [hpt, hvx]
  -- the square, for a germ pulled back from the ambient scheme
  have key : ∀ a : ↥((integralComponentAt (f.base x)).subscheme.presheaf.stalk (ψ.base v)),
      immersionResidueFieldEquiv f hbij x
          (pointClosureFunctionFieldEquiv (f.base x)
            (algebraMap ↥((integralComponentAt (f.base x)).subscheme.presheaf.stalk (ψ.base v))
              ↥((integralComponentAt (f.base x)).subscheme.functionField) a)) =
        pointClosureFunctionFieldEquiv x (functionFieldEquiv_openImmersion ψ
          (algebraMap ↥((integralComponentAt (f.base x)).subscheme.presheaf.stalk (ψ.base v))
            ↥((integralComponentAt (f.base x)).subscheme.functionField) a)) := by
    intro a
    rw [pointClosureFunctionFieldEquiv_comparison f x ψ hψ hbij v hspec hspec' a,
      functionFieldEquiv_openImmersion_eq_dominantFunctionFieldMap,
      ← algebraMap_functionField_stalkMap ψ v a]
  -- every element of the function field is a quotient of two such germs
  by_cases hb : b = 0
  · rw [hb, map_zero, map_zero, map_zero, map_zero]
  obtain ⟨a, a', ha, ha', hfrac⟩ := exists_div_algebraMap_stalk_eq (ψ.base v) hb
  rw [← hfrac]
  simp only [map_div₀]
  rw [key a, key a']

end Comparison

/-! ### Naturality of the local coefficient -/

/-- **The summand `ord_{closure {x}}` of the divisor differential of Stacks 0GU3 is natural along
a morphism carrying reduced closures to reduced closures.** The coefficient at `t` of the
principal divisor on `closure {x}` of the rational function attached to a transported Milnor
K-class is the coefficient at `f t` of the principal divisor on `closure {f x}` of the rational
function attached to the class itself.

The hypothesis `hind` — a specialization of images comes from a specialization — holds for either
immersion, both being inducing. -/
theorem pointClosureOrd_comparison (C : ChowSituation.{u}) {X Z : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (q : Z ⟶ C.S) [LocallyOfFiniteType q] (f : Z ⟶ X) (x : Z)
    (ψ : (integralComponentAt x).subscheme ⟶ (integralComponentAt (f.base x)).subscheme)
    [IsOpenImmersion ψ]
    (hψ : ψ ≫ (integralComponentAt (f.base x)).subschemeι =
      (integralComponentAt x).subschemeι ≫ f)
    (hbij : ∀ t : Z, Function.Bijective (f.residueFieldMap t).hom)
    (hind : ∀ t : Z, f.base x ⤳ f.base t → x ⤳ t)
    (u : MilnorKTheory (X.residueField (f.base x)) 1) (t : Z) :
    pointClosureOrd C q x
        (milnorKTransport (immersionResidueFieldEquiv f hbij x : _ →+* _) 1 u) t =
      pointClosureOrd C p (f.base x) u (f.base t) := by
  let : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x).subschemeι ≫ q)
  let : IsLocallyNoetherian (integralComponentAt (f.base x)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt (f.base x)).subschemeι ≫ p)
  have : IsDominant ψ := by
    rw [isDominant_iff]
    exact (IsOpenImmersion.isOpen_range ψ).dense (Set.range_nonempty _)
  by_cases hmem : t ∈ Set.range (integralComponentAt x).subschemeι.base
  · obtain ⟨z, rfl⟩ := hmem
    rw [← subschemeι_pointClosureComparison f x ψ hψ z, pointClosureOrd_subschemeι,
      pointClosureOrd_subschemeι,
      rationalFunctionsEquivFunctionField_integralComponentFunction,
      rationalFunctionsEquivFunctionField_integralComponentFunction,
      ← principalCycle_functionFieldEquiv_openImmersion_apply ψ]
    refine congrArg (fun c : ↥((integralComponentAt x).subscheme.functionField) ↦
      principalCycle (integralComponentAt x).subscheme c z) ?_
    refine (pointClosureFunctionFieldEquiv x).injective ?_
    rw [RingEquiv.apply_symm_apply,
      ← pointClosureFunctionFieldEquiv_comparison_functionField f x ψ hψ hbij,
      RingEquiv.apply_symm_apply]
    have htr : Additive.toMul (milnorKTheoryOneAddEquiv ↥(Z.residueField x)
          (milnorKTransport (immersionResidueFieldEquiv f hbij x : _ →+* _) 1 u)) =
        Units.map ((immersionResidueFieldEquiv f hbij x :
            ↥(X.residueField (f.base x)) →+* ↥(Z.residueField x)) :
          ↥(X.residueField (f.base x)) →* ↥(Z.residueField x))
          (Additive.toMul (milnorKTheoryOneAddEquiv ↥(X.residueField (f.base x)) u)) :=
      congrArg Additive.toMul (milnorKTheoryOneAddEquiv_milnorKTransport _ u)
    exact congrArg Units.val htr
  · have hnot : t ∉ closure ({x} : Set Z) := by
      rw [← coe_support_integralComponentAt x,
        ← Scheme.IdealSheafData.range_subschemeι (integralComponentAt x)]
      exact hmem
    have hnot' : f.base t ∉ closure ({f.base x} : Set X) := fun hcon ↦
      hnot (specializes_iff_mem_closure.mp
        (hind t (specializes_iff_mem_closure.mpr hcon)))
    rw [pointClosureOrd_eq_zero_of_notMem_closure C q x _ hnot,
      pointClosureOrd_eq_zero_of_notMem_closure C p (f.base x) u hnot']

/-- **The summand of the divisor differential of Stacks 0GU3 is natural along an open
immersion.** -/
theorem pointClosureOrd_isOpenImmersion (C : ChowSituation.{u}) {X U : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (r : U ⟶ C.S) [LocallyOfFiniteType r] (j : U ⟶ X)
    [IsOpenImmersion j] (hbij : ∀ t : U, Function.Bijective (j.residueFieldMap t).hom) (u : U)
    (w : MilnorKTheory (X.residueField (j.base u)) 1) (t : U) :
    pointClosureOrd C r u
        (milnorKTransport (immersionResidueFieldEquiv j hbij u : _ →+* _) 1 w) t =
      pointClosureOrd C p (j.base u) w (j.base t) :=
  pointClosureOrd_comparison C p r j u (pointClosureOpenComparison j u)
    (pointClosureOpenComparison_subschemeι j u) hbij
    (fun _ hspec ↦ j.isOpenEmbedding.isInducing.specializes_iff.mp hspec) w t

/-- **The summand of the divisor differential of Stacks 0GU3 is natural along a closed
immersion.** -/
theorem pointClosureOrd_isClosedImmersion (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (s : Y ⟶ C.S) [LocallyOfFiniteType s] (i : Y ⟶ X)
    [IsClosedImmersion i] (hbij : ∀ t : Y, Function.Bijective (i.residueFieldMap t).hom) (y : Y)
    (w : MilnorKTheory (X.residueField (i.base y)) 1) (t : Y) :
    pointClosureOrd C s y
        (milnorKTransport (immersionResidueFieldEquiv i hbij y : _ →+* _) 1 w) t =
      pointClosureOrd C p (i.base y) w (i.base t) := by
  obtain ⟨e, he⟩ := exists_iso_integralComponentAt_comp i y
  have : IsOpenImmersion e.hom := inferInstance
  exact pointClosureOrd_comparison C p s i y e.hom he hbij
    (fun _ hspec ↦ i.isClosedEmbedding.isInducing.specializes_iff.mp hspec) w t

end Stacks.Chow

end
