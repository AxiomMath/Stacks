module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.ClosureOfOpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.OpenImmersionRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.ClosedCoverExactSequence
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.OpenImmersion

/-!
# Lifting a rational equivalence from an open subscheme

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, let `V ⊆ X` be an open subscheme and let `i : Y ⟶ X` be a closed
immersion whose image is the complement of `V`. Stacks 02RX says that a rational equivalence
between two `k`-cycles on `X` that holds after restriction to `V` holds on `X` itself up to a
cycle coming from `Y`: if `α|_V ∼ β|_V` then there is a `k`-cycle `γ` on `Y` with
`α ∼ β + i_* γ`.

Read on classes, this statement is the second assertion of Stacks 02RX: the sequence of abelian
groups

  `A_k(Y) → A_k(X) → A_k(V) → 0`,

with first map the pushforward `i_*` along the closed immersion and second map the restriction
`j^*` to the open subscheme, is an exact complex. Its three constituent assertions are
`Stacks.Chow.exact_chowPushforward_chowGroupOpensRestrict`, exactness at `A_k(X)` — which carries
both the vanishing of the composite and the description of the kernel of `j^*` — and
`Stacks.Chow.surjective_chowGroupOpensRestrictOfIsOpenImmersion`, exactness at `A_k(V)`. The maps
are `i_* = Stacks.Chow.chowPushforwardOfIsClosedImmersion` and
`j^* = Stacks.Chow.chowGroupOpensRestrictOfIsOpenImmersion`.

The closed subscheme `Y` is not required to carry the reduced induced structure: the only
hypothesis on `i` is that its image is the complement of the image of `V.ι`.

## Main results

* `Stacks.Chow.exists_rationallyEquivalent_properPushforward_of_cycleGroupRestrict`: a rational
  equivalence of `k`-cycles after restriction to `V` lifts to `X` up to a pushforward from `Y`.
* `Stacks.Chow.exact_chowPushforward_chowGroupOpensRestrict`: the localization sequence of Chow
  groups is exact at `A_k(X)`.
* `Stacks.Chow.surjective_chowGroupOpensRestrictOfIsOpenImmersion`: the localization sequence of
  Chow groups is exact at `A_k(V)`, that is, restriction of Chow classes to an open subscheme is
  surjective.
* `Stacks.Chow.principalDivisorPushforward_apply_of_isOpenImmersion`: the coefficient at a point
  of an open subscheme of the pushed-forward principal divisor of a rational function on an
  integral closed subscheme of the ambient scheme is the coefficient of the restricted rational
  function on the part of that subscheme lying over the open subscheme.
* `Stacks.Chow.isDominant_closureSubschemeOpenMap`: the comparison morphism from an integral
  closed subscheme of an open subscheme to its closure in the ambient scheme is dominant.

## References

* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02RC](https://stacks.math.columbia.edu/tag/02RC)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0BE3](https://stacks.math.columbia.edu/tag/0BE3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The comparison morphism to the closure is dominant -/

/-- The comparison morphism from an integral closed subscheme of an open subscheme to its closure
in the ambient scheme is dominant. -/
theorem isDominant_closureSubschemeOpenMap {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (I : U.IdealSheafData) [IsIntegral I.subscheme] :
    IsDominant (IdealSheaf.closureSubschemeOpenMap j I) := by
  have _ : IsIntegral (IdealSheaf.closureIdeal j I).subscheme :=
    IdealSheaf.closureIdeal_integral j I
  rw [isDominant_iff]
  exact (IsOpenImmersion.isOpen_range (IdealSheaf.closureSubschemeOpenMap j I)).dense
    (Set.range_nonempty _)

/-! ### Coefficients of pushed-forward principal divisors -/

/-- The coefficient at a point of an integral closed subscheme `W ⊆ X` of the pushforward to `X`
of the principal divisor of a nonzero rational function on `W` is the coefficient of that
principal divisor at the point itself. -/
theorem principalDivisorPushforward_apply_image (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (W : X.IdealSheafData)
    [hW : IsIntegral W.subscheme] [IsLocallyNoetherian W.subscheme]
    (g : (rationalFunctions W.subscheme)ˣ) (w : W.subscheme) :
    principalDivisorPushforward C p W hW g (W.subschemeι.base w) =
      principalCycle W.subscheme ((rationalFunctionsEquivFunctionField W.subscheme).1
        (g : rationalFunctions W.subscheme)) w :=
  algebraicCycle_map_relativeDimension_apply_image C (W.subschemeι ≫ p) p W.subschemeι rfl _ w

/-- Let `j : U ⟶ X` be an open immersion, let `W ⊆ X` and `I ⊆ U` be integral closed
subschemes identified by `W ∩ U = I`, and let `m : I ⟶ W` be the resulting dominant open
immersion. Then the pushforward to `X` of the principal divisor of a nonzero rational function
`g` on `W` has, at a point of `U`, the same coefficient as the pushforward to `U` of the
principal divisor of the restriction of `g` to `I`. -/
theorem principalDivisorPushforward_apply_of_isOpenImmersion (C : ChowSituation.{u})
    {U X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sU : U ⟶ C.S)
    [LocallyOfFiniteType sU] (j : U ⟶ X) [IsOpenImmersion j] (I : U.IdealSheafData)
    (W : X.IdealSheafData) [hI : IsIntegral I.subscheme] [hW : IsIntegral W.subscheme]
    (m : I.subscheme ⟶ W.subscheme) [IsOpenImmersion m] [IsDominant m]
    (hm : m ≫ W.subschemeι = I.subschemeι ≫ j) (hcomap : W.comap j = I)
    (g : (rationalFunctions W.subscheme)ˣ) (x : U) :
    principalDivisorPushforward C sX W hW g (j.base x) =
      principalDivisorPushforward C sU I hI
        (rationalFunctionsUnitsMulEquivOfOpenImmersion m g) x := by
  have _ : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ sX)
  have _ : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (I.subschemeι ≫ sU)
  have hsupp : (I.support : Set U) = j.base ⁻¹' (W.support : Set X) := by
    rw [← hcomap, Scheme.IdealSheafData.support_comap]
    rfl
  by_cases hx : x ∈ (I.support : Set U)
  · rw [← I.range_subschemeι] at hx
    obtain ⟨z, rfl⟩ := hx
    have hpt : W.subschemeι.base (m.base z) = j.base (I.subschemeι.base z) :=
      congrArg (fun r : I.subscheme ⟶ X ↦ r.base z) hm
    rw [← hpt, principalDivisorPushforward_apply_image C sX W g (m.base z),
      principalDivisorPushforward_apply_image C sU I _ z,
      rationalFunctionsUnitsMulEquivOfOpenImmersion_coe,
      principalCycle_rationalFunctionsRingEquivOfOpenImmersion_apply]
  · have hxW : x ∉ j.base ⁻¹' (W.support : Set X) := by rwa [← hsupp]
    have hL := Function.notMem_support.mp fun hne ↦
      hxW (support_principalDivisorPushforward_subset C sX W hW g hne)
    have hR := Function.notMem_support.mp fun hne ↦
      hx (support_principalDivisorPushforward_subset C sU I hI
        (rationalFunctionsUnitsMulEquivOfOpenImmersion m g) hne)
    rw [hL, hR]

/-! ### Lifting a rational equivalence from an open subscheme -/

/-- Let `V ⊆ X` be an open subscheme and let `i : Y ⟶ X` be a closed immersion whose image is the
complement of `V`. If two `k`-cycles on `X` become rationally equivalent after restriction to `V`,
then they are rationally equivalent on `X` up to the pushforward of a `k`-cycle on `Y`. -/
@[stacks 02RX "lifting a rational equivalence from an open subscheme"]
theorem exists_rationallyEquivalent_properPushforward_of_cycleGroupRestrict
    (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sY)
    (V : X.Opens) (hcomplement : Set.range i.base = (Set.range V.ι.base)ᶜ)
    (k : ℤ) (α β : CycleGroup C sX k)
    (h : RationallyEquivalent C (V.ι ≫ sX) k
      (cycleGroupOpensRestrict C sX V k α) (cycleGroupOpensRestrict C sX V k β)) :
    ∃ γ : CycleGroup C sY k,
      RationallyEquivalent C sX k α (β + properPushforward C sY sX i hi k γ) := by
  classical
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  obtain ⟨J, I, hI, hDimI, hLocalI, g, hg⟩ :=
    (mem_rationalEquivalences C (V.ι ≫ sX) k _).mp h
  have _ : ∀ a, IsIntegral (I a).subscheme := hI
  have hW : ∀ a, IsIntegral (IdealSheaf.closureIdeal V.ι (I a)).subscheme := fun a ↦
    IdealSheaf.closureIdeal_integral V.ι (I a)
  have _ : ∀ a, IsDominant (IdealSheaf.closureSubschemeOpenMap V.ι (I a)) := fun a ↦
    isDominant_closureSubschemeOpenMap V.ι (I a)
  have hDimW : ∀ a, schemeDeltaDimension C
      ((IdealSheaf.closureIdeal V.ι (I a)).subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt) := fun a ↦
    closureIdeal_schemeDeltaDimension C V.ι sX (V.ι ≫ sX) rfl (I a) (hDimI a)
  have hLocalW : LocallyFinite
      fun a ↦ ((IdealSheaf.closureIdeal V.ι (I a)).support : Set X) :=
    IdealSheaf.closureIdeal_family_isLocallyFinite V.ι I hLocalI
  set g' := fun a ↦ (rationalFunctionsUnitsMulEquivOfOpenImmersion
    (IdealSheaf.closureSubschemeOpenMap V.ι (I a))).symm (g a) with hg'
  obtain ⟨ε, hε⟩ := exists_principalDivisorFamilySum C sX k
    (fun a ↦ IdealSheaf.closureIdeal V.ι (I a)) hW hDimW hLocalW g'
  have hεzero : IsRationallyEquivalentToZero C sX k ε :=
    ⟨J, fun a ↦ IdealSheaf.closureIdeal V.ι (I a), hW, hDimW, hLocalW, g', hε⟩
  have hεopen : cycleGroupOpensRestrict C sX V k ε =
      cycleGroupOpensRestrict C sX V k α - cycleGroupOpensRestrict C sX V k β := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    rw [cycleGroupOpensRestrict_apply, hε (V.ι.base x), hg x]
    simp only [principalDivisorFamilyCoefficient]
    refine finsum_congr fun a ↦ ?_
    have hkey := principalDivisorPushforward_apply_of_isOpenImmersion C sX (V.ι ≫ sX) V.ι
      (I a) (IdealSheaf.closureIdeal V.ι (I a))
      (IdealSheaf.closureSubschemeOpenMap V.ι (I a))
      (IdealSheaf.closureSubschemeOpenMap_comp_subschemeι V.ι (I a))
      (IdealSheaf.closureIdeal_comap V.ι (I a))
      (g' a) x
    rwa [hg', MulEquiv.apply_symm_apply] at hkey
  have hzeroOpen : cycleGroupRestrict C sX (V.ι ≫ sX) V.ι rfl k (α - β - ε) = 0 := by
    rw [← cycleGroupOpensRestrict_eq_cycleGroupRestrict, map_sub, map_sub, hεopen, sub_self]
  obtain ⟨γ, hγ⟩ := (cycleGroupRestrict_eq_zero_iff C sX sY (V.ι ≫ sX) i hi V.ι rfl
    hcomplement k (α - β - ε)).mp hzeroOpen
  refine ⟨γ, ?_⟩
  show α - (β + properPushforward C sY sX i hi k γ) ∈ rationalEquivalences C sX k
  rwa [show α - (β + properPushforward C sY sX i hi k γ) = ε by rw [hγ]; abel]

/-! ### The localization sequence of Chow groups -/

/-- The localization sequence of Chow groups is exact at `A_k(V)`: restriction of `k`-cycle
classes to an open subscheme `V ⊆ X` is surjective. -/
@[stacks 02RX "surjectivity onto the Chow group of the open subscheme"]
theorem surjective_chowGroupOpensRestrictOfIsOpenImmersion (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (V : X.Opens) (k : ℤ) :
    Function.Surjective (chowGroupOpensRestrictOfIsOpenImmersion C sX V k) := by
  intro q
  obtain ⟨d, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
  obtain ⟨c, hc⟩ := cycleGroupRestrict_surjective C sX (V.ι ≫ sX) V.ι rfl k d
  refine ⟨QuotientAddGroup.mk' _ c, ?_⟩
  rw [chowGroupOpensRestrictOfIsOpenImmersion_mk, cycleGroupOpensRestrict_eq_cycleGroupRestrict,
    hc]

/-- The localization sequence of Chow groups is exact at `A_k(X)`: for an open subscheme `V ⊆ X`
and a closed immersion `i : Y ⟶ X` whose image is the complement of `V`, a `k`-cycle class on `X`
restricts to zero on `V` exactly when it is the pushforward of a `k`-cycle class on `Y`. -/
@[stacks 02RX "exactness at the Chow group of the ambient scheme"]
theorem exact_chowPushforward_chowGroupOpensRestrict (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sY)
    (V : X.Opens) (hcomplement : Set.range i.base = (Set.range V.ι.base)ᶜ) (k : ℤ) :
    Function.Exact (chowPushforwardOfIsClosedImmersion C sY sX i hi k)
      (chowGroupOpensRestrictOfIsOpenImmersion C sX V k) := by
  intro b
  refine ⟨fun hzero ↦ ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ b
    rw [chowGroupOpensRestrictOfIsOpenImmersion_mk] at hzero
    have h : RationallyEquivalent C (V.ι ≫ sX) k (cycleGroupOpensRestrict C sX V k c)
        (cycleGroupOpensRestrict C sX V k 0) := by
      show cycleGroupOpensRestrict C sX V k c - cycleGroupOpensRestrict C sX V k 0 ∈
        rationalEquivalences C (V.ι ≫ sX) k
      rw [map_zero, sub_zero]
      exact (QuotientAddGroup.eq_zero_iff _).mp hzero
    obtain ⟨γ, hγ⟩ := exists_rationallyEquivalent_properPushforward_of_cycleGroupRestrict C sX sY
      i hi V hcomplement k c 0 h
    rw [zero_add] at hγ
    refine ⟨QuotientAddGroup.mk' _ γ, ?_⟩
    rw [chowPushforwardOfIsClosedImmersion_mk, ← sub_eq_zero, ← map_sub]
    refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
    rw [← neg_sub c]
    exact neg_mem hγ
  · rintro ⟨a, rfl⟩
    obtain ⟨d, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
    have hz := (cycleGroupRestrict_eq_zero_iff C sX sY (V.ι ≫ sX) i hi V.ι rfl hcomplement k
      (properPushforward C sY sX i hi k d)).mpr ⟨d, rfl⟩
    rw [chowPushforwardOfIsClosedImmersion_mk, chowGroupOpensRestrictOfIsOpenImmersion_mk,
      cycleGroupOpensRestrict_eq_cycleGroupRestrict, hz, map_zero]

end Stacks.Chow

end
