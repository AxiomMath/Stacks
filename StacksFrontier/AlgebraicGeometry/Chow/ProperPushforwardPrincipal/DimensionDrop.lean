module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullbackCycles.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDropCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ActionOnCycles
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dimension-drop branch of the pushforward of a principal divisor

Let `C = (S, δ)` be a Chow situation, let `p : X ⟶ Y` be proper over `S`, let `V ⊆ X` be an
integral closed subscheme of delta-dimension `k + 1` and let `g` be a nonzero rational function
on `V`. If the scheme-theoretic image `T = V.map p` does not have delta-dimension `k + 1`, then
the proper pushforward of `div(g)` along `p` vanishes, granted
`Stacks.Chow.GenericFibreDegreeVanishes`, which asserts for the restriction `π : V ⟶ T` of `p`
and the generic point `η` of `T` that

  `∑_{x ↦ η} ord_x(g) · [κ(x) : κ(η)] = 0`.

Together with the case where the image keeps delta-dimension `k + 1`, this gives Stacks 02S2 for
an arbitrary proper morphism under the same hypothesis. Over a one-point base the hypothesis
specializes to Stacks 02RU.

## Main definitions

* `Stacks.Chow.GenericFibreDegreeVanishes` — for a proper dominant morphism `π : V ⟶ T` of
  integral schemes over the base with `dim_δ(V) = dim_δ(T) + 1`, the weighted sum of the orders
  of vanishing of a nonzero rational function over the fibre of `π` at the generic point of `T`
  vanishes.

## Main results

* `Stacks.Chow.schemeDeltaDimension_le_of_isDominant'` — a dominant morphism does not raise the
  delta-dimension of the target above that of the source.
* `Stacks.Chow.properPushforward_apply_eq_zero_of_relativeDimension_ne` — away from relative
  dimension `k` the coefficient of the proper pushforward of a `k`-cycle vanishes.
* `Stacks.Chow.properPushforwardPrincipalDivisor_eq_zero_of_schemeDeltaDimension_ne` — the
  proper pushforward of `div(g)` vanishes when the image drops in delta-dimension, granted
  `Stacks.Chow.GenericFibreDegreeVanishes`.
* `Stacks.Chow.properPushforwardKillsPrincipalDivisor_of_genericFibreDegreeVanishes`,
  `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_genericFibreDegreeVanishes`
  and `Stacks.Chow.properPushforward_rationallyEquivalent_of_genericFibreDegreeVanishes` —
  Stacks 02S2 for an arbitrary proper morphism, granted the same hypothesis.
* `Stacks.Chow.principalDivisorDegree_eq_zero_of_genericFibreDegreeVanishes` and
  `Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_genericFibreDegreeVanishes` —
  Stacks 02RU over a one-point base, granted the same hypothesis.

## References

* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 02RK](https://stacks.math.columbia.edu/tag/02RK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- The principal divisor of the zero rational function is the zero cycle. -/
theorem principalDivisorCycle_zero (C : ChowSituation.{u}) {X : Scheme.{u}} (s : X ⟶ C.S)
    [LocallyOfFiniteType s] [IsIntegral X] {n : ℤ}
    (hn : schemeDeltaDimension C s = (n : EInt)) :
    principalDivisorCycle C s hn (0 : X.functionField) = 0 := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  rw [show ((principalDivisorCycle C s hn (0 : X.functionField) :
    AlgebraicCycle X ℤ)) x = X.ord (0 : X.functionField) x from rfl, Scheme.ord_zero]
  rfl

/-! ### Delta-dimension along a dominant morphism -/

/-- A dominant morphism does not raise the delta-dimension: if `π : V ⟶ T` is dominant between
integral schemes locally of finite type over the base, then `dim_δ(T) ≤ dim_δ(V)`, the structure
morphism of `V` being `π ≫ sT`. -/
@[ega "IV 4.1.2" "(i), special case"]
theorem schemeDeltaDimension_le_of_isDominant' (C : ChowSituation.{u}) {V T : Scheme.{u}}
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (π : V ⟶ T) [LocallyOfFiniteType π] [IsDominant π]
    [IsIntegral V] [IsIntegral T] :
    schemeDeltaDimension C sT ≤ schemeDeltaDimension C (π ≫ sT) := by
  have hgen : π.base (genericPoint V) = genericPoint T :=
    ((tfae_isDominant_of_isIntegral π).out 1 2).mp (inferInstance : IsDominant π)
  let _ : Algebra (T.residueField (π.base (genericPoint V))) (V.residueField (genericPoint V)) :=
    (π.residueFieldMap (genericPoint V)).hom.toAlgebra
  set r : ℕ := Cardinal.toNat (Algebra.trdeg (T.residueField (π.base (genericPoint V)))
    (V.residueField (genericPoint V))) with hr
  have hrel := relativeDimension_comp_add_of_trdeg C.dimensionFunction π sT
    (genericPoint V) r rfl
  rw [schemeDeltaDimension_eq_genericPoint C sT, schemeDeltaDimension_eq_genericPoint C (π ≫ sT)]
  refine WithBotTop.coe_le_coe.mpr ?_
  rw [hrel, hgen]
  omega

/-! ### Coefficients of a proper pushforward and relative dimension -/

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- At a point of the target whose relative dimension is not `k`, the coefficient of the proper
pushforward of a `k`-cycle vanishes. -/
theorem properPushforward_apply_eq_zero_of_relativeDimension_ne (f : X ⟶ Y) [IsProper f]
    (hf : f ≫ sY = sX) (k : ℤ) (c : CycleGroup C sX k) (y : Y)
    (hy : relativeDimension C.dimensionFunction sY y ≠ k) :
    (properPushforward C sX sY f hf k c).1 y = 0 := by
  by_contra hne
  exact hy ((mem_cyclesOfDimension_iff_forall_point C sY k _).mp
    (properPushforward C sX sY f hf k c).2 y hne)

/-- The weighted pushforward of the zero cycle is the zero cycle, for arbitrary weights. -/
theorem algebraicCycle_map_zero {V T : Scheme.{u}} (π : V ⟶ T) [QuasiCompact π]
    (wV : V → ℤ) (wT : T → ℤ) :
    AlgebraicCycle.map π wV wT (0 : AlgebraicCycle V ℤ) = 0 := by
  refine Function.locallyFinsuppWithin.ext fun y ↦ ?_
  simp [AlgebraicCycle.map, Function.locallyFinsupp.map, AlgebraicCycle.mapCoeff]

/-! ### The degree of a principal divisor on the generic fibre -/

/-- For every proper dominant morphism `π : V ⟶ T` of integral schemes locally of finite type
over the base with `dim_δ(V) = n` and `dim_δ(T) = n - 1`, and every nonzero rational function `f`
on `V`,

  `∑_{x ↦ η} ord_x(f) · [κ(x) : κ(η)] = 0`

where `η` is the generic point of `T` and the sum is over the fibre of `π` at `η`. -/
def GenericFibreDegreeVanishes : Prop :=
  ∀ (C : ChowSituation.{u}) {V T : Scheme.{u}} (sT : T ⟶ C.S) [LocallyOfFiniteType sT]
    (π : V ⟶ T) [IsProper π] [IsDominant π] [IsIntegral V] [IsIntegral T]
    [IsLocallyNoetherian V] {n : ℤ},
    schemeDeltaDimension C (π ≫ sT) = (n : EInt) →
      schemeDeltaDimension C sT = ((n - 1 : ℤ) : EInt) →
        ∀ f : V.functionField, f ≠ 0 →
          (∑ᶠ x ∈ π.base ⁻¹' {genericPoint T}, V.ord f x * (π.residueDegree x : ℤ)) = 0

/-! ### Vanishing when the image drops in delta-dimension -/

variable (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX)

include hp

/-- Let `p : X ⟶ Y` be proper over the base, let `V ⊆ X` be an integral closed subscheme of
delta-dimension `k + 1` and let `g` be a nonzero rational function on `V`. Granted
`Stacks.Chow.GenericFibreDegreeVanishes`, if the scheme-theoretic image `V.map p` does not have
delta-dimension `k + 1`, then the proper pushforward of `div(g)` along `p` vanishes. -/
theorem properPushforwardPrincipalDivisor_eq_zero_of_schemeDeltaDimension_ne
    (hvanish : GenericFibreDegreeVanishes.{u}) (k : ℤ)
    (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (hdim : schemeDeltaDimension C (V.subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt))
    (hdimT : schemeDeltaDimension C ((V.map p).subschemeι ≫ sY) ≠ ((k + 1 : ℤ) : EInt))
    (g : (rationalFunctions V.subscheme)ˣ) :
    properPushforwardPrincipalDivisor C sX sY p V hV g = 0 := by
  have hT : IsIntegral (V.map p).subscheme := isIntegral_subscheme_map_of_isProper p V hV
  have := hV
  have := hT
  set π : V.subscheme ⟶ (V.map p).subscheme := (V.subschemeι ≫ p).toImage with hπdef
  have hπ : π ≫ (V.map p).subschemeι = V.subschemeι ≫ p :=
    (V.subschemeι ≫ p).toImage_imageι
  have _ : IsProper π := isProper_toImage (V.subschemeι ≫ p)
  have _ : IsDominant π := inferInstanceAs (IsDominant (V.subschemeι ≫ p).toImage)
  set sT : (V.map p).subscheme ⟶ C.S := (V.map p).subschemeι ≫ sY with hsT
  have hπs : π ≫ sT = V.subschemeι ≫ sX := by
    rw [hsT, ← Category.assoc, hπ, Category.assoc, hp]
  have _ : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ sX)
  have _ : IsLocallyNoetherian (V.map p).subscheme := LocallyOfFiniteType.isLocallyNoetherian sT
  set eV := (rationalFunctionsEquivFunctionField V.subscheme).1 with heV
  set f : V.subscheme.functionField := eV (g : rationalFunctions V.subscheme) with hf
  have hfne : f ≠ 0 := by
    rw [hf]
    exact (g.isUnit.map eV.toRingHom.toMonoidHom).ne_zero
  have hVdim : schemeDeltaDimension C (π ≫ sT) = ((k + 1 : ℤ) : EInt) := by
    rw [schemeDeltaDimension_eq_genericPoint C (π ≫ sT), hπs,
      ← schemeDeltaDimension_eq_genericPoint C (V.subschemeι ≫ sX)]
    exact hdim
  set d : ℤ := relativeDimension C.dimensionFunction sT (genericPoint (V.map p).subscheme) with hd
  have hTdim : schemeDeltaDimension C sT = (d : EInt) :=
    schemeDeltaDimension_eq_genericPoint C sT
  have hdle : d ≤ k + 1 := by
    have hle := schemeDeltaDimension_le_of_isDominant' C sT π
    rw [hTdim, hVdim] at hle
    exact WithBotTop.coe_le_coe.mp hle
  have hdne : d ≠ k + 1 := fun h ↦ hdimT (by rw [hTdim, h])
  have hzero : properPushforward C (π ≫ sT) sT π rfl ((k + 1) - 1)
      (principalDivisorCycle C (π ≫ sT) hVdim f) = 0 := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
    by_cases hy : relativeDimension C.dimensionFunction sT y = (k + 1) - 1
    · have hygen : y = genericPoint (V.map p).subscheme := by
        by_contra hne
        have hlt := relativeDimension_le_sub_one_of_ne_genericPoint C sT hTdim hne
        omega
      have hdk : d = (k + 1) - 1 := by rw [← hy, hygen]
      have hcoef := hvanish C sT π hVdim (by rw [hTdim, hdk]) f hfne
      rw [properPushforward_apply_of_relativeDimension_eq C (π ≫ sT) sT π rfl _ _ y hy, hygen,
        show (∑ᶠ x ∈ π.base ⁻¹' {genericPoint (V.map p).subscheme},
            (principalDivisorCycle C (π ≫ sT) hVdim f).1 x * (π.residueDegree x : ℤ)) =
            ∑ᶠ x ∈ π.base ⁻¹' {genericPoint (V.map p).subscheme},
              V.subscheme.ord f x * (π.residueDegree x : ℤ) from
          finsum_congr fun x ↦ finsum_congr fun _ ↦ by
            rw [principalDivisorCycle_apply C (π ≫ sT) hVdim f x], hcoef]
      simp
    · exact properPushforward_apply_eq_zero_of_relativeDimension_ne C (π ≫ sT) sT π rfl _ _ y hy
  have hcycle : AlgebraicCycle.map π
      (relativeDimension C.dimensionFunction (π ≫ sT))
      (relativeDimension C.dimensionFunction sT)
      (principalCycle V.subscheme f) = 0 := congrArg Subtype.val hzero
  calc properPushforwardPrincipalDivisor C sX sY p V hV g
      = AlgebraicCycle.map (V.subschemeι ≫ p)
          (relativeDimension C.dimensionFunction (V.subschemeι ≫ sX))
          (relativeDimension C.dimensionFunction sY) (principalCycle V.subscheme f) :=
        algebraicCycle_map_comp_relativeDimension C (V.subschemeι ≫ sX) sX sY V.subschemeι p
          rfl hp _
    _ = AlgebraicCycle.map (π ≫ (V.map p).subschemeι)
          (relativeDimension C.dimensionFunction (V.subschemeι ≫ sX))
          (relativeDimension C.dimensionFunction sY) (principalCycle V.subscheme f) :=
        algebraicCycle_map_congr hπ.symm _ _ _
    _ = AlgebraicCycle.map (V.map p).subschemeι
          (relativeDimension C.dimensionFunction sT)
          (relativeDimension C.dimensionFunction sY)
          (AlgebraicCycle.map π
            (relativeDimension C.dimensionFunction (V.subschemeι ≫ sX))
            (relativeDimension C.dimensionFunction sT)
            (principalCycle V.subscheme f)) :=
        (algebraicCycle_map_comp_relativeDimension C (V.subschemeι ≫ sX) sT sY π
          (V.map p).subschemeι hπs rfl _).symm
    _ = 0 := by
        rw [show relativeDimension C.dimensionFunction (V.subschemeι ≫ sX) =
            relativeDimension C.dimensionFunction (π ≫ sT) from by rw [hπs], hcycle,
          algebraicCycle_map_zero]

/-! ### Stacks 02S2 for an arbitrary proper morphism -/

/-- Granted `Stacks.Chow.GenericFibreDegreeVanishes`, for every integral closed subscheme
`V ⊆ X` of delta-dimension `k + 1` and every nonzero rational function `g` on `V`, the proper
pushforward of `div(g)` along `p` is either zero or the principal divisor of a rational function
on the scheme-theoretic image `V.map p`. -/
theorem properPushforwardKillsPrincipalDivisor_of_genericFibreDegreeVanishes
    (hvanish : GenericFibreDegreeVanishes.{u}) (k : ℤ) :
    ProperPushforwardKillsPrincipalDivisor C sX sY p k :=
  properPushforwardKillsPrincipalDivisor_of_vanishing_of_dimension_drop C sX sY p hp k
    fun V hV hdim hdimT g ↦
      properPushforwardPrincipalDivisor_eq_zero_of_schemeDeltaDimension_ne C sX sY p hp
        hvanish k V hV hdim hdimT g

/-- Granted `Stacks.Chow.GenericFibreDegreeVanishes`, proper pushforward of
`k`-cycles along an arbitrary proper morphism over the base carries cycles rationally equivalent
to zero to cycles rationally equivalent to zero. -/
theorem properPushforwardFactorsThroughRationalEquivalence_of_genericFibreDegreeVanishes
    (hvanish : GenericFibreDegreeVanishes.{u}) (k : ℤ) :
    ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k :=
  properPushforwardFactorsThroughRationalEquivalence_of_killsPrincipalDivisor C sX sY p hp k
    (properPushforwardKillsPrincipalDivisor_of_genericFibreDegreeVanishes C sX sY p hp hvanish k)

/-- Granted `Stacks.Chow.GenericFibreDegreeVanishes`, the proper pushforwards of rationally
equivalent cycles are rationally equivalent. -/
theorem properPushforward_rationallyEquivalent_of_genericFibreDegreeVanishes
    (hvanish : GenericFibreDegreeVanishes.{u}) (k : ℤ) {α β : CycleGroup C sX k}
    (h : RationallyEquivalent C sX k α β) :
    RationallyEquivalent C sY k (properPushforward C sX sY p hp k α)
      (properPushforward C sX sY p hp k β) :=
  properPushforward_rationallyEquivalent C sX sY p hp k
    (properPushforwardFactorsThroughRationalEquivalence_of_genericFibreDegreeVanishes
      C sX sY p hp hvanish k) h

end Stacks.Chow

namespace Stacks.Chow

/-! ### The case of a one-point base -/

variable (C : ChowSituation.{u}) [IsIntegral C.S] [Subsingleton C.S] {X : Scheme.{u}}

/-- Over a one-point base with vanishing dimension function, granted
`Stacks.Chow.GenericFibreDegreeVanishes`, the degree of the principal divisor of a nonzero
rational function on a proper integral curve vanishes. -/
theorem principalDivisorDegree_eq_zero_of_genericFibreDegreeVanishes
    (hvanish : GenericFibreDegreeVanishes.{u}) (hδ : ∀ s : C.S, C.dimensionFunction s = 0)
    (c : X ⟶ C.S) [IsProper c] [IsIntegral X] [IsLocallyNoetherian X]
    (hdim : schemeDeltaDimension C c = ((1 : ℤ) : EInt)) (f : X.functionField) (hf : f ≠ 0) :
    principalDivisorDegree c f = 0 := by
  have _ : IsDominant c := ⟨by
    refine denseRange_iff_closure_range.mpr (Set.eq_univ_of_forall fun s ↦ ?_)
    have hne : Nonempty X := ⟨genericPoint X⟩
    exact subset_closure ⟨Classical.arbitrary X, Subsingleton.elim _ s⟩⟩
  have hVdim : schemeDeltaDimension C (c ≫ 𝟙 C.S) = ((1 : ℤ) : EInt) := by
    rw [schemeDeltaDimension_eq_genericPoint C (c ≫ 𝟙 C.S), Category.comp_id,
      ← schemeDeltaDimension_eq_genericPoint C c]
    exact hdim
  have hTdim : schemeDeltaDimension C (𝟙 C.S) = (((1 : ℤ) - 1 : ℤ) : EInt) := by
    rw [schemeDeltaDimension_eq_genericPoint C (𝟙 C.S), relativeDimension_id, hδ]
    rfl
  have hsum := hvanish C (𝟙 C.S) c hVdim hTdim f hf
  rw [principalDivisorDegree, ← hsum]
  refine (finsum_mem_univ _).symm.trans (finsum_congr fun x ↦ ?_)
  rw [show ((c : X ⟶ C.S)).base ⁻¹' {genericPoint C.S} = (Set.univ : Set X) from
    Set.eq_univ_of_forall fun x ↦ Subsingleton.elim _ _]

/-- Over a one-point base with vanishing dimension function, granted
`Stacks.Chow.GenericFibreDegreeVanishes`, the proper pushforward to the base of the principal
divisor of a nonzero rational function on a proper integral curve vanishes. -/
theorem properPushforward_principalDivisorCycle_eq_zero_of_genericFibreDegreeVanishes
    (hvanish : GenericFibreDegreeVanishes.{u}) (hδ : ∀ s : C.S, C.dimensionFunction s = 0)
    (c : X ⟶ C.S) [IsProper c] [IsIntegral X] [IsLocallyNoetherian X]
    (hdim : schemeDeltaDimension C c = ((1 : ℤ) : EInt)) (f : X.functionField) (hf : f ≠ 0) :
    properPushforward C c (𝟙 C.S) c (Category.comp_id c) 0
      (principalDivisorCycle C c hdim f) = 0 := by
  have _ : Nonempty C.S := ⟨genericPoint C.S⟩
  exact (properPushforward_principalDivisorCycle_eq_zero_iff C hδ c hdim f).mpr
    (principalDivisorDegree_eq_zero_of_genericFibreDegreeVanishes C hvanish hδ c hdim f hf)

end Stacks.Chow

end
