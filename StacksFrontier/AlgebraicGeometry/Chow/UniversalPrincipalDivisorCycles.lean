module

public import StacksFrontier.AlgebraicGeometry.Chow.EnvelopeCycleLift
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.FunctionField
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.InfinityCartier
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroCartier
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroIdeal
public import StacksFrontier.AlgebraicGeometry.Divisors.IntegralLocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.LocallyPrincipalPullback.Basic

/-!
# The principal divisor of a rational function through its graph

This file continues `StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor`, which
constructs the closure `Y` of the graph of a section `s ∈ Γ(X, U)` inside `X ×_S ℙ¹_S`, its two
projections `p : Y ⟶ X`, `q : Y ⟶ ℙ¹_S`, the fibres `Y₀ = q⁻¹D₀`, `Y_∞ = q⁻¹D_∞` and the
rational function on `Y` induced by a unit section on `U`.

What is added here is, first, the content of part (3) of Tag 02RQ: the pullbacks `Y₀` and `Y_∞` are
defined, that is, they are effective Cartier divisors on `Y`. They are locally principal because
`D₀` and `D_∞` are, and the local generator is a nonzerodivisor because `Y` is integral and neither
fibre is all of `Y` — the generic point of `Y` lies in the affine chart of `ℙ¹_S`, which `D_∞`
misses, and its coordinate there is the unit section, so `D₀` misses it too.

Second, the comparison of `Y` with `X` as objects of a Chow situation: the open `p⁻¹(U) ⊆ Y` is
the image of `U` under an open immersion, so `p` carries the generic point of `Y` to the generic
point of `X` and induces an isomorphism of function fields. Two consequences are the
delta-dimension of `Y` and the identity of part (5) of Tag 02RQ,

  `div_X(f) = p_* div_Y(f)`.

Part (5) is Tag 02RT, the pushforward formula for a proper dominant morphism, specialised to
this `p`: the function-field extension is trivial, so the norm appearing in 02RT is the
identity.

## Main results

* `Stacks.Chow.isOpenImmersion_graphInclusion`: `U ⟶ Y` is an open immersion.
* `Stacks.Chow.graphInclusion_comp_graphLineProjection`: the graph followed by `q` is the
  morphism `U ⟶ ℙ¹_S` attached to the section.
* `Stacks.Chow.notMem_support_lineZeroDivisor_sectionToLine` and
  `Stacks.Chow.notMem_support_lineInfinityDivisor_sectionToLine`: the image of `U` in `ℙ¹_S`
  meets neither `D₀` nor `D_∞`, with
  `Stacks.Chow.notMem_support_graphZeroFiber_genericPoint` and
  `Stacks.Chow.notMem_support_graphInfinityFiber_genericPoint` the consequence at the generic
  point of `Y`.
* `Stacks.Chow.isPullbackDefined_zeroDivisor` and
  `Stacks.Chow.isPullbackDefined_infinityDivisor`: the two halves of part (3) of Tag 02RQ.
* `Stacks.Chow.genericPoint_graphClosure` and `Stacks.Chow.graphProjection_genericPoint`: the
  generic point of `Y` is the image of the generic point of `U`, and `p` carries it to the
  generic point of `X`.
* `Stacks.Chow.isDominant_graphProjection`: `p` is dominant.
* `Stacks.Chow.bijective_dominantFunctionFieldMap_graphProjection`,
  `Stacks.Chow.finrank_functionField_graphClosure` and
  `Stacks.Chow.norm_dominantFunctionFieldMap_graphProjection`: `p` induces an isomorphism
  `R(X) ≅ R(Y)`, so that extension has degree one and its norm is the identity.
* `Stacks.Chow.schemeDeltaDimension_graphClosure`: `dim_δ(Y) = dim_δ(X)`.
* `Stacks.Chow.dominantFunctionFieldMap_graphRationalFunction`: the function-field map of `p`
  carries the rational function of `s` on `X` to the rational function of `s` on `Y`.
* `Stacks.Chow.principalDivisorCycle_eq_properPushforward`: the identity of part (5) of
  Tag 02RQ.

Parts (4) and (6) of the tag — `div_Y(f) = [Y₀]_{n-1} - [Y_∞]_{n-1}` on `Y`, and the same
identity on `X` — are not here. Part (4) needs the local equation of `Y₀` at a codimension-one
point of `Y` to be identified with the rational function, and its multiplicity with the length
of the quotient of the local ring by that equation; part (6) is part (4) together with the
pushforward formula for the cycle of a closed subscheme, Tag 02R6, which this repository does
not have.

## Implementation notes

The statements here are made for `U ⟶ X` quasi-compact, the setting of
`Stacks.Chow.isIso_graphProjection_restrict`; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor`. In a Chow situation the
hypothesis is automatic, and the statements of Tag 02RQ there, with the integrality of `Y`, the
density of `p⁻¹(U)` and the delta-dimension of `Y` derived rather than assumed, are in
`StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles.GraphConstruction`.

The identification of the generic points is `AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion`
applied twice, to `U ⟶ Y` and to `U ⟶ X`; the first needs `U ⟶ Y` to be an open immersion,
which is `Stacks.Chow.isIso_graphRestrictLift` composed with the base change of `U ⟶ X`. From
there the residue-field map of `p` at the generic point of `Y` is an isomorphism by
cancellation, which is what feeds
`Stacks.Chow.relativeDimension_eq_of_residueFieldMap_isIso` for the delta-dimension.

The rational function of Tag 01RU is `Stacks.Chow.rationalFunctions`, a rational map to the
affine line, while `AlgebraicGeometry.Scheme.ord` and hence
`Stacks.Chow.principalDivisorCycle` are stated on `AlgebraicGeometry.Scheme.functionField`. The
two are identified by `Stacks.Chow.rationalFunctionsEquivFunctionField`, and the statements here
use that identification, as the rest of the chapter does.

Part (3) is deduced from `Stacks.Divisors.isEffectiveCartierDivisor_of_isLocallyPrincipal`, so
no affine-local chart is rebuilt and nothing is reproved: the only inputs are that `D₀` and
`D_∞` are effective Cartier divisors on `ℙ¹_S` (proved in `.UniversalPrincipalDivisor.ZeroCartier`
and `.InfinityCartier`), Tag 053P
`Stacks.Divisors.isLocallyPrincipal_comap` together with
`Stacks.Divisors.isLocallyPrincipal_of_isEffectiveCartierDivisor`, and the two generic-point
statements above.

## References

* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 01WV](https://stacks.math.columbia.edu/tag/01WV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- Over a field, an extension of degree one has the identity as its norm. -/
private theorem norm_algebraMap_of_finrank_one {R S : Type*} [Field R] [CommRing S] [Algebra R S]
    (h : Module.finrank R S = 1) (a : R) : Algebra.norm R (algebraMap R S a) = a := by
  rw [Algebra.norm_algebraMap, h, pow_one]

/-- The norm of the algebra structure given by a bijective ring homomorphism out of a field is
the identity. -/
private theorem norm_toAlgebra_of_bijective {R S : Type*} [Field R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Bijective φ) (a : R) :
    letI : Algebra R S := φ.toAlgebra
    Algebra.norm R (φ a) = a := by
  let _ : Algebra R S := φ.toAlgebra
  have halg : algebraMap R S = φ := RingHom.algebraMap_toAlgebra φ
  have h1 : Module.finrank R S = 1 :=
    Module.finrank_of_bijective_algebraMap (by rw [halg]; exact hφ)
  have h2 := norm_algebraMap_of_finrank_one h1 a
  rw [halg] at h2
  exact h2

/-- The function-field map of a dominant morphism of integral schemes depends only on the
morphism; the dominance instance is a proposition. -/
private theorem dominantFunctionFieldMap_congr {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    {f f' : A ⟶ B} [IsDominant f] [IsDominant f'] (h : f = f') :
    dominantFunctionFieldMap f = dominantFunctionFieldMap f' := by
  subst h
  rfl

/-! ### `U ⟶ Y` is an open immersion -/

/-- The graph `U ⟶ Y` is an open immersion onto `p⁻¹(U)`: it is the isomorphism
`U ≅ p⁻¹(U)` of part (2) followed by the base change of the open immersion `U ⟶ X`. -/
instance isOpenImmersion_graphInclusion {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens)
    (s : Γ(X, U)) [QuasiCompact U.ι] : IsOpenImmersion (graphInclusion sX U s) := by
  have := isIso_graphRestrictLift sX U s
  rw [← graphRestrictLift_fst sX U s]
  infer_instance

section GenericPoint

variable {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U))
  [IsIntegral X] [Nonempty U.toScheme] [QuasiCompact U.ι]
  [IsIntegral (graphClosure sX U s)]

/-- A nonempty open of an integral scheme is dense, hence its immersion is dominant. -/
instance isDominant_opens_ι_of_nonempty : IsDominant U.ι :=
  Opens.isDominant_ι (U.2.dense (Set.nonempty_coe_sort.mp ‹Nonempty U.toScheme›))

/-- The generic point of `Y` is the image of the generic point of `U` under the graph. -/
theorem genericPoint_graphClosure :
    (graphInclusion sX U s).base (genericPoint U.toScheme) =
      genericPoint (graphClosure sX U s) :=
  genericPoint_eq_of_isOpenImmersion (graphInclusion sX U s)

/-- The projection `p : Y ⟶ X` carries the generic point of `Y` to the generic point of `X`. -/
theorem graphProjection_genericPoint :
    (graphProjection sX U s).base (genericPoint (graphClosure sX U s)) = genericPoint X := by
  rw [← genericPoint_graphClosure sX U s]
  change ((graphInclusion sX U s) ≫ (graphProjection sX U s)).base _ = _
  rw [graphInclusion_comp_graphProjection]
  exact genericPoint_eq_of_isOpenImmersion U.ι

/-- The projection `p : Y ⟶ X` is dominant: it hits the generic point of `X`. -/
instance isDominant_graphProjection : IsDominant (graphProjection sX U s) :=
  ((tfae_isDominant_of_isIntegral (graphProjection sX U s)).out 1 2).mpr
    (graphProjection_genericPoint sX U s)

/-- At the generic point of `Y` the projection induces an isomorphism of residue fields: it does
so after composing with the graph, which is an open immersion. -/
theorem isIso_residueFieldMap_graphProjection :
    IsIso ((graphProjection sX U s).residueFieldMap (genericPoint (graphClosure sX U s))) := by
  have key : IsIso ((graphInclusion sX U s ≫ graphProjection sX U s).residueFieldMap
      (genericPoint U.toScheme)) := by
    rw [graphInclusion_comp_graphProjection]
    infer_instance
  rw [Scheme.residueFieldMap_comp] at key
  rw [← genericPoint_graphClosure sX U s]
  exact (isIso_comp_right_iff _
    ((graphInclusion sX U s).residueFieldMap (genericPoint U.toScheme))).mp key

/-- The projection `p : Y ⟶ X` induces an isomorphism of function fields: the composite with the
graph is the function-field map of the dominant open immersion `U ⟶ X`, which is bijective, and
the graph's own function-field map is injective. -/
theorem bijective_dominantFunctionFieldMap_graphProjection :
    Function.Bijective (dominantFunctionFieldMap (graphProjection sX U s)) := by
  refine ⟨RingHom.injective _, fun b => ?_⟩
  have hcomp : dominantFunctionFieldMap (graphInclusion sX U s ≫ graphProjection sX U s) =
      (dominantFunctionFieldMap (graphInclusion sX U s)).comp
        (dominantFunctionFieldMap (graphProjection sX U s)) :=
    dominantFunctionFieldMap_comp _ _
  have hsurj : Function.Surjective
      (dominantFunctionFieldMap (graphInclusion sX U s ≫ graphProjection sX U s)) := by
    rw [dominantFunctionFieldMap_congr (graphInclusion_comp_graphProjection sX U s)]
    exact (functionFieldEquiv_openImmersion U.ι).surjective
  obtain ⟨a, ha⟩ := hsurj (dominantFunctionFieldMap (graphInclusion sX U s) b)
  rw [hcomp] at ha
  exact ⟨a, RingHom.injective (dominantFunctionFieldMap (graphInclusion sX U s)) ha⟩

/-- The function-field extension induced by `p : Y ⟶ X` has degree one. The extension is
carried as an instance argument together with the hypothesis that its structure map is the
function-field map of `p`, as in
`StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward`. -/
theorem finrank_functionField_graphClosure
    [Algebra X.functionField (graphClosure sX U s).functionField]
    (halg : algebraMap X.functionField (graphClosure sX U s).functionField =
      dominantFunctionFieldMap (graphProjection sX U s)) :
    Module.finrank X.functionField (graphClosure sX U s).functionField = 1 := by
  refine Module.finrank_of_bijective_algebraMap ?_
  rw [halg]
  exact bijective_dominantFunctionFieldMap_graphProjection sX U s

/-- The norm of the function-field extension induced by `p : Y ⟶ X` is the identity, that
extension having degree one. -/
theorem norm_dominantFunctionFieldMap_graphProjection (a : X.functionField) :
    letI : Algebra X.functionField (graphClosure sX U s).functionField :=
      (dominantFunctionFieldMap (graphProjection sX U s)).toAlgebra
    Algebra.norm X.functionField (dominantFunctionFieldMap (graphProjection sX U s) a) = a :=
  norm_toAlgebra_of_bijective _ (bijective_dominantFunctionFieldMap_graphProjection sX U s) a

end GenericPoint

/-! ### Part (3): the pullbacks of `D₀` and `D_∞` to `Y` are defined -/

/-- The graph `U ⟶ Y` followed by the projection to `ℙ¹_S` is the morphism `U ⟶ ℙ¹_S` attached
to the section. -/
theorem graphInclusion_comp_graphLineProjection {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens)
    (s : Γ(X, U)) :
    graphInclusion sX U s ≫ graphLineProjection sX U s = sectionToLine sX U s := by
  change (sectionGraph sX U s).toImage ≫ ((sectionGraph sX U s).imageι ≫
      pullback.snd sX (relativeProjectiveLine S ↘ S)) = sectionToLine sX U s
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, sectionGraph, pullback.lift_snd]

/-- The affine coordinate does not vanish anywhere on the image of `U ⟶ 𝔸¹_S` attached to a
unit section: that coordinate pulls back to the section itself, which is a unit. -/
theorem mem_basicOpen_affineCoordinate {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens)
    (g : (Γ(X, U))ˣ) (x : U.toScheme) :
    (sectionToAffineLine sX U ↑g).base x ∈
      (affineLineOver S).basicOpen (affineCoordinate S) := by
  have h := Scheme.preimage_basicOpen_top (sectionToAffineLine sX U ↑g) (affineCoordinate S)
  rw [sectionToAffineLine_appTop_affineCoordinate] at h
  have hx : x ∈ U.toScheme.basicOpen (U.topIso.inv (g : Γ(X, U))) := by
    rw [Scheme.basicOpen_of_isUnit _ (IsUnit.map U.topIso.inv.hom g.isUnit)]
    trivial
  rw [← h] at hx
  exact hx

/-- `D₀` does not meet the image of the morphism `U ⟶ ℙ¹_S` attached to a unit section: on the
affine chart `D₀` is cut out by the coordinate, which pulls back to the unit section. -/
theorem notMem_support_lineZeroDivisor_sectionToLine {X S : Scheme.{u}} (sX : X ⟶ S)
    (U : X.Opens) (g : (Γ(X, U))ˣ) (x : U.toScheme) :
    (sectionToLine sX U ↑g).base x ∉
      ((lineZeroDivisor S).support : Set (relativeProjectiveLine S)) := by
  intro hx
  have hz : (sectionToAffineLine sX U ↑g).base x ∈
      ((lineZeroDivisor S).comap (affineChart S)).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hx
  obtain ⟨B, hzB⟩ := Stacks.Divisors.exists_affineOpens_mem
    ((sectionToAffineLine sX U ↑g).base x)
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hzB,
    zeroDivisor_ideal_comap_affineChart, Scheme.mem_zeroLocus_iff] at hz
  refine hz _ (Ideal.subset_span rfl) ?_
  rw [Scheme.basicOpen_res]
  exact ⟨hzB, mem_basicOpen_affineCoordinate sX U g x⟩

/-- `D_∞` does not meet the affine chart at all, so in particular it does not meet the image of
the morphism `U ⟶ ℙ¹_S` attached to a section. -/
theorem notMem_support_lineInfinityDivisor_sectionToLine {X S : Scheme.{u}} (sX : X ⟶ S)
    (U : X.Opens) (s : Γ(X, U)) (x : U.toScheme) :
    (sectionToLine sX U s).base x ∉
      ((lineInfinityDivisor S).support : Set (relativeProjectiveLine S)) := by
  intro hx
  have hz : (sectionToAffineLine sX U s).base x ∈
      ((lineInfinityDivisor S).comap (affineChart S)).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hx
  rw [comap_lineInfinityDivisor_affineChart, Scheme.IdealSheafData.support_top] at hz
  exact hz

section Fibres

variable {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (g : (Γ(X, U))ˣ)
  [IsIntegral X] [QuasiCompact U.ι]

/-- The generic point of `Y` is not in the pullback of `D` along `q` if the image of `U` in `ℙ¹_S`
misses `D`. -/
private theorem notMem_support_comap_graphLineProjection_genericPoint [Nonempty U.toScheme]
    [IsIntegral (graphClosure sX U ↑g)] (D : (relativeProjectiveLine S).IdealSheafData)
    (hD : ∀ x : U.toScheme, (sectionToLine sX U ↑g).base x ∉ (D.support : Set _)) :
    genericPoint (graphClosure sX U ↑g) ∉
      ((D.comap (graphLineProjection sX U ↑g)).support : Set (graphClosure sX U ↑g)) := by
  rw [← genericPoint_graphClosure sX U ↑g]
  intro h
  refine hD (genericPoint U.toScheme) ?_
  rw [← graphInclusion_comp_graphLineProjection sX U ↑g]
  rw [Scheme.IdealSheafData.support_comap] at h
  exact h

/-- The pullback of an effective Cartier divisor `D` on `ℙ¹_S` along `q : Y ⟶ ℙ¹_S` is defined
when the image of `U` misses `D`: it is locally principal, and its local generator is a
nonzerodivisor because `Y` is integral and the generic point of `Y` is not in the pullback. -/
private theorem isPullbackDefined_graphLineProjection_of_notMem (hU : Dense (U : Set X))
    (D : (relativeProjectiveLine S).IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (h : ∀ x : U.toScheme, (sectionToLine sX U ↑g).base x ∉ (D.support : Set _)) :
    Stacks.Divisors.IsPullbackDefined (graphLineProjection sX U ↑g) D := by
  have hne : Nonempty U.toScheme := by
    obtain ⟨x, hx⟩ := hU.nonempty
    exact ⟨⟨x, hx⟩⟩
  have hY : IsIntegral (graphClosure sX U ↑g) := isIntegral_graphClosure sX U ↑g hU
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_isLocallyPrincipal _ ?_
    (Stacks.Divisors.isLocallyPrincipal_comap _ _
      (Stacks.Divisors.isLocallyPrincipal_of_isEffectiveCartierDivisor _ hD))
  intro hbot
  refine notMem_support_comap_graphLineProjection_genericPoint sX U g D h ?_
  rw [hbot, Scheme.IdealSheafData.support_bot]
  trivial

/-- The generic point of `Y` is not in `Y₀`: it is the image of the generic point of `U`, whose
image in `ℙ¹_S` misses `D₀` because the section is a unit. -/
theorem notMem_support_graphZeroFiber_genericPoint [Nonempty U.toScheme]
    [IsIntegral (graphClosure sX U ↑g)] :
    genericPoint (graphClosure sX U ↑g) ∉
      ((graphZeroFiber sX U ↑g).support : Set (graphClosure sX U ↑g)) :=
  notMem_support_comap_graphLineProjection_genericPoint sX U g _
    fun x => notMem_support_lineZeroDivisor_sectionToLine sX U g x

/-- The generic point of `Y` is not in `Y_∞`: its image in `ℙ¹_S` lies in the affine chart,
which `D_∞` does not meet. -/
theorem notMem_support_graphInfinityFiber_genericPoint [Nonempty U.toScheme]
    [IsIntegral (graphClosure sX U ↑g)] :
    genericPoint (graphClosure sX U ↑g) ∉
      ((graphInfinityFiber sX U ↑g).support : Set (graphClosure sX U ↑g)) :=
  notMem_support_comap_graphLineProjection_genericPoint sX U g _
    fun x => notMem_support_lineInfinityDivisor_sectionToLine sX U ↑g x

/-- The pullback `Y₀ = q⁻¹D₀` along
`q : Y ⟶ ℙ¹_S` is defined. `Y₀` is locally principal because `D₀` is an effective Cartier
divisor, and the local generator is a nonzerodivisor because `Y` is integral and `Y₀` is not all
of `Y`: the generic point of `Y` is not in `Y₀`. -/
theorem isPullbackDefined_zeroDivisor (hU : Dense (U : Set X)) :
    Stacks.Divisors.IsPullbackDefined (graphLineProjection sX U ↑g) (lineZeroDivisor S) :=
  isPullbackDefined_graphLineProjection_of_notMem sX U g hU _
    (lineZeroDivisor_isEffectiveCartierDivisor S)
    fun x => notMem_support_lineZeroDivisor_sectionToLine sX U g x

/-- The pullback `Y_∞ = q⁻¹D_∞` along `q : Y ⟶ ℙ¹_S` is defined. -/
theorem isPullbackDefined_infinityDivisor (hU : Dense (U : Set X)) :
    Stacks.Divisors.IsPullbackDefined (graphLineProjection sX U ↑g) (lineInfinityDivisor S) :=
  isPullbackDefined_graphLineProjection_of_notMem sX U g hU _
    (lineInfinityDivisor_isEffectiveCartierDivisor S)
    fun x => notMem_support_lineInfinityDivisor_sectionToLine sX U ↑g x

end Fibres

/-! ### The delta-dimension of `Y`, and part (5) -/

section Cycles

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] [IsIntegral X] (U : X.Opens) (g : (Γ(X, U))ˣ)

/-- `Y` has the same delta-dimension as `X`: both are integral, and `p` carries the generic
point of `Y` to the generic point of `X` with an isomorphism of residue fields. -/
theorem schemeDeltaDimension_graphClosure [QuasiCompact U.ι] (n : ℤ)
    (hn : schemeDeltaDimension C sX = (n : EInt)) (hU : Dense (U : Set X))
    (hft : LocallyOfFiniteType (graphBaseMorphism sX U ↑g)) :
    letI : LocallyOfFiniteType (graphBaseMorphism sX U ↑g) := hft
    schemeDeltaDimension C (graphBaseMorphism sX U ↑g) = (n : EInt) := by
  have hne : Nonempty U.toScheme := by
    obtain ⟨x, hx⟩ := hU.nonempty
    exact ⟨⟨x, hx⟩⟩
  have hY : IsIntegral (graphClosure sX U ↑g) := isIntegral_graphClosure sX U ↑g hU
  rw [schemeDeltaDimension_eq_genericPoint C (graphBaseMorphism sX U ↑g),
    show graphBaseMorphism sX U (g : Γ(X, U)) = graphProjection sX U ↑g ≫ sX from rfl,
    relativeDimension_eq_of_residueFieldMap_isIso C sX (graphProjection sX U ↑g)
      (genericPoint (graphClosure sX U ↑g)) (isIso_residueFieldMap_graphProjection sX U ↑g),
    graphProjection_genericPoint sX U ↑g, ← schemeDeltaDimension_eq_genericPoint C sX]
  exact hn

omit [LocallyOfFiniteType sX] in
/-- The function-field map of `p : Y ⟶ X` carries the rational function represented by a
section `s` on the dense open `U ⊆ X` to the rational function represented by its pullback on
`p⁻¹(U) ⊆ Y`, which is the rational function of `Y` that Tag 02RQ uses. -/
theorem dominantFunctionFieldMap_graphRationalFunction [Nonempty U.toScheme] [QuasiCompact U.ι]
    [IsIntegral (graphClosure sX U ↑g)] (hU : Dense (U : Set X))
    (hd : GraphPreimageDense sX U ↑g) :
    dominantFunctionFieldMap (graphProjection sX U ↑g)
        ((rationalFunctionsEquivFunctionField X).1 (ofSection X ⟨U, hU⟩ ↑g)) =
      (rationalFunctionsEquivFunctionField (graphClosure sX U ↑g)).1
        ↑(graphRationalFunction sX U g hd) := by
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.2).mpr (by simpa using ‹Nonempty U.toScheme›)
  have hneW : Nonempty (graphPreimage sX U ↑g).toScheme :=
    Set.nonempty_coe_sort.mpr hd.nonempty
  have hηW : genericPoint (graphClosure sX U ↑g) ∈ graphPreimage sX U ↑g :=
    ((genericPoint_spec (graphClosure sX U ↑g)).mem_open_set_iff
      (graphPreimage sX U ↑g).2).mpr (by simpa using hd.nonempty)
  rw [(rationalFunctionsEquivFunctionField X).2 ⟨U, hU⟩ ↑g hηU,
    show (↑(graphRationalFunction sX U g hd) : rationalFunctions (graphClosure sX U ↑g)) =
      ofSection (graphClosure sX U ↑g) ⟨graphPreimage sX U ↑g, hd⟩
        (((graphProjection sX U ↑g).app U).hom ↑g) from
      ofSectionRingHom_apply _ _ _,
    (rationalFunctionsEquivFunctionField (graphClosure sX U ↑g)).2
      ⟨graphPreimage sX U ↑g, hd⟩ _ hηW]
  have hcomm := DFunLike.congr_fun
    (appLE_germToFunctionField_commutes (graphProjection sX U ↑g) U
      (graphPreimage sX U ↑g) le_rfl) (g : Γ(X, U))
  rw [Scheme.Hom.appLE_eq_app] at hcomm
  exact hcomm.symm

/-- The principal divisor on `X` is the proper
pushforward along `p` of the principal divisor on `Y`. This is Tag 02RT for the proper dominant
morphism `p`, whose function-field extension has degree one, so that the norm occurring there is
the identity. -/
theorem principalDivisorCycle_eq_properPushforward [QuasiCompact U.ι] (n : ℤ)
    (hn : schemeDeltaDimension C sX = (n : EInt))
    (f : (rationalFunctions X)ˣ) (hU : Dense (U : Set X))
    (hf : ofSection X ⟨U, hU⟩ ↑g = (f : rationalFunctions X))
    (hd : GraphPreimageDense sX U ↑g)
    (hYint : IsIntegral (graphClosure sX U ↑g))
    (hYft : LocallyOfFiniteType (graphBaseMorphism sX U ↑g))
    (hp : IsProper (graphProjection sX U ↑g)) :
    letI : IsIntegral (graphClosure sX U ↑g) := hYint
    letI : LocallyOfFiniteType (graphBaseMorphism sX U ↑g) := hYft
    letI : IsProper (graphProjection sX U ↑g) := hp
    ∀ hYdim : schemeDeltaDimension C (graphBaseMorphism sX U ↑g) = (n : EInt),
      principalDivisorCycle C sX hn ((rationalFunctionsEquivFunctionField X).1 ↑f) =
        properPushforward C (graphBaseMorphism sX U ↑g) sX (graphProjection sX U ↑g) rfl (n - 1)
          (principalDivisorCycle C (graphBaseMorphism sX U ↑g) hYdim
            ((rationalFunctionsEquivFunctionField (graphClosure sX U ↑g)).1
              ↑(graphRationalFunction sX U g hd))) := by
  intro hYdim
  have hne : Nonempty U.toScheme := by
    obtain ⟨x, hx⟩ := hU.nonempty
    exact ⟨⟨x, hx⟩⟩
  have hfWne : (rationalFunctionsEquivFunctionField (graphClosure sX U ↑g)).1
      ↑(graphRationalFunction sX U g hd) ≠ 0 := fun h =>
    (graphRationalFunction sX U g hd).ne_zero
      ((rationalFunctionsEquivFunctionField (graphClosure sX U ↑g)).1.injective
        (h.trans (map_zero _).symm))
  rw [properPushforward_principalDivisorCycle C (graphBaseMorphism sX U ↑g) sX hYdim hn
    (graphProjection sX U ↑g) rfl _ hfWne,
    ← dominantFunctionFieldMap_graphRationalFunction C sX U g hU hd, ← hf]
  exact (congrArg (principalDivisorCycle C sX hn)
    (norm_dominantFunctionFieldMap_graphProjection sX U ↑g _)).symm

end Cycles

end Stacks.Chow

end
