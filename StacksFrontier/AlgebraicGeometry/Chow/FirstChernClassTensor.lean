module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapRuleIndependence
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponentModuleIso
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.InvertibleChernSpecialization
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionIndependence
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkGenerators
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberPrincipal

/-!
# Additivity of the first Chern class cap product

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project and let `L`, `N` be invertible `𝒪_X`-modules. Stacks 02SP asserts

  `c₁(L) ∩ α + c₁(N) ∩ α = c₁(L ⊗_{𝒪_X} N) ∩ α`  in  `A_k(X)`  for  `α ∈ Z_{k+1}(X)`,

together with `c₁(𝒪_X) ∩ α = 0`.

The cap product is `Stacks.Chow.firstChernClassCapOfInvertible`, the coefficientwise extension of
the component rule of an invertible module. On an integral closed subscheme `W ⊆ X` of
delta-dimension `k + 1` that rule is the divisor cycle of a *chosen* nonzero meromorphic section
of `L|_W`, so the identity cannot hold at the level of cycles — three unrelated choices are made
— and the content is twofold:

* on each `W` the three divisor cycles satisfy
  `div_{(L ⊗ N)|_W}(u) ∼_{rat} div_{L|_W}(s) + div_{N|_W}(t)`, because the product `s ⊗ t` is a
  nonzero meromorphic section of `L|_W ⊗ N|_W` whose divisor is the sum of the two divisors
  (Stacks 02SL, here in the generic-stalk model), because `(L ⊗ N)|_W ≅ L|_W ⊗ N|_W`
  (Stacks 01CD) and the divisor of a meromorphic section is invariant under an isomorphism of
  modules, and because the class of the divisor cycle does not depend on the section
  (Stacks 02SJ (2), `Stacks.Chow.firstChernComponentClass_eq_mk_of_ne_zero`);
* those rational equivalences, one on each integral component of `α`, may be summed. The family
  of components of a cycle is only *locally* finite, so this needs the carriers of Stacks 02RZ;
  the library already assembles them, in `Stacks.Chow.firstChernClassCap_congr`, and that is
  what is applied here.

The vanishing on the structure sheaf is then formal: `𝒪_X ⊗ 𝒪_X ≅ 𝒪_X`, so additivity gives
`c₁(𝒪_X) ∩ α + c₁(𝒪_X) ∩ α = c₁(𝒪_X) ∩ α`.

## Main results

* `Stacks.Chow.firstChernClassCapOfInvertible_tensorObj` — **Stacks 02SP**, the additivity.
* `Stacks.Chow.firstChernClassCapOfInvertible_unit` — **Stacks 02SP**, the vanishing of
  `c₁(𝒪_X) ∩ −`.
* `Stacks.Chow.firstChernClassCapOfInvertible_congr` — the cap product depends only on the
  isomorphism class of the invertible module.
* `Stacks.Divisors.orderOfVanishing_tensorStalkTmul` — Stacks 02SL coefficientwise, in the
  generic-stalk model: the order of vanishing of a product of meromorphic sections is the sum of
  the orders.
* `Stacks.Chow.rationallyEquivalent_firstChernComponentCycleRule_tensorObj` — Stacks 02SP on a
  single integral component.

## Implementation notes

### Which model of a meromorphic section

Throughout, a meromorphic section of `L` on an integral scheme is an element of the generic stalk
`L_η`, which is the model `Stacks.Chow.firstChernComponentCycleRule` is built from; see the module
documentation of `StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder`. Stacks 02SL is therefore
re-proved here for `Stacks.Divisors.orderOfVanishing` rather than imported from
`StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TensorSection`, which proves it for
`AlgebraicGeometry.orderOfVanishingMeromorphic`, the sheaf-theoretic model: the two are different
constants and bridging them is Stacks 01X5 (2), which this repository does not have. The
mathematical argument is the same one — a product of stalk bases is a stalk basis
(`AlgebraicGeometry.isStalkBasis_tensorStalkTmul`), the coordinate of `s ⊗ t` is the product of
the coordinates, and `AlgebraicGeometry.Scheme.ord` is additive.

### What is reused rather than re-proved

Nothing about the behaviour of the cap product under a change of component rule is proved here.
That two rules with rationally equivalent components have the same cap product is
`Stacks.Chow.firstChernClassCap_congr`
(`StacksFrontier.AlgebraicGeometry.Chow.ChernCapRuleIndependence`), and the transport of a stalk
basis, a coordinate, an order of vanishing and a component cycle along an isomorphism of modules
is the `mapStalkLinearMap` family of
`StacksFrontier.AlgebraicGeometry.Chow.ChernComponentModuleIso`. Both modules are imported and
their declarations are used directly.

### The two spelling crossings

`Stacks.Chow.pullbackTensorObjIso` is Stacks 01CD, `Stacks.RingedSpace.comparisonBifunctorIso`,
read at a morphism of schemes rather than of ringed spaces, and
`Stacks.Chow.tensorObjUnitIso` is `Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso` read at
`AlgebraicGeometry.Scheme.Modules.tensorObj`. Each is the ambient declaration with an ascribed
type, which is what crosses the definitional-but-not-reducible identification of the two
spellings; no new comparison morphism is constructed and nothing is rewritten across the
boundary.

### No `@[stacks 02SO]` here

The cap product this file is about is the one of
`StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule`, whose identification with the
first Chern class cap product of the source rests on Stacks 01X5 (2); see the module
documentation there. The present file adds no further gap: both results below are unconditional
statements about `Stacks.Chow.firstChernClassCapOfInvertible`.

## References

* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 02SL](https://stacks.math.columbia.edu/tag/02SL)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-! ### Nonvanishing under the stalk map of an isomorphism -/

/-- The stalk map of an isomorphism of modules is injective, so it does not kill a nonzero
element. -/
theorem stalkLinearMap_ne_zero {A B : X.Modules} (e : A ⟶ B) [IsIso e] {x : X}
    {m : A.presheaf.stalk x} (hm : m ≠ 0) :
    AlgebraicGeometry.stalkLinearMap A B e x m ≠ 0 := by
  intro h0
  refine hm ((AlgebraicGeometry.bijective_stalkLinearMap A B e x).injective ?_)
  rw [h0, map_zero]

variable [IsIntegral X] [IsLocallyNoetherian X]

/-! ### Stacks 02SL in the generic-stalk model -/

omit [IsLocallyNoetherian X] in
/-- **The coordinate of a product of meromorphic sections is the product of the coordinates.**
If `m` is a stalk basis of `A_x` with `s = a · m` generically and `n` is one of `B_x` with
`t = b · n`, then `m ⊗ n` is a stalk basis of `(A ⊗_{𝒪_X} B)_x` and `s ⊗ t = (a · b)(m ⊗ n)`
generically, because the product of stalk elements is bilinear and commutes with specialization
from the generic point. -/
theorem isCoordinateAt_tensorStalkTmul {A B : X.Modules} {x : X}
    {s : A.presheaf.stalk (genericPoint X)} {t : B.presheaf.stalk (genericPoint X)}
    {a b : X.functionField} (ha : IsCoordinateAt A x s a) (hb : IsCoordinateAt B x t b) :
    IsCoordinateAt (Scheme.Modules.tensorObj A B) x
      (AlgebraicGeometry.tensorStalkTmul A B (genericPoint X) s t) (a * b) := by
  obtain ⟨m, hm, hsa⟩ := ha
  obtain ⟨n, hn, htb⟩ := hb
  refine ⟨AlgebraicGeometry.tensorStalkTmul A B x m n,
    AlgebraicGeometry.isStalkBasis_tensorStalkTmul A B x hm hn, ?_⟩
  rw [hsa, htb, AlgebraicGeometry.tensorStalkTmul_smul_smul]
  exact congrArg (fun z ↦ (a * b) • z)
    (AlgebraicGeometry.tensorStalkTmul_stalkSpecializes A B
      ((genericPoint_spec X).specializes trivial) m n)

omit [IsLocallyNoetherian X] in
/-- A meromorphic section with a nonzero coordinate is nonzero: the generic value of a stalk
basis is a basis of the generic stalk over the function field. -/
theorem ne_zero_of_isCoordinateAt {A : X.Modules} {x : X} (hA : IsTrivializedNear A x)
    {s : A.presheaf.stalk (genericPoint X)} {a : X.functionField} (ha : IsCoordinateAt A x s a)
    (ha0 : a ≠ 0) : s ≠ 0 := by
  obtain ⟨m, hm, hsa⟩ := ha
  intro h0
  refine ha0 ((hm.toGenericStalk hA).injective ?_)
  show a • toGenericStalk A x m = (0 : X.functionField) • toGenericStalk A x m
  rw [zero_smul, ← hsa, h0]

omit [IsLocallyNoetherian X] in
/-- **Stacks 02SL: the product of two nonzero meromorphic sections is nonzero**, in the
generic-stalk model. -/
theorem tensorStalkTmul_ne_zero {A B : X.Modules} (hA : IsTrivializedNear A (genericPoint X))
    (hB : IsTrivializedNear B (genericPoint X))
    (hAB : IsTrivializedNear (Scheme.Modules.tensorObj A B) (genericPoint X))
    {s : A.presheaf.stalk (genericPoint X)} {t : B.presheaf.stalk (genericPoint X)}
    (hs : s ≠ 0) (ht : t ≠ 0) :
    AlgebraicGeometry.tensorStalkTmul A B (genericPoint X) s t ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_isCoordinateAt hA s
  obtain ⟨b, hb⟩ := exists_isCoordinateAt hB t
  exact ne_zero_of_isCoordinateAt hAB (isCoordinateAt_tensorStalkTmul ha hb)
    (mul_ne_zero (ha.ne_zero hs) (hb.ne_zero ht))

/-- **Stacks 02SL coefficientwise, in the generic-stalk model.** The order of vanishing along a
prime divisor `Z` of a product of nonzero meromorphic sections of `A` and `B` is the sum of the
two orders: the coordinate of the product at the generic point of `Z` is the product of the two
coordinates, and the order of vanishing of a product of nonzero rational functions is the sum of
the orders. -/
theorem orderOfVanishing_tensorStalkTmul {A B : X.Modules} {Z : PrimeDivisor X}
    (hA : IsTrivializedNear A Z.genericPoint) (hB : IsTrivializedNear B Z.genericPoint)
    (hAB : IsTrivializedNear (Scheme.Modules.tensorObj A B) Z.genericPoint)
    {s : A.presheaf.stalk (genericPoint X)} {t : B.presheaf.stalk (genericPoint X)}
    (hs : s ≠ 0) (ht : t ≠ 0) :
    orderOfVanishing (Scheme.Modules.tensorObj A B)
        (AlgebraicGeometry.tensorStalkTmul A B (genericPoint X) s t) Z =
      orderOfVanishing A s Z + orderOfVanishing B t Z := by
  obtain ⟨a, ha⟩ := exists_isCoordinateAt hA s
  obtain ⟨b, hb⟩ := exists_isCoordinateAt hB t
  rw [orderOfVanishing_eq hAB (isCoordinateAt_tensorStalkTmul ha hb),
    orderOfVanishing_eq hA ha, orderOfVanishing_eq hB hb,
    X.ord_mul (ha.ne_zero hs) (hb.ne_zero ht)]

end Stacks.Divisors

namespace Stacks.Chow

open Stacks.Divisors

/-! ### The two invertibility statements and the two spelling crossings -/

/-- **Stacks 01CT (1).** The tensor product of two invertible `𝒪_X`-modules is invertible. This
is `Stacks.SheafOfModules.isInvertible_tensorSheaf` read through the comparison of the two
spellings of invertibility.

`StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TensorSection` has the same statement as a
`local instance`, and `Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf` has it at the
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` spelling; neither is usable here, the
first because it is file-local and the second because instance search does not see through the
change of spelling. -/
instance isInvertible_tensorObj {X : Scheme.{u}} (L N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.Modules.tensorObj L N) := by
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  exact (Stacks.SheafOfModules.isInvertible_tensorSheaf X.sheaf.obj X.ringCatSheaf.property
    L N).toAlgebraicGeometry

/-- **Stacks 01CD** at a morphism of schemes: the pullback of a tensor product of modules is the
tensor product of the pullbacks. This is `Stacks.RingedSpace.comparisonBifunctorIso` at the
underlying morphism of ringed spaces, with its type ascribed in the spelling
`AlgebraicGeometry.Scheme.Modules.tensorObj` of chapter 42. -/
def pullbackTensorObjIso {X Y : Scheme.{u}} (f : X ⟶ Y) (L N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (Scheme.Modules.tensorObj L N) ≅
      Scheme.Modules.tensorObj ((Scheme.Modules.pullback f).obj L)
        ((Scheme.Modules.pullback f).obj N) :=
  (Stacks.RingedSpace.comparisonBifunctorIso f.toLRSHom.toShHom).app (L, N)

/-- The right unit constraint `L ⊗_{𝒪_X} 𝒪_X ≅ L`, in the spelling
`AlgebraicGeometry.Scheme.Modules.tensorObj`. -/
def tensorObjUnitIso (X : Scheme.{u}) (L : X.Modules) :
    Scheme.Modules.tensorObj L (SheafOfModules.unit X.ringCatSheaf) ≅ L :=
  Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso X.sheaf.obj X.ringCatSheaf.property L

/-! ### Proper pushforward is `ℤ`-linear -/

variable (C : ChowSituation.{u})

/-- The coefficient of the proper pushforward of an integer multiple of a cycle.

`Stacks.Chow.properPushforward_add` is the additive half of this in the library; the integral
multiple is not public there, only as a `private` lemma of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClasses.FlatPullbackInvertible`. -/
theorem properPushforward_zsmul_apply {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX)
    (k : ℤ) (n : ℤ) (c : CycleGroup C sX k) (y : Y) :
    (properPushforward C sX sY f hf k (n • c)).1 y =
      n * (properPushforward C sX sY f hf k c).1 y := by
  have h : properPushforward C sX sY f hf k (n • c) =
      n • properPushforward C sX sY f hf k c :=
    map_zsmul (properPushforwardHom C sX sY f hf k) n c
  rw [h]
  simp

/-! ### The cap product is additive in the component rule -/

variable {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)

/-- **The cap product is additive in the component rule.** The extension of the pointwise sum of
two component rules is the sum of the two extensions, already at the level of cycles. -/
theorem extendCycleGroup_firstChernCapRule_add
    (chern₁ chern₂ : FirstChernComponentCycleRule C p k) (α : CycleGroup C p (k + 1)) :
    (firstChernCapRule C p k
          (fun W hW hDim ↦ chern₁ W hW hDim + chern₂ W hW hDim)).extendCycleGroup α =
      (firstChernCapRule C p k chern₁).extendCycleGroup α +
        (firstChernCapRule C p k chern₂).extendCycleGroup α := by
  classical
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  have htot : ∀ W : X.IdealSheafData,
      (firstChernCapRule C p k
            (fun W hW hDim ↦ chern₁ W hW hDim + chern₂ W hW hDim)).totalize W y =
        (firstChernCapRule C p k chern₁).totalize W y +
          (firstChernCapRule C p k chern₂).totalize W y := by
    intro W
    by_cases h : IsIntegral W.subscheme ∧
        schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)
    · rw [IntegralComponentRule.totalize_eq _ W h.1 h.2,
        IntegralComponentRule.totalize_eq _ W h.1 h.2,
        IntegralComponentRule.totalize_eq _ W h.1 h.2]
      show (properPushforward C (W.subschemeι ≫ p) p W.subschemeι rfl k
          (chern₁ W h.1 h.2 + chern₂ W h.1 h.2)).1 y = _
      rw [properPushforward_add]
      rfl
    · rw [IntegralComponentRule.totalize, IntegralComponentRule.totalize,
        IntegralComponentRule.totalize, dite_eq_right h, dite_eq_right h, dite_eq_right h]
      simp
  have hfin : ∀ chern : FirstChernComponentCycleRule C p k,
      (Function.support fun z : X ↦ α.1 z *
        (firstChernCapRule C p k chern).toComponentRule.cycle z y).Finite :=
    fun chern ↦ (firstChernCapRule C p k chern).toComponentRule.finite_support_extendTerm
      α.1.locallyFiniteSupport y
  have hL : ((firstChernCapRule C p k
        (fun W hW hDim ↦ chern₁ W hW hDim + chern₂ W hW hDim)).extendCycleGroup α).1 y =
      ∑ᶠ z : X, α.1 z *
        ((firstChernCapRule C p k chern₁).toComponentRule.cycle z y +
          (firstChernCapRule C p k chern₂).toComponentRule.cycle z y) := by
    refine finsum_congr fun z ↦ ?_
    exact congrArg (fun w : ℤ ↦ α.1 z * w) (htot (integralComponentAt z))
  rw [hL]
  have hsplit : ∀ z : X, α.1 z *
      ((firstChernCapRule C p k chern₁).toComponentRule.cycle z y +
        (firstChernCapRule C p k chern₂).toComponentRule.cycle z y) =
      α.1 z * (firstChernCapRule C p k chern₁).toComponentRule.cycle z y +
        α.1 z * (firstChernCapRule C p k chern₂).toComponentRule.cycle z y :=
    fun z ↦ mul_add _ _ _
  rw [finsum_congr hsplit, finsum_add_distrib (hfin chern₁) (hfin chern₂)]
  rfl

/-! ### The component rule of an invertible module, read on any nonzero section -/

variable (L N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

/-- The restriction of an invertible module to a closed subscheme is trivialized near every
point: Stacks 0B8L followed by `Stacks.Divisors.isTrivializedNear_of_isInvertible`.

This is not `Stacks.Divisors.IsTrivializedNear.pullback`, which carries the trivialization of the
module at the image point as its hypothesis; the hypothesis here is invertibility of the module
on the ambient scheme, and the two are discharged by different results. -/
theorem isTrivializedNear_pullback (W : X.IdealSheafData) (x : W.subscheme) :
    IsTrivializedNear ((Scheme.Modules.pullback W.subschemeι).obj L) x :=
  have := isInvertible_presheaf_modulePullback L W.subschemeι
  isTrivializedNear_of_isInvertible _ x

/-- The component rule of an invertible module is, up to rational equivalence, the divisor cycle
of any nonzero meromorphic section of its restriction to `W`. -/
private theorem mk_firstChernComponentCycleRule_eq (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (W : X.IdealSheafData) (hW : IsIntegral W.subscheme) [IsLocallyNoetherian W.subscheme]
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    {s : ((Scheme.Modules.pullback W.subschemeι).obj M).presheaf.stalk
      (genericPoint W.subscheme)} (hs : s ≠ 0) :
    (QuotientAddGroup.mk (firstChernComponentCycleRule C p k M W hW hDim) :
        chowGroup C (W.subschemeι ≫ p) k) =
      QuotientAddGroup.mk
        (chernComponentCycle C (W.subschemeι ≫ p) hDim (isTrivializedNear_pullback M W) s) :=
  have := hW
  firstChernComponentClass_eq_mk_of_ne_zero C p k M W hDim hs

/-! ### Stacks 02SL for the component cycle -/

/-- **Stacks 02SL for the divisor cycle.** On an integral scheme of delta-dimension `k + 1` the
divisor cycle of the product of two nonzero meromorphic sections of `A` and `B` is the sum of
their divisor cycles. -/
theorem chernComponentCycle_tensorStalkTmul {Y : Scheme.{u}} (q : Y ⟶ C.S)
    [LocallyOfFiniteType q] [IsIntegral Y] [IsLocallyNoetherian Y]
    (hk : schemeDeltaDimension C q = ((k + 1 : ℤ) : EInt)) {A B : Y.Modules}
    (hA : ∀ x : Y, IsTrivializedNear A x) (hB : ∀ x : Y, IsTrivializedNear B x)
    (hAB : ∀ x : Y, IsTrivializedNear (Scheme.Modules.tensorObj A B) x)
    {s : A.presheaf.stalk (genericPoint Y)} {t : B.presheaf.stalk (genericPoint Y)}
    (hs : s ≠ 0) (ht : t ≠ 0) :
    chernComponentCycle C q hk hAB
          (AlgebraicGeometry.tensorStalkTmul A B (genericPoint Y) s t) =
      chernComponentCycle C q hk hA s + chernComponentCycle C q hk hB t := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  have hadd : ((chernComponentCycle C q hk hA s + chernComponentCycle C q hk hB t :
        CycleGroup C q k) : AlgebraicCycle Y ℤ) x =
      ((chernComponentCycle C q hk hA s : CycleGroup C q k) : AlgebraicCycle Y ℤ) x +
        ((chernComponentCycle C q hk hB t : CycleGroup C q k) : AlgebraicCycle Y ℤ) x := rfl
  rw [hadd]
  by_cases hx : ∃ Z : Divisors.PrimeDivisor Y, Z.genericPoint = x
  · obtain ⟨Z, rfl⟩ := hx
    rw [chernComponentCycle_genericPoint, chernComponentCycle_genericPoint,
      chernComponentCycle_genericPoint]
    exact orderOfVanishing_tensorStalkTmul (hA _) (hB _) (hAB _) hs ht
  · have hne : ∀ Z : Divisors.PrimeDivisor Y, Z.genericPoint ≠ x := fun Z hZ ↦ hx ⟨Z, hZ⟩
    rw [chernComponentCycle_eq_zero _ _ hk _ _ x hne,
      chernComponentCycle_eq_zero _ _ hk _ _ x hne,
      chernComponentCycle_eq_zero _ _ hk _ _ x hne, add_zero]

/-! ### The component rules of `L`, `N` and `L ⊗ N` -/

/-- **Stacks 02SP on an integral component.** On an integral closed subscheme `W ⊆ X` of
delta-dimension `k + 1` the component cycle of `L ⊗_{𝒪_X} N` is rationally equivalent to the sum
of the component cycles of `L` and of `N`.

Choose nonzero meromorphic sections `s` of `L|_W` and `t` of `N|_W`. Their product is a nonzero
meromorphic section of `L|_W ⊗ N|_W` with divisor the sum of the two divisors (Stacks 02SL), and
`(L ⊗ N)|_W ≅ L|_W ⊗ N|_W` (Stacks 01CD) carries it to a nonzero meromorphic section of
`(L ⊗ N)|_W` with the same divisor. Each of the three component rules is the class of the divisor
cycle of any nonzero section (Stacks 02SJ (2)). -/
theorem rationallyEquivalent_firstChernComponentCycleRule_tensorObj (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    RationallyEquivalent C (W.subschemeι ≫ p) k
      (firstChernComponentCycleRule C p k (Scheme.Modules.tensorObj L N) W hW hDim)
      (firstChernComponentCycleRule C p k L W hW hDim +
        firstChernComponentCycleRule C p k N W hW hDim) := by
  have := hW
  have hNoe : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ p)
  set A : W.subscheme.Modules := (Scheme.Modules.pullback W.subschemeι).obj L with hAdef
  set B : W.subscheme.Modules := (Scheme.Modules.pullback W.subschemeι).obj N with hBdef
  set P : W.subscheme.Modules :=
    (Scheme.Modules.pullback W.subschemeι).obj (Scheme.Modules.tensorObj L N) with hPdef
  have hA : ∀ x : W.subscheme, IsTrivializedNear A x := isTrivializedNear_pullback L W
  have hB : ∀ x : W.subscheme, IsTrivializedNear B x := isTrivializedNear_pullback N W
  have hP : ∀ x : W.subscheme, IsTrivializedNear P x :=
    isTrivializedNear_pullback (Scheme.Modules.tensorObj L N) W
  -- Stacks 01CD at the closed immersion of `W`
  set e : P ≅ Scheme.Modules.tensorObj A B := pullbackTensorObjIso W.subschemeι L N with hedef
  have hAB : ∀ x : W.subscheme, IsTrivializedNear (Scheme.Modules.tensorObj A B) x :=
    fun x ↦ IsTrivializedNear.mapStalkLinearMap P (Scheme.Modules.tensorObj A B) e.hom x (hP x)
  -- the chosen nonzero sections of `L|_W` and `N|_W`
  obtain ⟨s, hs⟩ := exists_ne_zero_genericStalk (hA (genericPoint W.subscheme))
  obtain ⟨t, ht⟩ := exists_ne_zero_genericStalk (hB (genericPoint W.subscheme))
  set v := AlgebraicGeometry.tensorStalkTmul A B (genericPoint W.subscheme) s t with hvdef
  have hv : v ≠ 0 :=
    tensorStalkTmul_ne_zero (hA (genericPoint W.subscheme)) (hB (genericPoint W.subscheme))
      (hAB (genericPoint W.subscheme)) hs ht
  set u := AlgebraicGeometry.stalkLinearMap (Scheme.Modules.tensorObj A B) P e.inv
    (genericPoint W.subscheme) v with hudef
  have hu : u ≠ 0 := stalkLinearMap_ne_zero e.inv hv
  -- the three component rules, read on `u`, `s` and `t`
  have hmkP := mk_firstChernComponentCycleRule_eq C p k (Scheme.Modules.tensorObj L N) W hW hDim hu
  have hmkL := mk_firstChernComponentCycleRule_eq C p k L W hW hDim hs
  have hmkN := mk_firstChernComponentCycleRule_eq C p k N W hW hDim ht
  -- the divisor identity
  have hcycle : chernComponentCycle C (W.subschemeι ≫ p) hDim hP u =
      chernComponentCycle C (W.subschemeι ≫ p) hDim hA s +
        chernComponentCycle C (W.subschemeι ≫ p) hDim hB t := by
    rw [hudef, chernComponentCycle_mapStalkLinearMap C (W.subschemeι ≫ p) hDim
      (Scheme.Modules.tensorObj A B) P e.inv hAB hP v]
    exact chernComponentCycle_tensorStalkTmul C k (W.subschemeι ≫ p) hDim hA hB hAB hs ht
  refine QuotientAddGroup.eq_iff_sub_mem.1 ?_
  rw [QuotientAddGroup.mk_add, hmkP, hmkL, hmkN, ← QuotientAddGroup.mk_add, hcycle]

/-- **Stacks 02SP on an integral component, for isomorphic modules.** Isomorphic invertible
modules have rationally equivalent component cycles on every integral closed subscheme. -/
theorem rationallyEquivalent_firstChernComponentCycleRule_of_iso (e : L ≅ N)
    (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    RationallyEquivalent C (W.subschemeι ≫ p) k
      (firstChernComponentCycleRule C p k L W hW hDim)
      (firstChernComponentCycleRule C p k N W hW hDim) := by
  have := hW
  have hNoe : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ p)
  set A : W.subscheme.Modules := (Scheme.Modules.pullback W.subschemeι).obj L with hAdef
  set B : W.subscheme.Modules := (Scheme.Modules.pullback W.subschemeι).obj N with hBdef
  have hA : ∀ x : W.subscheme, IsTrivializedNear A x := isTrivializedNear_pullback L W
  have hB : ∀ x : W.subscheme, IsTrivializedNear B x := isTrivializedNear_pullback N W
  set f : A ≅ B := (Scheme.Modules.pullback W.subschemeι).mapIso e with hfdef
  obtain ⟨s, hs⟩ := exists_ne_zero_genericStalk (hA (genericPoint W.subscheme))
  set u := AlgebraicGeometry.stalkLinearMap A B f.hom (genericPoint W.subscheme) s with hudef
  have hu : u ≠ 0 := stalkLinearMap_ne_zero f.hom hs
  have hmkL := mk_firstChernComponentCycleRule_eq C p k L W hW hDim hs
  have hmkN := mk_firstChernComponentCycleRule_eq C p k N W hW hDim hu
  refine QuotientAddGroup.eq_iff_sub_mem.1 ?_
  rw [hmkL, hmkN, hudef,
    chernComponentCycle_mapStalkLinearMap C (W.subschemeι ≫ p) hDim A B f.hom hA hB s]

/-! ### Stacks 02SP -/

/-- The cap product of an invertible module is the class of the coefficientwise extension of its
component rule. -/
theorem firstChernClassCapOfInvertible_eq_mk (α : CycleGroup C p (k + 1)) :
    firstChernClassCapOfInvertible C p k L α =
      QuotientAddGroup.mk
        ((firstChernCapRule C p k (firstChernComponentCycleRule C p k L)).extendCycleGroup α) :=
  rfl

/-- **The cap product depends only on the isomorphism class of the invertible module.** -/
theorem firstChernClassCapOfInvertible_congr (e : L ≅ N) (α : CycleGroup C p (k + 1)) :
    firstChernClassCapOfInvertible C p k L α = firstChernClassCapOfInvertible C p k N α :=
  firstChernClassCap_congr C p k _ _
    (rationallyEquivalent_firstChernComponentCycleRule_of_iso C p k L N e) α

/-- **Stacks 02SP.** Let `(S, δ)` be the base situation of chapter 42, let `X` be locally of
finite type over `S` and let `L`, `N` be invertible `𝒪_X`-modules. Then

  `c₁(L) ∩ α + c₁(N) ∩ α = c₁(L ⊗_{𝒪_X} N) ∩ α`

in `A_k(X)` for every `α ∈ Z_{k+1}(X)`. The companion assertion of the same tag,
`c₁(𝒪_X) ∩ α = 0`, is `Stacks.Chow.firstChernClassCapOfInvertible_unit`, deduced from this one
through `𝒪_X ⊗_{𝒪_X} 𝒪_X ≅ 𝒪_X`.

The cap product is the one of `StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule`; see
the module documentation for why no `@[stacks 02SO]` attribute accompanies it. -/
@[stacks 02SP "additivity in the invertible module"]
theorem firstChernClassCapOfInvertible_tensorObj (α : CycleGroup C p (k + 1)) :
    firstChernClassCapOfInvertible C p k L α + firstChernClassCapOfInvertible C p k N α =
      firstChernClassCapOfInvertible C p k (Scheme.Modules.tensorObj L N) α := by
  rw [firstChernClassCapOfInvertible_eq_mk, firstChernClassCapOfInvertible_eq_mk,
    firstChernClassCapOfInvertible_eq_mk, ← QuotientAddGroup.mk_add,
    ← extendCycleGroup_firstChernCapRule_add]
  exact (firstChernClassCap_congr C p k _ _
    (rationallyEquivalent_firstChernComponentCycleRule_tensorObj C p k L N) α).symm

/-- **Stacks 02SP.** `c₁(𝒪_X) ∩ α = 0` in `A_k(X)` for every `α ∈ Z_{k+1}(X)`.

Additivity applied to `L = N = 𝒪_X` together with `𝒪_X ⊗_{𝒪_X} 𝒪_X ≅ 𝒪_X` gives
`c₁(𝒪_X) ∩ α + c₁(𝒪_X) ∩ α = c₁(𝒪_X) ∩ α`.

The companion assertion of the same tag is
`Stacks.Chow.firstChernClassCapOfInvertible_tensorObj`. -/
@[stacks 02SP "vanishing on the structure sheaf"]
theorem firstChernClassCapOfInvertible_unit (α : CycleGroup C p (k + 1)) :
    firstChernClassCapOfInvertible C p k (SheafOfModules.unit X.ringCatSheaf) α = 0 := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.Modules.tensorObj (SheafOfModules.unit X.ringCatSheaf)
        (SheafOfModules.unit X.ringCatSheaf)) :=
    isInvertible_tensorObj _ _
  have hdouble := firstChernClassCapOfInvertible_tensorObj C p k
    (SheafOfModules.unit X.ringCatSheaf) (SheafOfModules.unit X.ringCatSheaf) α
  have hiso : firstChernClassCapOfInvertible C p k
        (Scheme.Modules.tensorObj (SheafOfModules.unit X.ringCatSheaf)
          (SheafOfModules.unit X.ringCatSheaf)) α =
      firstChernClassCapOfInvertible C p k (SheafOfModules.unit X.ringCatSheaf) α :=
    firstChernClassCapOfInvertible_congr C p k _ _
      (tensorObjUnitIso X (SheafOfModules.unit X.ringCatSheaf)) α
  have hsum : firstChernClassCapOfInvertible C p k (SheafOfModules.unit X.ringCatSheaf) α +
      firstChernClassCapOfInvertible C p k (SheafOfModules.unit X.ringCatSheaf) α =
      0 + firstChernClassCapOfInvertible C p k (SheafOfModules.unit X.ringCatSheaf) α := by
    rw [zero_add]
    exact hdouble.trans hiso
  exact add_right_cancel hsum

end Stacks.Chow

end
