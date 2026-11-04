module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.SectionGysinRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.PrincipalDivisorComponents
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.GysinRationalEquivalenceReduction
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.CanonicalSectionComponent
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ContainedComponentComparison
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinZeroSectionDischarge
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ZeroSchemeKeyFormula
import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackRationallyCompatible

/-!
# Discharging the single-component datum of Stacks 02TO

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `L` be an invertible `𝒪_X`-module and let `s ∈ Γ(X, L)` be a global
section with zero scheme `i : D = Z(s) ⟶ X`. The vanishing of Stacks 02TO reduces, by
`Stacks.Chow.gysinOfInvertibleFactorsThroughRationalEquivalence_of_components`, to one geometric
input: for every integral closed subscheme `V ⊆ X` of delta-dimension `k + 2` and every nonzero
rational function `f` on `V`, the Gysin cycle of the pushforward of `div_V(f)` is rationally
equivalent to zero on `D`, with witnesses over `V`. This file proves that input, so Stacks 02TO
and the descended map `i^* : A_{k+1}(X) ⟶ A_k(D)` hold with no hypothesis.

## The argument

Stacks 02TA, at the level of cycles and with its carrier retained
(`Stacks.Chow.isRationallyEquivalentToZeroWithin_gysinRule_extendCycleGroup_properPushforward`),
reduces the input to the case `X = V` integral, for the restricted pair `(L|_V, s|_V)` and the
principal divisor `div(f)` itself: a rational equivalence on `Z(s|_V)` is carried into `D` by the
morphism `Z(s|_V) ⟶ D` of Remark 0B6Y, and its witnesses lie over `V`.

On an integral `Y` of delta-dimension `k + 2` with an invertible `M` and `t ∈ Γ(Y, M)`, the case
`t = 0` is `Stacks.Chow.gysinRule_extendCycleGroup_eq_zero_of_section_eq_zero`, where
`Z(0) = Y`. For `t ≠ 0` the key formula Stacks 0AYC is applied on `Y` to the pair `(M, t)` and
`(𝒪_Y, f)`, in the situation of Stacks 0AYB produced by `Stacks.Chow.keyFormulaSituationOf` with
its generators replaced by `Stacks.Chow.withGysinGenerators`: the generator of `𝒪_Y` is the unit
section, so the divisors `div_{𝒪_Y|Z_i}(t_i|_{Z_i})` vanish
(`Stacks.Chow.restrictedWeilDivisorAt_germ_one`), and the generator of `M` at a member `Z_i` off
`Z(t)` is the germ of `t`, so the ratio `f_i` is `1` there and the tame symbols of those members
drop out of the formula. The key formula therefore exhibits

`∑_i ord_{Z_i}(f) · (Z_i → Y)_* div_{M|Z_i}(m_i|_{Z_i})`

as a locally finite sum of principal divisors on the members contained in `Z(t)`.

The Gysin cycle of `div(f)` on `Z(t)`, pushed forward to `Y`, differs from that cycle by the
locally finite sum of the component comparisons
`Stacks.Chow.isRationallyEquivalentToZeroWithin_properPushforward_gysinComponentCycle_sub`: on a
member inside `Z(t)` the Gysin rule takes the contained branch and the discrepancy is a rational
equivalence on `Z_i ⊆ Z(t)` (Stacks 02SJ (2)), while on a member not inside `Z(t)` both cycles
are the fundamental cycle of the intersection `Z_i ∩ Z(t)` and there is none. Every witness
therefore lies inside `Z(t)`, and
`Stacks.Chow.isRationallyEquivalentToZero_of_properPushforward_isRationallyEquivalentToZeroWithin`
descends the whole equivalence into `Z(t)`.

## Main definitions

* `Stacks.Chow.gysinGenerator` — the germ of `t` at `ξ` where that germ generates `M_ξ`, and an
  arbitrary generator elsewhere.
* `Stacks.Chow.withGysinGenerators` — the situation of Stacks 0AYB with those generators.
* `Stacks.Chow.gysinChowOfInvertible` — **Stacks 02TO**: the descended Gysin map
  `i^* : A_{k+1}(X) ⟶ A_k(D)`, with no hypothesis.

## Main results

* `Stacks.Chow.isStalkBasis_germ_of_notMem_support_zeroScheme` — a nonzero global section
  generates the stalk at every point off its zero scheme.
* `Stacks.Chow.weilDivisorAlgebraicCycle_restrictedWeilDivisorAt_germ_of_not_le` — on a component
  not inside `Z(t)` the divisor of the restricted section is the cycle of the intersection.
* `Stacks.Chow.isRationallyEquivalentToZeroWithin_properPushforward_gysinComponentCycle_sub` — the
  component comparison, read on the ambient scheme and witnessed inside `Z_ξ ∩ Z(t)`.
* `Stacks.Chow.isRationallyEquivalentToZero_gysinRule_extendCycleGroup_principalCycle` — the
  integral case: the Gysin cycle of a principal divisor is rationally equivalent to zero on the
  zero scheme.
* `Stacks.Chow.gysinOfInvertibleKillsPrincipalDivisorOnComponent` — **the single-component datum
  of Stacks 02TO, discharged.**
* `Stacks.Chow.gysinOfInvertibleFactorsThroughRationalEquivalence` — **Stacks 02TO**, the
  vanishing, with no hypothesis.

## References

* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02SK](https://stacks.math.columbia.edu/tag/02SK)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

attribute [local instance] isIntegral_integralComponentAt

/-! ### Two closure properties of rational equivalence within a carrier -/

/-- The difference of two cycles rationally equivalent to zero within a subset is rationally
equivalent to zero within it. -/
private theorem isRationallyEquivalentToZeroWithin_sub (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {α β : CycleGroup C p k} {T : Set X}
    (hα : IsRationallyEquivalentToZeroWithin C p k α T)
    (hβ : IsRationallyEquivalentToZeroWithin C p k β T) :
    IsRationallyEquivalentToZeroWithin C p k (α - β) T := by
  rw [sub_eq_add_neg]
  exact Stacks.Chow.isRationallyEquivalentToZeroWithin_add C p k hα
    (Stacks.Chow.isRationallyEquivalentToZeroWithin_neg C p k hβ)

/-! ### The cycle of the zero Weil divisor -/

/-- The cycle of the zero Weil divisor is the zero cycle. -/
private theorem weilDivisorAlgebraicCycle_zero {Z : Scheme.{u}} :
    weilDivisorAlgebraicCycle (0 : Stacks.Divisors.WeilDivisor Z) = 0 := by
  refine Function.locallyFinsuppWithin.ext fun z ↦ ?_
  simp [weilDivisorAlgebraicCycle_apply, weilDivisorCoeff]

/-! ### Containment in a closed subscheme of the component at a point -/

/-- **A closed subscheme contains the integral component at a point exactly when that point lies
in its support.** The integral component is the vanishing ideal of the closure of the point, so
this is the Galois connection between supports and vanishing ideals. -/
theorem le_integralComponentAt_iff_mem_support {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    I ≤ integralComponentAt x ↔ x ∈ (I.support : Set X) := by
  rw [integralComponentAt, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
    TopologicalSpace.Closeds.closure_le, Set.singleton_subset_iff]

/-- The support of the integral component at a point of the support of `I` lies in that of `I`. -/
private theorem coe_support_integralComponentAt_subset_support {X : Scheme.{u}}
    (I : X.IdealSheafData) {x : X} (hx : x ∈ (I.support : Set X)) :
    ((integralComponentAt x).support : Set X) ⊆ I.support := by
  rw [coe_support_integralComponentAt]
  exact (I.support.isClosed.closure_subset_iff).mpr (Set.singleton_subset_iff.mpr hx)

/-! ### A global section generates where its zero scheme does not meet -/

/-- **A nonzero global section of an invertible module generates the stalk at every point off its
zero scheme.** On an integral scheme the zero scheme `Z(t)` is an effective Cartier divisor and
`AlgebraicGeometry.invertibleSheafIsoZeroScheme` identifies `(M, t)` with `(𝒪_Y(Z(t)), 1_{Z(t)})`;
the canonical section generates `𝒪_Y(Z(t))` exactly off `Z(t)`, by
`Stacks.Divisors.nonvanishingLocus_canonicalSections`, and a stalk basis is carried to a stalk
basis by the stalk map of an isomorphism. -/
theorem isStalkBasis_germ_of_notMem_support_zeroScheme {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (t : Γ(M, ⊤)) (ht : t ≠ 0) {ξ : Y}
    (hξ : ξ ∉ ((Stacks.Divisors.zeroScheme Y M t).support : Set Y)) :
    IsStalkBasis M ξ (M.presheaf.germ ⊤ ξ trivial t) := by
  have hst : (Stacks.Divisors.sectionsOfTop M t).eval (op ⊤) = t :=
    Stacks.Divisors.sectionsOfTop_eval_top M t
  have hne : (Stacks.Divisors.sectionsOfTop M t).eval (op ⊤) ≠ 0 := by rw [hst]; exact ht
  have hreg : ∀ U : Y.Opens, Function.Injective fun r : Γ(Y, U) =>
      r • M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t := by
    have h := injective_smul_res_of_isRegularSection M (Stacks.Divisors.sectionsOfTop M t)
      (isRegularSection_of_eval_top_ne_zero M (Stacks.Divisors.sectionsOfTop M t) hne)
    rwa [hst] at h
  have hE : IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme Y M t) := by
    have h := isEffectiveCartierDivisor_zeroScheme_of_eval_top_ne_zero Y M
      (Stacks.Divisors.sectionsOfTop M t) hne
    rwa [hst] at h
  obtain ⟨φ, hsec⟩ : ∃ φ : M ≅ divisorSheaf (Stacks.Divisors.zeroScheme Y M t),
      φ.hom.val.app (op ⊤) t =
        divisorSheafGlobalSection (Stacks.Divisors.zeroScheme Y M t) :=
    ⟨invertibleSheafIsoZeroScheme M t hreg, invertibleSheafIsoZeroScheme_section M t hreg⟩
  have happ : φ.inv.val.app (op ⊤)
      (divisorSheafGlobalSection (Stacks.Divisors.zeroScheme Y M t)) = t := by
    rw [← hsec]
    exact congrArg (fun ψ : M ⟶ M => Scheme.Modules.Hom.app ψ ⊤ t) φ.hom_inv_id
  have hmem : ξ ∈ Stacks.SheafOfModules.nonvanishingLocus (X := Y.toRingedSpace)
      (invertibleSheaf (Stacks.Divisors.zeroScheme Y M t))
      (canonicalSections (Stacks.Divisors.zeroScheme Y M t)) := by
    rw [nonvanishingLocus_canonicalSections (Stacks.Divisors.zeroScheme Y M t)]
    exact hξ
  have h1 : IsStalkBasis (divisorSheaf (Stacks.Divisors.zeroScheme Y M t)) ξ
      ((divisorSheaf (Stacks.Divisors.zeroScheme Y M t)).presheaf.germ ⊤ ξ trivial
        (divisorSheafGlobalSection (Stacks.Divisors.zeroScheme Y M t))) :=
    isStalkBasis_germ_top_of_mem_nonvanishingLocus
      (divisorSheaf (Stacks.Divisors.zeroScheme Y M t))
      (canonicalSections (Stacks.Divisors.zeroScheme Y M t)) hmem
  have hgerm : stalkLinearMap (divisorSheaf (Stacks.Divisors.zeroScheme Y M t)) M φ.inv ξ
        ((divisorSheaf (Stacks.Divisors.zeroScheme Y M t)).presheaf.germ ⊤ ξ trivial
          (divisorSheafGlobalSection (Stacks.Divisors.zeroScheme Y M t))) =
      M.presheaf.germ ⊤ ξ trivial t :=
    (stalkLinearMap_germ _ M φ.inv ⊤ ξ trivial _).trans
      (congrArg (fun z : Γ(M, ⊤) => M.presheaf.germ ⊤ ξ trivial z) happ)
  rw [← hgerm]
  exact h1.mapStalkLinearMap (divisorSheaf (Stacks.Divisors.zeroScheme Y M t)) M φ.inv ξ

/-! ### The divisor of a restricted global section on a component off the zero scheme -/

open Stacks.AlgebraicGeometry.SectionsBaseChange in
/-- **The restriction to `Z_ξ` of the germ of a global section is the germ of its pullback.** Both
sides are the image of `t` under the base-change map on stalks at the generic point of `Z_ξ`. -/
theorem restrictStalk_germ_top {Y : Scheme.{u}} (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (t : Γ(M, ⊤)) (ξ : Y) :
    restrictStalk (integralComponentAt ξ) M (genericPointOf_integralComponentAt ξ)
        (M.presheaf.germ ⊤ ξ trivial t) =
      (restrictModule (integralComponentAt ξ) M).presheaf.germ ⊤
        (genericPoint (integralComponentAt ξ).subscheme) trivial
        (AlgebraicGeometry.pullbackGlobalSections (integralComponentAt ξ).subschemeι M t) := by
  rw [show AlgebraicGeometry.pullbackGlobalSections (integralComponentAt ξ).subschemeι M t =
      pullbackUnitSections (integralComponentAt ξ).subschemeι M ⊤ t by
    rw [AlgebraicGeometry.pullbackGlobalSections_eq_unit]; rfl]
  exact pullbackStalkAt_germ (integralComponentAt ξ).subschemeι M
    (genericPoint (integralComponentAt ξ).subscheme) (genericPointOf_integralComponentAt ξ)
    ⊤ trivial t

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q]
  (M : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
  (t : Γ(M, ⊤))

include C q in
/-- **On a component not inside the zero scheme, the divisor of the restricted section is the
cycle of the intersection.** For a point `ξ` whose integral component `Z_ξ` of delta-dimension
`k + 1` is not contained in `Z(t)`, the restriction `t|_{Z_ξ}` is a nonzero meromorphic section of
`M|_{Z_ξ}`, and Stacks 02SK on `Z_ξ` identifies its divisor with the fundamental cycle of the
zero scheme `Z(t) ∩ Z_ξ` of that restriction.

This is the lemma
`Stacks.Chow.weilDivisorAlgebraicCycle_restrictedWeilDivisorAt_germ_divisorSheafGlobalSection`, for
an arbitrary pair `(M, t)` in place of the invertible sheaf of an effective Cartier divisor and its
canonical section; the hypothesis replacing `ξ ∉ E` is the one
`Stacks.Chow.pullbackGlobalSections_subschemeι_ne_zero` asks for. -/
theorem weilDivisorAlgebraicCycle_restrictedWeilDivisorAt_germ_of_not_le (ξ : Y)
    (hξ : ¬ Stacks.Divisors.zeroScheme Y M t ≤ integralComponentAt ξ) (k : ℤ)
    (hk : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ q) =
      ((k + 1 : ℤ) : EInt)) :
    weilDivisorAlgebraicCycle
        (restrictedWeilDivisorAt C q ξ (M.presheaf.germ ⊤ ξ trivial t)) =
      (cycleAssociatedToClosedSubscheme C ((integralComponentAt ξ).subschemeι ≫ q)
        ((Stacks.Divisors.zeroScheme Y M t).comap
          (integralComponentAt ξ).subschemeι).subschemeι k).1 := by
  have _ := isLocallyNoetherian_integralComponentAt C q ξ
  have _ := Stacks.ChernCap42.isInvertible_sheafObj_modulePullback M
    (integralComponentAt ξ).subschemeι
  have key := Stacks.ChernCap42.chernComponentCycle_coe_eq_cycleAssociatedToZeroScheme C k
    ((integralComponentAt ξ).subschemeι ≫ q) (restrictModule (integralComponentAt ξ) M) hk _
    (pullbackGlobalSections_subschemeι_ne_zero M t (integralComponentAt ξ)
      (isIntegral_integralComponentAt ξ) hξ)
    (isTrivializedNear_restrictModule (integralComponentAt ξ) M)
  rw [genericValue_meromorphicSectionOfSection,
    zeroScheme_pullback (integralComponentAt ξ).subschemeι M t] at key
  rw [← key]
  exact congrArg weilDivisorAlgebraicCycle
    (congrArg (weilDivisorOfMeromorphicSection
        (isTrivializedNear_restrictModule (integralComponentAt ξ) M))
      (restrictStalk_germ_top M t ξ))

/-! ### The Gysin component cycle, pushed forward to the ambient scheme -/

variable (k : ℤ)

include C q in
/-- **On a component inside the zero scheme the pushed-forward Gysin component cycle is the
pushforward of the chosen representative.** The Gysin rule takes the contained branch
`Stacks.Chow.gysinComponentCycle_of_le`, and the two pushforwards compose. -/
theorem properPushforward_gysinComponentCycle_eq_of_le (W : Y.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ q) = ((k + 1 : ℤ) : EInt))
    (h : Stacks.Divisors.zeroScheme Y M t ≤ W) :
    properPushforward C ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) q
        (Stacks.Divisors.zeroScheme Y M t).subschemeι rfl k
        (gysinComponentCycle C q k M t (firstChernComponentClass C q k M) W hW hDim) =
      properPushforward C (W.subschemeι ≫ q) q W.subschemeι rfl k
        (Quotient.out (firstChernComponentClass C q k M W hW hDim)) := by
  rw [gysinComponentCycle_of_le C q k M t (firstChernComponentClass C q k M) W hW hDim h,
    properPushforward_properPushforward C (W.subschemeι ≫ q)
      ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) q
      (Scheme.IdealSheafData.inclusion h) (Stacks.Divisors.zeroScheme Y M t).subschemeι
      (by simp) rfl k]
  exact congrFun (properPushforward_congr C (W.subschemeι ≫ q) q
    (Scheme.IdealSheafData.inclusion h ≫ (Stacks.Divisors.zeroScheme Y M t).subschemeι)
    W.subschemeι (Scheme.IdealSheafData.inclusion_subschemeι h) _ rfl k) _

include C q in
/-- **On a component not inside the zero scheme the pushed-forward Gysin component cycle is the
pushforward of the intersection cycle.** The Gysin rule takes the uncontained branch
`Stacks.Chow.gysinComponentCycle_of_not_le`, whose value is the fundamental cycle of the
scheme-theoretic intersection `W ∩ Z(t)` formed inside `Z(t)`; forming it inside `W` instead gives
the same closed subscheme of `Y`, by `Stacks.ChernCap42.exists_iso_comap_sup` twice and
`sup_comm`. -/
theorem properPushforward_gysinComponentCycle_eq_of_not_le (W : Y.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ q) = ((k + 1 : ℤ) : EInt))
    (h : ¬ Stacks.Divisors.zeroScheme Y M t ≤ W) :
    properPushforward C ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) q
        (Stacks.Divisors.zeroScheme Y M t).subschemeι rfl k
        (gysinComponentCycle C q k M t (firstChernComponentClass C q k M) W hW hDim) =
      properPushforward C (W.subschemeι ≫ q) q W.subschemeι rfl k
        (cycleAssociatedToClosedSubscheme C (W.subschemeι ≫ q)
          ((Stacks.Divisors.zeroScheme Y M t).comap W.subschemeι).subschemeι k) := by
  obtain ⟨e₁, he₁⟩ := Stacks.ChernCap42.exists_iso_comap_sup W
    (Stacks.Divisors.zeroScheme Y M t) W.subschemeι (Iso.refl _) (by simp)
  obtain ⟨e₂, he₂⟩ := Stacks.ChernCap42.exists_iso_comap_sup
    (Stacks.Divisors.zeroScheme Y M t) W
    (Stacks.Divisors.zeroScheme Y M t).subschemeι (Iso.refl _) (by simp)
  rw [gysinComponentCycle_of_not_le C q k M t (firstChernComponentClass C q k M) W hW hDim h,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) q
      (Stacks.Divisors.zeroScheme Y M t).subschemeι rfl
      (W.comap (Stacks.Divisors.zeroScheme Y M t).subschemeι).subschemeι k,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (W.subschemeι ≫ q) q W.subschemeι rfl
      ((Stacks.Divisors.zeroScheme Y M t).comap W.subschemeι).subschemeι k,
    cycleAssociatedToClosedSubscheme_eq_of_iso C q
      ((W.comap (Stacks.Divisors.zeroScheme Y M t).subschemeι).subschemeι ≫
        (Stacks.Divisors.zeroScheme Y M t).subschemeι)
      (Stacks.Divisors.zeroScheme Y M t ⊔ W).subschemeι e₂ he₂ k,
    cycleAssociatedToClosedSubscheme_eq_of_iso C q
      (((Stacks.Divisors.zeroScheme Y M t).comap W.subschemeι).subschemeι ≫ W.subschemeι)
      (W ⊔ Stacks.Divisors.zeroScheme Y M t).subschemeι e₁ he₁ k, sup_comm]

/-! ### The per-component comparison on the ambient scheme -/

include C q in
/-- **The component comparison the proof of Stacks 02TO needs, read on the ambient scheme.** For
a point `ξ` whose integral component `Z_ξ` has delta-dimension `k + 1` and a generator `m` of
`M_ξ` which is the germ of `t` whenever `Z_ξ` is not contained in `Z(t)`, the pushforward to `Y`
of the Gysin component cycle of `Z_ξ` differs from the pushforward of the divisor
`div_{M|Z_ξ}(m|_{Z_ξ})` by a cycle rationally equivalent to zero, witnessed inside
`Z_ξ ∩ Z(t)`.

In the contained case the Gysin component cycle is the pushforward of a representative of
`c₁(M|_{Z_ξ}) ∩ [Z_ξ]`, and the divisor is another representative of the same class
(Stacks 02SJ (2)), so the discrepancy is a rational equivalence on `Z_ξ`, which lies inside
`Z(t)`. In the uncontained case both cycles are the fundamental cycle of the intersection
`Z_ξ ∩ Z(t)` and there is no discrepancy at all; that is why the carrier stays inside `Z(t)`,
which is what the descent into `Z(t)` asks for. -/
theorem isRationallyEquivalentToZeroWithin_properPushforward_gysinComponentCycle_sub (ξ : Y)
    (hDim : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ q) =
      ((k + 1 : ℤ) : EInt)) {m : M.presheaf.stalk ξ} (hm : IsStalkBasis M ξ m)
    (hmt : ¬ Stacks.Divisors.zeroScheme Y M t ≤ integralComponentAt ξ →
      m = M.presheaf.germ ⊤ ξ trivial t) :
    IsRationallyEquivalentToZeroWithin C q k
      (properPushforward C ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) q
          (Stacks.Divisors.zeroScheme Y M t).subschemeι rfl k
          (gysinComponentCycle C q k M t (firstChernComponentClass C q k M)
            (integralComponentAt ξ) (isIntegral_integralComponentAt ξ) hDim) -
        properPushforward C ((integralComponentAt ξ).subschemeι ≫ q) q
          (integralComponentAt ξ).subschemeι rfl k
          (chernCycleOfRestrictedStalk C q k M (integralComponentAt ξ)
            (isIntegral_integralComponentAt ξ) hDim (genericPointOf_integralComponentAt ξ) m))
      (((integralComponentAt ξ).support : Set Y) ∩
        ((Stacks.Divisors.zeroScheme Y M t).support : Set Y)) := by
  have _ := isLocallyNoetherian_integralComponentAt C q ξ
  by_cases h : Stacks.Divisors.zeroScheme Y M t ≤ integralComponentAt ξ
  · have hc : firstChernComponentClass C q k M (integralComponentAt ξ)
          (isIntegral_integralComponentAt ξ) hDim =
        QuotientAddGroup.mk (chernCycleOfRestrictedStalk C q k M (integralComponentAt ξ)
          (isIntegral_integralComponentAt ξ) hDim (genericPointOf_integralComponentAt ξ) m) :=
      firstChernComponentClass_eq_mk_of_ne_zero C q k M (integralComponentAt ξ) hDim
        (restrictStalk_ne_zero M (integralComponentAt ξ)
          (genericPointOf_integralComponentAt ξ) hm)
    have hre : IsRationallyEquivalentToZero C ((integralComponentAt ξ).subschemeι ≫ q) k
        (Quotient.out (firstChernComponentClass C q k M (integralComponentAt ξ)
            (isIntegral_integralComponentAt ξ) hDim) -
          chernCycleOfRestrictedStalk C q k M (integralComponentAt ξ)
            (isIntegral_integralComponentAt ξ) hDim (genericPointOf_integralComponentAt ξ) m) :=
      QuotientAddGroup.eq_iff_sub_mem.mp ((Quotient.out_eq _).trans hc)
    have hpush := properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion C
      ((integralComponentAt ξ).subschemeι ≫ q) q (integralComponentAt ξ).subschemeι rfl k hre
    rw [properPushforward_sub,
      ← properPushforward_gysinComponentCycle_eq_of_le C q M t k (integralComponentAt ξ)
        (isIntegral_integralComponentAt ξ) hDim h] at hpush
    refine hpush.mono ?_
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Set.subset_inter subset_rfl (coe_support_integralComponentAt_subset_support _
      ((le_integralComponentAt_iff_mem_support _ ξ).1 h))
  · obtain rfl := hmt h
    have hcyc : chernCycleOfRestrictedStalk C q k M (integralComponentAt ξ)
          (isIntegral_integralComponentAt ξ) hDim (genericPointOf_integralComponentAt ξ)
          (M.presheaf.germ ⊤ ξ trivial t) =
        cycleAssociatedToClosedSubscheme C ((integralComponentAt ξ).subschemeι ≫ q)
          ((Stacks.Divisors.zeroScheme Y M t).comap
            (integralComponentAt ξ).subschemeι).subschemeι k :=
      Subtype.ext ((val_chernCycleOfRestrictedStalk C q k M ξ hDim _).trans
        (weilDivisorAlgebraicCycle_restrictedWeilDivisorAt_germ_of_not_le C q M t ξ h k hDim))
    rw [hcyc, properPushforward_gysinComponentCycle_eq_of_not_le C q M t k
      (integralComponentAt ξ) (isIntegral_integralComponentAt ξ) hDim h, sub_self]
    exact isRationallyEquivalentToZeroWithin_zero C q k _

/-! ### The situation of Stacks 0AYB adapted to the section and a rational function -/

section Situation

open Stacks.Ample (unitModule unitStalkEquiv)

variable [IsIntegral Y] [IsLocallyNoetherian Y]

omit [IsLocallyNoetherian Y] in
/-- **A nonzero global section of an invertible module on an integral scheme is a nonzero
meromorphic section.** A section one of whose germs vanishes is zero,
`Stacks.ChernCap42.eq_zero_of_germ_eq_zero`. -/
theorem germ_genericPoint_ne_zero_of_ne_zero (ht : t ≠ 0) :
    M.presheaf.germ ⊤ (genericPoint Y) trivial t ≠ 0 := by
  have _ := Stacks.ChernCap42.isInvertible_stacks_of_algebraicGeometry M
  exact fun h0 ↦ ht (Stacks.ChernCap42.eq_zero_of_germ_eq_zero M t h0)

/-- **The generator of `M_ξ` the Gysin comparison asks for**: the germ of `t` at `ξ` where that
germ generates the stalk — which is the case at every point off the zero scheme `Z(t)` — and an
arbitrary generator elsewhere. -/
def gysinGenerator (ξ : Y) : M.presheaf.stalk ξ :=
  open Classical in
  haveI := isInvertible_presheaf M
  if _ : IsStalkBasis M ξ (M.presheaf.germ ⊤ ξ trivial t) then M.presheaf.germ ⊤ ξ trivial t
  else (exists_isStalkBasis (isTrivializedNear_of_isInvertible M ξ)).choose

omit [IsIntegral Y] [IsLocallyNoetherian Y] in
/-- The prescribed generator generates. -/
theorem isStalkBasis_gysinGenerator (ξ : Y) : IsStalkBasis M ξ (gysinGenerator M t ξ) := by
  classical
  have _ := isInvertible_presheaf M
  rw [gysinGenerator]
  split
  · assumption
  · exact (exists_isStalkBasis (isTrivializedNear_of_isInvertible M ξ)).choose_spec

/-- **Off the zero scheme the prescribed generator is the germ of the section.** -/
theorem gysinGenerator_eq_germ (ht : t ≠ 0) {ξ : Y}
    (hξ : ¬ Stacks.Divisors.zeroScheme Y M t ≤ integralComponentAt ξ) :
    gysinGenerator M t ξ = M.presheaf.germ ⊤ ξ trivial t := by
  classical
  have hmem : ξ ∉ ((Stacks.Divisors.zeroScheme Y M t).support : Set Y) := fun hmem ↦
    hξ ((le_integralComponentAt_iff_mem_support _ ξ).2 hmem)
  have hb := isStalkBasis_germ_of_notMem_support_zeroScheme M t ht hmem
  rw [gysinGenerator]
  split
  · rfl
  · exact absurd hb ‹_›

/-- **The situation of Stacks 0AYB with the generators the Gysin comparison asks for**: the
generator of `M` at `ξ_i` is the germ of `t` wherever that generates, and the generator of the
structure sheaf is the unit section, so that the second restricted divisor vanishes. -/
def withGysinGenerators (ℱ : KeyFormulaSituation M (unitModule Y)) :
    KeyFormulaSituation M (unitModule Y) :=
  haveI := UnitModule.isInvertible (X := Y)
  { ℱ with
    localGeneratorL := fun i ↦ gysinGenerator M t (ℱ.componentPoint i)
    localGeneratorN := fun i ↦ (unitModule Y).presheaf.germ ⊤ (ℱ.componentPoint i) trivial
      (show Γ(unitModule Y, ⊤) from (1 : Γ(Y, ⊤)))
    isStalkBasis_localGeneratorL := fun i ↦ isStalkBasis_gysinGenerator M t (ℱ.componentPoint i)
    isStalkBasis_localGeneratorN := fun i ↦
      isStalkBasis_germ_one ⊤ (ℱ.componentPoint i) trivial }

variable (ℱ : KeyFormulaSituation M (unitModule Y))

omit [IsLocallyNoetherian Y] in
/-- `withGysinGenerators` has the same meromorphic section of `M` as `ℱ`. -/
@[simp]
theorem withGysinGenerators_sectionL : (withGysinGenerators M t ℱ).sectionL = ℱ.sectionL := rfl

omit [IsLocallyNoetherian Y] in
/-- `withGysinGenerators` has the same meromorphic section of the structure sheaf as `ℱ`. -/
@[simp]
theorem withGysinGenerators_sectionN : (withGysinGenerators M t ℱ).sectionN = ℱ.sectionN := rfl

omit [IsLocallyNoetherian Y] in
/-- `withGysinGenerators` has the same `i`-th component as `ℱ`. -/
@[simp]
theorem withGysinGenerators_component (i : ℱ.Index) :
    (withGysinGenerators M t ℱ).component i = ℱ.component i := rfl

omit [IsLocallyNoetherian Y] in
/-- The generator of `M` at the generic point of the `i`-th component of `withGysinGenerators`
is `gysinGenerator` there. -/
@[simp]
theorem withGysinGenerators_localGeneratorL (i : ℱ.Index) :
    (withGysinGenerators M t ℱ).localGeneratorL i = gysinGenerator M t (ℱ.componentPoint i) :=
  rfl

/-- **The prescribed situation has `f_i = 1` at every member off the zero scheme.** There the
chosen generator is the germ of `t`, whose generic value is the meromorphic section itself. -/
theorem withGysinGenerators_ratioL_eq_one (ht : t ≠ 0) (i : ℱ.Index)
    (hsection : ℱ.sectionL = M.presheaf.germ ⊤ (genericPoint Y) trivial t)
    (hξ : ¬ Stacks.Divisors.zeroScheme Y M t ≤ integralComponentAt (ℱ.componentPoint i)) :
    (withGysinGenerators M t ℱ).ratioL i = 1 := by
  refine ((withGysinGenerators M t ℱ).ratioL_eq_one_iff i).mpr ?_
  change toGenericStalk M (ℱ.componentPoint i) (gysinGenerator M t (ℱ.componentPoint i)) =
    ℱ.sectionL
  rw [gysinGenerator_eq_germ M t ht hξ,
    toGenericStalk_germ (Opens.mem_top (ℱ.componentPoint i)) (Opens.mem_top (genericPoint Y))]
  exact hsection.symm

/-! ### The integral case of the single-component datum -/

include C q in
/-- **The single-component input to Stacks 02TO on an integral scheme, for a situation of
Stacks 0AYB with adapted generators.** On an integral, locally Noetherian `Y` of delta-dimension
`k + 2` locally of finite type over the base, let `M` be an invertible module with a global
section `t`, and let `ℱ` be a situation of Stacks 0AYB for `M` and `𝒪_Y` whose generator of
`𝒪_Y` is the unit section, whose generator of `M` is the germ of `t` at every member off `Z(t)`
— so that `f_i = 1` there — and whose second divisor cycle `div_{𝒪_Y}(h)` is presented by the
family. Then the Gysin cycle of that divisor is rationally equivalent to zero on `Z(t)`.

This is the heart of the proof of Stacks 02TO. The key formula Stacks 0AYC exhibits

`∑_i ord_{Z_i}(h) · (Z_i → Y)_* div_{M|Z_i}(m_i|_{Z_i})`

as a locally finite sum of principal divisors on the members `Z_i` lying in `Z(t)`, the
`f_i = 1` members dropping out and the divisors of the unit section vanishing
(`Stacks.Chow.restrictedWeilDivisorAt_germ_one`). The Gysin cycle of `div(h)` pushed forward to
`Y` differs from it by the locally finite sum of the component comparisons
`Stacks.Chow.isRationallyEquivalentToZeroWithin_properPushforward_gysinComponentCycle_sub`, each
witnessed inside `Z_i ∩ Z(t)`. So the whole discrepancy is witnessed inside `Z(t)`, and descends
into `Z(t)` by
`Stacks.Chow.isRationallyEquivalentToZero_of_properPushforward_isRationallyEquivalentToZeroWithin`.
-/
theorem isRationallyEquivalentToZero_gysinRule_extendCycleGroup_of_keyFormulaSituation
    (hn : schemeDeltaDimension C q = ((k + 1 + 1 : ℤ) : EInt))
    (ℱ : KeyFormulaSituation M (unitModule Y))
    (hgenN : ∀ i, ℱ.localGeneratorN i = (unitModule Y).presheaf.germ ⊤ (ℱ.componentPoint i)
      trivial (show Γ(unitModule Y, ⊤) from (1 : Γ(Y, ⊤))))
    (hratio : ∀ i, ¬ Stacks.Divisors.zeroScheme Y M t ≤
      integralComponentAt (ℱ.componentPoint i) → ℱ.ratioL i = 1)
    (hgenL : ∀ i, ¬ Stacks.Divisors.zeroScheme Y M t ≤
        integralComponentAt (ℱ.componentPoint i) →
      ℱ.localGeneratorL i = M.presheaf.germ ⊤ (ℱ.componentPoint i) trivial t)
    (β : CycleGroup C q (k + 1))
    (hβ : ∀ x : Y, β.1 x = ∑ᶠ i, ℱ.orderN i *
      (cycleAssociatedToClosedSubscheme C q
        (integralComponentAt (ℱ.componentPoint i)).subschemeι (k + 1)).1 x) :
    IsRationallyEquivalentToZero C ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) k
      ((gysinRule C q k M t (firstChernComponentClass C q k M)).extendCycleGroup β) := by
  classical
  have hn2 : schemeDeltaDimension C q = ((k + 2 : ℤ) : EInt) := by
    rw [hn, show (k + 1 + 1 : ℤ) = k + 2 from by ring]
  have hdim : ∀ i : ℱ.Index,
      schemeDeltaDimension C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ q) =
        ((k + 1 : ℤ) : EInt) :=
    ℱ.schemeDeltaDimension_integralComponentAt_componentPoint C q k hn2
  have hlocal : LocallyFinite fun i : ℱ.Index ↦
      ((integralComponentAt (ℱ.componentPoint i)).support : Set Y) :=
    ℱ.locallyFinite_support_integralComponentAt
  -- the two families of `k`-cycles on `Y`: the Gysin component cycles and the restricted divisors
  set gc : ℱ.Index → CycleGroup C q k := fun i ↦
    properPushforward C ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) q
      (Stacks.Divisors.zeroScheme Y M t).subschemeι rfl k
      (gysinComponentCycle C q k M t (firstChernComponentClass C q k M)
        (integralComponentAt (ℱ.componentPoint i)) (isIntegral_integralComponentAt _) (hdim i))
    with hgc
  set dv : ℱ.Index → CycleGroup C q k := fun i ↦
    properPushforward C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ q) q
      (integralComponentAt (ℱ.componentPoint i)).subschemeι rfl k
      (chernCycleOfRestrictedStalk C q k M (integralComponentAt (ℱ.componentPoint i))
        (isIntegral_integralComponentAt _) (hdim i) (genericPointOf_integralComponentAt _)
        (ℱ.localGeneratorL i))
    with hdv
  -- both families are supported on their own member
  have hsuppgc : ∀ i : ℱ.Index, Function.support (gc i).1 ⊆
      ((integralComponentAt (ℱ.componentPoint i)).support : Set Y) := by
    intro i y hy
    simp only [hgc] at hy
    by_cases hr : y ∈ Set.range (Stacks.Divisors.zeroScheme Y M t).subschemeι.base
    · obtain ⟨z, rfl⟩ := hr
      rw [Function.mem_support, properPushforward_apply_image_of_isClosedImmersion] at hy
      exact support_gysinComponentCycle_subset C q k M t (firstChernComponentClass C q k M)
        (integralComponentAt (ℱ.componentPoint i)) (isIntegral_integralComponentAt _) (hdim i) hy
    · exact absurd (properPushforward_apply_of_notMem_range C
        ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) q
        (Stacks.Divisors.zeroScheme Y M t).subschemeι rfl k _ hr) hy
  have hsuppdv : ∀ i : ℱ.Index, Function.support (dv i).1 ⊆
      ((integralComponentAt (ℱ.componentPoint i)).support : Set Y) := by
    intro i
    simp only [hdv]
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact support_properPushforward_subset C
      ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ q) q
      (integralComponentAt (ℱ.componentPoint i)).subschemeι rfl k _
  have hfin : ∀ d : ℱ.Index → CycleGroup C q k, (∀ i, Function.support (d i).1 ⊆
      ((integralComponentAt (ℱ.componentPoint i)).support : Set Y)) → ∀ y : Y,
      (Function.support fun i : ℱ.Index ↦ ℱ.orderN i * (d i).1 y).Finite :=
    fun d hd y ↦ finite_support_of_locallyFinite _ hlocal
      (fun i y ↦ ℱ.orderN i * (d i).1 y)
      (fun i y hy ↦ hd i (right_ne_zero_of_mul (by exact hy))) y
  have hfingc := hfin gc hsuppgc
  have hfindv : ∀ y : Y,
      (Function.support fun i : ℱ.Index ↦ -(ℱ.orderN i * (dv i).1 y)).Finite := fun y ↦
    (hfin dv hsuppdv y).subset fun i hi ↦ neg_ne_zero.1 hi
  -- the Gysin cycle of `β`, pushed forward to `Y`, is the weighted sum of the `gc i`
  have hpushβ : ∀ y : Y,
      (properPushforward C ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) q
          (Stacks.Divisors.zeroScheme Y M t).subschemeι rfl k
          ((gysinRule C q k M t (firstChernComponentClass C q k M)).extendCycleGroup β)).1 y =
        ∑ᶠ i : ℱ.Index, ℱ.orderN i * (gc i).1 y := by
    intro y
    by_cases hr : y ∈ Set.range (Stacks.Divisors.zeroScheme Y M t).subschemeι.base
    · obtain ⟨z, rfl⟩ := hr
      rw [properPushforward_apply_image_of_isClosedImmersion,
        (gysinRule C q k M t
            (firstChernComponentClass C q k M)).extendCycleGroup_apply_of_presentation
          (fun i ↦ integralComponentAt (ℱ.componentPoint i))
          (fun i ↦ isIntegral_integralComponentAt _) hdim hlocal ℱ.orderN β hβ z]
      refine finsum_congr fun i ↦ ?_
      simp only [hgc]
      rw [properPushforward_apply_image_of_isClosedImmersion]
      rfl
    · rw [properPushforward_apply_of_notMem_range C
        ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) q
        (Stacks.Divisors.zeroScheme Y M t).subschemeι rfl k _ hr]
      refine ((finsum_congr fun i ↦ ?_).trans finsum_zero).symm
      simp only [hgc]
      rw [properPushforward_apply_of_notMem_range C
        ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) q
        (Stacks.Divisors.zeroScheme Y M t).subschemeι rfl k _ hr, mul_zero]
  -- pushing forward an integer multiple
  have hzsmul : ∀ (i : ℱ.Index) (m : ℤ)
      (c : CycleGroup C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ q) k),
      properPushforward C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ q) q
          (integralComponentAt (ℱ.componentPoint i)).subschemeι rfl k (m • c) =
        m • properPushforward C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ q) q
          (integralComponentAt (ℱ.componentPoint i)).subschemeι rfl k c := fun i m c ↦
    map_zsmul (properPushforwardHom C
      ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ q) q
      (integralComponentAt (ℱ.componentPoint i)).subschemeι rfl k) m c
  -- the divisor of the generator of the structure sheaf vanishes
  have hNzero : ∀ i : ℱ.Index, (ℱ.toKeyFormulaData C q).restrictedDivisorN i = 0 := by
    intro i
    change weilDivisorAlgebraicCycle (restrictedWeilDivisorAt C q (ℱ.componentPoint i)
      (ℱ.localGeneratorN i)) = 0
    rw [hgenN i, restrictedWeilDivisorAt_germ_one]
    exact weilDivisorAlgebraicCycle_zero
  -- so the `i`-th summand of the left hand side is minus a multiple of the restricted divisor
  have hcd : ∀ i : ℱ.Index, (ℱ.toKeyFormulaData C q).componentDifference i =
      (-(ℱ.orderN i • chernCycleOfRestrictedStalk C q k M
        (integralComponentAt (ℱ.componentPoint i)) (isIntegral_integralComponentAt _)
        (hdim i) (genericPointOf_integralComponentAt _) (ℱ.localGeneratorL i))).1 := by
    intro i
    change (ℱ.toKeyFormulaData C q).orderL i • (ℱ.toKeyFormulaData C q).restrictedDivisorN i -
      (ℱ.toKeyFormulaData C q).orderN i • (ℱ.toKeyFormulaData C q).restrictedDivisorL i = _
    rw [hNzero i, smul_zero, zero_sub]
    rfl
  -- the left hand side of the key formula is minus the weighted sum of the `dv i`
  have hleft : ∀ y : Y, (ℱ.toKeyFormulaData C q).leftCoeff C q y =
      ∑ᶠ i : ℱ.Index, -(ℱ.orderN i * (dv i).1 y) := by
    intro y
    change ∑ᶠ i : ℱ.Index, closedSubschemeCyclePushforward C q
      (integralComponentAt (ℱ.componentPoint i))
      ((ℱ.toKeyFormulaData C q).componentDifference i) y = _
    refine finsum_congr fun i ↦ ?_
    rw [hcd i]
    change (properPushforward C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ q) q
      (integralComponentAt (ℱ.componentPoint i)).subschemeι rfl k
      (-(ℱ.orderN i • chernCycleOfRestrictedStalk C q k M
        (integralComponentAt (ℱ.componentPoint i)) (isIntegral_integralComponentAt _)
        (hdim i) (genericPointOf_integralComponentAt _) (ℱ.localGeneratorL i)))).1 y = _
    rw [properPushforward_neg, hzsmul i]
    simp only [hdv]
    rfl
  -- the left hand side of the key formula, as a `k`-cycle
  have hmemα : (ℱ.toKeyFormulaData C q).leftCycle C q ∈ cyclesOfDimension C q k := by
    have h := (ℱ.toKeyFormulaData C q).leftCycle_mem_cyclesOfDimension C q hn2
      (deltaDimensionFunction_apply C q)
    rwa [show (k + 2 - 2 : ℤ) = k from by ring] at h
  set α : CycleGroup C q k := ⟨(ℱ.toKeyFormulaData C q).leftCycle C q, hmemα⟩ with hα
  -- the key formula: `α` is rationally equivalent to zero inside `Z(t)`
  have hαzero : IsRationallyEquivalentToZeroWithin C q k α
      ((Stacks.Divisors.zeroScheme Y M t).support : Set Y) := by
    refine (ℱ.isRationallyEquivalentToZeroWithin_leftCoeff C q
      (fun i ↦ ℱ.componentPoint i ∈ ((Stacks.Divisors.zeroScheme Y M t).support : Set Y))
      (fun i hi ↦ hratio i fun hle ↦ hi ((le_integralComponentAt_iff_mem_support _ _).1 hle))
      hdim α fun x ↦ rfl).mono ?_
    exact Set.iUnion_subset fun j ↦ coe_support_integralComponentAt_subset_support _ j.2
  -- the component comparisons, summed over the locally finite family
  have hsum : IsRationallyEquivalentToZeroWithin C q k
      (properPushforward C ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) q
        (Stacks.Divisors.zeroScheme Y M t).subschemeι rfl k
        ((gysinRule C q k M t (firstChernComponentClass C q k M)).extendCycleGroup β) + α)
      (⋃ i : ℱ.Index, ((integralComponentAt (ℱ.componentPoint i)).support : Set Y) ∩
        ((Stacks.Divisors.zeroScheme Y M t).support : Set Y)) := by
    refine rationallyEquivalentToZeroWithin_finsum C q k
      (fun i ↦ ℱ.orderN i • (gc i - dv i))
      (fun i ↦ ((integralComponentAt (ℱ.componentPoint i)).support : Set Y) ∩
        ((Stacks.Divisors.zeroScheme Y M t).support : Set Y))
      (hlocal.subset fun i ↦ Set.inter_subset_left) (fun i ↦ ?_) fun y ↦ ?_
    · refine isRationallyEquivalentToZeroWithin_zsmul C q k
        (isRationallyEquivalentToZeroWithin_properPushforward_gysinComponentCycle_sub C q M t k
          (ℱ.componentPoint i) (hdim i) (ℱ.isStalkBasis_localGeneratorL i) (hgenL i))
        (ℱ.orderN i) fun x ↦ ?_
      rfl
    · rw [cycleGroup_add_apply, hpushβ y, hα]
      change _ + (ℱ.toKeyFormulaData C q).leftCoeff C q y = _
      rw [hleft y, ← finsum_add_distrib (hfingc y) (hfindv y)]
      refine finsum_congr fun i ↦ ?_
      have hzs : ((ℱ.orderN i • (gc i - dv i) : CycleGroup C q k)).1 y =
        ℱ.orderN i * ((gc i).1 y - (dv i).1 y) := rfl
      rw [hzs]
      ring
  -- subtracting the key formula leaves the Gysin cycle, witnessed inside `Z(t)`
  have hpush : IsRationallyEquivalentToZeroWithin C q k
      (properPushforward C ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) q
        (Stacks.Divisors.zeroScheme Y M t).subschemeι rfl k
        ((gysinRule C q k M t (firstChernComponentClass C q k M)).extendCycleGroup β))
      ((Stacks.Divisors.zeroScheme Y M t).support : Set Y) := by
    have h := isRationallyEquivalentToZeroWithin_sub C q k
      (hsum.mono (Set.iUnion_subset fun _ ↦ Set.inter_subset_right)) hαzero
    rwa [add_sub_cancel_right] at h
  refine isRationallyEquivalentToZero_of_properPushforward_isRationallyEquivalentToZeroWithin C
    ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) q
    (Stacks.Divisors.zeroScheme Y M t).subschemeι rfl k _ ?_
  rwa [Scheme.IdealSheafData.range_subschemeι]

include C q in
/-- **The single-component input to Stacks 02TO on an integral scheme, with no hypothesis.** On an
integral, locally Noetherian scheme `Y` of delta-dimension `k + 2` locally of finite type over the
base, the Gysin cycle of the principal divisor of a nonzero rational function, taken for any
global section `t` of an invertible module `M`, is rationally equivalent to zero on the zero
scheme `Z(t)`.

For `t = 0` this is `Stacks.Chow.gysinRule_extendCycleGroup_eq_zero_of_section_eq_zero`, where
`Z(0) = Y`. For `t ≠ 0` the section is a nonzero meromorphic section of `M`, the rational
function is a nonzero meromorphic section of `𝒪_Y`, and
`Stacks.Chow.keyFormulaSituationOf` produces a situation of Stacks 0AYB for the pair; replacing
its generators by `Stacks.Chow.withGysinGenerators` makes
`Stacks.Chow.isRationallyEquivalentToZero_gysinRule_extendCycleGroup_of_keyFormulaSituation`
apply, the divisor cycle of the rational function being presented by the family
(`Stacks.Chow.KeyFormulaSituation.weilDivisorAlgebraicCycle_weilDivisorN_apply`). -/
theorem isRationallyEquivalentToZero_gysinRule_extendCycleGroup_principalCycle
    (hn : schemeDeltaDimension C q = ((k + 1 + 1 : ℤ) : EInt)) (f : Y.functionField)
    (hf : f ≠ 0) (β : CycleGroup C q (k + 1))
    (hβ : (β : AlgebraicCycle Y ℤ) = principalCycle Y f) :
    IsRationallyEquivalentToZero C ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) k
      ((gysinRule C q k M t (firstChernComponentClass C q k M)).extendCycleGroup β) := by
  by_cases ht : t = 0
  · subst ht
    exact gysinRule_extendCycleGroup_eq_zero_of_section_eq_zero C q hn M f hf β hβ
  · have hn2 : schemeDeltaDimension C q = ((k + 2 : ℤ) : EInt) := by
      rw [hn, show (k + 1 + 1 : ℤ) = k + 2 from by ring]
    have htη := germ_genericPoint_ne_zero_of_ne_zero M t ht
    have hf' : (unitStalkEquiv Y (genericPoint Y)).symm f ≠ 0 := fun h0 ↦ hf (by
      have h1 := congrArg (unitStalkEquiv Y (genericPoint Y)) h0
      rwa [LinearEquiv.apply_symm_apply, map_zero] at h1)
    set ℱ₀ := keyFormulaSituationOf M (unitModule Y)
      (M.presheaf.germ ⊤ (genericPoint Y) trivial t)
      ((unitStalkEquiv Y (genericPoint Y)).symm f) htη hf'
    refine isRationallyEquivalentToZero_gysinRule_extendCycleGroup_of_keyFormulaSituation C q M t k
      hn (withGysinGenerators M t ℱ₀) (fun i ↦ rfl)
      (fun i hi ↦ withGysinGenerators_ratioL_eq_one M t ℱ₀ ht i rfl hi)
      (fun i hi ↦ gysinGenerator_eq_germ M t ht hi) β fun x ↦ ?_
    have hprin := KeyFormulaSituation.weilDivisorAlgebraicCycle_weilDivisorN_eq_principalCycle
      (withGysinGenerators M t ℱ₀) f rfl
    rw [show β.1 x = principalCycle Y f x from by rw [hβ], ← hprin]
    exact (withGysinGenerators M t ℱ₀).weilDivisorAlgebraicCycle_weilDivisorN_apply C q k hn2 x

end Situation

/-! ### The single-component datum, and Stacks 02TO -/

section Datum

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- **The single-component input to Stacks 02TO, with no hypothesis.** For every integral closed
subscheme `V ⊆ X` of delta-dimension `k + 2` and every nonzero rational function `f` on `V`, the
Gysin cycle of the pushforward of `div_V(f)` is rationally equivalent to zero on the zero scheme
`Z(s)`, with witnesses over `V`.

Stacks 02TA, in the cycle-level form
`Stacks.Chow.isRationallyEquivalentToZeroWithin_gysinRule_extendCycleGroup_properPushforward`,
reduces the statement to the same one on `V` for the restricted pair `(L|_V, s|_V)`, where it is
`Stacks.Chow.isRationallyEquivalentToZero_gysinRule_extendCycleGroup_principalCycle`; the
morphism `Z(s|_V) ⟶ Z(s)` of Remark 0B6Y carries that rational equivalence into `Z(s)` with
witnesses over `V`, by Stacks 02S2 in the carrier-retaining form
`Stacks.Chow.properPushforward_isRationallyEquivalentToZeroWithin_of_killsPrincipalDivisor`. -/
theorem gysinOfInvertibleKillsPrincipalDivisorOnComponent :
    GysinOfInvertibleKillsPrincipalDivisorOnComponent C p k L s := by
  intro V hV hDim f
  have _ := hV
  have _ : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ p)
  have hfne := rationalFunctionsEquivFunctionField_ne_zero V.subscheme f
  have hmemγ : principalCycle V.subscheme
      ((rationalFunctionsEquivFunctionField V.subscheme).1 (f : rationalFunctions V.subscheme)) ∈
      cyclesOfDimension C (V.subschemeι ≫ p) (k + 1) := by
    have h := principalCycle_mem_cyclesOfDimension C (V.subschemeι ≫ p) hDim
      ((rationalFunctionsEquivFunctionField V.subscheme).1 (f : rationalFunctions V.subscheme))
    rwa [show (k + 1 + 1 - 1 : ℤ) = k + 1 from by ring] at h
  set γ : CycleGroup C (V.subschemeι ≫ p) (k + 1) := ⟨_, hmemγ⟩
  -- the cycle of the datum is the pushforward of the principal cycle on `V`
  rw [show (⟨principalDivisorPushforward C p V hV f,
        principalDivisorPushforward_mem_cyclesOfDimension C p (k + 1) V hV hDim f⟩ :
      CycleGroup C p (k + 1)) =
      properPushforward C (V.subschemeι ≫ p) p V.subschemeι rfl (k + 1) γ from
    Subtype.ext (principalDivisorPushforward_eq_properPushforward C p V hV (k + 1) f γ rfl)]
  -- Stacks 02TA for the closed immersion of `V`
  have h02TA := isRationallyEquivalentToZeroWithin_gysinRule_extendCycleGroup_properPushforward C p
    (V.subschemeι ≫ p) V.subschemeι rfl L s k γ
  rw [closure_range_subschemeι] at h02TA
  -- the integral case on `V`
  have hVcase := isRationallyEquivalentToZero_gysinRule_extendCycleGroup_principalCycle C
    (V.subschemeι ≫ p) ((Scheme.Modules.pullback V.subschemeι).obj L)
    (AlgebraicGeometry.pullbackGlobalSections V.subschemeι L s) k hDim
    ((rationalFunctionsEquivFunctionField V.subscheme).1 (f : rationalFunctions V.subscheme))
    hfne γ rfl
  -- carried into `Z(s)` along the morphism of Remark 0B6Y
  have hpush := properPushforward_isRationallyEquivalentToZeroWithin_of_killsPrincipalDivisor C
    ((pullbackZeroScheme V.subschemeι L s).subschemeι ≫ (V.subschemeι ≫ p))
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackMap V.subschemeι L s)
    (zeroSchemePullbackMap_comp_structureMorphism V.subschemeι L s p (V.subschemeι ≫ p) rfl) k
    (properPushforwardKillsPrincipalDivisor_of_isProper C
      ((pullbackZeroScheme V.subschemeι L s).subschemeι ≫ (V.subschemeι ≫ p))
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackMap V.subschemeι L s)
      (zeroSchemePullbackMap_comp_structureMorphism V.subschemeι L s p (V.subschemeι ≫ p) rfl) k)
    hVcase
  have hsub : closure (Set.range (zeroSchemePullbackMap V.subschemeι L s).base) ⊆
      (Stacks.Divisors.zeroScheme X L s).subschemeι.base ⁻¹' (V.support : Set X) :=
    closure_minimal (range_zeroSchemePullbackMap_subset_preimage_support L s V)
      (V.support.isClosed.preimage (Stacks.Divisors.zeroScheme X L s).subschemeι.continuous)
  have h := Stacks.Chow.isRationallyEquivalentToZeroWithin_add C
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k h02TA (hpush.mono hsub)
  rwa [sub_add_cancel] at h

/-- **Stacks 02TO, with no hypothesis.** The Gysin homomorphism of the zero scheme of a global
section of an invertible module kills every `(k+1)`-cycle rationally equivalent to zero.

The single-component case the source's proof reduces to is
`Stacks.Chow.gysinOfInvertibleKillsPrincipalDivisorOnComponent`, proved above, and the reduction
to it is `Stacks.Chow.gysinOfInvertibleFactorsThroughRationalEquivalence_of_components`. -/
@[stacks 02TO "the Gysin map factors through rational equivalence, with no hypothesis: the \
single-component case the source's proof reduces to is proved here, as \
`gysinOfInvertibleKillsPrincipalDivisorOnComponent`, from the key formula 0AYC"]
theorem gysinOfInvertibleFactorsThroughRationalEquivalence :
    GysinOfInvertibleFactorsThroughRationalEquivalence C p k L s :=
  gysinOfInvertibleFactorsThroughRationalEquivalence_of_components C p k L s
    (gysinOfInvertibleKillsPrincipalDivisorOnComponent C p k L s)

/-- **Stacks 02TO, with no hypothesis.** The Gysin homomorphism of the zero scheme `D = Z(s)` of a
global section of an invertible module, descended to Chow groups,

  `i^* : A_{k+1}(X) ⟶ A_k(D)`.

This is `Stacks.Chow.gysinHomomorphismOnChowOfInvertibleOfComponents` with its single-component
datum supplied, and `Stacks.Chow.eq_gysinHomomorphismOnChowOfInvertible` says it is the only
homomorphism of Chow groups agreeing with the Gysin map of Stacks 02T8 on cycle
representatives. -/
@[stacks 02TO "the descended map i^* : A_{k+1}(X) ⟶ A_k(D), with no hypothesis: the \
single-component datum is proved, in `gysinOfInvertibleKillsPrincipalDivisorOnComponent`"]
def gysinChowOfInvertible : chowGroup C p (k + 1) →+
    chowGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k :=
  gysinHomomorphismOnChowOfInvertibleOfComponents C p k L s
    (gysinOfInvertibleKillsPrincipalDivisorOnComponent C p k L s)

/-- The descended Gysin map agrees with the Gysin homomorphism of Stacks 02T8 on cycle
representatives, which is the formula that determines it. -/
@[simp]
theorem gysinChowOfInvertible_mk (α : CycleGroup C p (k + 1)) :
    gysinChowOfInvertible C p k L s (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1)) α) =
      gysinHomomorphismOfInvertible C p k L s α :=
  rfl

end Datum

end Stacks.Chow

end
