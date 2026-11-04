module

public import StacksFrontier.AlgebraicGeometry.Chow.Codimension.CohenMacaulayCase
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalCycle
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.SmoothIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.ChernCharacterVectorBundle
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeCurveDimension
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackShortExactLocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.RestrictOpen
public import StacksFrontier.RingTheory.Length.RingEquiv
public import StacksFrontier.Topology.Noetherian.LocallyConnected

/-!
# The Gysin map, the Chern character and `CH_*(X) ⊗ 𝐐`

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
local complete intersection morphism of schemes locally of finite type over `S` for which the
Gysin map `f^! ∈ A^*(X ⟶ Y)^∧` of Stacks 0FF3 exists. This file assembles the ingredients that
Stacks 0FF9 and Stacks 0FFA use about `f^!` and the intersection product `α · β = ch(α') ∩ β` of
Stacks Section 0FEX, at the level of the operators on `CH_*(-) ⊗ 𝐐 = ⨁_k CH_k(-) ⊗ 𝐐`.

* Pullback of vector bundles `f^* : K_0(Vect(Y)) ⟶ K_0(Vect(X))`, `[ℰ] ↦ [f^*ℰ]`, is additive
  because pullback keeps short exact sequences of finite locally free modules; and the Chern
  character commutes with restriction, `res_f ch_p(α) = ch_p(f^*α)`, because the power sums
  `P_p` do.
* The rational Gysin map `f^! : CH_*(Y) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐` is `β ↦ ∑_q f^!_q β`, the sum over the
  degrees of the parts `f^!_q ∈ A^q(X ⟶ Y)` of `f^!`; when `X` has finitely many connected
  components, for instance when `X` is quasi-compact, only finitely many of them are nonzero
  (Stacks 0FE0).
* Stacks 0FF6, that `f^!` commutes with every class `c ∈ A^p(Y)`, gives
  `f^!(ch(α) ∩ β) = ch(f^*α) ∩ f^!β`; and the proper-pushforward law of the class `ch_p(α)` gives
  the projection formula `f_*(ch(f^*α) ∩ γ) = ch(α) ∩ f_*γ` for `f` proper.
* Stacks 0FF7 at `Y' = Y` gives `f^![Y] = [X]` for `X`, `Y` Noetherian and Cohen–Macaulay, in
  particular regular.

## Main definitions

* `AlgebraicGeometry.VectorBundleKZero.pullback` — `f^* : K_0(Vect(Y)) ⟶ K_0(Vect(X))`.
* `Stacks.Chow.rationalChowMap` — the map of `CH_*(-) ⊗ 𝐐` induced degree by degree by maps of
  Chow groups.
* `Stacks.Chow.lciGysinRational` — the Gysin map `f^! : CH_*(Y) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`.
* `Stacks.Chow.rationalProperChowPushforward` — proper pushforward `CH_*(X) ⊗ 𝐐 ⟶ CH_*(Y) ⊗ 𝐐`.

## Main results

* `Stacks.Chow.rationalChowCohomologyRestriction_chernCharacterVectorBundle` —
  `res_f ch_p(α) = ch_p(f^*α)`.
* `Stacks.Chow.finite_lciGysinSupport` — the degree support of `f^!` is finite when `X` has
  finitely many connected components.
* `Stacks.Chow.lciGysinRational_chernCharacterCap` — `f^!(ch(α) ∩ β) = ch(f^*α) ∩ f^!β`.
* `Stacks.Chow.rationalProperChowPushforward_chernCharacterCap` — the projection formula
  `f_*(ch(f^*α) ∩ γ) = ch(α) ∩ f_*γ`.
* `Stacks.Chow.chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion` — `[X]_k|_U = [U]_k`
  for every open `U ⊆ X` and every `k`.
* `Stacks.Chow.lciGysinRational_rationalFundamentalClass` — `f^![Y] = [X]` in `CH_*(X) ⊗ 𝐐`.

## Implementation notes

The parts of `f^!` are read through the embedding `A^*(X ⟶ Y)^∧ ⟶ ∏_q A^q(X ⟶ Y)` of Stacks 0FE0
(`Stacks.Chow.lciGysinMapComponent`). The rational Gysin map is their sum `∑ᶠ q`, which needs no
choice of a finite set of degrees: it is the sum over any finite set containing the support
(`Stacks.Chow.lciGysinRational_eq_sum`). Without finiteness of the support the sum is a junk
value.

The operators `ch(α) ∩ -` on `CH_*(-) ⊗ 𝐐` are sums over the degrees `p` below a bound read off
`δ`; for the commutation with `f^!` and with `f_*` both `δ_{X/S}` and `δ_{Y/S}` are assumed
bounded below, which holds for Noetherian schemes of finite dimension
(`Stacks.Chow.exists_bounds_relativeDimension`).

For `f^![Y] = [X]` the source cites Stacks 0FF7 directly. That tag,
`Stacks.Chow.completedCapFundamentalClass_completedBivariantRestriction_lciGysinMap`, is stated
for the restrictions of `f^!` along test schemes `Y' ⟶ Y`, componentwise on the connected
components of `X' = X ×_Y Y'`. Here the computation is done on `X` itself, on each of
its finitely many connected components `X_a`: there `f^!` is concentrated in the degree
`n_b - n_a` and satisfies the cap formula on test schemes pure of a given `δ`-dimension (the
input of the proof of Stacks 0FF7), applied to the connected component `Y_b` of `Y` containing
the image of `X_a`, the fundamental class `[Y]_n` restricting to `[Y_b]_n`.

## References

* [Stacks Project, Tag 0FF9](https://stacks.math.columbia.edu/tag/0FF9)
* [Stacks Project, Tag 0FFA](https://stacks.math.columbia.edu/tag/0FFA)
* [Stacks Project, Tag 0FEX](https://stacks.math.columbia.edu/tag/0FEX)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FF6](https://stacks.math.columbia.edu/tag/0FF6)
* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0FE3](https://stacks.math.columbia.edu/tag/0FE3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

/-! ### Pullback on `K_0(Vect)` -/

namespace AlgebraicGeometry.VectorBundleKZero

variable {X Y : Scheme.{u}}

open Classical in
/-- **Pullback `f^* : K_0(Vect(Y)) ⟶ K_0(Vect(X))`** along a morphism of schemes `f : X ⟶ Y`: the
additive map sending the class of a finite locally free module `ℰ` to the class of `f^*ℰ`. It is
well defined because `f^*` keeps finite local freeness and short exact sequences of finite
locally free modules
(`AlgebraicGeometry.Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree`). -/
def pullback (f : X ⟶ Y) : VectorBundleKZero Y →+ VectorBundleKZero X :=
  liftAddHom
    (fun M => if Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) M
      then classOf X ((Scheme.Modules.pullback f).obj M) else 0)
    (fun M hM => ite_eq_right hM)
    (fun {E F G} a b w hE hF hG _ _ hex => by
      rw [ite_eq_left hE, ite_eq_left hF, ite_eq_left hG]
      have hS : (ShortComplex.mk a b w).ShortExact := { exact := hex }
      have hS' := Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree f _ hS
      have : Mono ((Scheme.Modules.pullback f).map a) := hS'.mono_f
      have : Epi ((Scheme.Modules.pullback f).map b) := hS'.epi_g
      exact classOf_shortExact _ _ _
        ⟨(Stacks.Chow.isFiniteLocallyFree_pullbackObj E f).exists_isFiniteLocallyFreeData⟩
        ⟨(Stacks.Chow.isFiniteLocallyFree_pullbackObj F f).exists_isFiniteLocallyFreeData⟩
        ⟨(Stacks.Chow.isFiniteLocallyFree_pullbackObj G f).exists_isFiniteLocallyFreeData⟩
        hS'.exact)

/-- `f^*[ℰ] = [f^*ℰ]` for a finite locally free module `ℰ`. -/
theorem pullback_classOf (f : X ⟶ Y) (M : Y.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    pullback f (classOf Y M) = classOf X ((Scheme.Modules.pullback f).obj M) := by
  rw [pullback, liftAddHom_classOf, ite_eq_left ⟨hM.exists_isFiniteLocallyFreeData⟩]

end AlgebraicGeometry.VectorBundleKZero

namespace Stacks.Chow

/-! ### Restriction of the Chern character -/

section Restriction

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX)

/-- The component of degree `p` of the restriction of a total class is the restriction of
Stacks 0B7F, `Stacks.Chow.chowCohomologyRestrictionOfEq`, of its component of degree `p`. -/
theorem TotalChowClass.res_apply_eq_chowCohomologyRestrictionOfEq (c : TotalChowClass C sY)
    (p : ℕ) :
    TotalChowClass.res f hf c p =
      chowCohomologyRestrictionOfEq C sX sY hf (gysinSystemOfInvertible C)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p (c p) := by
  subst hf
  rfl

/-- **Restriction of `P_p` on `K_0(Vect)`**: `res_f P_p(α) = P_p(f^*α)` for `α ∈ K_0(Vect(Y))`. -/
theorem TotalChowClass.res_powerSumKHom (p : ℕ) (a : VectorBundleKZero Y) :
    TotalChowClass.res f hf (powerSumKHom C sY p a) =
      powerSumKHom C sX p (VectorBundleKZero.pullback f a) := by
  refine DFunLike.congr_fun (VectorBundleKZero.addHom_ext
    (φ := (TotalChowClass.res f hf :
      TotalChowClass C sY →+* TotalChowClass C sX).toAddMonoidHom.comp (powerSumKHom C sY p))
    (ψ := (powerSumKHom C sX p).comp (VectorBundleKZero.pullback f)) fun M hM => ?_) a
  have := isFiniteLocallyFree_pullbackObj M f
  change TotalChowClass.res f hf (powerSumKHom C sY p (VectorBundleKZero.classOf Y M)) =
    powerSumKHom C sX p (VectorBundleKZero.pullback f (VectorBundleKZero.classOf Y M))
  rw [powerSumKHom_classOf, VectorBundleKZero.pullback_classOf, powerSumKHom_classOf]
  exact res_powerSumOfFiniteLocallyFree C sY M f hf p

/-- `ch_p(α) = P_p(α)/p!`. -/
theorem chernCharacterVectorBundle_apply (a : VectorBundleKZero X) (p : ℕ) :
    chernCharacterVectorBundle C sX a p =
      ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] powerSumKHom C sX p a p :=
  rfl

/-- **The Chern character commutes with restriction**: for `f : X ⟶ Y` and `α ∈ K_0(Vect(Y))`,
the restriction `A^p(Y) ⊗ 𝐐 ⟶ A^p(X) ⊗ 𝐐` of Stacks 0B7F carries `ch_p(α)` to `ch_p(f^*α)`. -/
theorem rationalChowCohomologyRestriction_chernCharacterVectorBundle
    (a : VectorBundleKZero Y) (p : ℕ) :
    ((chowCohomologyRestrictionOfEq C sX sY hf (gysinSystemOfInvertible C)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p).toIntLinearMap.baseChange
          ℚ) (chernCharacterVectorBundle C sY a p) =
      chernCharacterVectorBundle C sX (VectorBundleKZero.pullback f a) p := by
  rw [chernCharacterVectorBundle_apply, chernCharacterVectorBundle_apply,
    LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
    ← TotalChowClass.res_apply_eq_chowCohomologyRestrictionOfEq, TotalChowClass.res_powerSumKHom]

end Restriction

/-! ### Maps of `CH_*(-) ⊗ 𝐐` induced degree by degree -/

section RationalMap

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- The `𝐐`-linear map `CH_*(Y) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐` induced by additive maps
`φ_n : CH_n(Y) ⟶ CH_{d(n)}(X)`, one for each degree `n`. -/
def rationalChowMap (d : ℤ → ℤ) (φ : ∀ n : ℤ, chowGroup C sY n →+ chowGroup C sX (d n)) :
    (DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) →ₗ[ℚ]
      DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j :=
  DirectSum.toModule ℚ ℤ _ fun n =>
    DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) (d n) ∘ₗ
      (φ n).toIntLinearMap.baseChange ℚ

/-- The map induced by `φ` takes `CH_n(Y) ⊗ 𝐐` to `CH_{d(n)}(X) ⊗ 𝐐` by `φ_n ⊗ 𝐐`. -/
theorem rationalChowMap_lof (d : ℤ → ℤ) (φ : ∀ n : ℤ, chowGroup C sY n →+ chowGroup C sX (d n))
    (n : ℤ) (t : ℚ ⊗[ℤ] chowGroup C sY n) :
    rationalChowMap C sX sY d φ (DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) n t) =
      DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) (d n)
        ((φ n).toIntLinearMap.baseChange ℚ t) := by
  simp only [rationalChowMap, DirectSum.toModule_lof, LinearMap.comp_apply]

/-- The map induced by `φ` sends `r ⊗ α`, `α ∈ CH_n(Y)`, to `r ⊗ φ_n(α)`. -/
theorem rationalChowMap_of_tmul (d : ℤ → ℤ)
    (φ : ∀ n : ℤ, chowGroup C sY n →+ chowGroup C sX (d n)) (n : ℤ) (r : ℚ)
    (α : chowGroup C sY n) :
    rationalChowMap C sX sY d φ (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) n (r ⊗ₜ α)) =
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) (d n) (r ⊗ₜ φ n α) := by
  rw [← DirectSum.lof_eq_of ℚ, rationalChowMap_lof, LinearMap.baseChange_tmul,
    AddMonoidHom.coe_toIntLinearMap, DirectSum.lof_eq_of]

/-- The maps induced by `φ = 0` vanish. -/
theorem rationalChowMap_zero (d : ℤ → ℤ) :
    rationalChowMap C sX sY d (fun _ => 0) = 0 :=
  DirectSum.linearMap_ext ℚ fun n => LinearMap.ext fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul r α =>
      rw [LinearMap.comp_apply, rationalChowMap_lof, LinearMap.baseChange_tmul,
        AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.zero_apply, TensorProduct.tmul_zero,
        map_zero, LinearMap.comp_apply, LinearMap.zero_apply]
    | add t t' ht ht' => rw [map_add, map_add, ht, ht']

end RationalMap

/-! ### The rational Gysin map -/

section Gysin

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX) (hlci : IsLocalCompleteIntersectionMorphism f) (h : GysinMapExists f)

/-- The degrees `q` in which the Gysin map `f^! ∈ A^*(X ⟶ Y)^∧` of Stacks 0FF3 has a nonzero
part `f^! ∈ A^q(X ⟶ Y)`. -/
def lciGysinSupport : Set ℤ :=
  {q | lciGysinMapComponent C sX sY hf hlci h q ≠ 0}

/-- **The Gysin map has finite degree support when `X` has finitely many connected
components**: on each connected component its support is finite (Stacks 0FE0). -/
theorem finite_lciGysinSupport [Finite (_root_.ConnectedComponents X)] :
    (lciGysinSupport C sX sY hf hlci h).Finite := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  refine (Set.finite_iUnion fun i : _root_.ConnectedComponents X =>
    DFinsupp.finite_support (lciGysinMap C sX sY hf hlci h i)).subset fun q hq => ?_
  by_contra hn
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_not] at hn
  refine hq ?_
  change (bivariantConnectedComponentEquiv C _ sX sY f hf q _ _ _).symm
    (fun i => lciGysinMap C sX sY hf hlci h i q) = 0
  rw [show (fun i => lciGysinMap C sX sY hf hlci h i q) = 0 from funext hn, map_zero]

/-- The Gysin map `f^! : CH_*(Y) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐` in degree `q`, taking `CH_n(Y) ⊗ 𝐐` to
`CH_{n-q}(X) ⊗ 𝐐`. -/
def lciGysinRationalComponent (q : ℤ) :
    (DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) →ₗ[ℚ]
      DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j :=
  rationalChowMap C sX sY (· - q) (lciGysinChow C sX sY hf hlci h q)

/-- The Gysin map `CH_n(Y) ⟶ CH_{n-q}(X)` in a degree `q` outside its support vanishes. -/
theorem lciGysinChow_eq_zero {q : ℤ} (hq : q ∉ lciGysinSupport C sX sY hf hlci h) (n : ℤ) :
    lciGysinChow C sX sY hf hlci h q n = 0 := by
  have h0 : lciGysinMapComponent C sX sY hf hlci h q = 0 := not_not.1 hq
  refine AddMonoidHom.ext fun β => ?_
  simp only [lciGysinChow, BivariantClass.capTargetHom_apply, BivariantClass.capTarget, h0,
    BivariantClass.zero_cap, map_zero, AddMonoidHom.zero_apply]

/-- The Gysin map in a degree outside its support vanishes. -/
theorem lciGysinRationalComponent_eq_zero {q : ℤ} (hq : q ∉ lciGysinSupport C sX sY hf hlci h) :
    lciGysinRationalComponent C sX sY hf hlci h q = 0 := by
  rw [lciGysinRationalComponent, funext (lciGysinChow_eq_zero C sX sY hf hlci h hq),
    rationalChowMap_zero]

/-- **The Gysin map `f^! : CH_*(Y) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`** of a local complete intersection morphism
for which the Gysin map exists (Stacks 0FF3): `β ↦ ∑_q f^!_q β`, the sum over the degrees `q` of
the parts `f^!_q ∈ A^q(X ⟶ Y)` of `f^!`. When `X` has finitely many connected components, for
instance when `X` is quasi-compact, only finitely many are nonzero
(`Stacks.Chow.finite_lciGysinSupport`). -/
def lciGysinRational :
    (DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) →ₗ[ℚ]
      DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j :=
  ∑ᶠ q : ℤ, lciGysinRationalComponent C sX sY hf hlci h q

/-- The Gysin map is the sum of its parts over any finite set of degrees containing its
support. -/
theorem lciGysinRational_eq_sum (s : Finset ℤ)
    (hs : lciGysinSupport C sX sY hf hlci h ⊆ s) :
    lciGysinRational C sX sY hf hlci h = ∑ q ∈ s, lciGysinRationalComponent C sX sY hf hlci h q :=
  finsum_eq_sum_of_support_subset _ fun q hq => hs <| by
    by_contra h0
    exact hq (lciGysinRationalComponent_eq_zero C sX sY hf hlci h h0)

/-- The Gysin map is the sum of its parts over the finite degree support. -/
private theorem lciGysinRational_eq_sum_toFinset [Finite (_root_.ConnectedComponents X)] :
    lciGysinRational C sX sY hf hlci h =
      ∑ q ∈ (finite_lciGysinSupport C sX sY hf hlci h).toFinset,
        lciGysinRationalComponent C sX sY hf hlci h q :=
  lciGysinRational_eq_sum C sX sY hf hlci h _
    (Set.Finite.coe_toFinset (finite_lciGysinSupport C sX sY hf hlci h)).symm.subset

/-- **The value of the Gysin map on `r ⊗ β`**, `β ∈ CH_n(Y)`: `∑_q r ⊗ f^!_q β`, the term of
degree `q` lying in `CH_{n-q}(X) ⊗ 𝐐`, for `X` with finitely many connected components. -/
theorem lciGysinRational_of_tmul [Finite (_root_.ConnectedComponents X)] (n : ℤ) (r : ℚ)
    (β : chowGroup C sY n) :
    lciGysinRational C sX sY hf hlci h
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) n (r ⊗ₜ β)) =
      ∑ q ∈ (finite_lciGysinSupport C sX sY hf hlci h).toFinset,
        DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) (n - q)
          (r ⊗ₜ lciGysinChow C sX sY hf hlci h q n β) := by
  rw [lciGysinRational_eq_sum_toFinset, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun q _ => rationalChowMap_of_tmul C sX sY _ _ n r β

/-- The value of the Gysin map on `CH_n(Y) ⊗ 𝐐`, for `X` with finitely many connected
components. -/
theorem lciGysinRational_lof [Finite (_root_.ConnectedComponents X)] (n : ℤ)
    (t : ℚ ⊗[ℤ] chowGroup C sY n) :
    lciGysinRational C sX sY hf hlci h
        (DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) n t) =
      ∑ q ∈ (finite_lciGysinSupport C sX sY hf hlci h).toFinset,
        DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) (n - q)
          ((lciGysinChow C sX sY hf hlci h q n).toIntLinearMap.baseChange ℚ t) := by
  rw [lciGysinRational_eq_sum_toFinset, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun q _ => rationalChowMap_lof C sX sY _ _ n t

/-! ### The Gysin map commutes with Chern classes -/

/-- **Stacks 0FF6 on `CH_*(Y) ⊗ 𝐐`, in one degree**: the part `f^!_q` of the Gysin map commutes
with the cap product of `c ∈ A^p(Y) ⊗ 𝐐`, `f^!_q(c ∩ β) = res(c) ∩ f^!_q β`. -/
theorem lciGysinRationalComponent_comp_rationalChowCap (q p : ℤ)
    (y : rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sY p) :
    lciGysinRationalComponent C sX sY hf hlci h q ∘ₗ
        rationalChowCap C (gysinSystemOfInvertible C) sY p y =
      rationalChowCap C (gysinSystemOfInvertible C) sX p
          (((chowCohomologyRestrictionOfEq C sX sY hf (gysinSystemOfInvertible C)
              (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p).toIntLinearMap.baseChange
                ℚ) y) ∘ₗ
        lciGysinRationalComponent C sX sY hf hlci h q := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.comp_zero, LinearMap.zero_comp]
  | add y y' hy hy' =>
    rw [map_add, map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hy, hy']
  | tmul r c =>
    refine rationalChowHomology_linearMap_ext C sY fun k s β => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, rationalChowCap_of_tmul,
      lciGysinRationalComponent, rationalChowMap_of_tmul, rationalChowMap_of_tmul,
      LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap, rationalChowCap_of_tmul]
    refine of_tmul_eq_of_tmul_of_heq C sX (by ring) _ ?_
    rw [lciGysinChow, BivariantClass.capTargetHom_apply,
      BivariantClass.capTarget_chowCohomologyCap_of_bivariantCommute C
        (gysinSystemOfInvertible C) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) sX sY
        f hf p q (lciGysinMapComponent C sX sY hf hlci h q) c
        ((completedCommutesAfterBaseChange_lciGysinMap C sX sY hf hlci h
          q).commutesWithEveryClass (𝟙 Y) p _) k β]
    exact chowGroupDegreeEquiv_heq _ _ _ _

/-- **Stacks 0FF6 on `CH_*(Y) ⊗ 𝐐`**: the Gysin map commutes with the cap product of
`c ∈ A^p(Y) ⊗ 𝐐`, `f^!(c ∩ β) = res(c) ∩ f^!β`, for `X` with finitely many connected
components. -/
theorem lciGysinRational_comp_rationalChowCap [Finite (_root_.ConnectedComponents X)] (p : ℤ)
    (y : rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sY p) :
    lciGysinRational C sX sY hf hlci h ∘ₗ rationalChowCap C (gysinSystemOfInvertible C) sY p y =
      rationalChowCap C (gysinSystemOfInvertible C) sX p
          (((chowCohomologyRestrictionOfEq C sX sY hf (gysinSystemOfInvertible C)
              (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p).toIntLinearMap.baseChange
                ℚ) y) ∘ₗ
        lciGysinRational C sX sY hf hlci h := by
  rw [lciGysinRational_eq_sum_toFinset]
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.sum_apply,
    map_sum]
  exact Finset.sum_congr rfl fun q _ => LinearMap.congr_fun
    (lciGysinRationalComponent_comp_rationalChowCap C sX sY hf hlci h q p y) x

/-- A lower bound for the relative dimension function, as a bound at every point. -/
private theorem exists_le_relativeDimension {T : Scheme.{u}} (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT]
    (hT : BddBelow (Set.range (relativeDimension C.dimensionFunction sT))) :
    ∃ lo : ℤ, ∀ x : T, lo ≤ relativeDimension C.dimensionFunction sT x :=
  hT.imp fun _ h x => h ⟨x, rfl⟩

/-- **The Gysin map commutes with the Chern character** (Stacks 0FF6 for `c = ch(α)`): for
`α ∈ K_0(Vect(Y))` and `β ∈ CH_*(Y) ⊗ 𝐐`,

  `f^!(ch(α) ∩ β) = ch(f^*α) ∩ f^!β`,

for `X` with finitely many connected components and `δ_{X/S}`, `δ_{Y/S}` bounded below (so that
the operators `ch(-) ∩ -` are the sums over all degrees). -/
theorem lciGysinRational_chernCharacterCap [Finite (_root_.ConnectedComponents X)]
    (hX : BddBelow (Set.range (relativeDimension C.dimensionFunction sX)))
    (hY : BddBelow (Set.range (relativeDimension C.dimensionFunction sY)))
    (a : VectorBundleKZero Y) (β : DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) :
    lciGysinRational C sX sY hf hlci h (chernCharacterCap C sY a β) =
      chernCharacterCap C sX (VectorBundleKZero.pullback f a)
        (lciGysinRational C sX sY hf hlci h β) := by
  obtain ⟨loX, hX'⟩ := exists_le_relativeDimension C sX hX
  obtain ⟨loY, hY'⟩ := exists_le_relativeDimension C sY hY
  refine LinearMap.congr_fun (f := lciGysinRational C sX sY hf hlci h ∘ₗ chernCharacterCap C sY a)
    (g := chernCharacterCap C sX (VectorBundleKZero.pullback f a) ∘ₗ
      lciGysinRational C sX sY hf hlci h) (DirectSum.linearMap_ext ℚ fun k => ?_) β
  refine LinearMap.ext fun t => ?_
  set S := (finite_lciGysinSupport C sX sY hf hlci h).toFinset
  set N : ℕ := (k - loY).toNat + ∑ q ∈ S, (k - q - loX).toNat
  have hNY : ∀ p : ℕ, (p : ℤ) ≤ k - loY → p ∈ Finset.range (N + 1) := fun p hp => by
    rw [Finset.mem_range]
    have : 0 ≤ ∑ q ∈ S, (k - q - loX).toNat := Nat.zero_le _
    omega
  have hNX : ∀ q ∈ S, ∀ p : ℕ, (p : ℤ) ≤ k - q - loX → p ∈ Finset.range (N + 1) :=
    fun q hq p hp => by
      rw [Finset.mem_range]
      have := Finset.single_le_sum (f := fun q => (k - q - loX).toNat) (fun _ _ => Nat.zero_le _)
        hq
      omega
  simp only [LinearMap.comp_apply]
  rw [chernCharacterCap_lof_eq_sum C sY loY hY' a k t _ hNY, map_sum, lciGysinRational_lof,
    map_sum]
  have hstep : ∀ p : ℕ,
      lciGysinRational C sX sY hf hlci h
          (rationalChowCap C (gysinSystemOfInvertible C) sY p (chernCharacterVectorBundle C sY a p)
            (DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) k t)) =
        rationalChowCap C (gysinSystemOfInvertible C) sX p
          (chernCharacterVectorBundle C sX (VectorBundleKZero.pullback f a) p)
          (lciGysinRational C sX sY hf hlci h
            (DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) k t)) := fun p => by
    rw [← rationalChowCohomologyRestriction_chernCharacterVectorBundle C sX sY hf,
      ← LinearMap.comp_apply,
      lciGysinRational_comp_rationalChowCap, LinearMap.comp_apply]
  rw [Finset.sum_congr rfl fun p _ => hstep p, lciGysinRational_lof]
  simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [chernCharacterCap_lof_eq_sum C sX loX hX' _ (k - q) _ _ (hNX q hq)]

/-- **The Gysin map commutes with the Chern character on `K_0(Vect(Y)) ⊗ 𝐐`**: for
`x ∈ K_0(Vect(Y)) ⊗ 𝐐`, `f^!(ch(x) ∩ β) = ch(f^*x) ∩ f^!β`, under the hypotheses of
`Stacks.Chow.lciGysinRational_chernCharacterCap`. -/
theorem lciGysinRational_rationalChernCharacterCap [Finite (_root_.ConnectedComponents X)]
    (hX : BddBelow (Set.range (relativeDimension C.dimensionFunction sX)))
    (hY : BddBelow (Set.range (relativeDimension C.dimensionFunction sY)))
    (x : ℚ ⊗[ℤ] VectorBundleKZero Y) (β : DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) :
    lciGysinRational C sX sY hf hlci h (rationalChernCharacterCap C sY x β) =
      rationalChernCharacterCap C sX
        ((VectorBundleKZero.pullback f).toIntLinearMap.baseChange ℚ x)
        (lciGysinRational C sX sY hf hlci h β) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul r a =>
    rw [rationalChernCharacterCap_tmul, LinearMap.baseChange_tmul,
      AddMonoidHom.coe_toIntLinearMap, rationalChernCharacterCap_tmul, LinearMap.smul_apply,
      LinearMap.smul_apply, map_smul, lciGysinRational_chernCharacterCap C sX sY hf hlci h hX hY]
  | add x y hx hy =>
    rw [map_add, LinearMap.add_apply, map_add, hx, hy, map_add, map_add, LinearMap.add_apply]

end Gysin

/-! ### Proper pushforward on `CH_*(-) ⊗ 𝐐` and the projection formula -/

section Pushforward

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y} [IsProper f]
  (hf : f ≫ sY = sX)

/-- **Proper pushforward `f_* : CH_*(X) ⊗ 𝐐 ⟶ CH_*(Y) ⊗ 𝐐`** (Stacks 02R5, Stacks 02S2), degree by
degree. -/
def rationalProperChowPushforward :
    (DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) →ₗ[ℚ]
      DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j :=
  rationalChowMap C sY sX (fun k => k)
    fun k => properChowPushforward C sX sY f hf k (properPushforwardDescends C _ _ _ _ _)

/-- Proper pushforward on `CH_k(X) ⊗ 𝐐`. -/
theorem rationalProperChowPushforward_lof (k : ℤ) (t : ℚ ⊗[ℤ] chowGroup C sX k) :
    rationalProperChowPushforward C sX sY hf
        (DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) k t) =
      DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) k
        ((properChowPushforward C sX sY f hf k
          (properPushforwardDescends C _ _ _ _ _)).toIntLinearMap.baseChange ℚ t) :=
  rationalChowMap_lof C sY sX _ _ k t

/-- Proper pushforward of `r ⊗ α`, `α ∈ CH_k(X)`, is `r ⊗ f_*α`. -/
theorem rationalProperChowPushforward_of_tmul (k : ℤ) (r : ℚ) (α : chowGroup C sX k) :
    rationalProperChowPushforward C sX sY hf
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) k (r ⊗ₜ α)) =
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) k
        (r ⊗ₜ properChowPushforward C sX sY f hf k (properPushforwardDescends C _ _ _ _ _) α) :=
  rationalChowMap_of_tmul C sY sX _ _ k r α

/-- **The projection formula on `CH_*(-) ⊗ 𝐐`**: `f_*(res(c) ∩ α) = c ∩ f_*α` for a proper
`f : X ⟶ Y` and `c ∈ A^p(Y) ⊗ 𝐐`. -/
theorem rationalProperChowPushforward_comp_rationalChowCap (p : ℤ)
    (y : rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sY p) :
    rationalProperChowPushforward C sX sY hf ∘ₗ
        rationalChowCap C (gysinSystemOfInvertible C) sX p
          (((chowCohomologyRestrictionOfEq C sX sY hf (gysinSystemOfInvertible C)
              (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p).toIntLinearMap.baseChange
                ℚ) y) =
      rationalChowCap C (gysinSystemOfInvertible C) sY p y ∘ₗ
        rationalProperChowPushforward C sX sY hf := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.comp_zero, LinearMap.zero_comp]
  | add y y' hy hy' =>
    rw [map_add, map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hy, hy']
  | tmul r c =>
    refine rationalChowHomology_linearMap_ext C sX fun k s α => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul,
      AddMonoidHom.coe_toIntLinearMap, rationalChowCap_of_tmul,
      rationalProperChowPushforward_of_tmul, rationalProperChowPushforward_of_tmul,
      rationalChowCap_of_tmul, chowCohomologyCap_properChowPushforward_restriction]

/-- **The projection formula for the Chern character**: for a proper `f : X ⟶ Y`,
`α ∈ K_0(Vect(Y))` and `γ ∈ CH_*(X) ⊗ 𝐐`,

  `f_*(ch(f^*α) ∩ γ) = ch(α) ∩ f_*γ`,

for `δ_{X/S}` and `δ_{Y/S}` bounded below. -/
theorem rationalProperChowPushforward_chernCharacterCap
    (hX : BddBelow (Set.range (relativeDimension C.dimensionFunction sX)))
    (hY : BddBelow (Set.range (relativeDimension C.dimensionFunction sY)))
    (a : VectorBundleKZero Y) (γ : DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) :
    rationalProperChowPushforward C sX sY hf
        (chernCharacterCap C sX (VectorBundleKZero.pullback f a) γ) =
      chernCharacterCap C sY a (rationalProperChowPushforward C sX sY hf γ) := by
  obtain ⟨loX, hX'⟩ := exists_le_relativeDimension C sX hX
  obtain ⟨loY, hY'⟩ := exists_le_relativeDimension C sY hY
  refine LinearMap.congr_fun (f := rationalProperChowPushforward C sX sY hf ∘ₗ
      chernCharacterCap C sX (VectorBundleKZero.pullback f a))
    (g := chernCharacterCap C sY a ∘ₗ rationalProperChowPushforward C sX sY hf)
    (DirectSum.linearMap_ext ℚ fun k => LinearMap.ext fun t => ?_) γ
  simp only [LinearMap.comp_apply]
  rw [chernCharacterCap_lof_eq_sum C sX loX hX' _ k t (Finset.range ((k - loX).toNat +
      (k - loY).toNat + 1)) (fun p hp => by rw [Finset.mem_range]; omega), map_sum,
    rationalProperChowPushforward_lof, chernCharacterCap_lof_eq_sum C sY loY hY' a k _
      (Finset.range ((k - loX).toNat + (k - loY).toNat + 1))
      (fun p hp => by rw [Finset.mem_range]; omega)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← rationalChowCohomologyRestriction_chernCharacterVectorBundle C sX sY hf,
    ← LinearMap.comp_apply, rationalProperChowPushforward_comp_rationalChowCap,
    LinearMap.comp_apply, rationalProperChowPushforward_lof]

/-- **The projection formula for the Chern character on `K_0(Vect(Y)) ⊗ 𝐐`**: for
`x ∈ K_0(Vect(Y)) ⊗ 𝐐`, `f_*(ch(f^*x) ∩ γ) = ch(x) ∩ f_*γ`, under the hypotheses of
`Stacks.Chow.rationalProperChowPushforward_chernCharacterCap`. -/
theorem rationalProperChowPushforward_rationalChernCharacterCap
    (hX : BddBelow (Set.range (relativeDimension C.dimensionFunction sX)))
    (hY : BddBelow (Set.range (relativeDimension C.dimensionFunction sY)))
    (x : ℚ ⊗[ℤ] VectorBundleKZero Y) (γ : DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) :
    rationalProperChowPushforward C sX sY hf (rationalChernCharacterCap C sX
        ((VectorBundleKZero.pullback f).toIntLinearMap.baseChange ℚ x) γ) =
      rationalChernCharacterCap C sY x (rationalProperChowPushforward C sX sY hf γ) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul r a =>
    rw [LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
      rationalChernCharacterCap_tmul, rationalChernCharacterCap_tmul, LinearMap.smul_apply,
      LinearMap.smul_apply, map_smul,
      rationalProperChowPushforward_chernCharacterCap C sX sY hf hX hY]
  | add x y hx hy =>
    rw [map_add, map_add, LinearMap.add_apply, map_add, hx, hy, map_add, LinearMap.add_apply]

end Pushforward

/-! ### Fundamental classes and open subschemes -/

section Fundamental

variable (C : ChowSituation.{u}) {X U : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (v : U ⟶ X) [IsOpenImmersion v] (hv : v ≫ sX = sU)

include hv in
/-- **The fundamental cycle restricts to the fundamental cycle** along an open immersion
`v : U ⟶ X`, in every degree `k`: the generic points of `U` are the generic points of `X` lying
in `U`, with the same `δ` and isomorphic local rings. -/
theorem cycleGroupRestrict_fundamentalCycle (k : ℤ) :
    cycleGroupRestrict C sX sU v hv k (fundamentalCycle C sX k) = fundamentalCycle C sU k := by
  classical
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro z
  rw [cycleGroupRestrict_apply]
  have hδ : relativeDimension C.dimensionFunction sU z =
      relativeDimension C.dimensionFunction sX (v z) := by
    rw [← hv, relativeDimension_comp_isOpenImmersion]
  by_cases hz : z ∈ genericPoints U ∧ relativeDimension C.dimensionFunction sU z = k
  · have hvz : v z ∈ genericPoints X := v.isOpenEmbedding.mem_genericPoints_iff.2 hz.1
    have h1 := cycleAssociatedToClosedSubscheme_apply C sX (𝟙 X) k ⟨v z, hvz⟩
      (by change relativeDimension C.dimensionFunction sX (v z) = k; rw [← hδ]; exact hz.2)
    have h2 := cycleAssociatedToClosedSubscheme_apply C sU (𝟙 U) k ⟨z, hz.1⟩ hz.2
    change (cycleAssociatedToClosedSubscheme C sX (𝟙 X) k).1 (v z) =
      (cycleAssociatedToClosedSubscheme C sU (𝟙 U) k).1 z
    refine h1.trans (Eq.trans ?_ h2.symm)
    rw [componentMultiplicity_eq_length_stalk, componentMultiplicity_eq_length_stalk]
    exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) (Module.length_eq_of_ringEquiv
      (asIso (v.stalkMap z)).commRingCatIsoToRingEquiv)
  · change (cycleAssociatedToClosedSubscheme C sX (𝟙 X) k).1 (v z) =
      (cycleAssociatedToClosedSubscheme C sU (𝟙 U) k).1 z
    rw [cycleAssociatedToClosedSubscheme_apply_eq_zero C sX (𝟙 X) k (v z) ?_,
      cycleAssociatedToClosedSubscheme_apply_eq_zero C sU (𝟙 U) k z ?_]
    · rintro ⟨ξ, hξ, hd⟩
      exact hz ⟨hξ ▸ ξ.2, hd⟩
    · rintro ⟨ξ, hξ, hd⟩
      have hξ' : ξ.1 = v z := hξ
      refine hz ⟨v.isOpenEmbedding.mem_genericPoints_iff.1 (hξ' ▸ ξ.2), ?_⟩
      rw [hδ]
      exact hd

include hv in
/-- **The fundamental class restricts to the fundamental class** along an open immersion
`v : U ⟶ X`, in every degree `k`: `[X]_k|_U = [U]_k`, with no bound on the dimension of `X`. -/
theorem chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion (k : ℤ) :
    chowGroupRestrict C sX sU v hv k (fundamentalChowClass C sX k) =
      fundamentalChowClass C sU k := by
  rw [fundamentalChowClass, chowGroupRestrict_mk, cycleGroupRestrict_fundamentalCycle,
    fundamentalChowClass]

/-- On a scheme all of whose irreducible components have `δ`-dimension `n`, the fundamental class
vanishes in every degree `k ≠ n`. -/
theorem fundamentalChowClass_eq_zero_of_deltaDimension_eq {T : Scheme.{u}} (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] {n k : ℤ}
    (hT : ∀ W : irreducibleComponents T, deltaDimension C sT
      ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set T) W.2⟩ = n)
    (hk : k ≠ n) : fundamentalChowClass C sT k = 0 := by
  rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees C sT ?_,
    map_zero]
  rintro ⟨ξ, hξ, hδ⟩
  apply hk
  rw [← hδ, ← hT ⟨closure {ξ}, hξ⟩,
    deltaDimension_eq_of_isGenericPoint C _ _ ξ isGenericPoint_closure]

end Fundamental

/-! ### The Gysin map on fundamental classes -/

section GysinFundamental

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX) (hlci : IsLocalCompleteIntersectionMorphism f) (h : GysinMapExists f)

/-- The fundamental class vanishes in the degrees outside the finite set of its degrees. -/
private theorem fundamentalChowClass_eq_zero_of_notMem_toFinset {T : Scheme.{u}} (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] [IsNoetherian T] (n : ℤ)
    (hn : n ∉ (fundamentalClassDegrees_finite C sT).toFinset) :
    fundamentalChowClass C sT n = 0 := by
  rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees C sT
    fun h' => hn ((fundamentalClassDegrees_finite C sT).mem_toFinset.2 h'), map_zero]

/-- **The Gysin map on a connected component of `X`, on a fundamental class of `Y`.** Let `X`, `Y`
have dimension decompositions (Stacks 0FE3) with `Y` Cohen–Macaulay, let `X_a` be a connected
component of `X`, of `δ`-dimension `n_a`, lying over the connected component `Y_b` of `Y`, of
`δ`-dimension `n_b`. Then the part `f^!_q` of the Gysin map carries `[Y]_n` to a class whose
restriction to `X_a` is `[X_a]_{n_a}` if `q = n_b - n_a` and `n = n_b`, and zero otherwise.

On `X_a` the Gysin map is concentrated in the degree `n_b - n_a`, where it satisfies the cap
formula of the proof of Stacks 0FF7
(`SmoothFactorization.exists_hasCapFundamentalFormula_gysinMap_of_hasDimensionDecomposition`);
the cap product on the test scheme `Y` restricts over `Y_b` to the cap product on the test scheme
`Y_b` (Stacks 0B76 (2)), where `[Y]_n` restricts to `[Y_b]_n`, which is zero unless `n = n_b`, the
component `Y_b` being pure of `δ`-dimension `n_b`. -/
theorem chowGroupRestrict_lciGysinChow_fundamentalChowClass
    (hX : HasDimensionDecomposition (relativeDimension C.dimensionFunction sX))
    (hY : HasDimensionDecomposition (relativeDimension C.dimensionFunction sY))
    (hYcm : IsCohenMacaulay Y) (a : _root_.ConnectedComponents X) (q n : ℤ) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    chowGroupRestrict C sX ((X.connectedComponentOpens a).ι ≫ sX) (X.connectedComponentOpens a).ι
        rfl (n - q) (lciGysinChow C sX sY hf hlci h q n (fundamentalChowClass C sY n)) =
      if q = componentDeltaDimension C sY hY (f.continuous.connectedComponentsMap a) -
          componentDeltaDimension C sX hX a ∧
        n = componentDeltaDimension C sY hY (f.continuous.connectedComponentsMap a)
      then fundamentalChowClass C ((X.connectedComponentOpens a).ι ≫ sX) (n - q) else 0 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  set b := f.continuous.connectedComponentsMap a
  set nb := componentDeltaDimension C sY hY b
  set na := componentDeltaDimension C sX hX a
  set c := lciGysinMap C sX sY hf hlci h
  set F := lciGysinMapComponent C sX sY hf hlci h q
  obtain ⟨d, hd, hdeg⟩ := (Classical.choice ((gysinMapExists_iff_nonempty f).1 h) :
    SmoothFactorization f).exists_hasCapFundamentalFormula_gysinMap_of_hasDimensionDecomposition
      C sX sY hf hlci hX hY
  have hres : bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf q
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) F a = c a q :=
    restriction_completedBivariantSequence C (gysinSystemOfInvertible C) sX sY f hf
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
      (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
      (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) c q a
  -- the Gysin map in degree `q` on `[Y]_n`, as a restriction along `X_a ⟶ X ×_Y Y`
  set z := F.cap (𝟙 Y) n (fundamentalChowClass C (𝟙 Y ≫ sY) n)
  have he : (pullbackIdIso f).hom ≫ (pullback.fst f (𝟙 Y) ≫ sX) = sX := by
    rw [pullbackIdIso_hom_fst_assoc]
  set u₀ := (X.connectedComponentOpens a).ι ≫ (pullbackIdIso f).hom
  have hu₀ : u₀ ≫ (pullback.fst f (𝟙 Y) ≫ sX) = (X.connectedComponentOpens a).ι ≫ sX := by
    rw [Category.assoc, he]
  have hL : chowGroupRestrict C sX ((X.connectedComponentOpens a).ι ≫ sX)
      (X.connectedComponentOpens a).ι rfl (n - q)
      (lciGysinChow C sX sY hf hlci h q n (fundamentalChowClass C sY n)) =
      chowGroupRestrict C (pullback.fst f (𝟙 Y) ≫ sX) ((X.connectedComponentOpens a).ι ≫ sX) u₀
        hu₀ (n - q) z := by
    rw [lciGysinChow, BivariantClass.capTargetHom_apply, BivariantClass.capTarget,
      chowGroupCongr_fundamentalChowClass,
      ← chowGroupRestrict_eq_chowPushforwardOfIso_inv C _ sX (pullbackIdIso f) he,
      chowGroupRestrict_comp]
  rw [hL]
  have hu₀fst : 𝟙 _ ≫ (X.connectedComponentOpens a).ι = u₀ ≫ pullback.fst f (𝟙 Y) := by
    rw [Category.id_comp, Category.assoc, pullbackIdIso_hom_fst, Category.comp_id]
  by_cases hq : q = d a
  swap
  · -- `f^!` vanishes in degree `q` on `X_a`
    have hca : c a = DirectSum.of _ (d a) (c a (d a)) := (hd a).1
    have h0 : c a q = 0 := by
      rw [hca]
      exact DirectSum.of_eq_of_ne _ _ _ hq
    rw [chowGroupRestrict_cap_eq_zero_of_connectedComponentRestriction_eq_zero C
      (gysinSystemOfInvertible C) sX sY f hf q
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) F a (hres.trans h0) (𝟙 Y) n _ _
      u₀ hu₀ (𝟙 _) hu₀fst, ite_eq_right]
    rintro ⟨hq', -⟩
    exact hq (hq'.trans (hdeg a).symm)
  -- restricting the test scheme to `Y_b`
  set V := Y.connectedComponentOpens b
  have hm : V.ι ≫ 𝟙 Y = V.ι := Category.comp_id _
  set v' := baseChangeMapOfEq f (𝟙 Y) V.ι V.ι hm
  have sq := isPullback_baseChangeMapOfEq f (𝟙 Y) V.ι V.ι hm
  have : IsOpenImmersion v' := MorphismProperty.of_isPullback sq (P := @IsOpenImmersion)
    inferInstance
  have hvY : V.ι ≫ (𝟙 Y ≫ sY) = V.ι ≫ sY := by rw [Category.id_comp]
  have hcap := BivariantClass.cap_chowGroupRestrict C (gysinSystemOfInvertible C) sX sY f hf q F
    (𝟙 Y) V.ι V.ι hm v' sq (baseChangeMapOfEq_fst f (𝟙 Y) V.ι V.ι hm) n hvY
    (baseChangeMapOfEq_comp_structure sX f (𝟙 Y) V.ι V.ι hm)
    (fundamentalChowClass C (𝟙 Y ≫ sY) n)
  rw [chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion] at hcap
  -- the inclusion `X_a ⟶ X ×_Y Y` factors through `X ×_Y Y_b`
  set w : (X.connectedComponentOpens a : Scheme.{u}) ⟶ pullback f V.ι :=
    pullback.lift (X.connectedComponentOpens a).ι (f.resConnectedComponent a)
      (f.resConnectedComponent_comp_ι a).symm
  have hw : w ≫ v' = u₀ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, baseChangeMapOfEq_fst, pullback.lift_fst, Category.assoc,
        pullbackIdIso_hom_fst, Category.comp_id]
    · rw [Category.assoc, baseChangeMapOfEq_snd, pullback.lift_snd_assoc, Category.assoc,
        pullbackIdIso_hom_snd, Scheme.Hom.resConnectedComponent_comp_ι]
  have : IsOpenImmersion w := by
    have : IsOpenImmersion (w ≫ v') := by rw [hw]; infer_instance
    exact IsOpenImmersion.of_comp w v'
  have hwbase : w ≫ (pullback.fst f V.ι ≫ sX) = (X.connectedComponentOpens a).ι ≫ sX := by
    rw [pullback.lift_fst_assoc]
  have hR : chowGroupRestrict C (pullback.fst f (𝟙 Y) ≫ sX) ((X.connectedComponentOpens a).ι ≫ sX)
      u₀ hu₀ (n - q) z =
      chowGroupRestrict C (pullback.fst f V.ι ≫ sX) ((X.connectedComponentOpens a).ι ≫ sX) w
        hwbase (n - q) (F.cap V.ι n (fundamentalChowClass C (V.ι ≫ sY) n)) := by
    rw [← hcap, chowGroupRestrict_comp]
    exact congrFun (congrArg DFunLike.coe
      (chowGroupRestrict_congr C _ _ u₀ hu₀ (n - q) (w ≫ v') hw.symm _)) z
  rw [hR]
  have hT : ∀ W : irreducibleComponents (V : Scheme.{u}), deltaDimension C (V.ι ≫ sY)
      ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set V) W.2⟩ = nb :=
    deltaDimension_connectedComponentOpens C sY hY b
  by_cases hn : n = nb
  swap
  · rw [fundamentalChowClass_eq_zero_of_deltaDimension_eq C _ hT hn, map_zero, map_zero,
      ite_eq_right]
    rintro ⟨-, hn'⟩
    exact hn hn'
  rw [ite_eq_left ⟨hq.trans (hdeg a), hn⟩]
  subst hq
  refine chowGroupRestrict_cap_fundamentalChowClass_of_capFundamentalFormula C sX sY f hf F a
    ?_ V.ι (hn ▸ hT) ?_ ?_ _ w hwbase (𝟙 _) ?_
  · rw [hres]
    have hcf := (hd a).2 n
    exact hcf
  · intro ξ hξ
    rw [relativeDimension_comp_isOpenImmersion]
    have h1 := relativeDimension_le_componentDeltaDimension C sX hX (pullback.fst f V.ι ξ)
    have h2 : _root_.ConnectedComponents.mk (pullback.fst f V.ι ξ) = a := hξ
    rw [h2] at h1
    have h3 := hdeg a
    have h4 : componentDeltaDimension C sY hY (f.continuous.connectedComponentsMap a) = nb := rfl
    omega
  · intro ξ _ _
    have hcm := isCohenMacaulayLocalRing_stalk Y hYcm (V.ι (pullback.snd f V.ι ξ))
    exact (isCohenMacaulayLocalRing_iff_of_ringEquiv
      (asIso (V.ι.stalkMap (pullback.snd f V.ι ξ))).commRingCatIsoToRingEquiv).mp hcm
  · rw [Category.id_comp, pullback.lift_fst]

/-- **The Gysin map on the fundamental class, degree by degree.** For `X` with finitely many
connected components and `X`, `Y` with dimension decompositions (Stacks 0FE3), `Y`
Cohen–Macaulay, the parts of `f^![Y]` of degree `m` add up to `[X]_m`:

  `∑_q f^!_q [Y]_{m+q} = [X]_m`   in   `CH_m(X)`,

the sum over any finite set of degrees containing the support of `f^!`. On each connected
component `X_a` only the term `q = n_b - n_a` survives
(`Stacks.Chow.chowGroupRestrict_lciGysinChow_fundamentalChowClass`), and both sides restrict to
`[X_a]_m`, which vanishes unless `m = n_a`. -/
theorem sum_lciGysinChow_fundamentalChowClass [Finite (_root_.ConnectedComponents X)]
    (hX : HasDimensionDecomposition (relativeDimension C.dimensionFunction sX))
    (hY : HasDimensionDecomposition (relativeDimension C.dimensionFunction sY))
    (hYcm : IsCohenMacaulay Y) (s : Finset ℤ) (hs : lciGysinSupport C sX sY hf hlci h ⊆ s)
    (m : ℤ) :
    ∑ q ∈ s, chowGroupDegreeEquiv C sX (add_sub_cancel_right m q)
        (lciGysinChow C sX sY hf hlci h q (m + q) (fundamentalChowClass C sY (m + q))) =
      fundamentalChowClass C sX m := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  set D : _root_.ConnectedComponents X → ℤ := fun a =>
    componentDeltaDimension C sY hY (f.continuous.connectedComponentsMap a) -
      componentDeltaDimension C sX hX a
  set s' := s ∪ (Set.finite_range D).toFinset
  have hss' : ∑ q ∈ s, chowGroupDegreeEquiv C sX (add_sub_cancel_right m q)
        (lciGysinChow C sX sY hf hlci h q (m + q) (fundamentalChowClass C sY (m + q))) =
      ∑ q ∈ s', chowGroupDegreeEquiv C sX (add_sub_cancel_right m q)
        (lciGysinChow C sX sY hf hlci h q (m + q) (fundamentalChowClass C sY (m + q))) := by
    refine Finset.sum_subset Finset.subset_union_left fun q _ hq => ?_
    rw [lciGysinChow_eq_zero C sX sY hf hlci h (fun h' => hq (hs h')), AddMonoidHom.zero_apply,
      map_zero]
  rw [hss']
  refine chowGroup_eq_of_chowGroupRestrict_preimage_connectedComponent_eq (C := C) sX (𝟙 X) m
    fun a => ?_
  change chowGroupRestrict C sX ((X.connectedComponentOpens a).ι ≫ sX)
      (X.connectedComponentOpens a).ι rfl m _ =
    chowGroupRestrict C sX ((X.connectedComponentOpens a).ι ≫ sX)
      (X.connectedComponentOpens a).ι rfl m _
  rw [map_sum, chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion]
  simp_rw [chowGroupRestrict_chowGroupDegreeEquiv]
  simp_rw [chowGroupRestrict_lciGysinChow_fundamentalChowClass C sX sY hf hlci h hX hY hYcm a]
  have hDa : D a ∈ s' := Finset.mem_union_right _ ((Set.finite_range D).mem_toFinset.2 ⟨a, rfl⟩)
  rw [Finset.sum_eq_single_of_mem (D a) hDa fun q _ hq => by
    rw [ite_eq_right fun h' => hq h'.1, map_zero]]
  have hpure := deltaDimension_connectedComponentOpens C sX hX a
  by_cases hm : m + D a = componentDeltaDimension C sY hY (f.continuous.connectedComponentsMap a)
  · rw [ite_eq_left ⟨rfl, hm⟩, chowGroupDegreeEquiv_fundamentalChowClass]
  · rw [ite_eq_right fun h' => hm h'.2, map_zero,
      fundamentalChowClass_eq_zero_of_deltaDimension_eq C _ hpure fun h' => hm (by
        simp only [D]
        omega)]

/-- A class of `CH_*(X)` placed in degree `i` is the same class, transported, placed in an equal
degree `j`. -/
theorem directSum_of_eq_of_chowGroupDegreeEquiv {i j : ℤ} (hij : i = j) (x : chowGroup C sX i) :
    DirectSum.of (fun k : ℤ => chowGroup C sX k) i x =
      DirectSum.of (fun k : ℤ => chowGroup C sX k) j (chowGroupDegreeEquiv C sX hij x) := by
  subst hij
  rfl

/-- **Stacks 0FF7 on `CH_*(X)`: the Gysin map carries `[Y]` to `[X]`.** For `X`, `Y` Noetherian
and Cohen–Macaulay (for instance regular) and `f : X ⟶ Y` a local complete intersection morphism
for which the Gysin map exists (Stacks 0FF3), the sum over all degrees of the parts of `f^![Y]`
is `[X]`:

  `∑_{n, q} f^!_q [Y]_n = [X] = ∑_m [X]_m`   in   `CH_*(X) = ⨁_m CH_m(X)`.

Degree by degree this is `Stacks.Chow.sum_lciGysinChow_fundamentalChowClass`; both schemes have
the dimension decompositions of Stacks 0FE3, being Cohen–Macaulay. -/
theorem sum_lciGysinChow_totalFundamentalClass [IsNoetherian X] [IsNoetherian Y]
    (hXcm : IsCohenMacaulay X) (hYcm : IsCohenMacaulay Y) :
    ∑ n ∈ (fundamentalClassDegrees_finite C sY).toFinset,
        ∑ q ∈ (finite_lciGysinSupport C sX sY hf hlci h).toFinset,
          DirectSum.of (fun k : ℤ => chowGroup C sX k) (n - q)
            (lciGysinChow C sX sY hf hlci h q n (fundamentalChowClass C sY n)) =
      totalFundamentalClass C sX := by
  classical
  have : Finite (_root_.ConnectedComponents X) :=
    TopologicalSpace.NoetherianSpace.finite_connectedComponents X
  have hX := HasDimensionDecomposition.of_isCohenMacaulay C X sX hXcm
  have hY := HasDimensionDecomposition.of_isCohenMacaulay C Y sY hYcm
  set DY := (fundamentalClassDegrees_finite C sY).toFinset
  set DX := (fundamentalClassDegrees_finite C sX).toFinset
  set S := (finite_lciGysinSupport C sX sY hf hlci h).toFinset
  set M := DX ∪ S.biUnion fun q => DY.image (· - q)
  set g : ℤ → ℤ → DirectSum ℤ (fun k : ℤ => chowGroup C sX k) := fun n q =>
    DirectSum.of (fun k : ℤ => chowGroup C sX k) (n - q)
      (lciGysinChow C sX sY hf hlci h q n (fundamentalChowClass C sY n))
  -- reindex each inner sum by the degree `m = n - q` of the result
  have hq : ∀ q ∈ S, ∑ n ∈ DY, g n q = ∑ m ∈ M, DirectSum.of (fun k : ℤ => chowGroup C sX k) m
      (chowGroupDegreeEquiv C sX (add_sub_cancel_right m q)
        (lciGysinChow C sX sY hf hlci h q (m + q) (fundamentalChowClass C sY (m + q)))) := by
    intro q hqS
    have hsub : DY ⊆ M.image (· + q) := fun n hn => Finset.mem_image.2
      ⟨n - q, Finset.mem_union_right _ (Finset.mem_biUnion.2
        ⟨q, hqS, Finset.mem_image.2 ⟨n, hn, rfl⟩⟩), sub_add_cancel n q⟩
    rw [Finset.sum_subset hsub fun n _ hn => by
        simp only [g]
        rw [fundamentalChowClass_eq_zero_of_notMem_toFinset C sY n hn, map_zero, map_zero],
      Finset.sum_image fun x _ y _ hxy => add_right_cancel hxy]
    exact Finset.sum_congr rfl fun m _ =>
      directSum_of_eq_of_chowGroupDegreeEquiv C sX (add_sub_cancel_right m q) _
  rw [Finset.sum_comm, Finset.sum_congr rfl hq, Finset.sum_comm]
  simp_rw [← map_sum]
  simp_rw [sum_lciGysinChow_fundamentalChowClass C sX sY hf hlci h hX hY hYcm S
    (Set.Finite.coe_toFinset (finite_lciGysinSupport C sX sY hf hlci h)).symm.subset]
  rw [totalFundamentalClass]
  exact (Finset.sum_subset Finset.subset_union_left fun m _ hm => by
    rw [fundamentalChowClass_eq_zero_of_notMem_toFinset C sX m hm, map_zero]).symm

/-- **Stacks 0FF7 on `CH_*(-) ⊗ 𝐐`: `f^![Y] = [X]`.** For `X`, `Y` Noetherian and
Cohen–Macaulay (for instance regular) and `f : X ⟶ Y` a local complete intersection morphism for
which the Gysin map exists (Stacks 0FF3), the rational Gysin map carries the fundamental class of
`Y` to that of `X`. This is the tensor product with `𝐐` of
`Stacks.Chow.sum_lciGysinChow_totalFundamentalClass`. -/
theorem lciGysinRational_rationalFundamentalClass [IsNoetherian X] [IsNoetherian Y]
    (hXcm : IsCohenMacaulay X) (hYcm : IsCohenMacaulay Y) :
    lciGysinRational C sX sY hf hlci h (rationalFundamentalClass C sY) =
      rationalFundamentalClass C sX := by
  classical
  have : Finite (_root_.ConnectedComponents X) :=
    TopologicalSpace.NoetherianSpace.finite_connectedComponents X
  set T : (DirectSum ℤ fun k : ℤ => chowGroup C sX k) →+
      DirectSum ℤ fun k : ℤ => ℚ ⊗[ℤ] chowGroup C sX k :=
    DirectSum.map fun k => (TensorProduct.mk ℤ ℚ (chowGroup C sX k) 1).toAddMonoidHom
  have hT : ∀ (k : ℤ) (x : chowGroup C sX k),
      T (DirectSum.of _ k x) = DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) k (1 ⊗ₜ x) :=
    fun k x => DirectSum.map_of _ k x
  have hR : rationalFundamentalClass C sX = T (totalFundamentalClass C sX) := by
    rw [rationalFundamentalClass_eq, totalFundamentalClass, map_sum]
    simp_rw [hT]
  rw [hR, ← sum_lciGysinChow_totalFundamentalClass C sX sY hf hlci h hXcm hYcm, map_sum,
    rationalFundamentalClass_eq, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [lciGysinRational_of_tmul, map_sum]
  simp_rw [hT]

/-- **Stacks 0FF7 on `CH_*(-) ⊗ 𝐐` for regular schemes: `f^![Y] = [X]`**, for `X`, `Y`
Noetherian and regular and `f` a local complete intersection morphism for which the Gysin map
exists, regular schemes being Cohen–Macaulay. -/
theorem lciGysinRational_rationalFundamentalClass_of_isRegular [IsNoetherian X] [IsNoetherian Y]
    (hXreg : IsRegular X) (hYreg : IsRegular Y) :
    lciGysinRational C sX sY hf hlci h (rationalFundamentalClass C sY) =
      rationalFundamentalClass C sX :=
  lciGysinRational_rationalFundamentalClass C sX sY hf hlci h (isCohenMacaulay_of_isRegular hXreg)
    (isCohenMacaulay_of_isRegular hYreg)

/-- **The Gysin map on `ch(α) ∩ [Y]`** (the computation in the proof of Stacks 0FF9): for `X`, `Y`
Noetherian and Cohen–Macaulay with `δ_{X/S}`, `δ_{Y/S}` bounded below,

  `f^!(ch(α) ∩ [Y]) = ch(f^*α) ∩ [X]`,

by Stacks 0FF6 (`Stacks.Chow.lciGysinRational_chernCharacterCap`) and `f^![Y] = [X]`
(`Stacks.Chow.lciGysinRational_rationalFundamentalClass`). -/
theorem lciGysinRational_chernCharacterCap_rationalFundamentalClass [IsNoetherian X]
    [IsNoetherian Y] (hXcm : IsCohenMacaulay X) (hYcm : IsCohenMacaulay Y)
    (hX : BddBelow (Set.range (relativeDimension C.dimensionFunction sX)))
    (hY : BddBelow (Set.range (relativeDimension C.dimensionFunction sY)))
    (a : VectorBundleKZero Y) :
    lciGysinRational C sX sY hf hlci h (chernCharacterCap C sY a (rationalFundamentalClass C sY)) =
      chernCharacterCap C sX (VectorBundleKZero.pullback f a) (rationalFundamentalClass C sX) := by
  have : Finite (_root_.ConnectedComponents X) :=
    TopologicalSpace.NoetherianSpace.finite_connectedComponents X
  rw [lciGysinRational_chernCharacterCap C sX sY hf hlci h hX hY,
    lciGysinRational_rationalFundamentalClass C sX sY hf hlci h hXcm hYcm]

end GysinFundamental

end Stacks.Chow

end
