module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusUnion
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistFlatness
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.EulerCharVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristicUnconditional
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.DivisorFirstDifference
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.ZeroDimensionalTensor
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.AmpleRestrict
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries

/-!
# The Euler characteristic of an invertible module on a union of two closed subschemes

For two closed subschemes `V(I)`, `V(J)` of a scheme `X` over a field `k`, with union
`V(I ⊓ J)` proper over `k`, and an invertible `𝒪_X`-module `ℋ`,

`χ(V(I ⊓ J), ℋ) + χ(V(I ⊔ J), ℋ) = χ(V(I), ℋ) + χ(V(J), ℋ)`,

where each `χ` is `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.eulerSum` of the
restriction (pullback) of `ℋ` to the closed subscheme.  When `I ⊓ J = ⊥` (so the union is `X`)
and the intersection `V(I ⊔ J)` is a `k`-rational point this reads

`χ(X, ℋ) + 1 = χ(V(I), ℋ) + χ(V(J), ℋ)`.

## Main results

* `AlgebraicGeometry.EulerSumUnionTwist.eulerSum_pullback_inf_add_eulerSum_pullback_sup`: the
  general identity, with no dimension hypothesis.
* `AlgebraicGeometry.EulerSumUnionTwist.eulerSum_eq_one_of_isIso`: an invertible module on a
  scheme isomorphic to `Spec k` has Euler characteristic one.
* `AlgebraicGeometry.EulerSumUnionTwist.eulerSum_add_one_of_inf_eq_bot_of_isIso_sup`: the
  rational-point case.

## References

* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.IdealSheafData
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace AlgebraicGeometry.EulerSumUnionTwist

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))

/-- Tensoring on the right with a fixed module `ℋ`, `𝒢 ↦ 𝒢 ⊗_{𝒪_X} ℋ`: the functor whose
exactness is the flatness of `ℋ`. -/
noncomputable abbrev twistFunctor (H : X.Modules) : X.Modules ⥤ X.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj H

/-- **The twist of the structure sheaf of a closed subscheme**: for a closed subscheme `Z` of
`X` with inclusion `i`, `i_* 𝒪_Z ⊗_{𝒪_X} ℋ ≅ i_*(i^* ℋ)`.  This is the projection formula for a
closed immersion followed by the left unitor on `Z`. -/
noncomputable def twistClosedSubschemeStructureSheafIso (K : X.IdealSheafData) (H : X.Modules) :
    (twistFunctor H).obj (closedSubschemeStructureSheaf K) ≅
      (Scheme.Modules.pushforward K.subschemeι).obj
        ((Scheme.Modules.pullback K.subschemeι).obj H) :=
  Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso K.subschemeι
      (SheafOfModules.unit K.subscheme.ringCatSheaf) H ≪≫
    (Scheme.Modules.pushforward K.subschemeι).mapIso
      (SheafOfModules.tensorSheafUnitLeftIso K.subscheme.toRingedSpace
        ((Scheme.Modules.pullback K.subschemeι).obj H))

/-- The Euler characteristic of a module pushed forward along a closed immersion is that of the
module. -/
theorem eulerSum_pushforward_of_isClosedImmersion {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (G : Z.Modules) :
    eulerSum k g ((Scheme.Modules.pushforward i).obj G) = eulerSum k (i ≫ g) G :=
  finsum_congr fun n => by
    rw [(cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k i g G n).toLinearEquiv.finrank_eq]

/-- The Euler characteristic of the twist of the structure sheaf of a closed subscheme is the
Euler characteristic of the restriction of the twisting module to that subscheme. -/
theorem eulerSum_twist_closedSubschemeStructureSheaf (K : X.IdealSheafData) (H : X.Modules) :
    eulerSum k g ((twistFunctor H).obj (closedSubschemeStructureSheaf K)) =
      eulerSum k (K.subschemeι ≫ g) ((Scheme.Modules.pullback K.subschemeι).obj H) :=
  (eulerSum_congr k g (twistClosedSubschemeStructureSheafIso K H)).trans
    (eulerSum_pushforward_of_isClosedImmersion k g K.subschemeι _)

variable (H : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H]

include H in
/-- The cohomology of the twist of the structure sheaf of a closed subscheme proper over `k` is
finite-dimensional ([Stacks, Tag 02O6] on the subscheme, carried across the closed
immersion). -/
theorem finiteDimensional_cohomologyOverField_twist (K : X.IdealSheafData)
    [IsProper (K.subschemeι ≫ g)] (n : ℕ) :
    FiniteDimensional k (cohomologyOverField k g
      ((twistFunctor H).obj (closedSubschemeStructureSheaf K)) n) := by
  have : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pullback K.subschemeι).obj H) :=
    SheafOfModules.isCoherent_of_isInvertible k (K.subschemeι ≫ g) _
  have h := finiteDimensional_cohomologyOverField_pushforward_of_isClosedImmersion k
    K.subschemeι g ((Scheme.Modules.pullback K.subschemeι).obj H) n
    (finiteDimensional_cohomologyOverField_of_isProper k (K.subschemeι ≫ g)
      ((Scheme.Modules.pullback K.subschemeι).obj H) n)
  exact Module.Finite.equiv
    (cohomologyOverFieldIso k g (twistClosedSubschemeStructureSheafIso K H) n).symm.toLinearEquiv

/-- The cohomology of the twist of the structure sheaf of a closed subscheme proper over `k`
vanishes in all large degrees. -/
theorem exists_isZero_cohomologyOverField_twist (K : X.IdealSheafData)
    [IsProper (K.subschemeι ≫ g)] :
    ∃ N : ℕ, ∀ n, N ≤ n → IsZero (cohomologyOverField k g
      ((twistFunctor H).obj (closedSubschemeStructureSheaf K)) n) := by
  have : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pullback K.subschemeι).obj H) :=
    SheafOfModules.isCoherent_of_isInvertible k (K.subschemeι ≫ g) _
  obtain ⟨N, hN⟩ := exists_isZero_cohomologyOverField_of_isProper k (K.subschemeι ≫ g)
  refine ⟨N, fun n hn => ?_⟩
  exact (hN _ (isQuasicoherent_of_isCoherent _) n hn).of_iso
    (cohomologyOverFieldIso k g (twistClosedSubschemeStructureSheafIso K H) n ≪≫
      (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k K.subschemeι g _ n).symm)

/-- Twisting by an invertible module is an exact functor: an invertible module is flat. -/
theorem exactFunctor_twistFunctor :
    exactFunctor X.Modules X.Modules (twistFunctor H) :=
  Stacks.SheafOfModules.isFlat_of_isInvertible (X := X.toRingedSpace) H
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ ‹_›)

/-- Twisting by an invertible module preserves zero morphisms. -/
instance preservesZeroMorphisms_twistFunctor : (twistFunctor H).PreservesZeroMorphisms := by
  obtain ⟨hlim, -⟩ := (exactFunctor_iff _).1 (exactFunctor_twistFunctor H)
  infer_instance

/-- Twisting by an invertible module carries short exact sequences to short exact sequences. -/
theorem shortExact_map_twistFunctor {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (twistFunctor H)).ShortExact := by
  obtain ⟨hlim, hcolim⟩ := (exactFunctor_iff _).1 (exactFunctor_twistFunctor H)
  exact hS.map_of_exact (twistFunctor H)

/-- Additivity of the Euler characteristic along the twist of the union–intersection sequence
`0 ⟶ 𝒪_{V(I ⊓ J)} ⟶ 𝒪_{V(I)} ⊞ 𝒪_{V(J)} ⟶ 𝒪_{V(I ⊔ J)} ⟶ 0` of [Stacks, Tag 0C4J]. -/
theorem eulerSum_twist_biprod_eq_inf_add_sup (I J : X.IdealSheafData)
    [IsProper ((I ⊓ J).subschemeι ≫ g)] [IsProper ((I ⊔ J).subschemeι ≫ g)] :
    eulerSum k g ((twistFunctor H).obj
        (closedSubschemeStructureSheaf I ⊞ closedSubschemeStructureSheaf J)) =
      eulerSum k g ((twistFunctor H).obj (closedSubschemeStructureSheaf (I ⊓ J))) +
        eulerSum k g ((twistFunctor H).obj (closedSubschemeStructureSheaf (I ⊔ J))) := by
  obtain ⟨hw, hSE⟩ := unionIntersection_shortExact I J
  obtain ⟨N₁, hN₁⟩ := exists_isZero_cohomologyOverField_twist k g H (I ⊓ J)
  obtain ⟨N₂, hN₂⟩ := exists_isZero_cohomologyOverField_twist k g H (I ⊔ J)
  have hT := shortExact_map_twistFunctor H hSE
  have e := finsum_alternating_finrank_cohomologyOverField_add_of_shortExact_of_outer k g
    hT (max N₁ N₂)
    (fun n _ => finiteDimensional_cohomologyOverField_twist k g H (I ⊓ J) n)
    (fun n _ => finiteDimensional_cohomologyOverField_twist k g H (I ⊔ J) n)
    (fun n hn => hN₁ n (le_of_max_le_left hn)) (fun n hn => hN₂ n (le_of_max_le_right hn))
  exact e

/-- Additivity of the Euler characteristic along the twist of the split sequence
`0 ⟶ 𝒪_{V(I)} ⟶ 𝒪_{V(I)} ⊞ 𝒪_{V(J)} ⟶ 𝒪_{V(J)} ⟶ 0`. -/
theorem eulerSum_twist_biprod_eq_add (I J : X.IdealSheafData)
    [IsProper (I.subschemeι ≫ g)] [IsProper (J.subschemeι ≫ g)] :
    eulerSum k g ((twistFunctor H).obj
        (closedSubschemeStructureSheaf I ⊞ closedSubschemeStructureSheaf J)) =
      eulerSum k g ((twistFunctor H).obj (closedSubschemeStructureSheaf I)) +
        eulerSum k g ((twistFunctor H).obj (closedSubschemeStructureSheaf J)) := by
  obtain ⟨N₃, hN₃⟩ := exists_isZero_cohomologyOverField_twist k g H I
  obtain ⟨N₄, hN₄⟩ := exists_isZero_cohomologyOverField_twist k g H J
  have hT := shortExact_map_twistFunctor H (biprodShortComplexSplitting
      (closedSubschemeStructureSheaf I) (closedSubschemeStructureSheaf J)).shortExact
  have e := finsum_alternating_finrank_cohomologyOverField_add_of_shortExact_of_outer k g
    hT (max N₃ N₄)
    (fun n _ => finiteDimensional_cohomologyOverField_twist k g H I n)
    (fun n _ => finiteDimensional_cohomologyOverField_twist k g H J n)
    (fun n hn => hN₃ n (le_of_max_le_left hn)) (fun n hn => hN₄ n (le_of_max_le_right hn))
  exact e

/-- **The Euler characteristic of an invertible module on a union of two closed subschemes.**
For ideal sheaves `I`, `J` on a scheme `X` over a field `k`, with the union `V(I ⊓ J)` proper
over `k`, and an invertible `𝒪_X`-module `ℋ`,

`χ(V(I ⊓ J), ℋ) + χ(V(I ⊔ J), ℋ) = χ(V(I), ℋ) + χ(V(J), ℋ)`,

each `χ` being `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.eulerSum` of the
restriction of `ℋ` to the closed subscheme.  No dimension hypothesis is needed. -/
theorem eulerSum_pullback_inf_add_eulerSum_pullback_sup (I J : X.IdealSheafData)
    [IsProper ((I ⊓ J).subschemeι ≫ g)] :
    eulerSum k ((I ⊓ J).subschemeι ≫ g) ((Scheme.Modules.pullback (I ⊓ J).subschemeι).obj H) +
        eulerSum k ((I ⊔ J).subschemeι ≫ g)
          ((Scheme.Modules.pullback (I ⊔ J).subschemeι).obj H) =
      eulerSum k (I.subschemeι ≫ g) ((Scheme.Modules.pullback I.subschemeι).obj H) +
        eulerSum k (J.subschemeι ≫ g) ((Scheme.Modules.pullback J.subschemeι).obj H) := by
  have : IsProper (I.subschemeι ≫ g) :=
    isProper_subschemeι_comp_of_le k g (inf_le_left : I ⊓ J ≤ I)
  have : IsProper (J.subschemeι ≫ g) :=
    isProper_subschemeι_comp_of_le k g (inf_le_right : I ⊓ J ≤ J)
  have : IsProper ((I ⊔ J).subschemeι ≫ g) :=
    isProper_subschemeι_comp_of_le k g (inf_le_left.trans le_sup_left : I ⊓ J ≤ I ⊔ J)
  rw [← eulerSum_twist_closedSubschemeStructureSheaf k g (I ⊓ J) H,
    ← eulerSum_twist_closedSubschemeStructureSheaf k g (I ⊔ J) H,
    ← eulerSum_twist_closedSubschemeStructureSheaf k g I H,
    ← eulerSum_twist_closedSubschemeStructureSheaf k g J H,
    ← eulerSum_twist_biprod_eq_inf_add_sup k g H I J, eulerSum_twist_biprod_eq_add k g H I J]

omit H in
/-- **The Euler characteristic of an invertible module on a rational point is one.**  If the
structure morphism `e : Z ⟶ Spec k` is an isomorphism, every invertible `𝒪_Z`-module `ℳ` is
trivial ([Stacks, Tag 0AYT] at rank one: `Z` is a point) and `χ(Z, ℳ) = h⁰(Z, 𝒪_Z) = 1`. -/
theorem eulerSum_eq_one_of_isIso {Z : Scheme.{u}} (e : Z ⟶ Spec (.of k)) [IsIso e]
    (M : Z.Modules) [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 M] :
    eulerSum k e M = 1 := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian e
  have : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k e
  have : Subsingleton Z := (Scheme.homeoOfIso (asIso e)).injective.subsingleton
  have hdim : topologicalKrullDim
      (SheafOfModules.supp (SheafOfModules.unit Z.ringCatSheaf)) ≤ 0 :=
    topologicalKrullDim_zero_of_discreteTopology _
  obtain ⟨e₀⟩ := nonempty_tensorModulesIso_of_topologicalKrullDim_supp_le_zero
    (SheafOfModules.unit Z.ringCatSheaf) hdim M
  have eM : M ≅ SheafOfModules.unit Z.ringCatSheaf :=
    (SheafOfModules.tensorSheafUnitLeftIso Z.toRingedSpace M).symm ≪≫ e₀
  rw [eulerSum_congr k e eM]
  have : IsAffine Z := IsAffine.of_isIso e
  have hvan : ∀ m, 0 < m →
      IsZero (cohomologyOverField k e (SheafOfModules.unit Z.ringCatSheaf) m) :=
    fun m hm => isZero_cohomologyOverField_pos_of_isAffine k e _ m hm
  unfold eulerSum
  rw [finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k e _
    (fun m hm => hvan m (by omega))]
  have : IsIso e.appTop := inferInstanceAs (IsIso (e.app ⊤))
  rw [finrank_cohomologyOverField_unit_zero_eq_one e]
  have : Subsingleton (cohomologyOverField k e (SheafOfModules.unit Z.ringCatSheaf) 1) :=
    ModuleCat.subsingleton_of_isZero (hvan 1 Nat.one_pos)
  rw [Module.finrank_zero_of_subsingleton]
  norm_num

/-- **The Euler characteristic of an invertible module on two closed subschemes meeting in a
rational point.**  Let `X` be proper over a field `k`, and let `I`, `J` be ideal sheaves with
`I ⊓ J = ⊥` — so `X` is the scheme-theoretic union of `V(I)` and `V(J)` — whose
scheme-theoretic intersection `V(I ⊔ J)` is a `k`-rational point, that is, its structure
morphism to `Spec k` is an isomorphism.  Then for every invertible `𝒪_X`-module `ℋ`,

`χ(X, ℋ) + 1 = χ(V(I), ℋ|_{V(I)}) + χ(V(J), ℋ|_{V(J)})`.

This is `AlgebraicGeometry.EulerSumUnionTwist.eulerSum_pullback_inf_add_eulerSum_pullback_sup`
with the union identified with `X` and the point contributing
`AlgebraicGeometry.EulerSumUnionTwist.eulerSum_eq_one_of_isIso`. -/
theorem eulerSum_add_one_of_inf_eq_bot_of_isIso_sup [IsProper g] (I J : X.IdealSheafData)
    (hIJ : I ⊓ J = ⊥) (hpt : IsIso ((I ⊔ J).subschemeι ≫ g)) :
    eulerSum k g H + 1 =
      eulerSum k (I.subschemeι ≫ g) ((Scheme.Modules.pullback I.subschemeι).obj H) +
        eulerSum k (J.subschemeι ≫ g) ((Scheme.Modules.pullback J.subschemeι).obj H) := by
  have key := eulerSum_pullback_inf_add_eulerSum_pullback_sup k g H I J
  have hbot : ∀ K : X.IdealSheafData, K = ⊥ →
      eulerSum k (K.subschemeι ≫ g) ((Scheme.Modules.pullback K.subschemeι).obj H) =
        eulerSum k g H := by
    rintro K rfl
    exact finsum_congr fun n => by
      rw [finrank_cohomologyOverField_pullback k (⊥ : X.IdealSheafData).subschemeι g H n]
  rw [hbot _ hIJ, eulerSum_eq_one_of_isIso k ((I ⊔ J).subschemeι ≫ g)] at key
  exact key

end AlgebraicGeometry.EulerSumUnionTwist

end
