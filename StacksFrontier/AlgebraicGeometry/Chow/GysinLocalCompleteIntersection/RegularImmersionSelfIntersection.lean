module

import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedChernComposite
import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapOnCyclesDescent
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinMapComposition
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionRegularImmersionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.GysinChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.FiniteLocallyFreeReflexive
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The self-intersection formula for a regular closed immersion

Let `k` be a field, let `P` be a scheme smooth over `k` of pure dimension `n` and let
`i : Y ⟶ P` be a regular closed immersion with `Y` of pure dimension `e`, so that `Y` has
codimension `c = n - e`; its normal sheaf `𝒩 = 𝒞_{Y/P}^∨` is finite locally free of rank `c`.
The *self-intersection formula* is

  `i^![Y] = c_c(𝒩) ∩ [Y]_e`   in   `CH_{e-c}(Y)`,

for `[Y] ∈ CH^c(P)` the class of the closed subscheme `Y`
(`Stacks.WeilCohomology.closedSubschemeClass`), `i^! : CH^c(P) ⟶ CH_{e-c}(Y)` the Gysin map of
Stacks 0FF3 (`Stacks.Chow.regularImmersionGysin`), and `c_c(𝒩) ∩ -` the cap product with the top
Chern class of Stacks 02U5/02U6 (`Stacks.Chow.GenuineChern.chernCap`). It is the excess
intersection formula of Stacks 0FBM for the cartesian square

```
Y --𝟙--→ Y
|        |
𝟙        i
↓        ↓
Y --i--→ P
```

whose base change `𝟙 : Y ⟶ Y` has zero conormal sheaf, so that the excess normal sheaf is all of
`𝒩`.

The proof runs as follows. The Gysin map of `i` is computed by the factorization `i = 𝟙 ∘ i`
(Stacks 0FF2): it is `c(Y ⟶ P, 𝒩) ∘ 𝟙^*`, and the flat pullback along the identity is the unit
of `A^*(P)^∧` (`Stacks.Chow.completedFlatPullbackOfSmooth_id`), so `i^!` is the class
`c(Y ⟶ P, 𝒩)` of Stacks 0FBK (`Stacks.Chow.lciGysinMap_eq_completedVirtualNormalGysinClass`).
The class `[Y]` lives on the part `P_n` of `P` of dimension `n`, where it is the pushforward of
`[Y ×_P P_n]_e`; capping commutes with this pushforward (Stacks 0B76 (1)), and at the test scheme
`Y ×_P P_n ⟶ P`, which factors through `i`, Stacks 0FBM at constant rank gives
`c_c(𝒩) ∩ [Y ×_P P_n]_e` (`Stacks.Chow.lciGysinBivariantClass_cap_fundamentalChowClass_of_factor`).

## Main results

* `Stacks.Chow.completedFlatPullbackOfSmooth_id` — the flat pullback along the identity is the
  unit of the completed bivariant ring.
* `Stacks.Chow.lciGysinMap_eq_completedVirtualNormalGysinClass` — the Gysin map of a regular
  closed immersion is the class of its normal sheaf.
* `Stacks.Chow.regularImmersionGysin_closedSubschemeClass_self` — the self-intersection formula
  `i^![Y] = c_c(𝒩) ∩ [Y]_e`.

## References

* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FF2](https://stacks.math.columbia.edu/tag/0FF2)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

/-! ### The flat pullback along the identity -/

section Identity

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [IsLocallyNoetherian X]

/-- **The flat pullback along the identity is the unit of `A^*(X)^∧`.** Both classes are
concentrated in degree `0` on every connected component of `X`, where they satisfy the formula of
Stacks 0FEA in every degree; such classes of a flat morphism agree. -/
theorem completedFlatPullbackOfSmooth_id :
    completedFlatPullbackOfSmooth C sX sX (𝟙 X) (Category.id_comp sX) =
      completedIdentityClass C sX := by
  have hrel : ∀ a : _root_.ConnectedComponents X,
      ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (Scheme.Hom.resConnectedComponent (𝟙 X) a) r :=
    fun a ↦ ⟨0, relativeDimension_of_isOpenImmersion _⟩
  rw [completedFlatPullbackOfSmooth_eq_completedFlatPullback C sX sX (𝟙 X) _ hrel]
  refine completedBivariantGroup.eq_of_hasCapFundamentalFormula C sX sX (𝟙 X)
    (Category.id_comp sX) hrel (hasCapFundamentalFormula_completedFlatPullback C sX sX (𝟙 X) _ hrel)
    (hasCapFundamentalFormula_completedIdentityClass C sX) (fun _ ↦ rfl) fun a ↦ ?_
  rw [flatComponentRelativeDimension_eq _ hrel a (relativeDimension_of_isOpenImmersion _),
    Nat.cast_zero, neg_zero]

end Identity

/-! ### The excess normal sheaf at a test scheme over `Y` -/

section Excess

variable {Y P : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i] [IsLocallyNoetherian Y]
  (hreg : IsRegularImmersion i)

/-- **The excess normal sheaf of the base change to a test scheme over `Y` is the pulled back
normal sheaf.** For a cartesian square with left arrow `𝟙 : T ⟶ T`, the conormal sheaf of `𝟙`
vanishes, so the kernel of the surjection of the base change of `𝒩` is all of its dual, and the
excess normal sheaf is the base change of `𝒩` itself. -/
def excessNormalSheafIsoOfIdentity {T : Scheme.{u}} (π : T ⟶ Y) (g : T ⟶ P)
    (sq : IsPullback (𝟙 T) π g i) [IsLocallyNoetherian T] :
    ((VirtualNormalBundle.ofIsRegularImmersion i hreg).baseChange i (𝟙 T) π g
        sq).excessNormalSheaf ≅
      (Scheme.Modules.pullback π).obj (dualSheaf (conormalModule i)) :=
  let 𝒩' : VirtualNormalBundle (𝟙 T) :=
    (VirtualNormalBundle.ofIsRegularImmersion i hreg).baseChange i (𝟙 T) π g sq
  haveI : IsIso (kernel.ι 𝒩'.conormalSurjection) :=
    kernel.ι_of_zero ((Stacks.Conormal.isZero_immersionConormalSheaf_of_isIso (𝟙 T)).eq_of_tgt
      _ _)
  haveI := isIso_toDoubleDual_of_isFiniteLocallyFree 𝒩'.bundle 𝒩'.isFiniteLocallyFree
  (dualMapIso (asIso (kernel.ι 𝒩'.conormalSurjection))).symm ≪≫
    (asIso (toDoubleDual 𝒩'.bundle)).symm

end Excess

/-- The Chern cap of the fundamental class depends only on the structure morphism and degree. -/
private theorem chernCap_fundamentalChowClass_heq (C : ChowSituation.{u}) (c : ℕ) {T : Scheme.{u}}
    (ℱ : T.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} ℱ c]
    (s s' : T ⟶ C.S) [LocallyOfFiniteType s] [LocallyOfFiniteType s'] (hs : s = s')
    (m m' : ℤ) (hm : m = m') :
    GenuineChern.chernCap C c s ℱ m (Fin.last c) (fundamentalChowClass C s m) ≍
      GenuineChern.chernCap C c s' ℱ m' (Fin.last c) (fundamentalChowClass C s' m') := by
  subst hs hm
  rfl

/-! ### The Gysin map of a regular closed immersion -/

section Gysin

variable (C : ChowSituation.{u}) {Y P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
  (i : Y ⟶ P) [IsClosedImmersion i] (hreg : IsRegularImmersion i)

/-- **The Gysin map of a regular closed immersion is the class of its normal sheaf.** For the
factorization `i = 𝟙 ∘ i` the Gysin map of Stacks 0FF3 is `c(Y ⟶ P, 𝒩) ∘ 𝟙^*`, with
`c(Y ⟶ P, 𝒩)` the class of Stacks 0FBQ (3) of the normal sheaf `𝒩 = 𝒞_{Y/P}^∨`; the flat pullback
along the identity is the unit (`Stacks.Chow.completedFlatPullbackOfSmooth_id`), and for a closed
immersion the class of Stacks 0FBQ (3) is that of Stacks 0FBK. By Stacks 0FF2 the factorization
computes `i^!`. -/
theorem lciGysinMap_eq_completedVirtualNormalGysinClass
    (hlci : IsLocalCompleteIntersectionMorphism i) (h : GysinMapExists i) :
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sP)
    lciGysinMap C (i ≫ sP) sP rfl hlci h =
      completedVirtualNormalGysinClass C (i ≫ sP) sP i rfl
        (VirtualNormalBundle.ofIsRegularImmersion i hreg) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sP)
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
  let F : SmoothFactorization i :=
    ⟨P, i, 𝟙 P, inferInstance, inferInstance, Category.comp_id i⟩
  refine (F.gysinMap_eq_lciGysinMap C (i ≫ sP) sP rfl hlci h).symm.trans
    ((eq_of_heq ?_).trans
      (completedVirtualNormalGysinClassOfOpen_eq_completedVirtualNormalGysinClass C (i ≫ sP) sP
        i rfl i.coborderRange i.liftCoborder i.liftCoborder_ι _))
  refine (completedBivariantGroup.copy_heq C _ _ _ _).trans ?_
  refine (completedBivariantCompositeOfInvertible_heq_congr C rfl (Category.id_comp sP) rfl rfl
    rfl (c' := completedVirtualNormalGysinClassOfImmersion C (i ≫ sP) sP i rfl
      (VirtualNormalBundle.ofIsRegularImmersion i hreg))
    (d' := completedIdentityClass C sP)
    (completedVirtualNormalGysinClassOfImmersion_ofIsRegularImmersion_heq_congr C
      (Category.id_comp sP) rfl _ _)
    ((completedFlatPullbackOfSmooth_heq_congr C (Category.id_comp sP) rfl).trans
      (heq_of_eq (completedFlatPullbackOfSmooth_id C sP)))).trans ?_
  exact completedBivariantCompositeOfInvertible_completedIdentityClass C (i ≫ sP) sP i rfl _

variable (c : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualSheaf (conormalModule i)) c]

include hreg in
/-- **The Gysin map of `i` on the fundamental class of a test scheme lying over `Y`.** Let
`π : T ⟶ Y` be a morphism and `g = i ∘ π`, so that `Y ×_P T = T`. If `dim_δ(T) ≤ m`, the degree
`c` term of `i^!` caps `[T]_m` at the test scheme `g` to `c_c(π^*𝒩) ∩ [T]_m`, read on the chosen
fibre product `Y ×_P T`.

This is Stacks 0FBM at constant rank for the square with left arrow `𝟙 : T ⟶ T`, a regular
immersion of codimension `0`, whose excess normal sheaf is `π^*𝒩`
(`Stacks.Chow.excessNormalSheafIsoOfIdentity`), with `i^!` the class of the normal sheaf
(`Stacks.Chow.lciGysinMap_eq_completedVirtualNormalGysinClass`). -/
theorem lciGysinBivariantClass_cap_fundamentalChowClass_of_factor
    (hlci : IsLocalCompleteIntersectionMorphism i) (h : GysinMapExists i) {T : Scheme.{u}}
    (π : T ⟶ Y) (g : T ⟶ P) [LocallyOfFiniteType g] (sq : IsPullback (𝟙 T) π g i) (m : ℤ)
    (hm : schemeDeltaDimension C (g ≫ sP) ≤ (m : EInt)) (q : ℤ) (hq : q = c) :
    haveI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback π
      (dualSheaf (conormalModule i)) c
    (lciGysinMapComponent C (i ≫ sP) sP rfl hlci h q).cap g m
        (fundamentalChowClass C (g ≫ sP) m) =
      chowPushforwardOfIso C (g ≫ sP) (pullback.fst i g ≫ i ≫ sP) sq.flip.isoPullback.hom
        (isoPullback_hom_comp_structureMorphism C (i ≫ sP) sP sq rfl (g ≫ sP)
          (Category.id_comp _)) (m - q)
        (chowGroupDegreeEquiv C (g ≫ sP) (by rw [hq, Fin.val_last])
          (GenuineChern.chernCap C c (g ≫ sP) ((Scheme.Modules.pullback π).obj
            (dualSheaf (conormalModule i))) m (Fin.last c)
            (fundamentalChowClass C (g ≫ sP) m))) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sP)
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sP)
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback π (dualSheaf (conormalModule i)) c
  set 𝒩 := VirtualNormalBundle.ofIsRegularImmersion i hreg
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle (0 + c) := by
    rw [Nat.zero_add]
    exact (inferInstance :
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualSheaf (conormalModule i)) c)
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule (𝟙 T)) 0 :=
    isFiniteLocallyFreeOfRank_zero_of_isZero _
      (Stacks.Conormal.isZero_immersionConormalSheaf_of_isIso (𝟙 T))
  have hreg' : IsRegularImmersion (𝟙 T) :=
    Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth (𝟙 T) (𝟙 T)
  obtain rfl : q = ((0 + c : ℕ) : ℤ) := by rw [hq, Nat.zero_add]
  have hcls : lciGysinMapComponent C (i ≫ sP) sP rfl hlci h ((0 + c : ℕ) : ℤ) =
      virtualNormalBundleClass C (i ≫ sP) sP i rfl 𝒩 (0 + c) := by
    rw [lciGysinMapComponent, lciGysinMap_eq_completedVirtualNormalGysinClass C sP i hreg hlci h,
      completedVirtualNormalGysinClass_eq_toCompleted C (i ≫ sP) sP i rfl 𝒩 (0 + c),
      completedBivariantSequenceOfInvertible_toCompleted_self]
  rw [hcls, virtualNormalBundleClass_cap_fundamentalChowClass_excess C (i ≫ sP) sP i rfl 𝒩 0 c
    (isVirtualNormalBundleClass_virtualNormalBundleClass C _ sP i rfl 𝒩 (0 + c)) g (𝟙 T) π sq
    (g ≫ sP) (Category.id_comp _) hreg' m hm]
  refine congrArg _ (eq_of_heq ((chowGroupDegreeEquiv_heq C _ _ _).trans (HEq.trans ?_
    (chowGroupDegreeEquiv_heq C _ _ _).symm)))
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.baseChange i (𝟙 T) π g sq).bundle
      (0 + c) :=
    isFiniteLocallyFreeOfRank_modulePullback π 𝒩.bundle (0 + c) inferInstance
  have := (𝒩.baseChange i (𝟙 T) π g sq).isFiniteLocallyFreeOfRank_excessNormalSheaf_of_add 0 c
  rw [GenuineChern.chernCap_congr C (g ≫ sP) c (excessNormalSheafIsoOfIdentity i hreg π g sq)]
  exact chernCap_fundamentalChowClass_heq C c _ _ _ rfl _ _ (by simp)

end Gysin

/-! ### The self-intersection formula -/

section SelfIntersection

open Stacks.WeilCohomology (dimPart partBase closedSubschemeClass closedSubschemeClass_apply
  isEmpty_dimPart_of_ne properChowPushforward_fundamentalChowClass_eq_mk)

variable {k : Type u} [Field k] {P Y : Scheme.{u}} (sP : P ⟶ (fieldChowSituation k).S) [Smooth sP]
  (i : Y ⟶ P) [IsClosedImmersion i] (hreg : IsRegularImmersion i)

/-- **The self-intersection formula** `i^![Y] = c_c(𝒩) ∩ [Y]_e`. Let `k` be a field, let `P` be
a scheme smooth over `k` of pure dimension `n` and let `i : Y ⟶ P` be a regular closed immersion
with `Y` of pure dimension `e`, of codimension `c = n - e`, whose normal sheaf
`𝒩 = 𝒞_{Y/P}^∨` is finite locally free of rank `c`. Then

  `i^![Y] = c_c(𝒩) ∩ [Y]_e`   in   `CH_{e-c}(Y)`,

for `[Y] ∈ CH^c(P)` the class of the closed subscheme `Y`
(`Stacks.WeilCohomology.closedSubschemeClass`), `i^!` the Gysin map of Stacks 0FF3
(`Stacks.Chow.regularImmersionGysin`) and `c_c(𝒩) ∩ -` the cap product with the `c`-th Chern
class of Stacks 02U5/02U6 (`Stacks.Chow.GenuineChern.chernCap`), read in degree
`e - c = e - (Fin.last c)`.

This is the excess intersection formula (Stacks 0FBM) for the square `Y ×_P Y = Y`, whose
excess normal sheaf is `𝒩`. Both sides are compared on the pieces `Y ×_P P_d` of `Y`; only the
piece over `P_n` is nonempty, and there `[Y]` is the pushforward of `[Y ×_P P_n]_e`, so the cap
product commutes with that pushforward (Stacks 0B76 (1)) and is computed at the test scheme
`Y ×_P P_n ⟶ P`, which factors through `i`
(`Stacks.Chow.lciGysinBivariantClass_cap_fundamentalChowClass_of_factor`). -/
@[sga "5 VII 9.2" "(1), special case"]
theorem regularImmersionGysin_closedSubschemeClass_self (e c n : ℕ) (hn : e + c = n)
    (hP : RelativeDimension sP n) (hY : RelativeDimension (i ≫ sP) e)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualSheaf (conormalModule i)) c] :
    regularImmersionGysin sP i hreg e c (closedSubschemeClass sP i c) =
      chowGroupDegreeEquiv (fieldChowSituation k) (i ≫ sP) (by rw [Fin.val_last])
        (GenuineChern.chernCap (fieldChowSituation k) c (i ≫ sP) (dualSheaf (conormalModule i))
          e (Fin.last c) (fundamentalChowClass (fieldChowSituation k) (i ≫ sP) e)) := by
  have hlci := isLocalCompleteIntersectionMorphism_of_isRegularImmersion i hreg
  have hex := GysinMapExists.of_isImmersion i
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sP)
  refine (chowGroupClopenRestrictEquiv (fieldChowSituation k) (i ≫ sP)
      (fun d : ULift.{u} ℕ ↦ pullback.fst i (dimPart sP d.down).ι ≫ i ≫ sP)
      (fun d : ULift.{u} ℕ ↦ pullback.fst i (dimPart sP d.down).ι) (fun _ ↦ rfl)
      (isClopenDecomposition_pullbackFst_dimPart sP i) _).injective (funext fun ⟨d⟩ ↦ ?_)
  dsimp only
  rw [chowGroupClopenRestrictEquiv_apply, chowGroupClopenRestrictEquiv_apply,
    chowGroupRestrict_regularImmersionGysin]
  subst hn
  by_cases hd : d = e + c
  swap
  · -- the pieces over the parts `P_d`, `d ≠ n`, are empty
    have : IsEmpty (dimPart sP d).toScheme := isEmpty_dimPart_of_ne sP hP hd
    have : IsEmpty (pullback i (dimPart sP d).ι : Scheme.{u}) :=
      ⟨fun x ↦ isEmptyElim (pullback.snd i (dimPart sP d).ι x)⟩
    have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k)
      (pullback.fst i (dimPart sP d).ι ≫ i ≫ sP) ((e : ℤ) - c)
    exact Subsingleton.elim _ _
  subst hd
  set ιn := (dimPart sP (e + c)).ι
  set π := pullback.fst i ιn
  set jn := pullback.snd i ιn
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback π (dualSheaf (conormalModule i)) c
  have hec : ((e + c : ℕ) : ℤ) - c = e := by push_cast; ring
  have hdimY : schemeDeltaDimension (fieldChowSituation k) (i ≫ sP) ≤ ((e : ℤ) : EInt) :=
    WeilCohomology.schemeDeltaDimension_le_of_forall_irreducibleComponent _
      (WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k (i ≫ sP) e hY)
  have hdimY' : schemeDeltaDimension (fieldChowSituation k) (i ≫ sP) ≤
      ((((e + c : ℕ) : ℤ) - c : ℤ) : EInt) := by
    rwa [hec]
  have hdimπ : ∀ ξ, relativeDimension (fieldChowSituation k).dimensionFunction
      ((π ≫ i) ≫ sP) ξ ≤ ((e + c : ℕ) : ℤ) - c := fun ξ ↦ by
    rw [Category.assoc, relativeDimension_comp_isOpenImmersion, hec]
    exact relativeDimension_le_of_schemeDeltaDimension_le' _ _ hdimY _
  have hdimYn : schemeDeltaDimension (fieldChowSituation k) ((π ≫ i) ≫ sP) ≤
      ((((e + c : ℕ) : ℤ) - c : ℤ) : EInt) := by
    simpa using schemeDeltaDimension_le_of_forall_relativeDimension_le _ _ (𝟙 _)
      (by simpa using hdimπ)
  have hq : jn ≫ partBase sP (e + c) = (π ≫ i) ≫ sP := by
    rw [Category.assoc]
    exact pullbackSnd_comp_structureMorphism_eq (fieldChowSituation k) (i ≫ sP) sP i rfl ιn
  -- `[Y]` on `P_n` is the pushforward of `[Y ×_P P_n]_e` along `Y ×_P P_n ⟶ P_n`
  have hmk : (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sP i
        (((e + c : ℕ) : ℤ) - c)) : chowGroup (fieldChowSituation k) sP (((e + c : ℕ) : ℤ) - c)) =
      properChowPushforward (fieldChowSituation k) (i ≫ sP) sP i rfl _
        (properPushforwardDescends _ _ _ _ _ _)
        (fundamentalChowClass (fieldChowSituation k) (i ≫ sP) (((e + c : ℕ) : ℤ) - c)) :=
    (properChowPushforward_fundamentalChowClass_eq_mk sP i _).symm
  have hYn : closedSubschemeClass sP i c (e + c) =
      properChowPushforward (fieldChowSituation k) ((π ≫ i) ≫ sP) (ιn ≫ sP) jn hq
        (((e + c : ℕ) : ℤ) - c) (properPushforwardDescends _ _ _ _ _ _)
        (fundamentalChowClass (fieldChowSituation k) ((π ≫ i) ≫ sP) (((e + c : ℕ) : ℤ) - c)) := by
    rw [closedSubschemeClass_apply, hmk,
      chowGroupRestrict_properChowPushforward (fieldChowSituation k) (i ≫ sP) sP
        ((π ≫ i) ≫ sP) (partBase sP (e + c)) i rfl π (Category.assoc _ _ _).symm ιn rfl jn hq
        (IsPullback.of_hasPullback i ιn) _ (properPushforwardDescends _ _ _ _ _ _)
        (properPushforwardDescends _ _ _ _ _ _),
      chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion (fieldChowSituation k)
        (i ≫ sP) _ π _ _]
  -- the cap product commutes with that pushforward (Stacks 0B76 (1)), and at the test scheme
  -- `Y ×_P P_n ⟶ P`, which factors through `i`, it is `c_c(𝒩) ∩ -` (Stacks 0FBM)
  have sq : IsPullback (𝟙 _) π (π ≫ i) i := IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  have hcap := BivariantClass.cap_properChowPushforward
    (lciGysinMapComponent (fieldChowSituation k) (i ≫ sP) sP rfl hlci hex
      (((e + c : ℕ) : ℤ) - e))
    (properPushforwardDescends (fieldChowSituation k)) ιn jn (π ≫ i) pullback.condition.symm
    sq.flip.isoPullback.inv sq.flip.isoPullback_inv_fst
    (by rw [← sq.flip.isoPullback_inv_snd, Category.assoc, Category.id_comp])
    (((e + c : ℕ) : ℤ) - c)
    (fundamentalChowClass (fieldChowSituation k) ((π ≫ i) ≫ sP) (((e + c : ℕ) : ℤ) - c))
  rw [regularImmersionPartGysin, AddMonoidHom.comp_apply, BivariantClass.capTargetHom_apply,
    regularImmersionPartGysinClass,
    bivariantRestriction_capTarget (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _), hYn,
    hcap, lciGysinBivariantClass_cap_fundamentalChowClass_of_factor (fieldChowSituation k) sP i
      hreg c hlci hex π (π ≫ i) sq _ hdimYn _ (by push_cast; ring),
    properChowPushforward_eq_chowPushforwardOfIso, chowPushforwardOfIso_comp_apply]
  -- the two pushforwards compose to the identity of `Y ×_P P_n`
  refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans
    (((chowPushforwardOfIso_heq_self (fieldChowSituation k)
      (sq.flip.isoPullback.hom ≫ sq.flip.isoPullback.inv) (Iso.hom_inv_id _) _ _ _).trans
    (chowGroupDegreeEquiv_heq _ _ _ _)).trans (HEq.trans ?_
      (chowGroupRestrict_heq_of_heq (fieldChowSituation k) (i ≫ sP) _ π rfl
        (by rw [Fin.val_last]) _ _ (chowGroupDegreeEquiv_heq _ _ _ _)).symm)))
  -- `c_c(𝒩) ∩ [Y]_e` restricts to `c_c(𝒩|_{Y ×_P P_n}) ∩ [Y ×_P P_n]_e` (Stacks 02U8)
  rw [GenuineChern.chernCap_chowGroupRestrict (fieldChowSituation k) (i ≫ sP) (π ≫ i ≫ sP) π rfl
      (dualSheaf (conormalModule i)) c _ (Iso.refl _),
    chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion (fieldChowSituation k)
      (i ≫ sP) _ π _ _]
  exact chernCap_fundamentalChowClass_heq _ c _ _ _ (Category.assoc _ _ _) _ _ hec

end SelfIntersection

end Stacks.Chow

end
