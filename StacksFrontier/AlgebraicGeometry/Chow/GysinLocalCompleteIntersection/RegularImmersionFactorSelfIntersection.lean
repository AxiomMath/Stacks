module

public import
  StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionSelfIntersection
public import
  StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.CodimensionGysinRegularImmersion
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinTransversal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassExteriorProduct
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso
public import StacksFrontier.AlgebraicGeometry.Conormal.SmoothRank
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapOnCyclesDescent
import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductCapCommutingEveryCap

/-!
# The excess intersection formula for a closed subscheme of a regularly embedded subscheme

Let `k` be a field, let `P` be a scheme smooth over `k` of pure dimension `n`, let `i : Y ⟶ P` be
a regular closed immersion with `Y` of pure dimension `e`, of codimension `c = n - e`, whose
normal sheaf `𝒩 = 𝒞_{Y/P}^∨` is finite locally free of rank `c`, and let `π : T ⟶ Y` be a closed
immersion with `T` of pure dimension `m`. Then

  `i^![T] = π_*(c_c(π^*𝒩) ∩ [T]_m)`   in   `CH_{m-c}(Y)`,

for `[T] ∈ CH^{n-m}(P)` the class of the closed subscheme `T` of `P`
(`Stacks.WeilCohomology.closedSubschemeClass`) and `i^!` the Gysin map of Stacks 0FF3
(`Stacks.Chow.regularImmersionGysin`). For `π = 𝟙` this is the self-intersection formula
`Stacks.Chow.regularImmersionGysin_closedSubschemeClass_self`. It is Stacks 0FBM for the
cartesian square with left arrow `𝟙 : T ⟶ T`, whose excess normal sheaf is `π^*𝒩`; the proof is
that of the self-intersection formula with the test scheme `T` in place of `Y`.

The file also compares the two Gysin maps of a regular immersion on classes graded by
codimension: for `Y` of pure dimension `e`, `codimensionGysin` is `regularImmersionGysin` read in
codimension (`Stacks.Chow.codimensionGysin_eq_chowGroupToCodimension_regularImmersionGysin`).

The application is the self-intersection of a smooth divisor `i : Y ⟶ X`, with `X`, `Y` of
dimensions `d + 1`, `d`: the inverse image of the diagonal of `X` along `i × i` is
`(i × i)^![Δ_X] = [Δ_Y] · pr₂^!(i^![Y]) = Δ_*(i^![Y])`
(`Stacks.Chow.codimensionGysin_prodHom_diagonalClass_of_divisor`). Here `Δ_Y` lies on the divisor
`1 × i : Y × Y ⟶ Y × X`, whose normal sheaf is `pr₂^*𝒩_{Y/X}` (Stacks 0473), so the excess
intersection formula applies with `T = Δ_Y`.

## Main results

* `Stacks.Chow.codimensionGysin_eq_chowGroupToCodimension_regularImmersionGysin`.
* `Stacks.Chow.regularImmersionGysin_closedSubschemeClass_of_factor`:
  `i^![T] = π_*(c_c(π^*𝒩) ∩ [T])`.
* `Stacks.Chow.dualConormalModuleIsoPullbackOfFlat`: the normal sheaf of a flat base change.
* `Stacks.Chow.codimensionGysin_prodHom_diagonalClass_of_divisor`: for a smooth divisor
  `i : Y ⟶ X`, `(i × i)^![Δ_X] = [Δ_Y] · pr₂^!(i^![Y])` in `CH^{d+1}(Y × Y)`.

## References

* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FFE](https://stacks.math.columbia.edu/tag/0FFE)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology (dimPart partBase closedSubschemeClass closedSubschemeClass_apply
  isEmpty_dimPart_of_ne properChowPushforward_fundamentalChowClass_eq_mk chowGroupToCodimension
  chowGroupToCodimension_apply_of_eq)

/-! ### The two Gysin maps on classes graded by codimension -/

section Codimension

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [Smooth sX] (i : Y ⟶ X) [IsClosedImmersion i] (hreg : IsRegularImmersion i) [Smooth (i ≫ sX)]

/-- **`codimensionGysin` is `regularImmersionGysin` read in codimension.** For a regular closed
immersion `i : Y ⟶ X` of schemes smooth over `k`, with `Y` of pure dimension `e`, the Gysin map
`i^! : CH^q(X) ⟶ CH^q(Y)` of classes graded by codimension (`Stacks.Chow.codimensionGysin`) is
`i^! : CH^q(X) ⟶ CH_{e-q}(Y)` (`Stacks.Chow.regularImmersionGysin`) followed by
`CH_{e-q}(Y) = CH^q(Y)`. Both are compared on the pieces `Y_{e,d}` of `Y`
(`Stacks.Chow.chowGroupRestrict_codimensionGysin_eq_regularImmersionPartGysin`). -/
theorem codimensionGysin_eq_chowGroupToCodimension_regularImmersionGysin {e : ℕ}
    (hY : RelativeDimension (i ≫ sX) e) (q : ℤ) (θ : codimensionChowGroup k sX q) :
    codimensionGysin (i ≫ sX) sX rfl q θ =
      chowGroupToCodimension (i ≫ sX) (e - q) q (regularImmersionGysin sX i hreg e q θ) := by
  funext d
  by_cases hd : d = e
  swap
  · have := isEmpty_dimPart_of_ne (i ≫ sX) hY hd
    exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty _ _ _) _ _
  subst hd
  rw [chowGroupToCodimension_apply_of_eq _ _ _ _ _ rfl, chowGroupDegreeEquiv_self]
  refine (chowGroupDimPartPieceEquiv (i ≫ sX) sX (f := i) d (d - q)).injective
    (funext fun e' ↦ ?_)
  obtain ⟨e'⟩ := e'
  rw [chowGroupDimPartPieceEquiv_apply, chowGroupDimPartPieceEquiv_apply,
    chowGroupRestrict_codimensionGysin_eq_regularImmersionPartGysin sX i hreg q θ d e',
    ← chowGroupRestrict_regularImmersionGysin sX i hreg d q θ e', chowGroupRestrict_comp,
    chowGroupRestrict_comp]
  exact DFunLike.congr_fun (chowGroupRestrict_congr (fieldChowSituation k) (i ≫ sX)
    (dimPartPieceBase (i ≫ sX) sX i d e') _ _ ((d : ℤ) - q) _
    (dimPartPieceToPullback_fst (i ≫ sX) sX i d e') _) _

/-- `Stacks.Chow.codimensionGysin_eq_chowGroupToCodimension_regularImmersionGysin` for a structure
morphism of `Y` equal to `i ≫ sX`, as a heterogeneous equality. -/
theorem codimensionGysin_heq_chowGroupToCodimension_regularImmersionGysin
    {sY : Y ⟶ (fieldChowSituation k).S} [Smooth sY] (hi : i ≫ sX = sY) {e : ℕ}
    (hY : RelativeDimension sY e) (q : ℤ) (θ : codimensionChowGroup k sX q) :
    codimensionGysin sY sX hi q θ ≍
      chowGroupToCodimension (i ≫ sX) (e - q) q (regularImmersionGysin sX i hreg e q θ) := by
  subst hi
  exact heq_of_eq
    (codimensionGysin_eq_chowGroupToCodimension_regularImmersionGysin sX i hreg hY q θ)

end Codimension

/-- **`CH_m(X) ⟶ CH^c(X)` is injective for `X` of pure dimension `e`, `m = e - c`**: the class is
recovered from its restriction to the part `X_e = X`. -/
theorem chowGroupToCodimension_injective_of_relativeDimension {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] {e : ℕ}
    (hX : RelativeDimension sX e) {m c : ℤ} (h : m = e - c) :
    Function.Injective (chowGroupToCodimension sX m c) := by
  intro a b hab
  have h1 := congrFun hab e
  rw [chowGroupToCodimension_apply_of_eq sX m c a e h,
    chowGroupToCodimension_apply_of_eq sX m c b e h] at h1
  have h2 := (chowGroupDegreeEquiv (fieldChowSituation k) (partBase sX e) h).injective h1
  have := Stacks.WeilCohomology.isIso_dimPart_self_ι sX hX
  rw [chowGroupRestrict_of_isIso] at h2
  exact (chowGroupEquivOfIso (fieldChowSituation k) _ _ _ _ m).injective h2

/-! ### The excess intersection formula at a closed subscheme of `Y` -/

section Factor

variable {k : Type u} [Field k] {P Y T : Scheme.{u}} (sP : P ⟶ (fieldChowSituation k).S)
  [Smooth sP] (i : Y ⟶ P) [IsClosedImmersion i] (hreg : IsRegularImmersion i) (π : T ⟶ Y)
  [IsClosedImmersion π]

/-- **The excess intersection formula `i^![T] = π_*(c_c(π^*𝒩) ∩ [T]_m)`.** Let `k` be a field,
let `P` be a scheme smooth over `k` of pure dimension `n`, let `i : Y ⟶ P` be a regular closed
immersion with `Y` of pure dimension `e`, of codimension `c = n - e`, whose normal sheaf
`𝒩 = 𝒞_{Y/P}^∨` is finite locally free of rank `c`, and let `π : T ⟶ Y` be a closed immersion
with `T` of pure dimension `m`, of codimension `q = n - m` in `P`. Then

  `i^![T] = π_*(c_c(π^*𝒩) ∩ [T]_m)`   in   `CH_{e-q}(Y) = CH_{m-c}(Y)`,

for `[T] ∈ CH^q(P)` the class of the closed subscheme `T` of `P`
(`Stacks.WeilCohomology.closedSubschemeClass`), `i^!` the Gysin map of Stacks 0FF3
(`Stacks.Chow.regularImmersionGysin`) and `c_c(π^*𝒩) ∩ -` the cap product with the `c`-th Chern
class (`Stacks.Chow.GenuineChern.chernCap`).

Both sides are compared on the pieces `Y ×_P P_d` of `Y`; only the piece over `P_n` is
nonempty. There `[T]` is the pushforward of `[T_n]`, `T_n = T ×_P P_n`, the cap product commutes
with that pushforward (Stacks 0B76 (1)), and at the test scheme `T_n ⟶ P`, which factors through
`i`, Stacks 0FBM gives `c_c(𝒩|_{T_n}) ∩ [T_n]`
(`Stacks.Chow.lciGysinBivariantClass_cap_fundamentalChowClass_of_factor`); on the other side
restriction to the piece commutes with `π_*` (Stacks 02RG) and with `c_c(π^*𝒩) ∩ -`
(Stacks 02U8). -/
theorem regularImmersionGysin_closedSubschemeClass_of_factor (e c n m q : ℕ) (hn : e + c = n)
    (hq : m + q = n) (hP : RelativeDimension sP n) (hT : RelativeDimension (π ≫ i ≫ sP) m)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualSheaf (conormalModule i)) c] :
    haveI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback π
      (dualSheaf (conormalModule i)) c
    regularImmersionGysin sP i hreg e q (closedSubschemeClass sP (π ≫ i) q) =
      chowGroupDegreeEquiv (fieldChowSituation k) (i ≫ sP) (by omega)
        (properChowPushforward (fieldChowSituation k) (π ≫ i ≫ sP) (i ≫ sP) π rfl
          ((m : ℤ) - c) (properPushforwardDescends _ _ _ _ _ _)
          (chowGroupDegreeEquiv (fieldChowSituation k) (π ≫ i ≫ sP) (by rw [Fin.val_last])
            (GenuineChern.chernCap (fieldChowSituation k) c (π ≫ i ≫ sP)
              ((Scheme.Modules.pullback π).obj (dualSheaf (conormalModule i))) m (Fin.last c)
              (fundamentalChowClass (fieldChowSituation k) (π ≫ i ≫ sP) m)))) := by
  have hlci := isLocalCompleteIntersectionMorphism_of_isRegularImmersion i hreg
  have hex := GysinMapExists.of_isImmersion i
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sP)
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (π ≫ i ≫ sP)
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback π (dualSheaf (conormalModule i)) c
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
      (pullback.fst i (dimPart sP d).ι ≫ i ≫ sP) ((e : ℤ) - q)
    exact Subsingleton.elim _ _
  subst hd
  set ιn := (dimPart sP (e + c)).ι
  set ρ := pullback.fst (π ≫ i) ιn
  set jn := pullback.snd (π ≫ i) ιn
  set πn := ρ ≫ π
  have hcond : πn ≫ i = jn ≫ ιn := by
    simp only [πn, Category.assoc]
    exact pullback.condition
  set κ : pullback (π ≫ i) ιn ⟶ pullback i ιn := pullback.lift πn jn hcond
  have : IsProper κ := by
    have : IsProper (κ ≫ pullback.snd i ιn) := by
      rw [pullback.lift_snd]; infer_instance
    exact IsProper.of_comp κ (pullback.snd i ιn)
  have hkq : ((e + c : ℕ) : ℤ) - q = m := by omega
  -- dimensions
  have hdimT0 : schemeDeltaDimension (fieldChowSituation k) (π ≫ i ≫ sP) ≤ ((m : ℤ) : EInt) :=
    WeilCohomology.schemeDeltaDimension_le_of_forall_irreducibleComponent _
      (WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k (π ≫ i ≫ sP) m hT)
  have hdimT' : schemeDeltaDimension (fieldChowSituation k) ((π ≫ i) ≫ sP) ≤
      ((((e + c : ℕ) : ℤ) - q : ℤ) : EInt) := by
    rw [hkq]
    simpa only [Category.assoc] using hdimT0
  have hdimρ : ∀ ξ, relativeDimension (fieldChowSituation k).dimensionFunction
      ((πn ≫ i) ≫ sP) ξ ≤ ((e + c : ℕ) : ℤ) - q := fun ξ ↦ by
    simp only [πn, Category.assoc]
    rw [relativeDimension_comp_isOpenImmersion, hkq]
    exact relativeDimension_le_of_schemeDeltaDimension_le' (fieldChowSituation k) _ hdimT0 _
  have hdimTn : schemeDeltaDimension (fieldChowSituation k) ((πn ≫ i) ≫ sP) ≤
      ((((e + c : ℕ) : ℤ) - q : ℤ) : EInt) := by
    simpa using schemeDeltaDimension_le_of_forall_relativeDimension_le _ _ (𝟙 _)
      (by simpa using hdimρ)
  have hρ : ρ ≫ (π ≫ i) ≫ sP = (πn ≫ i) ≫ sP := by simp only [πn, Category.assoc]
  have hjn : jn ≫ partBase sP (e + c) = (πn ≫ i) ≫ sP := by
    rw [← hρ]
    exact pullbackSnd_comp_structureMorphism_eq (fieldChowSituation k) ((π ≫ i) ≫ sP) sP (π ≫ i)
      rfl ιn
  -- `[T]` on `P_n` is the pushforward of `[T_n]` along `T_n ⟶ P_n`
  have hmk : (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sP
        (π ≫ i) (((e + c : ℕ) : ℤ) - q)) :
        chowGroup (fieldChowSituation k) sP (((e + c : ℕ) : ℤ) - q)) =
      properChowPushforward (fieldChowSituation k) ((π ≫ i) ≫ sP) sP (π ≫ i) rfl _
        (properPushforwardDescends _ _ _ _ _ _)
        (fundamentalChowClass (fieldChowSituation k) ((π ≫ i) ≫ sP) (((e + c : ℕ) : ℤ) - q)) :=
    (properChowPushforward_fundamentalChowClass_eq_mk sP (π ≫ i) _).symm
  have hTn : closedSubschemeClass sP (π ≫ i) q (e + c) =
      properChowPushforward (fieldChowSituation k) ((πn ≫ i) ≫ sP) (ιn ≫ sP) jn hjn
        (((e + c : ℕ) : ℤ) - q) (properPushforwardDescends _ _ _ _ _ _)
        (fundamentalChowClass (fieldChowSituation k) ((πn ≫ i) ≫ sP) (((e + c : ℕ) : ℤ) - q)) := by
    rw [closedSubschemeClass_apply, hmk,
      chowGroupRestrict_properChowPushforward (fieldChowSituation k) ((π ≫ i) ≫ sP) sP
        ((πn ≫ i) ≫ sP) (partBase sP (e + c)) (π ≫ i) rfl ρ hρ ιn rfl jn hjn
        (IsPullback.of_hasPullback (π ≫ i) ιn) _ (properPushforwardDescends _ _ _ _ _ _)
        (properPushforwardDescends _ _ _ _ _ _),
      chowGroupRestrict_fundamentalChowClass (fieldChowSituation k)
        ((π ≫ i) ≫ sP) _ ρ _ _ hdimT']
  -- the cap product commutes with that pushforward (Stacks 0B76 (1)), and at the test scheme
  -- `T_n ⟶ P`, which factors through `i`, it is `c_c(𝒩) ∩ -` (Stacks 0FBM)
  have sq : IsPullback (𝟙 _) πn (πn ≫ i) i := IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  have hfst : (sq.flip.isoPullback.inv ≫ κ) ≫ pullback.fst i ιn = pullback.fst i (πn ≫ i) := by
    refine (Category.assoc _ _ _).trans ?_
    rw [pullback.lift_fst]
    exact sq.flip.isoPullback_inv_fst
  have hsnd : (sq.flip.isoPullback.inv ≫ κ) ≫ pullback.snd i ιn =
      pullback.snd i (πn ≫ i) ≫ jn := by
    refine (Category.assoc _ _ _).trans ?_
    rw [pullback.lift_snd, ← sq.flip.isoPullback_inv_snd, Category.comp_id]
  have hκw : κ ≫ pullback.fst i ιn ≫ i ≫ sP = (πn ≫ i) ≫ sP := by
    rw [pullback.lift_fst_assoc]
    simp only [πn, Category.assoc]
  have hcap := BivariantClass.cap_properChowPushforward
    (lciGysinMapComponent (fieldChowSituation k) (i ≫ sP) sP rfl hlci hex
      (((e + c : ℕ) : ℤ) - e))
    (properPushforwardDescends (fieldChowSituation k)) ιn jn (πn ≫ i) hcond.symm
    (sq.flip.isoPullback.inv ≫ κ) hfst hsnd (((e + c : ℕ) : ℤ) - q)
    (fundamentalChowClass (fieldChowSituation k) ((πn ≫ i) ≫ sP) (((e + c : ℕ) : ℤ) - q))
  rw [regularImmersionPartGysin, AddMonoidHom.comp_apply, BivariantClass.capTargetHom_apply,
    regularImmersionPartGysinClass,
    bivariantRestriction_capTarget (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _), hTn,
    hcap, lciGysinBivariantClass_cap_fundamentalChowClass_of_factor (fieldChowSituation k) sP i
      hreg c hlci hex πn (πn ≫ i) sq _ hdimTn _ (by push_cast; ring),
    ← properChowPushforward_eq_chowPushforwardOfIso _ _ _ _ _ _
      (properPushforwardDescends _ _ _ _ _ _),
    ← properChowPushforward_comp_apply (fieldChowSituation k) _ _ _ sq.flip.isoPullback.hom
      (sq.flip.isoPullback.inv ≫ κ) κ (Iso.hom_inv_id_assoc _ _) _ _ hκw _ _ _
      (properPushforwardDescends _ _ _ _ _ _)]
  -- the other side: restriction to the piece commutes with `π_*` (Stacks 02RG) and with the cap
  -- product (Stacks 02U8)
  have hsqκ : IsPullback ρ κ π (pullback.fst i ιn) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback i ιn)
    rw [pullback.lift_snd]
    exact IsPullback.of_hasPullback (π ≫ i) ιn
  have hρ' : ρ ≫ π ≫ i ≫ sP = (πn ≫ i) ≫ sP := by simp only [πn, Category.assoc]
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback πn (dualSheaf (conormalModule i)) c
  rw [chowGroupRestrict_chowGroupDegreeEquiv,
    chowGroupRestrict_properChowPushforward (fieldChowSituation k) (π ≫ i ≫ sP) (i ≫ sP)
      ((πn ≫ i) ≫ sP) (pullback.fst i ιn ≫ i ≫ sP) π rfl ρ hρ' (pullback.fst i ιn) rfl κ hκw hsqκ
      _ (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _),
    chowGroupRestrict_chowGroupDegreeEquiv,
    GenuineChern.chernCap_chowGroupRestrict (fieldChowSituation k) (π ≫ i ≫ sP) ((πn ≫ i) ≫ sP) ρ
      hρ' ((Scheme.Modules.pullback π).obj (dualSheaf (conormalModule i))) c _
      ((Scheme.Modules.pullbackComp ρ π).app _).symm,
    chowGroupRestrict_fundamentalChowClass (fieldChowSituation k)
      (π ≫ i ≫ sP) _ ρ _ _ hdimT0]
  have key : ∀ m₁ m₂ d₁ d₂ : ℤ, m₁ = m₂ → d₁ = d₂ →
      ∀ (h₁ : m₁ - ((Fin.last c : ℕ) : ℤ) = d₁) (h₂ : m₂ - ((Fin.last c : ℕ) : ℤ) = d₂),
      properChowPushforward (fieldChowSituation k) ((πn ≫ i) ≫ sP) (pullback.fst i ιn ≫ i ≫ sP)
          κ hκw d₁ (properPushforwardDescends _ _ _ _ _ _)
          (chowGroupDegreeEquiv (fieldChowSituation k) ((πn ≫ i) ≫ sP) h₁
            (GenuineChern.chernCap (fieldChowSituation k) c ((πn ≫ i) ≫ sP)
              ((Scheme.Modules.pullback πn).obj (dualSheaf (conormalModule i))) m₁ (Fin.last c)
              (fundamentalChowClass (fieldChowSituation k) ((πn ≫ i) ≫ sP) m₁))) ≍
        properChowPushforward (fieldChowSituation k) ((πn ≫ i) ≫ sP) (pullback.fst i ιn ≫ i ≫ sP)
          κ hκw d₂ (properPushforwardDescends _ _ _ _ _ _)
          (chowGroupDegreeEquiv (fieldChowSituation k) ((πn ≫ i) ≫ sP) h₂
            (GenuineChern.chernCap (fieldChowSituation k) c ((πn ≫ i) ≫ sP)
              ((Scheme.Modules.pullback πn).obj (dualSheaf (conormalModule i))) m₂ (Fin.last c)
              (fundamentalChowClass (fieldChowSituation k) ((πn ≫ i) ≫ sP) m₂))) := by
    rintro m₁ _ d₁ _ rfl rfl _ _
    rfl
  refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans (HEq.trans ?_
    (chowGroupDegreeEquiv_heq _ _ _ _).symm))
  exact key _ _ _ _ hkq (by omega) _ _

end Factor

/-! ### The normal sheaf of a flat base change -/

section NormalSheafBaseChange

variable {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X') [IsImmersion i] [IsImmersion i']
  (f : Z ⟶ Z') (g : X ⟶ X') [Flat g] (sq : IsPullback i f g i')

/-- **The normal sheaf of a flat base change is the pulled back normal sheaf**,
`𝒞_{Z/X}^∨ ≅ f^*(𝒞_{Z'/X'}^∨)`, for a cartesian square of immersions `i = i' ×_{X'} X` along a
flat `g : X ⟶ X'` with `𝒞_{Z'/X'}` finite locally free: the conormal sheaf of the base change is
the pulled back conormal sheaf (Stacks 0473), and duality commutes with pullback of finite locally
free modules. -/
def dualConormalModuleIsoPullbackOfFlat
    (hi' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (conormalModule i')) :
    dualSheaf (conormalModule i) ≅
      (Scheme.Modules.pullback f).obj (dualSheaf (conormalModule i')) :=
  dualMapIso (@asIso _ _ _ _ (Stacks.Immersion.immersionConormalSheafMap i i' f g
      (Stacks.Immersion.toShHom_square sq.w))
      (Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat i i' f g sq)) ≪≫
    (@asIso _ _ _ _ (pullbackDualMap f (conormalModule i'))
      (pullbackDualMap_isIso f (conormalModule i') hi')).symm ≪≫
    ((Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjointUniq
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
        f.toLRSHom.toShHom)).symm.app _

end NormalSheafBaseChange

/-! ### The inverse image of the diagonal along `i × i` for a divisor `i` -/

section DivisorProduct

open Stacks.WeilCohomology (prodBase prodHom prodHom_comp_prodBase graphToProd
  codimensionGysin_prodHom_id_diagonal codimensionIntersectionProduct_closedSubschemeClass
  chowGroupToCodimension_congr relativeDimension_prodBase relativeDimension_congr)

variable {k : Type u} [Field k] {Y X : Scheme.{u}} (sY : Y ⟶ (fieldChowSituation k).S)
  (sX : X ⟶ (fieldChowSituation k).S) [Smooth sY] [Smooth sX] [IsSeparated sY] [IsSeparated sX]
  (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sY)

/-- **`(i × i)^![Δ_X] = [Δ_Y] · pr₂^!(i^![Y])` for a smooth divisor `i : Y ⟶ X`.** Let `X` and `Y`
be smooth over `k`, separated, of constant dimensions `d + 1` and `d`, and let `i : Y ⟶ X` be a
closed immersion over `k`. Then in `CH^{d+1}(Y × Y)`

  `(i × i)^![Δ_X] = [Δ_Y] · pr₂^!(i^![Y])`,

for the Gysin maps of Stacks 0FF3 graded by codimension (`Stacks.Chow.codimensionGysin`), `[Δ]`
and `[Y]` the classes of the closed subschemes, and `·` the intersection product of Section 0FC0;
the right side is `Δ_*(i^![Y])` (Stacks 0FFE).

Write `i × i = (i × 1) ∘ (1 × i)`. The graph of `i` is the inverse image of `Δ_X` along `i × 1`,
transversally (`Stacks.WeilCohomology.codimensionGysin_prodHom_id_diagonal`). The graph is the
image of `Δ_Y` under the divisor `1 × i : Y × Y ⟶ Y × X`, so by the excess intersection formula
(`Stacks.Chow.regularImmersionGysin_closedSubschemeClass_of_factor`)
`(1 × i)^![Γ_i] = Δ_*(c₁(Δ^*𝒩_{1×i}) ∩ [Y])`, and `𝒩_{1×i} = pr₂^*𝒩_{Y/X}` (Stacks 0473), so
`Δ^*𝒩_{1×i} = 𝒩_{Y/X}`; and `c₁(𝒩_{Y/X}) ∩ [Y] = i^![Y]` is the self-intersection formula
(`Stacks.Chow.regularImmersionGysin_closedSubschemeClass_self`). On the other side
`[Δ_Y] · pr₂^!ν = Δ_*(Δ^!pr₂^!ν) = Δ_*ν` by Stacks 0FFE
(`Stacks.WeilCohomology.codimensionIntersectionProduct_closedSubschemeClass`) and functoriality
of the Gysin map. -/
theorem codimensionGysin_prodHom_diagonalClass_of_divisor {d : ℕ} (hY : RelativeDimension sY d)
    (hX : RelativeDimension sX (d + 1)) :
    codimensionGysin (prodBase sY sY) (prodBase sX sX)
        (prodHom_comp_prodBase sX sX sY sY i i hi hi) ((d + 1 : ℕ) : ℤ)
        (closedSubschemeClass (prodBase sX sX) (pullback.diagonal sX) ((d + 1 : ℕ) : ℤ)) =
      codimensionIntersectionProduct k (prodBase sY sY) d 1
        (closedSubschemeClass (prodBase sY sY) (pullback.diagonal sY) d)
        (codimensionGysin (prodBase sY sY) sY (f := pullback.snd sY sY) pullback.condition.symm 1
          (codimensionGysin sY sX hi 1 (closedSubschemeClass sX i 1))) := by
  have : Smooth (i ≫ sX) := by rw [hi]; infer_instance
  have hY' : RelativeDimension (i ≫ sX) d := relativeDimension_congr hi.symm hY
  have : IsClosedImmersion (pullback.diagonal sY) := IsSeparated.isClosedImmersion_diagonal
  -- the morphisms `1 × i`, `i × 1`, `Δ_Y`
  have hj : prodHom sY sX sY sY (𝟙 Y) i (Category.id_comp _) hi ≫ prodBase sY sX =
      prodBase sY sY := prodHom_comp_prodBase _ _ _ _ _ _ _ _
  have hψ : prodHom sX sX sY sX i (𝟙 X) hi (Category.id_comp _) ≫ prodBase sX sX =
      prodBase sY sX := prodHom_comp_prodBase _ _ _ _ _ _ _ _
  have hjψ : prodHom sY sX sY sY (𝟙 Y) i (Category.id_comp _) hi ≫
      prodHom sX sX sY sX i (𝟙 X) hi (Category.id_comp _) = prodHom sX sX sY sY i i hi hi := by
    ext <;> simp
  have hΔj : pullback.diagonal sY ≫ prodHom sY sX sY sY (𝟙 Y) i (Category.id_comp _) hi =
      graphToProd sY sX i hi := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.comp_id, pullback.diagonal_fst]
    · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd_assoc]
  have hΔ : pullback.diagonal sY ≫ prodBase sY sY = sY := pullback.diagonal_fst_assoc _ _
  have hΔsnd : pullback.diagonal sY ≫ pullback.snd sY sY = 𝟙 Y := pullback.diagonal_snd _
  -- `1 × i` is the base change of `i` along `pr₂ : Y × X ⟶ X`
  have sqj : IsPullback (prodHom sY sX sY sY (𝟙 Y) i (Category.id_comp _) hi)
      (pullback.snd sY sY) (pullback.snd sY sX) i := by
    refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback sY sX)
    have h1 : prodHom sY sX sY sY (𝟙 Y) i (Category.id_comp _) hi ≫ pullback.fst sY sX =
        pullback.fst sY sY := by simp
    rw [h1, hi]
    exact IsPullback.of_hasPullback sY sY
  have : IsClosedImmersion (prodHom sY sX sY sY (𝟙 Y) i (Category.id_comp _) hi) :=
    MorphismProperty.of_isPullback sqj.flip ‹IsClosedImmersion i›
  -- regularity and dimensions
  have : Smooth (prodHom sY sX sY sY (𝟙 Y) i (Category.id_comp _) hi ≫ prodBase sY sX) := by
    rw [hj]; infer_instance
  have : Smooth (pullback.diagonal sY ≫ prodBase sY sY) := by rw [hΔ]; infer_instance
  have hregi := Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth i sX
  have hregj := Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth
    (prodHom sY sX sY sY (𝟙 Y) i (Category.id_comp _) hi) (prodBase sY sX)
  have hregΔ := Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth
    (pullback.diagonal sY) (prodBase sY sY)
  have hYY : RelativeDimension (prodBase sY sY) (d + d) := relativeDimension_prodBase k sY sY hY hY
  have hYX : RelativeDimension (prodBase sY sX) (d + 1 + d) :=
    relativeDimension_prodBase k sY sX hY hX
  have hΔdim : RelativeDimension (pullback.diagonal sY ≫
      prodHom sY sX sY sY (𝟙 Y) i (Category.id_comp _) hi ≫ prodBase sY sX) d :=
    relativeDimension_congr (by rw [hj, hΔ]) hY
  have hΔdim' : RelativeDimension (pullback.diagonal sY ≫ prodBase sY sY) d :=
    relativeDimension_congr hΔ.symm hY
  -- the normal sheaves: `𝒩_{Y/X}` has rank one, and `𝒩_{1×i} = pr₂^*𝒩_{Y/X}`
  have hCi := Stacks.Conormal.isFiniteLocallyFreeOfRank_conormalSheaf_of_relativeDimension i sX
    (d + 1) d hX hY'
  rw [show d + 1 - d = 1 by omega] at hCi
  have hNi : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (dualSheaf (conormalModule i)) 1 :=
    isFiniteLocallyFreeOfRank_dualSheaf _ 1 hCi
  have eN := dualConormalModuleIsoPullbackOfFlat
    (prodHom sY sX sY sY (𝟙 Y) i (Category.id_comp _) hi) i (pullback.snd sY sY)
    (pullback.snd sY sX) sqj (isFiniteLocallyFree_conormalModule i hregi)
  have hNj : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (dualSheaf (conormalModule (prodHom sY sX sY sY (𝟙 Y) i (Category.id_comp _) hi))) 1 :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso eN.symm
      (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ 1)
  have eΔ : (Scheme.Modules.pullback (pullback.diagonal sY)).obj
      (dualSheaf (conormalModule (prodHom sY sX sY sY (𝟙 Y) i (Category.id_comp _) hi))) ≅
        dualSheaf (conormalModule i) :=
    (Scheme.Modules.pullback (pullback.diagonal sY)).mapIso eN ≪≫
      (Scheme.Modules.pullbackComp (pullback.diagonal sY) (pullback.snd sY sY)).app _ ≪≫
      eqToIso (congrArg (fun φ : Y ⟶ Y ↦ (Scheme.Modules.pullback φ).obj
        (dualSheaf (conormalModule i))) hΔsnd) ≪≫
      (Scheme.Modules.pullbackId Y).app (dualSheaf (conormalModule i))
  -- `(i × i)^! = (1 × i)^! (i × 1)^!`, and `(i × 1)^![Δ_X] = [Γ_i] = [Δ_Y ≫ (1 × i)]`
  have hcls : ∀ (g g' : Y ⟶ pullback sY sX) [IsClosedImmersion g] [IsClosedImmersion g'],
      g = g' → closedSubschemeClass (prodBase sY sX) g ((d + 1 : ℕ) : ℤ) =
        closedSubschemeClass (prodBase sY sX) g' ((d + 1 : ℕ) : ℤ) := by
    rintro g _ _ _ rfl
    rfl
  rw [codimensionGysin_congr (prodBase sY sY) (prodBase sX sX) hjψ.symm _
      (by rw [Category.assoc, hψ, hj]),
    codimensionGysin_comp (prodBase sY sY) (prodBase sY sX) hj (prodBase sX sX) hψ,
    codimensionGysin_prodHom_id_diagonal sY sX i hi hY hX, ← hcls _ _ hΔj]
  -- `ν = i^![Y]` and `Δ^!pr₂^!ν = ν`, both read through `regularImmersionGysin`
  have hA := codimensionGysin_heq_chowGroupToCodimension_regularImmersionGysin sX i hregi hi hY 1
    (closedSubschemeClass sX i 1)
  have hB := codimensionGysin_heq_chowGroupToCodimension_regularImmersionGysin (prodBase sY sY)
    (pullback.diagonal sY) hregΔ hΔ hY 1
    (codimensionGysin (prodBase sY sY) sY (f := pullback.snd sY sY) pullback.condition.symm 1
      (codimensionGysin sY sX hi 1 (closedSubschemeClass sX i 1)))
  have hC : codimensionGysin sY (prodBase sY sY) hΔ 1
      (codimensionGysin (prodBase sY sY) sY (f := pullback.snd sY sY) pullback.condition.symm 1
        (codimensionGysin sY sX hi 1 (closedSubschemeClass sX i 1))) =
      codimensionGysin sY sX hi 1 (closedSubschemeClass sX i 1) := by
    rw [← codimensionGysin_comp sY (prodBase sY sY) hΔ sY pullback.condition.symm,
      codimensionGysin_congr sY sY hΔsnd _ (Category.id_comp _), codimensionGysin_id]
  have injHEq : ∀ (s s' : Y ⟶ (fieldChowSituation k).S) [Smooth s] [Smooth s'], s = s' →
      RelativeDimension s d → ∀ (a : chowGroup (fieldChowSituation k) s ((d : ℤ) - 1))
      (b : chowGroup (fieldChowSituation k) s' ((d : ℤ) - 1)),
      chowGroupToCodimension s ((d : ℤ) - 1) 1 a ≍ chowGroupToCodimension s' ((d : ℤ) - 1) 1 b →
        a ≍ b := by
    rintro s _ _ _ rfl hs a b h
    exact heq_of_eq (chowGroupToCodimension_injective_of_relativeDimension s hs (by ring)
      (eq_of_heq h))
  have hinj := injHEq (i ≫ sX) (pullback.diagonal sY ≫ prodBase sY sY) (by rw [hi, hΔ]) hY' _ _
    (hA.symm.trans ((heq_of_eq hC.symm).trans hB))
  have hself := regularImmersionGysin_closedSubschemeClass_self sX i hregi d 1 (d + 1) rfl hX hY'
  -- congruences in the structure morphisms
  have ccongr : ∀ (s s' : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType s]
      [LocallyOfFiniteType s'], s = s' →
      GenuineChern.chernCap (fieldChowSituation k) 1 s (dualSheaf (conormalModule i)) d
          (Fin.last 1) (fundamentalChowClass (fieldChowSituation k) s d) ≍
        GenuineChern.chernCap (fieldChowSituation k) 1 s' (dualSheaf (conormalModule i)) d
          (Fin.last 1) (fundamentalChowClass (fieldChowSituation k) s' d) := by
    rintro s _ _ _ rfl
    rfl
  have pcongr : ∀ (s s' : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType s]
      [LocallyOfFiniteType s'] (t t' : pullback sY sY ⟶ (fieldChowSituation k).S)
      [LocallyOfFiniteType t] [LocallyOfFiniteType t'] (h : pullback.diagonal sY ≫ t = s)
      (h' : pullback.diagonal sY ≫ t' = s'), s = s' → t = t' → ∀ (m m' : ℤ), m = m' →
      ∀ (hf : ProperPushforwardFactorsThroughRationalEquivalence (fieldChowSituation k) s t
        (pullback.diagonal sY) h m)
      (hf' : ProperPushforwardFactorsThroughRationalEquivalence (fieldChowSituation k) s' t'
        (pullback.diagonal sY) h' m')
      (x : chowGroup (fieldChowSituation k) s m) (x' : chowGroup (fieldChowSituation k) s' m'),
      x ≍ x' → properChowPushforward (fieldChowSituation k) s t (pullback.diagonal sY) h m hf x ≍
        properChowPushforward (fieldChowSituation k) s' t' (pullback.diagonal sY) h' m' hf' x' := by
    rintro s _ _ _ t _ _ _ h h' rfl rfl m _ rfl hf hf' x x' hx
    cases hx
    rfl
  -- assembly
  refine eq_of_heq ((codimensionGysin_heq_chowGroupToCodimension_regularImmersionGysin
    (prodBase sY sX) (prodHom sY sX sY sY (𝟙 Y) i (Category.id_comp _) hi) hregj hj hYY _ _).trans
    ?_)
  rw [regularImmersionGysin_closedSubschemeClass_of_factor (prodBase sY sX)
      (prodHom sY sX sY sY (𝟙 Y) i (Category.id_comp _) hi) hregj (pullback.diagonal sY) (d + d) 1
      (d + 1 + d) d (d + 1) (by omega) (by omega) hYX hΔdim,
    codimensionIntersectionProduct_closedSubschemeClass (prodBase sY sY) (pullback.diagonal sY)
      hregΔ d hΔdim' (d : ℤ) 1]
  refine chowGroupToCodimension_congr _ hj (by push_cast; ring) _ ?_
  refine (chowGroupDegreeEquiv_heq _ _ _ _).trans (pcongr _ _ _ _ _ _ (by rw [hj]) hj _ _
    (by push_cast; ring) _ _ _ _ ?_)
  refine (chowGroupDegreeEquiv_heq _ _ _ _).trans ?_
  rw [GenuineChern.chernCap_congr _ _ 1 eΔ]
  refine (ccongr _ (i ≫ sX) (by rw [hj, hΔ, hi])).trans ?_
  refine HEq.trans ?_ hinj
  exact (chowGroupDegreeEquiv_heq _ _ _ _).symm.trans (heq_of_eq hself.symm)

end DivisorProduct

end Stacks.Chow

end
