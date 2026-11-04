module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalCapRegularFormula
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.FundamentalClass
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.CodimConormalRank
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.CodimLocal

/-!
# The formula at vanishing excess for the Gysin class of the diagonal

Let `g : Y ⟶ Z` be smooth of constant relative dimension `d`, with `Y` locally of
finite type over the base `(S, δ)`, and write `P = Y ×_Z Y`. The Gysin class
`Δ^! ∈ A^d(Y ⟶ P)` of the diagonal (Stacks 0FBR, `Stacks.Chow.diagonalGysinClass`) is the
composite `c(Y ⟶ U, 𝒩) ∘ ι^*` of flat pullback along the inclusion `ι : U ⟶ P` of the open
subscheme in which the diagonal is closed with the class of Stacks 0FBK of the closed factor
`Δ' : Y ⟶ U` (Stacks 0FEZ).

This file shows that `Δ^!` satisfies the formula `c ∩ [V]_n = [Y ×_P V]_{n - d}` over regular
base changes (`Stacks.Chow.BivariantClass.CapRegularFormula`, which for the class of Stacks 0FBK
is the excess intersection formula of Stacks 0FBM at vanishing excess) as soon as the closed
factor `c(Y ⟶ U, 𝒩)` does. This is the form in which the formula for the canonical diagonal class
enters Stacks 0FFD.

## Main results

* `Stacks.Chow.BivariantClass.capRegularFormula_of_isVirtualNormalGysinClass` and
  `Stacks.Chow.virtualNormalGysinClass_capRegularFormula`: a class satisfying the relation of
  Stacks 0FBK, in particular `c(Z ⟶ X, 𝒩)`, satisfies the formula over regular base changes —
  Stacks 0FBM at vanishing excess, with the rank of the conormal sheaf of a regular closed
  immersion of codimension `r`.
* `Stacks.Chow.diagonalGysinClass_capCohenMacaulayFormula_of_closedFactor` — for `g` separated or
  not, if `c(Y ⟶ U, 𝒩)` satisfies the formula in degree `n`, then `Δ^!` satisfies the conclusion
  of Stacks 0FEA in degree `n` (`Stacks.Chow.BivariantClass.CapCohenMacaulayFormula`).
* `Stacks.Chow.diagonalGysinClass_capCohenMacaulayFormula` — **`Δ^!` satisfies the conclusion of
  Stacks 0FEA in every degree**, which is what Stacks 0FFD uses.
* `Stacks.Chow.diagonalGysinClass_capRegularFormula_of_closedFactor` and
  `Stacks.Chow.diagonalGysinClass_capRegularFormula` — for `g` separated, `Δ^!` satisfies the
  formula over regular base changes.

## Implementation notes

For a test morphism `V ⟶ P` put `V' = U ×_P V`, open in `V`. Then `ι^* ∩ [V]_n = [V']_n`
(restriction of a fundamental class to an open subscheme), and `Y ×_U V' ≅ Y ×_P V`, the
identification `Stacks.Chow.diagonalGysinClass_cap_heq` reads the cap operation of `Δ^!`
through. The hypotheses of the formula pass from `V` to `V'`: purity of dimension because `V'` is
open in `V`, the dimension bound because `Y ×_U V' ⟶ Y ×_P V` is an open immersion, and
regularity of `Y ×_U V' ⟶ V'` because it is the base change of `Y ×_P V ⟶ V` along the open
immersion `V' ⟶ V`
(`Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularClosedImmersionOfCodim.of_isPullback`).

## References

* [Stacks Project, Tag 0FBR](https://stacks.math.columbia.edu/tag/0FBR)
* [Stacks Project, Tag 0FEZ](https://stacks.math.columbia.edu/tag/0FEZ)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FFD](https://stacks.math.columbia.edu/tag/0FFD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

/-- A scheme whose irreducible components all have `δ`-dimension `n` has `δ`-dimension `≤ n`. -/
private theorem schemeDeltaDimension_le_of_forall_deltaDimension_eq (C : ChowSituation.{u})
    {V : Scheme.{u}} (f : V ⟶ C.S) [LocallyOfFiniteType f] {n : ℤ}
    (hV : ∀ T : irreducibleComponents V,
      deltaDimension C f ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents (T : Set V) T.2⟩ = n) :
    schemeDeltaDimension C f ≤ (n : EInt) := by
  have hle := relativeDimension_le_of_forall_genericPoint C f fun W => hV W
  simpa using schemeDeltaDimension_le_of_forall_relativeDimension_le C f (𝟙 V)
    (by simpa using hle)

/-! ### Stacks 0FBM at vanishing excess, as the formula over regular base changes -/

section VanishingExcess

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X)
  [IsClosedImmersion i] (hi : i ≫ sX = sZ) (𝒩 : VirtualNormalBundle i) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

/-- **A class satisfying the relation of Stacks 0FBK satisfies the formula over regular base
changes.** Let `c ∈ A^r(Z ⟶ X)` satisfy `p^* ∘ c = ι_* ∘ j^* ∘ C` for a virtual normal sheaf `𝒩` of
constant rank `r` (`Stacks.Chow.IsVirtualNormalBundleClass`), for instance `c(Z ⟶ X, 𝒩)`. Then `c`
satisfies `Stacks.Chow.BivariantClass.CapRegularFormula` in every degree: when `Z ×_X V ⟶ V` is a
regular closed immersion of codimension `r`, its conormal sheaf has rank `r`
(`IsRegularClosedImmersionOfCodim.isFiniteLocallyFreeOfRank_conormalModule`), and Stacks 0FBM at
vanishing excess (`Stacks.Chow.virtualNormalBundleClass_cap_fundamentalChowClass`) gives
`c ∩ [V]_n = [Z ×_X V]_{n - r}`. -/
theorem BivariantClass.capRegularFormula_of_isVirtualNormalGysinClass
    {c : BivariantClass C G sZ sX i hi (r : ℤ)}
    (hc : IsVirtualNormalBundleClass C sZ sX i hi G 𝒩 r c) (n : ℤ) :
    c.CapRegularFormula C G sZ sX i hi r n := by
  intro V gV _ hV _ hreg
  have := hreg.isFiniteLocallyFreeOfRank_conormalModule
  exact virtualNormalBundleClass_cap_fundamentalChowClass C sZ sX i hi 𝒩 r hc gV (pullback.snd i gV)
    (pullback.fst i gV) (IsPullback.of_hasPullback i gV).flip _ rfl hreg.isRegularImmersion n
    (schemeDeltaDimension_le_of_forall_deltaDimension_eq C (gV ≫ sX) hV)

/-- **The class `c(Z ⟶ X, 𝒩)` of Stacks 0FBK satisfies the formula over regular base changes**
in every degree, for a virtual normal sheaf of constant rank `r`. -/
theorem virtualNormalGysinClass_capRegularFormula (n : ℤ) :
    (virtualNormalBundleClass C sZ sX i hi 𝒩 r).CapRegularFormula C (gysinSystemOfInvertible C)
      sZ sX i hi r n :=
  BivariantClass.capRegularFormula_of_isVirtualNormalGysinClass C _ sZ sX i hi 𝒩 r
    (isVirtualNormalBundleClass_virtualNormalBundleClass C sZ sX i hi 𝒩 r) n

end VanishingExcess

/-- A cartesian square stays cartesian when its arrows are replaced by equal ones. -/
private theorem isPullback_congr {𝒞 : Type*} [Category 𝒞] {P X Y W : 𝒞} {fst fst' : P ⟶ X}
    {snd : P ⟶ Y} {f f' : X ⟶ W} {b b' : Y ⟶ W} (h : IsPullback fst snd f b) (e₁ : fst = fst')
    (e₂ : f = f') (e₃ : b = b') : IsPullback fst' snd f' b' := by
  subst e₁ e₂ e₃
  exact h

/-- The comparison `Y ×_U V' ⟶ Y ×_P V` is an open immersion, a base change of `V' ⟶ V`. -/
private theorem exists_isOpenImmersion_pullback_diagonal_coborder {Y Z : Scheme.{u}}
    (g : Y ⟶ Z) {V : Scheme.{u}}
    (gV : V ⟶ pullback g g) :
    ∃ a : pullback (pullback.diagonal g).liftCoborder
        (pullback.fst (pullback.diagonal g).coborderRange.ι gV) ⟶ pullback (pullback.diagonal g) gV,
      a ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      a ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ pullback.snd (pullback.diagonal g).coborderRange.ι gV ∧
      IsPullback a (pullback.snd _ _) (pullback.snd (pullback.diagonal g) gV)
        (pullback.snd (pullback.diagonal g).coborderRange.ι gV) ∧ IsOpenImmersion a := by
  have hΔ : (pullback.diagonal g).liftCoborder ≫ (pullback.diagonal g).coborderRange.ι =
      pullback.diagonal g := (pullback.diagonal g).liftCoborder_ι
  have hcond : pullback.fst (pullback.diagonal g).coborderRange.ι gV ≫
      (pullback.diagonal g).coborderRange.ι =
        pullback.snd (pullback.diagonal g).coborderRange.ι gV ≫ gV := pullback.condition
  let a : pullback (pullback.diagonal g).liftCoborder
        (pullback.fst (pullback.diagonal g).coborderRange.ι gV) ⟶
      pullback (pullback.diagonal g) gV :=
    pullback.lift (pullback.fst _ _)
      (pullback.snd _ _ ≫ pullback.snd (pullback.diagonal g).coborderRange.ι gV)
      (calc pullback.fst _ _ ≫ pullback.diagonal g
            = pullback.fst _ _ ≫ (pullback.diagonal g).liftCoborder ≫
                (pullback.diagonal g).coborderRange.ι := by rw [hΔ]
          _ = pullback.snd _ _ ≫ pullback.fst (pullback.diagonal g).coborderRange.ι gV ≫
                (pullback.diagonal g).coborderRange.ι := pullback.condition_assoc _
          _ = (pullback.snd _ _ ≫ pullback.snd (pullback.diagonal g).coborderRange.ι gV) ≫
                gV := by rw [hcond, Category.assoc])
  have ha : a ≫ pullback.snd (pullback.diagonal g) gV =
      pullback.snd _ _ ≫ pullback.snd (pullback.diagonal g).coborderRange.ι gV :=
    pullback.lift_snd _ _ _
  have hout : IsPullback (pullback.fst (pullback.diagonal g).liftCoborder
        (pullback.fst (pullback.diagonal g).coborderRange.ι gV))
      (pullback.snd (pullback.diagonal g).liftCoborder
        (pullback.fst (pullback.diagonal g).coborderRange.ι gV))
      (pullback.diagonal g) (pullback.snd (pullback.diagonal g).coborderRange.ι gV ≫ gV) := by
    have hD : IsPullback (𝟙 Y) (pullback.diagonal g).liftCoborder
        ((pullback.diagonal g).liftCoborder ≫ (pullback.diagonal g).coborderRange.ι)
        (pullback.diagonal g).coborderRange.ι :=
      IsPullback.of_horiz_isIso_mono ⟨by simp⟩
    exact isPullback_congr ((IsPullback.of_hasPullback _ _).paste_horiz hD) (by simp) hΔ hcond
  have sq : IsPullback a (pullback.snd _ _) (pullback.snd (pullback.diagonal g) gV)
      (pullback.snd (pullback.diagonal g).coborderRange.ι gV) :=
    IsPullback.of_right (isPullback_congr hout (pullback.lift_fst _ _ _).symm rfl rfl) ha
      (IsPullback.of_hasPullback (pullback.diagonal g) gV)
  exact ⟨a, pullback.lift_fst _ _ _, ha, sq, MorphismProperty.of_isPullback sq.flip inferInstance⟩

/-- The two routes `V' ⟶ V ⟶ S` and `V' ⟶ U ⟶ S` from `V' = U ×_P V` agree. -/
private theorem snd_coborder_comp_eq (C : ChowSituation.{u}) {Y Z : Scheme.{u}}
    (sY : Y ⟶ C.S) (g : Y ⟶ Z) {V : Scheme.{u}} (gV : V ⟶ pullback g g) :
    pullback.snd (pullback.diagonal g).coborderRange.ι gV ≫ (gV ≫ (pullback.fst g g ≫ sY)) =
      pullback.fst (pullback.diagonal g).coborderRange.ι gV ≫
        ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY)) := by
  rw [← Category.assoc, ← pullback.condition, Category.assoc]

variable (C : ChowSituation.{u}) {Y Z : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (g : Y ⟶ Z) [Smooth g] {d : ℕ} (hd : RelativeDimension g d)


/-- Purity of dimension passes from `V` to the open `V' = U ×_P V`. -/
private theorem forall_deltaDimension_pullback_coborder_eq {V : Scheme.{u}}
    (gV : V ⟶ pullback g g) [LocallyOfFiniteType gV] {n : ℤ}
    (hV : ∀ T : irreducibleComponents V, deltaDimension C (gV ≫ (pullback.fst g g ≫ sY))
      ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents (T : Set V) T.2⟩ = n) :
    ∀ T : irreducibleComponents
        (pullback (pullback.diagonal g).coborderRange.ι gV : Scheme.{u}),
      deltaDimension C (pullback.fst (pullback.diagonal g).coborderRange.ι gV ≫
          ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY)))
        ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents
          (T : Set (pullback (pullback.diagonal g).coborderRange.ι gV : Scheme.{u})) T.2⟩ =
        n := fun T => by
  have h := deltaDimension_irreducibleComponents_of_isOpenImmersion C
    (gV ≫ (pullback.fst g g ≫ sY)) hV (pullback.snd (pullback.diagonal g).coborderRange.ι gV) T
  simpa only [snd_coborder_comp_eq C sY g gV] using h

/-- The dimension bound passes from `Y ×_P V` to the open `Y ×_U V'`. -/
private theorem schemeDeltaDimension_pullback_liftCoborder_le {V : Scheme.{u}}
    (gV : V ⟶ pullback g g) [LocallyOfFiniteType gV] {n : ℤ}
    (hZV : schemeDeltaDimension C (pullback.fst (pullback.diagonal g) gV ≫
      (pullback.diagonal g ≫ (pullback.fst g g ≫ sY))) ≤ ((n - d : ℤ) : EInt)) :
    schemeDeltaDimension C (pullback.fst (pullback.diagonal g).liftCoborder
        (pullback.fst (pullback.diagonal g).coborderRange.ι gV) ≫
      ((pullback.diagonal g).liftCoborder ≫
        ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY)))) ≤
      ((n - d : ℤ) : EInt) := by
  obtain ⟨a, hafst, -, -, _⟩ := exists_isOpenImmersion_pullback_diagonal_coborder g gV
  have hbase : a ≫ (pullback.fst (pullback.diagonal g) gV ≫
        (pullback.diagonal g ≫ (pullback.fst g g ≫ sY))) =
      pullback.fst (pullback.diagonal g).liftCoborder
          (pullback.fst (pullback.diagonal g).coborderRange.ι gV) ≫
        ((pullback.diagonal g).liftCoborder ≫
          ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY))) := by
    rw [reassoc_of% hafst, Scheme.Hom.liftCoborder_ι_assoc]
  have hpt : ∀ w, relativeDimension C.dimensionFunction
      (pullback.fst (pullback.diagonal g).liftCoborder
          (pullback.fst (pullback.diagonal g).coborderRange.ι gV) ≫
        ((pullback.diagonal g).liftCoborder ≫
          ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY)))) w ≤ n - d :=
    fun w => by
      rw [← hbase, relativeDimension_comp_isOpenImmersion]
      exact relativeDimension_le_of_schemeDeltaDimension_le' C _ hZV _
  simpa using schemeDeltaDimension_le_of_forall_relativeDimension_le C _ (𝟙 _)
    (by simpa using hpt)

/-- The cap product of `Δ^!` follows from the formula for the closed factor over `V' = U ×_P V`. -/
private theorem diagonalGysinClass_cap_eq_of_closedFactor_cap_eq {V : Scheme.{u}}
    (gV : V ⟶ pullback g g) [LocallyOfFiniteType gV] {n : ℤ}
    (hdimV : schemeDeltaDimension C (gV ≫ (pullback.fst g g ≫ sY)) ≤ (n : EInt))
    (hform : (diagonalClosedFactorClass C sY g hd).cap
        (pullback.fst (pullback.diagonal g).coborderRange.ι gV) n
        (fundamentalChowClass C (pullback.fst (pullback.diagonal g).coborderRange.ι gV ≫
          ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY))) n) =
      fundamentalChowClass C (pullback.fst (pullback.diagonal g).liftCoborder
          (pullback.fst (pullback.diagonal g).coborderRange.ι gV) ≫
        ((pullback.diagonal g).liftCoborder ≫
          ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY)))) (n - d)) :
    (diagonalGysinClass C sY g hd).cap gV n
        (fundamentalChowClass C (gV ≫ (pullback.fst g g ≫ sY)) n) =
      fundamentalChowClass C (pullback.fst (pullback.diagonal g) gV ≫
        (pullback.diagonal g ≫ (pullback.fst g g ≫ sY))) (n - d) := by
  have h1 : (diagonalOpenPullbackClass C sY g).cap gV n
        (fundamentalChowClass C (gV ≫ (pullback.fst g g ≫ sY)) n) ≍
      fundamentalChowClass C (pullback.fst (pullback.diagonal g).coborderRange.ι gV ≫
        ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY))) n := by
    refine (flatPullbackBivariantCap_heq_chowGroupRestrict C _ _ _ rfl gV n _).trans ?_
    rw [chowGroupRestrict_fundamentalChowClass C _ _ _ _ n hdimV]
  -- transport of the cap and of the pushforward along the degree identifications
  have hcap : ∀ (k : ℤ) (hk : n = k)
      (β : chowGroup C (pullback.fst (pullback.diagonal g).coborderRange.ι gV ≫
        ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY))) k),
      β ≍ fundamentalChowClass C (pullback.fst (pullback.diagonal g).coborderRange.ι gV ≫
        ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY))) n →
      (diagonalClosedFactorClass C sY g hd).cap
          (pullback.fst (pullback.diagonal g).coborderRange.ι gV) k β ≍
        (diagonalClosedFactorClass C sY g hd).cap
          (pullback.fst (pullback.diagonal g).coborderRange.ι gV) n
          (fundamentalChowClass C (pullback.fst (pullback.diagonal g).coborderRange.ι gV ≫
            ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY))) n) := by
    intro k hk β hβ
    subst hk
    rw [eq_of_heq hβ]
  refine eq_of_heq ((diagonalGysinClass_cap_heq C sY g hd gV n _).trans ?_)
  have h2 := (hcap _ (by simp) _ h1).trans (heq_of_eq hform)
  have hpush : ∀ (k : ℤ) (hk : n - d = k)
      (β : chowGroup C (pullback.fst (pullback.diagonal g).liftCoborder
            (pullback.fst (pullback.diagonal g).coborderRange.ι gV) ≫
          ((pullback.diagonal g).liftCoborder ≫
            ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY)))) k),
      β ≍ fundamentalChowClass C (pullback.fst (pullback.diagonal g).liftCoborder
            (pullback.fst (pullback.diagonal g).coborderRange.ι gV) ≫
          ((pullback.diagonal g).liftCoborder ≫
            ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY)))) (n - d) →
      chowPushforwardOfIso C
          (pullback.fst (pullback.diagonal g).liftCoborder
              (pullback.fst (pullback.diagonal g).coborderRange.ι gV) ≫
            ((pullback.diagonal g).liftCoborder ≫
              ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY))))
          (pullback.fst (pullback.diagonal g) gV ≫
            (pullback.diagonal g ≫ (pullback.fst g g ≫ sY)))
          ((pullbackRightPullbackFstIso (pullback.diagonal g).coborderRange.ι gV
              (pullback.diagonal g).liftCoborder).hom ≫
            (pullback.congrHom (pullback.diagonal g).liftCoborder_ι rfl).hom)
          (by simp) k β ≍
        fundamentalChowClass C (pullback.fst (pullback.diagonal g) gV ≫
          (pullback.diagonal g ≫ (pullback.fst g g ≫ sY))) (n - d) := by
    intro k hk β hβ
    subst hk
    rw [eq_of_heq hβ, chowPushforwardOfIso_fundamentalChowClass]
  exact hpush _ (by simp) _ h2

/-- **`Δ^!` satisfies the formula at vanishing excess when its closed factor does.** Let `g` be
smooth and separated of constant relative dimension `d`. If the class `c(Y ⟶ U, 𝒩)` of Stacks
0FBK of the closed factor of the diagonal satisfies
`Stacks.Chow.BivariantClass.CapRegularFormula` in degree `n`, then so does the Gysin class
`Δ^! = c(Y ⟶ U, 𝒩) ∘ ι^*` of the diagonal: for `V ⟶ Y ×_Z Y` pure of `δ`-dimension `n` with
`dim_δ(Y ×_{Y ×_Z Y} V) ≤ n - d` and `Y ×_{Y ×_Z Y} V ⟶ V` regular of codimension `d`,
`Δ^! ∩ [V]_n = [Y ×_{Y ×_Z Y} V]_{n - d}`. -/
theorem diagonalGysinClass_capRegularFormula_of_closedFactor [IsSeparated g] {n : ℤ}
    (hc : (diagonalClosedFactorClass C sY g hd).CapRegularFormula C (gysinSystemOfInvertible C)
      _ _ (pullback.diagonal g).liftCoborder rfl d n) :
    (diagonalGysinClass C sY g hd).CapRegularFormula C (gysinSystemOfInvertible C) _ _
      (pullback.diagonal g) rfl d n := by
  intro V gV _ hV hZV hreg
  obtain ⟨a, -, -, sq, _⟩ := exists_isOpenImmersion_pullback_diagonal_coborder g gV
  exact diagonalGysinClass_cap_eq_of_closedFactor_cap_eq C sY g hd gV
    (schemeDeltaDimension_le_of_forall_deltaDimension_eq C _ hV)
    (hc _ (forall_deltaDimension_pullback_coborder_eq C sY g gV hV)
      (schemeDeltaDimension_pullback_liftCoborder_le C sY g gV hZV) (hreg.of_isPullback sq))

/-- **`Δ^!` satisfies the conclusion of Stacks 0FEA when its closed factor satisfies the formula at
vanishing excess**, for `g` smooth of constant relative dimension `d`, separated or not. If the
class `c(Y ⟶ U, 𝒩)` of Stacks 0FBK of the closed factor of the diagonal satisfies
`Stacks.Chow.BivariantClass.CapRegularFormula` in degree `n`, then the Gysin class `Δ^!` of the
diagonal satisfies `Stacks.Chow.BivariantClass.CapCohenMacaulayFormula` in degree `n`: for
`V ⟶ Y ×_Z Y` pure of `δ`-dimension `n` with `dim_δ(Y ×_{Y ×_Z Y} V) ≤ n - d` and `𝒪_{V, ξ}`
Cohen–Macaulay at the points `ξ` of `Y ×_{Y ×_Z Y} V` with `δ(ξ) = n - d`,
`Δ^! ∩ [V]_n = [Y ×_{Y ×_Z Y} V]_{n - d}`.

Over the open `V' = U ×_P V` of `V`, Stacks 0FEA applies to the closed immersion `Δ' : Y ⟶ U`,
whose normal bundle has rank `d`; the hypotheses pass from `V` to `V'` because `V' ⟶ V` and
`Y ×_U V' ⟶ Y ×_P V` are open immersions, the latter an isomorphism. -/
theorem diagonalGysinClass_capCohenMacaulayFormula_of_closedFactor {n : ℤ}
    (hc : (diagonalClosedFactorClass C sY g hd).CapRegularFormula C (gysinSystemOfInvertible C)
      _ _ (pullback.diagonal g).liftCoborder rfl d n) :
    (diagonalGysinClass C sY g hd).CapCohenMacaulayFormula C (gysinSystemOfInvertible C) _ _
      (pullback.diagonal g) rfl d n := by
  have hc' := (diagonalClosedFactorClass C sY g hd).capCohenMacaulayFormula_of_capRegularFormula
    C _ _ _ _ rfl d (diagonalVirtualNormalBundle g)
    (isFiniteLocallyFreeOfRank_diagonalVirtualNormalBundle g hd) hc
  intro V gV _ hV hZV hCM
  obtain ⟨a, -, ha, sq, _⟩ := exists_isOpenImmersion_pullback_diagonal_coborder g gV
  have hZV' : schemeDeltaDimension C
      (pullback.snd (pullback.diagonal g).liftCoborder
          (pullback.fst (pullback.diagonal g).coborderRange.ι gV) ≫
        (pullback.fst (pullback.diagonal g).coborderRange.ι gV ≫
          ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY)))) ≤
      ((n - d : ℤ) : EInt) := by
    simpa only [pullback.condition_assoc] using
      schemeDeltaDimension_pullback_liftCoborder_le C sY g gV
        (by simpa only [pullback.condition_assoc] using hZV)
  have hCM' : ∀ ξ : (pullback (pullback.diagonal g).liftCoborder
        (pullback.fst (pullback.diagonal g).coborderRange.ι gV) : Scheme.{u}),
      relativeDimension C.dimensionFunction
          (pullback.fst (pullback.diagonal g).coborderRange.ι gV ≫
            ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY)))
          ((pullback.snd (pullback.diagonal g).liftCoborder
            (pullback.fst (pullback.diagonal g).coborderRange.ι gV)).base ξ) = n - d →
      let : IsLocallyNoetherian (pullback (pullback.diagonal g).coborderRange.ι gV) :=
        LocallyOfFiniteType.isLocallyNoetherian
          (pullback.fst (pullback.diagonal g).coborderRange.ι gV ≫
            ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY)))
      IsCohenMacaulayLocalRing ((pullback (pullback.diagonal g).coborderRange.ι gV).presheaf.stalk
        ((pullback.snd (pullback.diagonal g).liftCoborder
          (pullback.fst (pullback.diagonal g).coborderRange.ι gV)).base ξ)) := by
    intro ξ hξ
    have hpt : (pullback.snd (pullback.diagonal g) gV).base (a.base ξ) =
        (pullback.snd (pullback.diagonal g).coborderRange.ι gV).base
          ((pullback.snd (pullback.diagonal g).liftCoborder
            (pullback.fst (pullback.diagonal g).coborderRange.ι gV)).base ξ) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ha]
    have hrel : relativeDimension C.dimensionFunction (gV ≫ (pullback.fst g g ≫ sY))
        ((pullback.snd (pullback.diagonal g) gV).base (a.base ξ)) = n - d := by
      rw [hpt, ← relativeDimension_comp_isOpenImmersion, snd_coborder_comp_eq C sY g gV]
      exact hξ
    let : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian
      (gV ≫ (pullback.fst g g ≫ sY))
    have key : ∀ (x y : V), x = y → IsCohenMacaulayLocalRing (V.presheaf.stalk x) →
        IsCohenMacaulayLocalRing (V.presheaf.stalk y) := by
      rintro x _ rfl hx
      exact hx
    have h := key _ _ hpt (hCM (a.base ξ) hrel)
    let : IsLocallyNoetherian (pullback (pullback.diagonal g).coborderRange.ι gV) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst (pullback.diagonal g).coborderRange.ι gV ≫
          ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY)))
    exact (isCohenMacaulayLocalRing_iff_of_ringEquiv
      (asIso ((pullback.snd (pullback.diagonal g).coborderRange.ι gV).stalkMap
        ((pullback.snd (pullback.diagonal g).liftCoborder
          (pullback.fst (pullback.diagonal g).coborderRange.ι gV)).base
            ξ))).commRingCatIsoToRingEquiv).mp h
  exact diagonalGysinClass_cap_eq_of_closedFactor_cap_eq C sY g hd gV
    (schemeDeltaDimension_le_of_forall_deltaDimension_eq C _ hV)
    (hc' _ (forall_deltaDimension_pullback_coborder_eq C sY g gV hV) hZV' hCM')


/-! ### The formula for `Δ^!` -/

/-- **The closed factor `c(Y ⟶ U, 𝒩)` of `Δ^!` satisfies the formula over regular base changes**
in every degree: it is the class of Stacks 0FBK of a virtual normal bundle of rank `d`. -/
theorem diagonalClosedFactorClass_capRegularFormula (n : ℤ) :
    (diagonalClosedFactorClass C sY g hd).CapRegularFormula C (gysinSystemOfInvertible C)
      _ _ (pullback.diagonal g).liftCoborder rfl d n := by
  have := isFiniteLocallyFreeOfRank_diagonalVirtualNormalBundle g hd
  exact virtualNormalGysinClass_capRegularFormula C _ _ _ rfl _ d n

/-- **Stacks 0FEA for the Gysin class of the diagonal.** For `g : Y ⟶ Z` smooth of constant
relative dimension `d`, separated or not, the Gysin class `Δ^! ∈ A^d(Y ⟶ Y ×_Z Y)` of Stacks 0FBR
satisfies `Stacks.Chow.BivariantClass.CapCohenMacaulayFormula` in every degree `n`: for
`V ⟶ Y ×_Z Y` pure of `δ`-dimension `n` with `dim_δ(Y ×_{Y ×_Z Y} V) ≤ n - d` and `𝒪_{V, ξ}`
Cohen–Macaulay at the points `ξ` of `Y ×_{Y ×_Z Y} V` with `δ(ξ) = n - d`,
`Δ^! ∩ [V]_n = [Y ×_{Y ×_Z Y} V]_{n - d}`. -/
theorem diagonalGysinClass_capCohenMacaulayFormula (n : ℤ) :
    (diagonalGysinClass C sY g hd).CapCohenMacaulayFormula C (gysinSystemOfInvertible C) _ _
      (pullback.diagonal g) rfl d n :=
  diagonalGysinClass_capCohenMacaulayFormula_of_closedFactor C sY g hd
    (diagonalClosedFactorClass_capRegularFormula C sY g hd n)

/-- **`Δ^!` satisfies the formula over regular base changes**, for `g` smooth and separated of
constant relative dimension `d` (Stacks 0FBM at vanishing excess for `Δ^!`). -/
theorem diagonalGysinClass_capRegularFormula [IsSeparated g] (n : ℤ) :
    (diagonalGysinClass C sY g hd).CapRegularFormula C (gysinSystemOfInvertible C) _ _
      (pullback.diagonal g) rfl d n :=
  diagonalGysinClass_capRegularFormula_of_closedFactor C sY g hd
    (diagonalClosedFactorClass_capRegularFormula C sY g hd n)

end Stacks.Chow

end
