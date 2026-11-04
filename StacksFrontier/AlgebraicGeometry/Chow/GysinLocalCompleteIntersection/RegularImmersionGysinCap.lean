module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassRestriction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GysinOpenImmersion

/-!
# The Gysin map of a regular immersion on `c ∩ [X]`

Let `k` be a field, `X` a scheme smooth over `k` and `i : Y ⟶ X` a regular closed immersion with
`Y` equidimensional of dimension `e`. For a total class `c ∈ ∏_q A^q(X)` write `c_q ∩ [X]` for the
class of `CH^q(X)` whose component on the part `X_d` of dimension `d` is `c_q|_{X_d} ∩ [X_d]_d`.
Then

  `i^!(c_q ∩ [X]) = c_q|_Y ∩ [Y]_e`   in   `CH_{e-q}(Y)`,

by Stacks 0FF6 and 0FF7 on each piece `Y ×_X X_d` (as in the proof of Stacks 0FFE).

## Main definitions

* `Stacks.Chow.totalChowClassCapFundamental`: `c_q ∩ [X] ∈ CH^q(X)`.

## Main results

* `Stacks.Chow.TotalChowClass.res_apply_eq_restrictionOfEq`: the components of the restriction of a
  total class are the restrictions of its components.
* `Stacks.Chow.regularImmersionGysin_totalChowClassCapFundamental`:
  `i^!(c_q ∩ [X]) = c_q|_Y ∩ [Y]_e`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology (dimPart partBase
  chowGroupRestrict_chowCohomologyCapFundamentalClass_of_isOpenImmersion
  deltaDimension_irreducibleComponent_of_relativeDimension
  schemeDeltaDimension_le_of_forall_irreducibleComponent)

section Res

variable {C : ChowSituation.{u}} {Y Y' : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY']

/-- The degree `p` component of the restriction of a total class along `h` is the restriction
(Stacks 0B7F) of its degree `p` component. -/
theorem TotalChowClass.res_apply_eq_restrictionOfEq (h : Y' ⟶ Y) [LocallyOfFiniteType h]
    (hs : h ≫ sY = sY') (c : TotalChowClass C sY) (p : ℕ) :
    TotalChowClass.res h hs c p =
      chowCohomologyRestrictionOfEq C sY' sY hs (gysinSystemOfInvertible C)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p (c p) := by
  subst hs
  rfl

end Res

section Cap

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX]

/-- **`c_q ∩ [X] ∈ CH^q(X)`** for a total class `c` of `X`: on the part `X_d` of dimension `d`, the
degree `q` component of `c|_{X_d}` capped with the fundamental class `[X_d]_d`. -/
def totalChowClassCapFundamental (c : TotalChowClass (fieldChowSituation k) sX) (q : ℕ) :
    codimensionChowGroup k sX q :=
  fun d ↦ chowCohomologyCapFundamentalClass (fieldChowSituation k)
    (gysinSystemOfInvertible (fieldChowSituation k)) (partBase sX d) d q
    (TotalChowClass.res (dimPart sX d).ι rfl c q)

variable {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
  (hreg : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i)

/-- **`i^!(c_q ∩ [X]) = c_q|_Y ∩ [Y]_e`** for a regular closed immersion `i : Y ⟶ X` with `Y`
equidimensional of dimension `e`. On the piece `Y ×_X X_d` both sides are
`c_q|_{Y ×_X X_d} ∩ [Y ×_X X_d]_e`: the left by Stacks 0FF6 and 0FF7 for the Gysin map of `i`
on `X_d`, the right because capping with the fundamental class commutes with restriction to an
open subscheme. -/
theorem regularImmersionGysin_totalChowClassCapFundamental (e : ℕ)
    (hY : RelativeDimension (i ≫ sX) e) (c : TotalChowClass (fieldChowSituation k) sX) (q : ℕ) :
    regularImmersionGysin sX i hreg e q (totalChowClassCapFundamental sX c q) =
      chowCohomologyCapFundamentalClass (fieldChowSituation k)
        (gysinSystemOfInvertible (fieldChowSituation k)) (i ≫ sX) e q
        (TotalChowClass.res i rfl c q) := by
  refine (chowGroupClopenRestrictEquiv (fieldChowSituation k) (i ≫ sX)
      (fun d : ULift.{u} ℕ ↦ pullback.fst i (dimPart sX d.down).ι ≫ i ≫ sX)
      (fun d : ULift.{u} ℕ ↦ pullback.fst i (dimPart sX d.down).ι) (fun _ ↦ rfl)
      (isClopenDecomposition_pullbackFst_dimPart sX i) (e - q)).injective (funext fun d ↦ ?_)
  obtain ⟨d⟩ := d
  have hgys : (gysinSystemOfInvertible (fieldChowSituation k)).IsNaturalUnderBaseChangeIso :=
    gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _
  have hq : pullback.snd i (dimPart sX d).ι ≫ partBase sX d =
      pullback.fst i (dimPart sX d).ι ≫ i ≫ sX :=
    pullbackSnd_comp_structureMorphism_eq _ (i ≫ sX) sX i rfl (dimPart sX d).ι
  have hYδ := deltaDimension_irreducibleComponent_of_relativeDimension k (i ≫ sX) e hY
  have hdimY : schemeDeltaDimension (fieldChowSituation k) (i ≫ sX) ≤ ((e : ℤ) : EInt) :=
    schemeDeltaDimension_le_of_forall_irreducibleComponent _ hYδ
  rw [chowGroupClopenRestrictEquiv_apply, chowGroupClopenRestrictEquiv_apply,
    chowGroupRestrict_regularImmersionGysin,
    chowGroupRestrict_chowCohomologyCapFundamentalClass_of_isOpenImmersion _ _ hgys _ _ _ _ rfl _
      hdimY]
  have hβ : regularImmersionPartGysin sX i hreg e d q (totalChowClassCapFundamental sX c q d) =
      chowCohomologyCapFundamentalClass (fieldChowSituation k)
        (gysinSystemOfInvertible (fieldChowSituation k))
        (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) e q
        (chowCohomologyRestrictionOfEq (fieldChowSituation k)
          (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) (partBase sX d) hq
          (gysinSystemOfInvertible (fieldChowSituation k)) hgys q
          (TotalChowClass.res (dimPart sX d).ι rfl c q)) :=
    eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans
      (BivariantClass.capTargetHom_chowCohomologyCapFundamentalClass_heq _ _ hgys _ _ q hq
        ((d : ℤ) - e) (regularImmersionPartGysinClass sX i hreg e d) _
        (regularImmersionPartGysinClass_commutesWithEveryClass sX i hreg e d (𝟙 _) q _) d
        (regularImmersionPartGysinClass_capTargetHom_fundamentalChowClass sX i hreg e hY d)
        (by ring)))
  rw [hβ, ← TotalChowClass.res_apply_eq_restrictionOfEq,
    ← TotalChowClass.res_apply_eq_restrictionOfEq, TotalChowClass.res_res,
    TotalChowClass.res_res]
  exact congrArg (fun c' ↦ chowCohomologyCapFundamentalClass (fieldChowSituation k)
    (gysinSystemOfInvertible (fieldChowSituation k))
    (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) e q (c' q))
    (TotalChowClass.res_congr pullback.condition.symm _ _ c)

end Cap

end Stacks.Chow

end
