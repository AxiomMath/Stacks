module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceGysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.Basic

/-!
# Total Chow cohomology classes on a decomposition into open and closed subschemes

Let `Y = ∐_{i ∈ I} Y_i` be a decomposition of a scheme locally of finite type over the base of
chapter 42 of the Stacks Project into open and closed subschemes. [Stacks, Tag 0FDZ] for the
identity of `Y` reads `A^p(Y) = ∏_i A^p(Y_i)`; in every degree it gives

  `∏_{p ≥ 0} A^p(Y) = ∏_i ∏_{p ≥ 0} A^p(Y_i)`

for total Chow cohomology classes: a total class on `Y` is determined by its restrictions to the
pieces (`Stacks.Chow.TotalChowClass.eq_of_res_eq`), and any family of total classes on the
pieces is the family of restrictions of one total class on `Y`
(`Stacks.Chow.TotalChowClass.glue`, `Stacks.Chow.TotalChowClass.res_glue`).

The restriction to a piece used here is the restriction map of [Stacks, Tag 0B7F] along the
inclusion `Y_i ⟶ Y`; the component of [Stacks, Tag 0FDZ] is a class for the restriction of the
identity to the piece. The two agree
(`Stacks.Chow.chowCohomologyRestriction_eq_pieceIdentityCongr`): both operate on a test scheme
`T ⟶ Y_i` as the original class does on `T ⟶ Y_i ⟶ Y`.

## Main definitions

* `Stacks.Chow.TotalChowClass.glue` — the total class with prescribed restrictions to the pieces.

## Main results

* `Stacks.Chow.chowCohomologyRestriction_eq_pieceIdentityCongr` — the restriction of Stacks 0B7F
  to a piece is the component of Stacks 0FDZ.
* `Stacks.Chow.TotalChowClass.eq_of_res_eq` — a total class is determined by its restrictions to
  the pieces.
* `Stacks.Chow.TotalChowClass.res_glue`, `Stacks.Chow.TotalChowClass.eq_glue` — the glued class
  is the unique class with the prescribed restrictions.

## References

* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {C : ChowSituation.{u}} {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {I : Type u} (U : I → Y.Opens)

/-- Every open subscheme lies in its own preimage under the identity, so a family of open
subschemes is a decomposition adapted to the identity in the sense of Stacks 0FDZ. -/
theorem opens_le_preimage_id (i : I) : U i ≤ (𝟙 Y) ⁻¹ᵁ U i := by simp

/-- The restriction of the identity to a piece is an isomorphism, being the identity. -/
instance isIso_pieceMap_id (i : I) :
    IsIso (pieceMap (𝟙 Y) U U id (opens_le_preimage_id U) i) := by
  rw [pieceMap_id]
  infer_instance

/-- **The restriction of Stacks 0B7F to a piece is the restriction of Stacks 0FDZ.** For a
family of open subschemes `U_i` of `Y` and `c ∈ A^p(Y)`, the restriction of `c` along the
inclusion `U_i ⟶ Y` is the component on `U_i` of `c` under Stacks 0FDZ for the identity of `Y`,
read as a class of `A^p(U_i)`. Both classes operate on a test scheme `g : T ⟶ U_i` as `c` does
on `T ⟶ U_i ⟶ Y`. -/
theorem chowCohomologyRestriction_eq_pieceIdentityCongr {p : ℤ}
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) (i : I) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) sY (U i).ι p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c =
      pieceIdentityCongr C (gysinSystemOfInvertible C) sY U (opens_le_preimage_id U) p i
        (pieceMap_comp_structureMorphism C sY sY (𝟙 Y) (Category.id_comp sY) U U id
          (opens_le_preimage_id U) i)
        (bivariantPieceRestrictionOfInvertible C sY sY (𝟙 Y) (Category.id_comp sY) p U U id
          (opens_le_preimage_id U) i c) := by
  refine BivariantClass.eq_of_idRule_eq C ((U i).ι ≫ sY) _ _ _ fun {T} g _ k α ↦ eq_of_heq ?_
  refine (BivariantClass.idRule_chowCohomologyRestriction_heq (U i).ι c g k α
    (chowGroupCongr C (Category.assoc g (U i).ι sY).symm k α)
    (chowGroupCongr_heq C _ k α).symm).trans ?_
  refine HEq.symm ((BivariantClass.isoRule_bivariantClassCongr_heq C ((U i).ι ≫ sY) _
    (pieceMap_id U (opens_le_preimage_id U) i) _ _ _ g k α).trans ?_)
  set pm := pieceMap (𝟙 Y) U U id (opens_le_preimage_id U) i
  set m := pieceComparison (𝟙 Y) U U id (opens_le_preimage_id U) i g
  have hm : m ≫ pullback.snd (𝟙 Y) (g ≫ (U i).ι) = pullback.snd pm g :=
    opensPullbackComparison_snd _ _ _ _ _ _
  have : IsIso m := by
    have : IsIso (m ≫ pullback.snd (𝟙 Y) (g ≫ (U i).ι)) := by rw [hm]; infer_instance
    exact IsIso.of_isIso_comp_right m (pullback.snd (𝟙 Y) (g ≫ (U i).ι))
  set x := c.cap (g ≫ (U i).ι) k (chowGroupCongr C (Category.assoc g (U i).ι sY).symm k α)
  change chowPushforwardOfIso C (pullback.fst pm g ≫ ((U i).ι ≫ sY)) (g ≫ ((U i).ι ≫ sY))
      (pullback.snd pm g) _ (k - p)
      (chowGroupRestrict C (pullback.fst (𝟙 Y) (g ≫ (U i).ι) ≫ sY)
        (pullback.fst pm g ≫ ((U i).ι ≫ sY)) m _ (k - p) x) ≍
    chowPushforwardOfIso C (pullback.fst (𝟙 Y) (g ≫ (U i).ι) ≫ sY) ((g ≫ (U i).ι) ≫ sY)
      (pullback.snd (𝟙 Y) (g ≫ (U i).ι)) _ (k - p) x
  rw [chowGroupRestrict_of_isIso, chowPushforwardOfIso_comp_apply]
  have hinv : inv m ≫ pullback.snd pm g = pullback.snd (𝟙 Y) (g ≫ (U i).ι) := by
    rw [IsIso.inv_comp_eq, hm]
  rw [chowPushforwardOfIso_congr_apply C _ _ _ _ hinv _ (by
    simpa only [Category.assoc] using
      pullbackSnd_comp_structureMorphism (Category.id_comp sY) (g ≫ (U i).ι))]
  exact chowPushforwardOfIso_heq _ _ _ rfl (Category.assoc g (U i).ι sY).symm rfl HEq.rfl

namespace TotalChowClass

/-- The restriction of a total class along `h`, with the structure morphism `h ≫ sY` itself,
is the restriction map of Stacks 0B7F in every degree. -/
theorem res_rfl_apply {Y' : Scheme.{u}} (h : Y' ⟶ Y) [LocallyOfFiniteType h]
    (c : TotalChowClass C sY) (p : ℕ) :
    res h rfl c p = chowCohomologyRestriction C (gysinSystemOfInvertible C) sY h (p : ℤ)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (c p) :=
  rfl

variable {U} (hU : IsClopenDecomposition U)

include hU in
/-- **A total class is determined by its restrictions to the pieces** of a decomposition of `Y`
into open and closed subschemes: Stacks 0FDZ in every degree. -/
theorem eq_of_res_eq {c d : TotalChowClass C sY}
    (h : ∀ i, res (U i).ι rfl c = res (U i).ι rfl d) : c = d := by
  refine ext fun p ↦ ?_
  refine (bivariantPieceEquivOfInvertible C sY sY (𝟙 Y) (Category.id_comp sY) (p : ℤ) U U id
    (opens_le_preimage_id U) hU).injective (funext fun i ↦ ?_)
  refine (pieceIdentityCongr C (gysinSystemOfInvertible C) sY U (opens_le_preimage_id U) (p : ℤ)
    i _).injective ?_
  simp only [bivariantPieceEquivOfInvertible_apply]
  rw [← chowCohomologyRestriction_eq_pieceIdentityCongr,
    ← chowCohomologyRestriction_eq_pieceIdentityCongr,
    ← res_rfl_apply, ← res_rfl_apply, h i]

/-- **The total class glued from classes on the pieces** of a decomposition of `Y` into open and
closed subschemes: in every degree, the class of Stacks 0FDZ whose components on the pieces are
the given ones. -/
def glue (d : ∀ i, TotalChowClass C ((U i).ι ≫ sY)) : TotalChowClass C sY := fun p ↦
  (bivariantPieceEquivOfInvertible C sY sY (𝟙 Y) (Category.id_comp sY) (p : ℤ) U U id
    (opens_le_preimage_id U) hU).symm fun i ↦
      (pieceIdentityCongr C (gysinSystemOfInvertible C) sY U (opens_le_preimage_id U) (p : ℤ) i
        _).symm (d i p)

/-- **The glued class restricts to the given classes on the pieces.** -/
theorem res_glue (d : ∀ i, TotalChowClass C ((U i).ι ≫ sY)) (i : I) :
    res (U i).ι rfl (glue hU d) = d i := by
  refine ext fun p ↦ ?_
  rw [res_rfl_apply, chowCohomologyRestriction_eq_pieceIdentityCongr,
    ← bivariantPieceEquivOfInvertible_apply C sY sY (𝟙 Y) (Category.id_comp sY) (p : ℤ) U U id
      (opens_le_preimage_id U) hU, glue, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- **The glued class is the only class with the given restrictions to the pieces.** -/
theorem eq_glue {d : ∀ i, TotalChowClass C ((U i).ι ≫ sY)} {c : TotalChowClass C sY}
    (h : ∀ i, res (U i).ι rfl c = d i) : c = glue hU d :=
  eq_of_res_eq hU fun i ↦ (h i).trans (res_glue hU d i).symm

end TotalChowClass

end Stacks.Chow

end
