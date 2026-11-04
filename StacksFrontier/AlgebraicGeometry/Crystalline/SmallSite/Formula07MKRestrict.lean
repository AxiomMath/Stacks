module

public import StacksFrontier.AlgebraicGeometry.Crystalline.RestrictPullback
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.HigherDirectImage

/-!
# Forming the situation `U/T` commutes with restriction to an open of `T'`

Let `(U', T', δ')` be an object of `Cris(X'/S')` and let `W` be an open of its ambient scheme
`T'`.  The remark [Stacks, Tag 07MJ] attaches to `(U', T', δ')` the crystalline situation `U/T`
with `T = S ×_{S'} T'` the divided power fibre product of [Stacks, Tag 07ME] and
`U = X ×_{X'} U'`, which is `Crystalline.GlobalCrystallineSituation.pullbackSituation`.  The
displayed equation (07MK) of that remark is an equation of sheaves on the small Zariski site of
`T'`; its left-hand side read at `W` is governed by the situation attached to the restriction
`(U', T', δ')|_W`, and its right-hand side at `W` by the open `g⁻¹W` of `T`, for `g : T ⟶ T'` the
second projection.  This file shows that forming `U/T` commutes with restricting to an open of
`T'`, in three statements, one for each of the three pieces of data.

* The divided power base: `S ×_{S'} (T'|_W)` is the restriction of `S ×_{S'} T'` to `g⁻¹W`.
* The scheme: `X ×_{X'} (U'|_{W₀})` is the restriction of `X ×_{X'} U'` to the preimage of `W₀`
  under the second projection, where `W₀` is the preimage of `W` in `U'`.
* The open: the preimage of `g⁻¹W` under the structure morphism `U ⟶ T` of `U/T` is the
  preimage of `W₀` under the second projection.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.pullbackBaseRestrictOpenIso`: **the comparison
  `(S ×_{S'} T')|_{g⁻¹W} ≅ S ×_{S'} (T'|_W)`** of divided power schemes.
* `Crystalline.GlobalCrystallineSituation.pullbackSourceRestrictOpenIso`: **the comparison
  `(X ×_{X'} U')|_{q⁻¹W₀} ≅ X ×_{X'} (U'|_{W₀})`** of schemes.

## Main results

* `Crystalline.GlobalCrystallineSituation.isPullback_pullbackBase_restrictOpen` and
  `...isPullback_pullbackSource_restrictOpen`: the two fibre squares the comparisons come from.
* `Crystalline.GlobalCrystallineSituation.sourceToBase_pullbackSituation_comp_snd`: the structure
  morphism `U ⟶ T` of `U/T` followed by `T ⟶ T'` is `U ⟶ U' ↪ T'`.
* `Crystalline.GlobalCrystallineSituation.preimage_sourceToBase_pullbackSituation`: the open of
  `U` cut out by `g⁻¹W` is the preimage of `W₀` under `U ⟶ U'`.

## References

* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 07MK](https://stacks.math.columbia.edu/tag/07MK)
* [Stacks Project, Tag 07ME](https://stacks.math.columbia.edu/tag/07ME)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

open DividedPowerScheme

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (A' : CrystallineThickening S') (W : A'.obj.thickening.target.scheme.Opens)

/-! ### The divided power base -/

/-- **`S ×_{S'} (T'|_W)` is the restriction of `S ×_{S'} T'` to `g⁻¹W`**, for `g : T ⟶ T'` the
second projection ([Stacks, Tag 07ME]). -/
theorem isPullback_pullbackBase_restrictOpen :
    IsPullback ((pullback.snd fS A'.obj.toBase).restrictPreimage W)
      ((pullbackBase S S' fS A').restrictι ((pullback.snd fS A'.obj.toBase).hom ⁻¹ᵁ W) ≫
        pullback.fst fS A'.obj.toBase)
      (A'.restrictOpen W).obj.toBase fS :=
  isPullback_restrictι_pullback fS A'.obj.toBase W

/-- **The comparison `(S ×_{S'} T')|_{g⁻¹W} ≅ S ×_{S'} (T'|_W)`**: the divided power base of the
situation attached to `(U', T', δ')|_W` is the restriction of the divided power base of the
situation attached to `(U', T', δ')` to the preimage of `W`. -/
def pullbackBaseRestrictOpenIso :
    (pullbackBase S S' fS A').restrict ((pullback.snd fS A'.obj.toBase).hom ⁻¹ᵁ W) ≅
      pullbackBase S S' fS (A'.restrictOpen W) :=
  (isPullback_pullbackBase_restrictOpen S S' fS A' W).flip.isoPullback

/-! ### The scheme -/

/-- **`X ×_{X'} (U'|_{W₀})` is the restriction of `X ×_{X'} U'` to `q⁻¹W₀`**, for `q` the second
projection and `W₀` the preimage of `W` in `U'`. -/
theorem isPullback_pullbackSource_restrictOpen :
    IsPullback (pullback.snd fX A'.obj.toX ∣_ (A'.obj.thickening.immersion ⁻¹ᵁ W))
      ((pullback.snd fX A'.obj.toX ⁻¹ᵁ (A'.obj.thickening.immersion ⁻¹ᵁ W)).ι ≫
        pullback.fst fX A'.obj.toX)
      (A'.restrictOpen W).obj.toX fX :=
  (isPullback_morphismRestrict (pullback.snd fX A'.obj.toX)
    (A'.obj.thickening.immersion ⁻¹ᵁ W)).paste_vert
      (IsPullback.of_hasPullback fX A'.obj.toX).flip

/-- **The comparison `(X ×_{X'} U')|_{q⁻¹W₀} ≅ X ×_{X'} (U'|_{W₀})`**: the scheme of the situation
attached to `(U', T', δ')|_W` is the restriction of the scheme of the situation attached to
`(U', T', δ')` to the preimage of `W₀`. -/
def pullbackSourceRestrictOpenIso :
    (pullback.snd fX A'.obj.toX ⁻¹ᵁ (A'.obj.thickening.immersion ⁻¹ᵁ W)).toScheme ≅
      pullbackSource S S' fX (A'.restrictOpen W) :=
  (isPullback_pullbackSource_restrictOpen S S' fX A' W).flip.isoPullback

/-! ### The open of `U` cut out by `g⁻¹W` -/

variable (hf : S.toClosedFiber ≫ closedFiberMap fS = fX ≫ S'.toClosedFiber)

include hf

/-- **The induced morphism `U ⟶ T₀` of [Stacks, Tag 07MJ], followed by `T₀ ↪ T` and the second
projection `T ⟶ T'`, is `U ⟶ U' ↪ T'`.** -/
theorem pullbackToClosedFiber_comp_closedFiberι_comp_snd :
    (pullbackToClosedFiber S S' fS fX hf A' ≫ closedFiberι (pullbackBase S S' fS A')) ≫
        (pullback.snd fS A'.obj.toBase).hom =
      pullback.snd fX A'.obj.toX ≫ A'.obj.thickening.immersion := by
  rw [Category.assoc, ← closedFiberMap_comp_closedFiberι, pullbackToClosedFiber_comp_snd_assoc,
    SchemeThickening.toClosedFiber_comp_closedFiberι]

/-- **The structure morphism `U ⟶ T` of the situation `U/T`, followed by the second projection
`T ⟶ T'`, is `U ⟶ U' ↪ T'`.** -/
theorem sourceToBase_pullbackSituation_comp_snd :
    sourceToBase (pullbackSituation S S' fS fX hf A') ≫
        (pullback.snd fS A'.obj.toBase).hom =
      pullback.snd fX A'.obj.toX ≫ A'.obj.thickening.immersion :=
  pullbackToClosedFiber_comp_closedFiberι_comp_snd S S' fS fX A' hf

/-- **The open of `U` over which the right-hand side of (07MK) at `W` is evaluated is the preimage
of `W₀` under `U ⟶ U'`**: the preimage of `g⁻¹W` under `U ⟶ T₀ ↪ T` is the preimage of
`W₀ = U' ∩ W` under the second projection of `U = X ×_{X'} U'`. -/
theorem preimage_pullbackToClosedFiber_closedFiberι :
    (pullbackToClosedFiber S S' fS fX hf A' ≫ closedFiberι (pullbackBase S S' fS A')) ⁻¹ᵁ
        ((pullback.snd fS A'.obj.toBase).hom ⁻¹ᵁ W) =
      pullback.snd fX A'.obj.toX ⁻¹ᵁ (A'.obj.thickening.immersion ⁻¹ᵁ W) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
    pullbackToClosedFiber_comp_closedFiberι_comp_snd S S' fS fX A' hf]

/-- `preimage_pullbackToClosedFiber_closedFiberι` with the structure morphism of the situation
`U/T` named as such. -/
theorem preimage_sourceToBase_pullbackSituation :
    sourceToBase (pullbackSituation S S' fS fX hf A') ⁻¹ᵁ
        ((pullback.snd fS A'.obj.toBase).hom ⁻¹ᵁ W) =
      pullback.snd fX A'.obj.toX ⁻¹ᵁ (A'.obj.thickening.immersion ⁻¹ᵁ W) :=
  preimage_pullbackToClosedFiber_closedFiberι S S' fS fX A' W hf

end Crystalline.GlobalCrystallineSituation

end

end
