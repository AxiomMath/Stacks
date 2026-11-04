module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.Properties
public import Mathlib.RingTheory.LaurentSeries
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change of a cyclic cover

Let `p : X ⟶ Z_S` be the cyclic cover `Spec_{Z_S}(Sym(L_S)/(φ - c))` of
`StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.Construction`, and let
`σ : S → S'` be a map of `k`-algebras. Since `X = 𝕃 ×_{𝔸¹_k} Spec S`, its base change
`X ×_{Spec S} Spec S'` is `𝕃 ×_{𝔸¹_k} Spec S'`, the cyclic cover attached to `S'` and `σ(c)`, and
likewise `Z_S ×_{Spec S} Spec S' = Z_{S'}`. Under these identifications the base change of `p` is
the cyclic cover map over `S'`.

Applied to `R = k[[π]] → K = k((π))` this identifies the generic fibre `X_K ⟶ Z_K` of `p` with
the cyclic cover attached to the unit `π` of `K`, which is finite étale.

## Main definitions

* `Stacks.CyclicCover.coverBaseChangeIso`: `X ×_{Spec S} Spec S' ≅ X_{S'}`.
* `Stacks.CyclicCover.baseChangeBaseChangeIso`: `Z_S ×_{Spec S} Spec S' ≅ Z_{S'}`.
* `Stacks.CyclicCover.coverMapBaseChange`: the base change `X ×_S S' ⟶ Z_S ×_S S'` of `p`.

## Main results

* `Stacks.CyclicCover.coverMapBaseChange_comp`: the base change of `p` is `p` over `S'`.
* `Stacks.CyclicCover.isFinite_coverMapBaseChange`,
  `Stacks.CyclicCover.etale_coverMapBaseChange`: the base change of `p` is finite, and étale when
  `n` and the image of `c` are invertible.

## References

* [Stacks Project, Tag 0CEH](https://stacks.math.columbia.edu/tag/0CEH)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace Polynomial

universe u

namespace Stacks.CyclicCover

variable {k : Type u} [Field k] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) {L : Z.Modules}
  [SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L] {n : ℕ}
  (φ : (situation f L).symmetricAlgebra.piece (n : ℤ) ≅ SheafOfModules.unit Z.ringCatSheaf)
  {S S' : Type u} [CommRing S] [Algebra k S] [CommRing S'] [Algebra k S'] (c : S)
  (σ : S →ₐ[k] S')

/-- The composite `Spec S' ⟶ Spec S ⟶ 𝔸¹_k` of `Spec σ` with the point `c` is the point `σ(c)`. -/
theorem pointMap_baseChange :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ pointMap (k := k) S c = pointMap S' (σ c) := by
  rw [pointMap, pointMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact Polynomial.ringHom_ext (fun r => by simp) (by simp)

/-- The composite `Spec S' ⟶ Spec S ⟶ Spec k` of `Spec σ` with the structure morphism of `Spec S`
is the structure morphism of `Spec S'`. -/
theorem specMap_algebraMap_baseChange :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap k S)) =
      Spec.map (CommRingCat.ofHom (algebraMap k S')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp

/-- **`X ×_{Spec S} Spec S' ≅ X_{S'}`**, the cyclic cover attached to `S'` and `σ(c)`. -/
def coverBaseChangeIso :
    pullback (coverSnd f φ S c) (Spec.map (CommRingCat.ofHom σ.toRingHom)) ≅
      cover f φ S' (σ c) :=
  pullbackLeftPullbackSndIso _ _ _ ≪≫ pullback.congrHom rfl (pointMap_baseChange c σ)

/-- **`Z_S ×_{Spec S} Spec S' ≅ Z_{S'}`.** -/
def baseChangeBaseChangeIso :
    pullback (baseChangeSnd f S) (Spec.map (CommRingCat.ofHom σ.toRingHom)) ≅ baseChange f S' :=
  pullbackLeftPullbackSndIso _ _ _ ≪≫ pullback.congrHom rfl (specMap_algebraMap_baseChange σ)

/-- The base change `X ×_{Spec S} Spec S' ⟶ Z_S ×_{Spec S} Spec S'` of `p`. -/
def coverMapBaseChange :
    pullback (coverSnd f φ S c) (Spec.map (CommRingCat.ofHom σ.toRingHom)) ⟶
      pullback (baseChangeSnd f S) (Spec.map (CommRingCat.ofHom σ.toRingHom)) :=
  pullback.map _ _ _ _ (coverMap f φ S c) (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- **The base change of `p` is `p` over `S'`.** -/
@[reassoc]
theorem coverMapBaseChange_comp :
    coverMapBaseChange f φ c σ ≫ (baseChangeBaseChangeIso f σ).hom =
      (coverBaseChangeIso f φ c σ).hom ≫ coverMap f φ S' (σ c) := by
  rw [baseChangeBaseChangeIso, coverBaseChangeIso, Iso.trans_hom, Iso.trans_hom,
    pullback.congrHom_hom, pullback.congrHom_hom]
  refine pullback.hom_ext ?_ ?_
  · simp only [coverMapBaseChange, Category.assoc, pullback.lift_fst,
      pullbackLeftPullbackSndIso_hom_fst_assoc, pullbackLeftPullbackSndIso_hom_fst,
      pullback.lift_fst_assoc, Category.comp_id, coverMap_fst]
  · simp only [coverMapBaseChange, Category.assoc, pullback.lift_snd,
      pullbackLeftPullbackSndIso_hom_snd, Category.comp_id, coverMap_snd]

/-- The base change of `p` and `p` over `S'` are isomorphic arrows. -/
def coverMapBaseChangeArrowIso :
    Arrow.mk (coverMapBaseChange f φ c σ) ≅ Arrow.mk (coverMap f φ S' (σ c)) :=
  Arrow.isoMk (coverBaseChangeIso f φ c σ) (baseChangeBaseChangeIso f σ)
    (coverMapBaseChange_comp f φ c σ).symm

/-- The base change of `p` is finite. -/
theorem isFinite_coverMapBaseChange (hn : n ≠ 0) : IsFinite (coverMapBaseChange f φ c σ) := by
  have := Stacks.Morphisms.isFinite_isZariskiLocalAtTarget.{u}
  have : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    Stacks.Morphisms.isFinite_isZariskiLocalAtTarget.toRespects
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite) (coverMapBaseChangeArrowIso f φ c σ)).2
    (isFinite_coverMap f φ S' (σ c) hn)

/-- **The base change of `p` is étale** when `n` is invertible in `k` and `σ(c)` is invertible. -/
theorem etale_coverMapBaseChange (hn : (n : k) ≠ 0) (hc : IsUnit (σ c)) :
    Etale (coverMapBaseChange f φ c σ) :=
  (MorphismProperty.arrow_mk_iso_iff (P := @Etale) (coverMapBaseChangeArrowIso f φ c σ)).2
    (etale_coverMap f φ S' (σ c) hn hc)

section GenericFibre

variable (k) in
/-- The inclusion `k[[π]] → k((π))`, as a map of `k`-algebras. -/
def powerSeriesToLaurent : PowerSeries k →ₐ[k] LaurentSeries k :=
  { algebraMap (PowerSeries k) (LaurentSeries k) with
    commutes' := fun r => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe]
      simp only [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rfl }

/-- **The morphism of generic fibres `X_K ⟶ Z_K` is finite étale**, where `R = k[[π]]`,
`K = k((π))`, `X_K = X ×_{Spec R} Spec K` and `Z_K = Z_R ×_{Spec R} Spec K`. -/
theorem isFinite_etale_genericFibre (hn : (n : k) ≠ 0) :
    IsFinite (coverMapBaseChange f φ (PowerSeries.X : PowerSeries k) (powerSeriesToLaurent k)) ∧
      Etale (coverMapBaseChange f φ (PowerSeries.X : PowerSeries k) (powerSeriesToLaurent k)) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine ⟨isFinite_coverMapBaseChange f φ _ _ hn0, etale_coverMapBaseChange f φ _ _ hn ?_⟩
  refine IsUnit.mk0 _ ?_
  simp [powerSeriesToLaurent]

end GenericFibre

end Stacks.CyclicCover

end
