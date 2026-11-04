module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilRealization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Isomorphisms of data (D0)–(D3) preserve the derived operations

An isomorphism `e : W ≅ W'` of data (D0)–(D3) (`Stacks.WeilCohomology.WeilData.Iso`) consists of
an isomorphism of Tate lines and natural isomorphisms of graded algebras. This file proves that
it is compatible with everything built from the data in Section 0FHA (Tag 0FHA): pullbacks and
cup products in every degree and twist, and — when it also preserves the trace maps — the
pairings of axiom (A) and the pushforwards defined from them by Poincaré duality, as well as
the Künneth maps of axiom (B).

The twisted cup products are defined through a coordinate of the Tate line
(`Stacks.WeilCohomology.tateCup`), and the isomorphism `F(1) ≅ F(1)'` does not carry the chosen
coordinate of `F(1)` to that of `F(1)'`. Since the twisted cup product does not depend on the
coordinate (`Stacks.WeilCohomology.tateCup_eq_with`), it suffices that tensor-power coordinates
are natural for isomorphisms of lines
(`Stacks.WeilCohomology.tateTwistCoordinates_tateTwistCongr`).

## Main results

* `Stacks.WeilCohomology.tateCup_tateTwistCongr`: twisted cup products are natural.
* `Stacks.WeilCohomology.WeilData.Iso.twEquiv_cupTw`, `...twEquiv_pullTw`: compatibility with
  cup products and pullbacks.
* `Stacks.WeilCohomology.WeilData.Iso.pairingTw_twEquiv`: the pairings of (A) are preserved.
* `Stacks.WeilCohomology.WeilData.Iso.twEquiv_pushforward`: pushforwards are preserved.
* `Stacks.WeilCohomology.WeilData.Iso.equiv_kunnethMap`: Künneth maps are preserved.

## References

* [Stacks Project, Section 45.9 (Tag 0FHA)](https://stacks.math.columbia.edu/tag/0FHA)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

universe u w uF uL uL' uU uU' uV uV' uW uW'

namespace Stacks.WeilCohomology

section Twists

variable {F : Type uF} [Field F]
  {L : Type uL} [AddCommGroup L] [Module F L] {L' : Type uL'} [AddCommGroup L'] [Module F L']

/-- Tensor-power coordinates are natural for isomorphisms of lines. -/
theorem tensorPowerCoordinates_congr (e : L ≃ₗ[F] L') (c' : L' ≃ₗ[F] F) (n : ℕ)
    (x : TensorPower F n L) :
    tensorPowerCoordinates c' n (PiTensorProduct.congr (fun _ ↦ e) x) =
      tensorPowerCoordinates (e.trans c') n x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    simp [tensorPowerCoordinates, PiTensorProduct.constantBaseRingEquiv_tprod]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Coordinates of integer powers of a line are natural for isomorphisms of lines. -/
theorem tateLineCoordinates_tateLineCongr (e : L ≃ₗ[F] L') (c' : L' ≃ₗ[F] F) (n : ℤ)
    (x : tateLine F L n) :
    tateLineCoordinates c' n (tateLineCongr e n x) = tateLineCoordinates (e.trans c') n x := by
  cases n with
  | ofNat m => exact tensorPowerCoordinates_congr e c' m x
  | negSucc m =>
    exact tensorPowerCoordinates_congr e.symm.dualMap
      (c'.symm.dualMap.trans (LinearMap.ringLmapEquivSelf F F F)) (m + 1) x

/-- Multiplication by a unit, applied. -/
theorem smulOfUnit_apply_eq_mul (u : Fˣ) (x : F) : LinearEquiv.smulOfUnit u x = (u : F) * x :=
  rfl

/-- Tensor-power coordinates scale by `uⁿ` when the coordinate of the line is scaled by `u`. -/
theorem tensorPowerCoordinates_smulOfUnit (c : L ≃ₗ[F] F) (u : Fˣ) (n : ℕ)
    (x : TensorPower F n L) :
    tensorPowerCoordinates (c.trans (LinearEquiv.smulOfUnit u)) n x =
      (u : F) ^ n * tensorPowerCoordinates c n x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    simp [tensorPowerCoordinates, PiTensorProduct.constantBaseRingEquiv_tprod,
      smulOfUnit_apply_eq_mul, Finset.prod_mul_distrib, mul_left_comm]
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

/-- Coordinates of integer powers of a line scale by `uⁿ` when the coordinate of the line is
scaled by `u`. -/
theorem tateLineCoordinates_smulOfUnit (c : L ≃ₗ[F] F) (u : Fˣ) (n : ℤ) (x : tateLine F L n) :
    tateLineCoordinates (c.trans (LinearEquiv.smulOfUnit u)) n x =
      ((u ^ n : Fˣ) : F) * tateLineCoordinates c n x := by
  cases n with
  | ofNat m =>
    simpa [tateLineCoordinates] using tensorPowerCoordinates_smulOfUnit c u m x
  | negSucc m =>
    have hsymm : (c.trans (LinearEquiv.smulOfUnit u)).symm 1 = ((u⁻¹ : Fˣ) : F) • c.symm 1 := by
      apply (c.trans (LinearEquiv.smulOfUnit u)).injective
      rw [LinearEquiv.apply_symm_apply, map_smul, LinearEquiv.trans_apply,
        LinearEquiv.apply_symm_apply, smulOfUnit_apply_eq_mul]
      simp
    have hdual : (c.trans (LinearEquiv.smulOfUnit u)).symm.dualMap.trans
        (LinearMap.ringLmapEquivSelf F F F) =
        (c.symm.dualMap.trans (LinearMap.ringLmapEquivSelf F F F)).trans
          (LinearEquiv.smulOfUnit u⁻¹) := by
      refine LinearEquiv.ext fun l ↦ ?_
      show l ((c.trans (LinearEquiv.smulOfUnit u)).symm 1) = ((u⁻¹ : Fˣ) : F) * l (c.symm 1)
      rw [hsymm, map_smul, smul_eq_mul]
    show tensorPowerCoordinates ((c.trans (LinearEquiv.smulOfUnit u)).symm.dualMap.trans
      (LinearMap.ringLmapEquivSelf F F F)) (m + 1) x = _
    rw [hdual, tensorPowerCoordinates_smulOfUnit]
    simp [tateLineCoordinates, zpow_negSucc, inv_pow]

variable {U : Type uU} [AddCommGroup U] [Module F U] {U' : Type uU'} [AddCommGroup U']
  [Module F U'] {V : Type uV} [AddCommGroup V] [Module F V] {V' : Type uV'} [AddCommGroup V']
  [Module F V'] {W : Type uW} [AddCommGroup W] [Module F W] {W' : Type uW'} [AddCommGroup W']
  [Module F W']

/-- Coordinates of Tate twists are natural for isomorphisms of lines and of vector spaces. -/
theorem tateTwistCoordinates_tateTwistCongr (e : L ≃ₗ[F] L') (φ : U ≃ₗ[F] U')
    (c' : L' ≃ₗ[F] F) (n : ℤ) (x : tateTwist F L U n) :
    tateTwistCoordinates c' n (tateTwistCongr e φ n x) =
      φ (tateTwistCoordinates (e.trans c') n x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u l =>
    rw [tateTwistCongr_tmul, tateTwistCoordinates_tmul, tateTwistCoordinates_tmul,
      tateLineCoordinates_tateLineCongr, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Coordinates of Tate twists scale by `uⁿ` when the coordinate of the line is scaled by `u`. -/
theorem tateTwistCoordinates_smulOfUnit (c : L ≃ₗ[F] F) (u : Fˣ) (n : ℤ)
    (x : tateTwist F L U n) :
    tateTwistCoordinates (c.trans (LinearEquiv.smulOfUnit u)) n x =
      ((u ^ n : Fˣ) : F) • tateTwistCoordinates c n x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v l =>
    rw [tateTwistCoordinates_tmul, tateTwistCoordinates_tmul, tateLineCoordinates_smulOfUnit,
      mul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- **Twisted cup products are natural**: if `φ_W (u ∪ v) = φ_U u ∪' φ_V v`, then the same holds
for the induced cup products `U(n) × V(m) → W(n + m)` along `F(1) ≅ F(1)'`. -/
theorem tateCup_tateTwistCongr (hL : Module.finrank F L = 1) (hL' : Module.finrank F L' = 1)
    (e : L ≃ₗ[F] L') (φU : U ≃ₗ[F] U') (φV : V ≃ₗ[F] V') (φW : W ≃ₗ[F] W')
    (cup : U →ₗ[F] V →ₗ[F] W) (cup' : U' →ₗ[F] V' →ₗ[F] W')
    (hcup : ∀ u v, φW (cup u v) = cup' (φU u) (φV v)) (n m k : ℤ) (h : n + m = k)
    (x : tateTwist F L U n) (y : tateTwist F L V m) :
    tateTwistCongr e φW k (tateCup hL cup n m k h x y) =
      tateCup hL' cup' n m k h (tateTwistCongr e φU n x) (tateTwistCongr e φV m y) := by
  set c' := tateLineCoordinate hL'
  rw [tateCup_eq_with hL (e.trans c'), tateCup_eq_with hL' c']
  apply (tateTwistCoordinates c' k).injective
  simp only [tateCupWith, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rw [tateTwistCoordinates_tateTwistCongr, tateTwistCoordinates_tateTwistCongr,
    tateTwistCoordinates_tateTwistCongr, LinearEquiv.apply_symm_apply, hcup]

end Twists

variable {k : Type u} [Field k] {F : Type w} [Field F]

namespace WeilData.Iso

variable {W W' : WeilData k F} (e : Iso W W')

/-- An isomorphism of data commutes with pullbacks of graded pieces. -/
theorem gradeEquiv_pullDeg {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (n : ℤ)
    (a : W.grade Y n) :
    e.gradeEquiv X n (W.pullDeg f n a) = W'.pullDeg f n (e.gradeEquiv Y n a) :=
  Subtype.ext (e.equiv_pull f a)

/-- An isomorphism of data commutes with cup products of graded pieces. -/
theorem gradeEquiv_cup (X : (SmoothProjectiveScheme k).FullSubcategory) (i j n : ℤ) (h : i + j = n)
    (a : W.grade X i) (b : W.grade X j) :
    e.gradeEquiv X n (W.cup X i j n h a b) =
      W'.cup X i j n h (e.gradeEquiv X i a) (e.gradeEquiv X j b) :=
  Subtype.ext (map_mul (e.equiv X) _ _)

/-- An isomorphism of data commutes with pullbacks of twisted graded pieces. -/
theorem twEquiv_pullTw {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (n m : ℤ)
    (a : W.Tw Y n m) :
    e.twEquiv X n m (W.pullTw f n m a) = W'.pullTw f n m (e.twEquiv Y n m a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a l =>
    rw [pullTw, pullTw, tateTwistMap, tateTwistMap, TensorProduct.map_tmul, twEquiv, twEquiv,
      tateTwistCongr_tmul, tateTwistCongr_tmul, TensorProduct.map_tmul, gradeEquiv_pullDeg]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- An isomorphism of data commutes with twisted cup products. -/
theorem twEquiv_cupTw (X : (SmoothProjectiveScheme k).FullSubcategory) (i j n : ℤ) (h : i + j = n)
    (s t m : ℤ) (h' : s + t = m) (a : W.Tw X i s) (b : W.Tw X j t) :
    e.twEquiv X n m (W.cupTw X i j n h s t m h' a b) =
      W'.cupTw X i j n h s t m h' (e.twEquiv X i s a) (e.twEquiv X j t b) :=
  tateCup_tateTwistCongr _ _ _ _ _ _ _ _ (e.gradeEquiv_cup X i j n h) s t m h' a b

/-- An isomorphism of data preserving the trace maps preserves the pairings of axiom (A). -/
theorem pairingTw_twEquiv (htr : e.PreservesTrace) (X : (SmoothProjectiveScheme k).FullSubcategory)
    (d : ℕ) (hX : IsNonemptyEquidimensional X d) (i j : ℤ) (h : i + j = 2 * d) (s t : ℤ)
    (h' : s + t = d) (a : W.Tw X i s) (b : W.Tw X j t) :
    W'.pairingTw X d hX i j h s t h' (e.twEquiv X i s a) (e.twEquiv X j t b) =
      W.pairingTw X d hX i j h s t h' a b := by
  rw [pairingTw, pairingTw, LinearMap.compr₂_apply, LinearMap.compr₂_apply, ← twEquiv_cupTw, htr]

/-- **Isomorphisms preserve pushforwards**, when they preserve the trace maps. -/
theorem twEquiv_pushforward (htr : e.PreservesTrace) (hA : W.PerfectPairing)
    (hA' : W'.PerfectPairing) {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    {d d' : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y d')
    (j t j' t' : ℤ) (hj : j' + 2 * d = j + 2 * d') (ht : t' + d = t + d') (a : W.Tw X j t) :
    e.twEquiv Y j' t' (W.pushforward hA f hX hY j t j' t' hj ht a) =
      W'.pushforward hA' f hX hY j t j' t' hj ht (e.twEquiv X j t a) := by
  have key : (e.twEquiv Y j' t').toLinearMap ∘ₗ W.pushforward hA f hX hY j t j' t' hj ht ∘ₗ
      (e.twEquiv X j t).symm.toLinearMap = W'.pushforward hA' f hX hY j t j' t' hj ht := by
    rw [W'.eq_pushforward_iff hA' f hX hY j t j' t' hj ht]
    intro b a
    obtain ⟨b, rfl⟩ := (e.twEquiv Y (2 * d - j) (d - t)).surjective b
    obtain ⟨a, rfl⟩ := (e.twEquiv X j t).surjective a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [← twEquiv_pullTw, pairingTw_twEquiv e htr, pairingTw_twEquiv e htr]
    exact W.pushforward_trace hA f hX hY j t j' t' hj ht b a
  rw [← key]
  simp

/-- **Isomorphisms preserve the Künneth maps** `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b` of axiom (B). -/
theorem equiv_kunnethMap (X Y : (SmoothProjectiveScheme k).FullSubcategory) (x : W.H X ⊗[F] W.H Y) :
    e.equiv _ (W.kunnethMap X Y x) =
      W'.kunnethMap X Y (TensorProduct.map (e.equiv X).toLinearMap (e.equiv Y).toLinearMap x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [kunnethMap_tmul, map_mul, e.equiv_pull, TensorProduct.map_tmul,
      AlgEquiv.toLinearMap_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

end WeilData.Iso

end Stacks.WeilCohomology

end
