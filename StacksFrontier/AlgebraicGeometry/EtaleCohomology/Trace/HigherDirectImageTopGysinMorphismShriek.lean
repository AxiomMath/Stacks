module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageTopGysinMorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekFamily
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteEtaleDirectImagePointwiseTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkMapSurjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.OfStrictTowerHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurvePurityInput
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.ClosedPointFiniteResidueField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointwiseMixedInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkPointChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.LisseFiniteLocallyConstant

/-!
# The Gysin morphism of `R² g_!` for the family `Rʳ g_! G`: the reduction to the finite levels

This file reduces `Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageTopGysinMorphismInput` for
the family `Rʳ g_! G` of stable images
(`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekFamily`) to the construction of a
morphism `φ : π_*(i⁻¹ G')(-1) ⟶ R² g_! G` surjective on the finite-level stalks at the geometric
points over closed points, `G'` the torsion-free model of `G`
(`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageTopGysinLevelInput`). The source is
`A = π_*(tw Z (i⁻¹ G'))` for a Tate twist `tw` (`Stacks.EtaleCohomology.LAdicTwistInput`): it is
lisse, its Frobenius traces are `#κ(w) ^ m` times those of `π_*(i⁻¹ G')` by
`Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkFrobenius_directImage_pow_of_pointwise`
with `a = 1`, which are those of `π_*(i⁻¹ G)` (the same with `a = 0`: `G'` is isogenous to `G`).
Surjectivity on the finite levels gives surjectivity on the rational stalks by
`Stacks.EtaleCohomology.LAdicSheaf.surjective_rationalStalkMap_of_surjective_finiteLevelStalkMap`.
When the hypotheses defining `R² g_! G` fail, `R² g_! G = 0` and `φ = 0`.

This is part of the Leray step of the reduction of the weight bound of Weil II to curves
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageTopGysinMorphismInput_of_levelInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- A morphism into a zero ℓ-adic sheaf is surjective on rational stalks. -/
theorem LAdicSheaf.surjective_rationalStalkMap_of_isZero {X : B.Scheme} [IsNoetherian X.1]
    {F G : LAdicSheaf.{u, u + 1} B X ℓ} (hG : IsZero G) (φ : F ⟶ G) (s : GeometricPoint X.1) :
    Function.Surjective (LAdicSheaf.rationalStalkMap φ s) := by
  intro y
  refine ⟨0, ?_⟩
  have h : LAdicSheaf.rationalStalkEndRingHom G s (1 : End G) =
      LAdicSheaf.rationalStalkEndRingHom G s 0 := by
    congr 1
    exact hG.eq_of_src _ _
  rw [map_one, map_zero] at h
  have hy : y = 0 := by
    have := LinearMap.congr_fun h y
    simpa using this
  rw [hy, map_zero]

/-- **The torsion-free model of a lisse ℓ-adic sheaf is lisse**: its levels `ℓᴺ G_{N+n}` are
finite locally constant on underlying abelian sheaves by
`Stacks.EtaleCohomology.LAdicSheaf.isFiniteLocallyConstant_underlyingLAdicLevel_torsionFreeModel`,
hence as sheaves of `ℤ/ℓⁿ⁺¹`-modules. -/
theorem LAdicSheaf.isLisse_flatModel {X : B.Scheme} [IsNoetherian X.1]
    (G : LAdicSheaf.{u, u + 1} B X ℓ) (hG : G.IsLisse) : (LAdicSheaf.flatModel B ℓ G).IsLisse :=
  fun n => by
    have h := LAdicSheaf.isFiniteLocallyConstant_underlyingLAdicLevel_torsionFreeModel G hG
      (LAdicSheaf.torsionBound G) n
    have := (Stacks.ConstantSheaf.isFiniteLocallyConstant_moduleSheaf_iff_forget₂ _ _ _).2 h
    infer_instance

/-- **The Frobenius traces of the torsion-free model are those of the sheaf**: `G' = ℓᴺ G` is
isogenous to `G`. -/
theorem LAdicSheaf.trace_rationalStalkFrobenius_pow_flatModel {X : B.Scheme} [IsNoetherian X.1]
    (G : LAdicSheaf.{u, u + 1} B X ℓ) (x : X.1) (hx : Finite (X.1.residueField x)) (k : ℕ)
    (hk : 1 ≤ k) :
    LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ
        (LAdicSheaf.flatModel B ℓ G) x hx ^ k) =
      LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ G x hx ^ k) := by
  obtain ⟨e, rfl⟩ : ∃ e, k = e + 1 := ⟨k - 1, by omega⟩
  have := hx
  simp only [LAdicSheaf.rationalStalkFrobenius]
  rw [← LAdicSheaf.rationalStalkEnd_iterate, ← LAdicSheaf.rationalStalkEnd_iterate]
  exact (LAdicSheaf.trace_rationalStalkEnd_of_isogeny
    (LAdicSheaf.toTorsionFreeModel G (LAdicSheaf.torsionBound G))
    (LAdicSheaf.fromTorsionFreeModel G (LAdicSheaf.torsionBound G)) (LAdicSheaf.torsionBound G)
    (LAdicSheaf.toTorsionFreeModel_comp_fromTorsionFreeModel G _)
    (LAdicSheaf.fromTorsionFreeModel_comp_toTorsionFreeModel G _) _).symm

/-- `#κ(x) = #κ(f(x)) ^ (e + 1)` for some `e`, at a point with finite residue field. -/
theorem exists_natCard_residueField_eq_pow_succ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [Finite (X.residueField x)] :
    ∃ e : ℕ, Finite (Y.residueField (f.base x)) ∧
      Nat.card (X.residueField x) = Nat.card (Y.residueField (f.base x)) ^ (e + 1) := by
  let : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have : Finite (Y.residueField (f.base x)) :=
    Finite.of_injective _ (algebraMap (Y.residueField (f.base x)) (X.residueField x)).injective
  have : Module.Finite (Y.residueField (f.base x)) (X.residueField x) := Module.Finite.of_finite
  have hpos : 0 < Module.finrank (Y.residueField (f.base x)) (X.residueField x) :=
    Module.finrank_pos
  refine ⟨Module.finrank (Y.residueField (f.base x)) (X.residueField x) - 1, inferInstance, ?_⟩
  rw [Nat.sub_add_cancel hpos]
  exact Module.natCard_eq_pow_finrank

/-- **The Frobenius traces of the inverse image of the torsion-free model are those of the inverse
image.** -/
theorem LAdicSheaf.trace_rationalStalkFrobenius_pow_inverseImage_flatModel {X Y : B.Scheme}
    [IsNoetherian X.1] [IsNoetherian Y.1] (i : X ⟶ Y) [LocallyOfFiniteType (B.inclusion.map i)]
    (G : LAdicSheaf.{u, u + 1} B Y ℓ) (x : X.1)
    (hx : Finite (X.1.residueField x)) (k : ℕ) (hk : 1 ≤ k) :
    LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ
        (LAdicSheaf.inverseImage i (LAdicSheaf.flatModel B ℓ G)) x hx ^ k) =
      LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ
        (LAdicSheaf.inverseImage i G) x hx ^ k) := by
  have : Finite ((B.inclusion.obj X).residueField x) := hx
  obtain ⟨e, hy, he⟩ := exists_natCard_residueField_eq_pow_succ (B.inclusion.map i) x
  rw [LAdicSheaf.trace_rationalStalkFrobenius_inverseImage_pow Y ℓ i _ x hx hy e he hk,
    LAdicSheaf.trace_rationalStalkFrobenius_inverseImage_pow Y ℓ i _ x hx hy e he hk,
    LAdicSheaf.trace_rationalStalkFrobenius_pow_flatModel B ℓ G _ hy _
      (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.succ_ne_zero e) (by omega)))]

/-- **The level form of the Gysin input for `R² g_! G`**: in the situation of
`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageTopGysinMorphismInput`, when the hypotheses
defining `R² g_! G` hold, there is a morphism from `π_*(tw Z (i⁻¹ G'))`, `G'` the torsion-free
model of `G`, to `R² g_! G` surjective on every finite-level stalk at the geometric points over
the closed points. -/
def LAdicSheaf.HigherDirectImageTopGysinLevelInput
    (tw : ∀ (X : B.Scheme) [IsNoetherian X.1], LAdicSheaf.{u, u + 1} B X ℓ →
      LAdicSheaf.{u, u + 1} B X ℓ) : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (p n : ℕ) [Fact p.Prime] [CharP k p],
    Fintype.card k = p ^ n → ℓ ≠ p → ∀ (U V Z : B.Scheme)
    [IsNoetherian U.1] [IsNoetherian V.1] [IsNoetherian Z.1] (g : U ⟶ V)
    [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map g)] [SmoothOfRelativeDimension 1 (B.inclusion.map g)]
    [IsAffineHom (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
    (i : Z ⟶ U) [IsClosedImmersion (B.inclusion.map i)] (π : Z ⟶ V)
    [IsFinite (B.inclusion.map π)] [Etale (B.inclusion.map π)], i ≫ g = π →
    ∀ f : Γ(B.inclusion.obj U, ⊤),
      Set.range (B.inclusion.map i).base = (B.inclusion.obj U).zeroLocus {f} →
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ B.inclusion.obj V),
      ∀ C : Set (Limits.pullback (B.inclusion.map g) w : Scheme.{u}),
        C ∈ irreducibleComponents _ → (∃ x ∈ C, ∃ y ∈ C, x ≠ y) →
        (C ∩ (Limits.pullback.fst (B.inclusion.map g) w).base ⁻¹'
          Set.range (B.inclusion.map i).base).Nonempty) →
    ∀ (fV : V.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fV] [Smooth fV]
      (G : LAdicSheaf.{u, u + 1} B U ℓ), G.IsLisse →
      LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G 2 →
    ∀ hA : (tw Z (LAdicSheaf.inverseImage i (LAdicSheaf.flatModel B ℓ G))).IsLisse,
    ∃ φ : SmallEtale.LAdicSheaf.directImage π
        (tw Z (LAdicSheaf.inverseImage i (LAdicSheaf.flatModel B ℓ G)))
        (LAdicSheaf.isFiniteTypeLocallyConstant_level_of_isLisse _ hA) ⟶
          LAdicSheaf.higherDirectImageShriek B ℓ g jg G 2,
      ∀ (w : closedPoints V.1) (m : ℕ),
        Function.Surjective (finiteLevelStalkMap φ (geometricPointAt V.1 w.1) m).hom

/-- **Reduction of the Gysin input for `R² g_!` to its finite levels**, for a Tate twist `tw`
(`Stacks.EtaleCohomology.LAdicTwistInput`). -/
theorem LAdicSheaf.higherDirectImageTopGysinMorphismInput_of_levelInput
    (tw : ∀ (X : B.Scheme) [IsNoetherian X.1], LAdicSheaf.{u, u + 1} B X ℓ →
      LAdicSheaf.{u, u + 1} B X ℓ) (hTw : LAdicTwistInput B ℓ tw)
    (hLev : LAdicSheaf.HigherDirectImageTopGysinLevelInput B ℓ tw) :
    LAdicSheaf.HigherDirectImageTopGysinMorphismInput
      (LAdicSheaf.higherDirectImageShriekFamily B ℓ) := by
  intro k _ _ p n _ _ hcard hℓp U V Z _ _ _ g _ _ _ _ _ jg i _ π _ _ hπ f hZ hfib fV _ _ G hG hR
  have hG' := LAdicSheaf.isLisse_flatModel B ℓ G hG
  have hi : (LAdicSheaf.inverseImage i (LAdicSheaf.flatModel B ℓ G)).IsLisse :=
    LAdicSheaf.IsLisse.inverseImage i hG'
  have : LocallyOfFiniteType (B.inclusion.map π ≫ fV) := inferInstance
  obtain ⟨hAl, hAtr⟩ := hTw k p n hcard hℓp Z (B.inclusion.map π ≫ fV)
    (LAdicSheaf.inverseImage i (LAdicSheaf.flatModel B ℓ G)) hi
  have hAf := LAdicSheaf.isFiniteTypeLocallyConstant_level_of_isLisse _ hAl
  have htrace : ∀ (hF : ∀ m, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant
        (ZMod (ℓ ^ (m + 1))) (SmallEtale.topology B Z.1 Z.property)
        ((LAdicSheaf.inverseImage i G).level m)) (w : closedPoints V.1) (m : ℕ), 1 ≤ m →
      LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B V ℓ
          (SmallEtale.LAdicSheaf.directImage π
            (tw Z (LAdicSheaf.inverseImage i (LAdicSheaf.flatModel B ℓ G))) hAf) w.1
          (finite_residueField fV w.1 w.2) ^ m) =
        (Nat.card (V.1.residueField w.1) : ℚ_[ℓ]) ^ m *
          LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B V ℓ
            (SmallEtale.LAdicSheaf.directImage π (LAdicSheaf.inverseImage i G) hF) w.1
            (finite_residueField fV w.1 w.2) ^ m) := by
    intro hF w m hm
    have : Finite (V.1.residueField w.1) := finite_residueField fV w.1 w.2
    have hi' := LAdicSheaf.isFiniteTypeLocallyConstant_level_of_isLisse _ hi
    have h1 := LAdicSheaf.trace_rationalStalkFrobenius_directImage_pow_of_pointwise π _ _ hAf hi' 1
      w.1 (fun x hx hfx k hk => by
        rw [one_mul]
        have : Finite ((B.inclusion.obj Z).residueField x) := hfx
        exact hAtr ⟨x, isClosed_singleton_of_finite_residueField (B.inclusion.map π ≫ fV) x⟩ k)
      m hm
    have h0 := LAdicSheaf.trace_rationalStalkFrobenius_directImage_pow_of_pointwise π _ _ hi' hF 0
      w.1 (fun x _ hfx k hk => by
        rw [zero_mul, pow_zero, one_mul]
        exact LAdicSheaf.trace_rationalStalkFrobenius_pow_inverseImage_flatModel B ℓ i G x hfx k hk)
      m hm
    rw [h1, h0, one_mul, zero_mul, pow_zero, one_mul]
  by_cases hcond : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G 2
  · obtain ⟨φ, hφ⟩ := hLev k p n hcard hℓp U V Z g jg i π hπ f hZ hfib fV G hG hcond hAl
    exact ⟨_, φ, SmallEtale.LAdicSheaf.directImage_isLisse π _ _, fun w =>
      LAdicSheaf.surjective_rationalStalkMap_of_surjective_finiteLevelStalkMap φ _ (hφ w),
      htrace⟩
  · have hz : IsZero (LAdicSheaf.higherDirectImageShriek B ℓ g jg G 2) := by
      rw [LAdicSheaf.higherDirectImageShriek, dite_eq_right hcond]
      exact LAdicSheaf.zeroSystem_isZero B V ℓ
    exact ⟨_, 0, SmallEtale.LAdicSheaf.directImage_isLisse π _ _, fun w =>
      LAdicSheaf.surjective_rationalStalkMap_of_isZero B ℓ hz _ _, htrace⟩

end Stacks.EtaleCohomology

end
