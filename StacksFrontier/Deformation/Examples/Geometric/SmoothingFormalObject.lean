module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.CartesianColimit
public import StacksFrontier.Deformation.BaseCategory.Pi
public import StacksFrontier.Deformation.Examples.Geometric.RingsTangentSpaceInjection
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Examples.Deformations.Schemes.LocalRing
public import StacksFrontier.Deformation.Examples.Geometric.RingsInfinitesimalAutomorphisms
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem

/-!
# The formal object of a family of local smoothings

Let `k` be a field. The formal disc `k⟦t⟧` is an object of the category `\widehat{𝒞}_k` of complete
local `k`-algebras with residue field `k` (`Deformation.Examples.Smoothing.powerSeriesObject`).
A flat `k⟦t⟧`-algebra `B` together with an identification `B / tB ≅ P` of `k`-algebras gives a
formal object of the deformation category `Def_P` of Stacks 0DY1 over `k⟦t⟧`: at level `n` it is
the flat `k⟦t⟧/𝔪^{n+1}`-algebra `B / 𝔪^{n+1} B`, with the transition maps the quotient maps. This
is the step of the proof of [Stacks, Tag 0E7Y] which reads "the system `(B_i/t^n B_i)` defines a
formal object of `Def_{𝒪_{X, p_i}}` over `k[[t]]`". It is carried out here for a finite family at
once, as a formal object of the product `∏ Def_{P_i}` over `𝒞_k`.

## Main definitions

* `Deformation.Examples.Smoothing.powerSeriesObject`: `k⟦t⟧` as an object of `\widehat{𝒞}_k`.
* `Deformation.Examples.Smoothing.levelHom`: the deformation `B / 𝔪^{n+1} B` of `P` over the
  `n`-th truncation of `k⟦t⟧`.
* `Deformation.Examples.Smoothing.formalObject`: the formal object of `Def_P`.
* `Deformation.Examples.Smoothing.piFormalObject`: the formal object of `∏ Def_{P_i}`.

## References

* [Stacks Project, Tag 0E7Y](https://stacks.math.columbia.edu/tag/0E7Y)
* [Stacks Project, Tag 06H3](https://stacks.math.columbia.edu/tag/06H3)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace Deformation.Examples.Smoothing

variable (k : Type u) [Field k]

/-- The residue field of `k⟦t⟧` is `k`, through the constant coefficient. -/
def powerSeriesResidueEquiv : ResidueField (PowerSeries k) ≃ₐ[k] k :=
  AlgEquiv.ofRingEquiv
    (f := (Ideal.quotEquivOfEq (PowerSeries.ker_coeff_eq_max_ideal (k := k)).symm).trans
      (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj))
    (fun a => by
      change PowerSeries.constantCoeff (algebraMap k (PowerSeries k) a) = a
      simp)

/-- **The formal disc as a complete local `k`-algebra with residue field `k`.** -/
abbrev powerSeriesObject : CompleteLocalAlgCat.{u, u, u} k k where
  carrier := PowerSeries k
  completeLocal :=
    { isNoetherian := inferInstance
      isLocal := inferInstance
      isComplete := by
        have : IsAdicComplete (maximalIdeal k) k := by
          rw [maximalIdeal_eq_bot]; infer_instance
        exact Stacks.CompleteLocalRing.RegularSubring.isAdicComplete_maximalIdeal_powerSeries k }
  residueEquiv := powerSeriesResidueEquiv k

section Level

variable (B : Type u) [CommRing B] [Algebra (PowerSeries k) B] [Module.Flat (PowerSeries k) B]
  (P : Type u) [CommRing P] [Algebra k P]

/-- The ideal `𝔪^{n+1}` of `k⟦t⟧` defining the `n`-th truncation. -/
abbrev truncIdeal (n : ℕ) : Ideal (PowerSeries k) :=
  maximalIdeal (PowerSeries k) ^ (n + 1)

/-- The ring `B / 𝔪^{n+1} B`. -/
abbrev levelFiber (n : ℕ) : Type u :=
  B ⧸ (truncIdeal k n).map (algebraMap (PowerSeries k) B)

/-- `B / 𝔪^{n+1} B` is flat over `k⟦t⟧ / 𝔪^{n+1}`, being the base change of `B`. -/
theorem flat_levelFiber (n : ℕ) :
    Module.Flat (PowerSeries k ⧸ truncIdeal k n) (levelFiber k B n) :=
  Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (truncIdeal k n)).toLinearEquiv

/-- The flat algebra `B / 𝔪^{n+1} B` over the `n`-th truncation of `k⟦t⟧`. -/
def levelFlat (n : ℕ) : FlatAlgebraCategory.{u, u} k k :=
  letI : Module.Flat (PowerSeries k ⧸ truncIdeal k n) (levelFiber k B n) :=
    flat_levelFiber k B n
  { base := (AdicTruncation.functor n).obj (powerSeriesObject k)
    fiber := levelFiber k B n
    algebra := inferInstanceAs (Algebra (PowerSeries k ⧸ truncIdeal k n) (levelFiber k B n))
    flat := inferInstanceAs
      (Module.Flat (PowerSeries k ⧸ truncIdeal k n) (levelFiber k B n)) }

omit [Module.Flat (PowerSeries k) B] in
/-- `𝔪^{n+2} B ⊆ 𝔪^{n+1} B`, so that `B / 𝔪^{n+2} B` maps onto `B / 𝔪^{n+1} B`. -/
theorem truncIdeal_map_le_succ (n : ℕ) :
    (truncIdeal k (n + 1)).map (algebraMap (PowerSeries k) B) ≤
      (truncIdeal k n).map (algebraMap (PowerSeries k) B) :=
  Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

omit [Module.Flat (PowerSeries k) B] in
/-- The structure map of `B / 𝔪^{n+1} B` over the truncation, on representatives. -/
theorem algebraMap_levelFiber_mk (n : ℕ) (r : PowerSeries k) :
    algebraMap (PowerSeries k ⧸ truncIdeal k n) (levelFiber k B n)
        (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (algebraMap (PowerSeries k) B r) := rfl

/-- **The transition map of the formal object**, as a base-change morphism of flat algebras over
the transition map of truncations of `k⟦t⟧`. -/
def levelFlatTransition (n : ℕ) : levelFlat k B (n + 1) ⟶ levelFlat k B n where
  base := (AdicTruncation.transitionNat n).app (powerSeriesObject k)
  map := CommRingCat.ofHom (Ideal.Quotient.factor (truncIdeal_map_le_succ k B n))
  cartesian := by
    refine (AlgebraicGeometry.FormalSpace.CartesianColimit.isPushout_of_surjective_of_ker_eq
      _ _ _ _ ?_ ?_ ?_ ?_).flip
    · ext x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    · exact Ideal.Quotient.factor_surjective
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : truncIdeal k (n + 1) ≤ truncIdeal k n)
    · exact Ideal.Quotient.factor_surjective (truncIdeal_map_le_succ k B n)
    · change RingHom.ker (Ideal.Quotient.factor (truncIdeal_map_le_succ k B n)) =
        (RingHom.ker (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
            truncIdeal k (n + 1) ≤ truncIdeal k n))).map
          (algebraMap (PowerSeries k ⧸ truncIdeal k (n + 1)) (levelFiber k B (n + 1)))
      rw [Ideal.Quotient.factor_ker, Ideal.Quotient.factor_ker, Ideal.map_map]
      have key : (algebraMap (PowerSeries k ⧸ truncIdeal k (n + 1)) (levelFiber k B (n + 1))).comp
          (Ideal.Quotient.mk (truncIdeal k (n + 1))) =
          (Ideal.Quotient.mk _).comp (algebraMap (PowerSeries k) B) :=
        RingHom.ext fun _ => rfl
      change _ = Ideal.map (algebraMap (PowerSeries k ⧸ truncIdeal k (n + 1))
        (levelFiber k B (n + 1))) (Ideal.map (Ideal.Quotient.mk (truncIdeal k (n + 1)))
          (truncIdeal k n))
      rw [Ideal.map_map, key]

variable [Algebra k B] [IsScalarTower k (PowerSeries k) B]
  (e : (B ⧸ Ideal.span {algebraMap (PowerSeries k) B PowerSeries.X}) ≃ₐ[k] P)

/-- The residue of a power series is its constant coefficient. -/
theorem powerSeriesResidueEquiv_residue (φ : PowerSeries k) :
    powerSeriesResidueEquiv k (residue (PowerSeries k) φ) = PowerSeries.constantCoeff φ := rfl

omit [Module.Flat (PowerSeries k) B] [Algebra k B] [IsScalarTower k (PowerSeries k) B] in
/-- `𝔪^{n+1} B ⊆ tB`. -/
theorem truncIdeal_map_le_span (n : ℕ) :
    (truncIdeal k n).map (algebraMap (PowerSeries k) B) ≤
      Ideal.span {algebraMap (PowerSeries k) B PowerSeries.X} := by
  have h : truncIdeal k n ≤ Ideal.span {(PowerSeries.X : PowerSeries k)} := by
    refine (Ideal.pow_le_self (Nat.succ_ne_zero n)).trans ?_
    show maximalIdeal (PowerSeries k) ≤ _
    rw [PowerSeries.maximalIdeal_eq_span_X]
  refine (Ideal.map_mono h).trans ?_
  rw [Ideal.map_span, Set.image_singleton]

/-- The reduction `B / 𝔪^{n+1} B ⟶ B / tB ≅ P`. -/
def levelToResidue (n : ℕ) : levelFiber k B n →+* P :=
  e.toRingHom.comp (Ideal.Quotient.factor (truncIdeal_map_le_span k B n))

omit [Module.Flat (PowerSeries k) B] in
/-- A power series and its constant coefficient agree in `B / tB`. -/
theorem mk_algebraMap_eq (φ : PowerSeries k) :
    Ideal.Quotient.mk (Ideal.span {algebraMap (PowerSeries k) B PowerSeries.X})
        (algebraMap (PowerSeries k) B φ) =
      algebraMap k _ (PowerSeries.constantCoeff φ) := by
  rw [IsScalarTower.algebraMap_apply k B, IsScalarTower.algebraMap_apply k (PowerSeries k) B,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq]
  obtain ⟨ψ, hψ⟩ := (PowerSeries.X_dvd_iff
    (φ := φ - PowerSeries.C (PowerSeries.constantCoeff φ))).mpr (by simp)
  have : algebraMap (PowerSeries k) B φ - algebraMap (PowerSeries k) B
      (algebraMap k (PowerSeries k) (PowerSeries.constantCoeff φ)) =
      algebraMap (PowerSeries k) B (φ - PowerSeries.C (PowerSeries.constantCoeff φ)) := by
    rw [map_sub]; rfl
  rw [this, hψ, map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

variable {k} in
/-- `𝔪^{n+1}` lies in the kernel of the constant coefficient. -/
theorem truncIdeal_le_ker (n : ℕ) :
    truncIdeal k n ≤ RingHom.ker (PowerSeries.constantCoeff (R := k)) := by
  rw [PowerSeries.ker_coeff_eq_max_ideal]
  exact Ideal.pow_le_self (Nat.succ_ne_zero n)

/-- The residue map of the `n`-th truncation of `k⟦t⟧`, as the constant coefficient. -/
def truncResidue (n : ℕ) : PowerSeries k ⧸ truncIdeal k n →+* k :=
  Ideal.Quotient.lift _ PowerSeries.constantCoeff fun _ ha =>
    RingHom.mem_ker.mp (truncIdeal_le_ker n ha)

/-- The residue map of a truncation on representatives. -/
theorem truncResidue_mk (n : ℕ) (φ : PowerSeries k) :
    truncResidue k n (Ideal.Quotient.mk _ φ) = PowerSeries.constantCoeff φ :=
  Ideal.Quotient.lift_mk _ _ _

/-- The kernel of the residue map of a truncation is generated by `t`. -/
theorem ker_truncResidue (n : ℕ) :
    RingHom.ker (truncResidue k n) =
      (Ideal.span {(PowerSeries.X : PowerSeries k)}).map (Ideal.Quotient.mk (truncIdeal k n)) := by
  rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective
    (RingHom.ker (truncResidue k n))]
  congr 1
  rw [RingHom.comap_ker]
  have : (truncResidue k n).comp (Ideal.Quotient.mk (truncIdeal k n)) =
      PowerSeries.constantCoeff := RingHom.ext fun φ => truncResidue_mk k n φ
  rw [this, PowerSeries.ker_coeff_eq_max_ideal, PowerSeries.maximalIdeal_eq_span_X]

/-- The residue map of the `n`-th truncation, as a morphism of `𝒞_k` to `k`. -/
def truncResidueHom (n : ℕ) :
    (AdicTruncation.functor n).obj (powerSeriesObject k) ⟶ residueFieldBase k k where
  hom :=
    { toRingHom := truncResidue k n
      commutes' := fun c => by
        change PowerSeries.constantCoeff (algebraMap k (PowerSeries k) c) = c
        simp }
  isLocal := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨φ, rfl⟩ : ∃ φ : PowerSeries k, Ideal.Quotient.mk (truncIdeal k n) φ = a :=
      Ideal.Quotient.mk_surjective a
    exact (PowerSeries.isUnit_iff_constantCoeff.mpr ha).map (Ideal.Quotient.mk (truncIdeal k n))
  residue_comm := by
    intro a
    obtain ⟨φ, rfl⟩ : ∃ φ : PowerSeries k, Ideal.Quotient.mk (truncIdeal k n) φ = a :=
      Ideal.Quotient.mk_surjective a
    rw [residueFieldBase_residueEquiv_residue]
    exact ((AdicTruncation.residueEquiv_residue_mk (powerSeriesObject k) n φ).trans
      (powerSeriesResidueEquiv_residue k φ)).symm

/-- **The level-`n` deformation of `P`**: the flat algebra `B / 𝔪^{n+1} B` with its reduction to
`P`, a base-change morphism to the trivial deformation `(k, P)`. -/
def levelHom (n : ℕ) : levelFlat k B n ⟶ residueFieldAlgebra (Λ := k) (k := k) P where
  base := truncResidueHom k n
  map := CommRingCat.ofHom (levelToResidue k B P e n)
  cartesian := by
    refine (AlgebraicGeometry.FormalSpace.CartesianColimit.isPushout_of_surjective_of_ker_eq
      _ _ _ _ ?_ ?_ ?_ ?_).flip
    · ext x
      obtain ⟨φ, rfl⟩ : ∃ φ : PowerSeries k, Ideal.Quotient.mk (truncIdeal k n) φ = x :=
        Ideal.Quotient.mk_surjective x
      change algebraMap k P (PowerSeries.constantCoeff φ) =
        e (Ideal.Quotient.mk _ (algebraMap (PowerSeries k) B φ))
      rw [mk_algebraMap_eq, AlgEquiv.commutes]
    · intro c
      exact ⟨Ideal.Quotient.mk _ (PowerSeries.C c), by
        change PowerSeries.constantCoeff (PowerSeries.C c) = c
        simp⟩
    · exact e.surjective.comp (Ideal.Quotient.factor_surjective _)
    · change RingHom.ker (levelToResidue k B P e n) = Ideal.map
        (algebraMap (PowerSeries k ⧸ truncIdeal k n) (levelFiber k B n))
        (RingHom.ker (truncResidue k n))
      rw [ker_truncResidue, levelToResidue, RingHom.ker_comp_of_injective _ e.injective,
        Ideal.Quotient.factor_ker, Ideal.map_map]
      have key : (algebraMap (PowerSeries k ⧸ truncIdeal k n) (levelFiber k B n)).comp
          (Ideal.Quotient.mk (truncIdeal k n)) =
          (Ideal.Quotient.mk _).comp (algebraMap (PowerSeries k) B) :=
        RingHom.ext fun _ => rfl
      rw [key, ← Ideal.map_map, Ideal.map_span, Ideal.map_span, Ideal.map_span]
      simp

/-- The transition maps of the levels commute with the reductions to `P`. -/
theorem levelFlatTransition_comp_levelHom (n : ℕ) :
    levelFlatTransition k B n ≫ levelHom k B P e n = levelHom k B P e (n + 1) := by
  apply FlatAlgebraCategory.Hom.ext
  · apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    obtain ⟨φ, rfl⟩ : ∃ φ : PowerSeries k, Ideal.Quotient.mk (truncIdeal k (n + 1)) φ = x :=
      Ideal.Quotient.mk_surjective x
    show truncResidue k n (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : truncIdeal k (n + 1) ≤ truncIdeal k n)
        (Ideal.Quotient.mk _ φ)) = truncResidue k (n + 1) (Ideal.Quotient.mk _ φ)
    rw [Ideal.Quotient.factor_mk, truncResidue_mk, truncResidue_mk]
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨b, rfl⟩ : ∃ b : B, Ideal.Quotient.mk
        ((truncIdeal k (n + 1)).map (algebraMap (PowerSeries k) B)) b = x :=
      Ideal.Quotient.mk_surjective x
    show e (Ideal.Quotient.factor (truncIdeal_map_le_span k B n)
        (Ideal.Quotient.factor (truncIdeal_map_le_succ k B n) (Ideal.Quotient.mk _ b))) =
      e (Ideal.Quotient.factor (truncIdeal_map_le_span k B (n + 1)) (Ideal.Quotient.mk _ b))
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk]

/-- **The formal object of `Def_P` over `k⟦t⟧`** given by `B` and `B / tB ≅ P`. -/
def formalObject : FormalObject (ringDeformationProjection k k P) where
  base := powerSeriesObject k
  level n := Over.mk (levelHom k B P e n)
  level_eq n := rfl
  transition n := Over.homMk (U := Over.mk (levelHom k B P e (n + 1)))
    (V := Over.mk (levelHom k B P e n)) (levelFlatTransition k B n)
    (levelFlatTransition_comp_levelHom k B P e n)
  transition_lift n := by
    change (ringDeformationProjection k k P).IsHomLift
      ((ringDeformationProjection k k P).map
        (Over.homMk (U := Over.mk (levelHom k B P e (n + 1)))
          (V := Over.mk (levelHom k B P e n)) (levelFlatTransition k B n)
          (levelFlatTransition_comp_levelHom k B P e n)))
      (Over.homMk (U := Over.mk (levelHom k B P e (n + 1)))
          (V := Over.mk (levelHom k B P e n)) (levelFlatTransition k B n)
          (levelFlatTransition_comp_levelHom k B P e n))
    infer_instance

end Level

section Pi

variable {ι : Type u} (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra (PowerSeries k) (B i)]
  [∀ i, Module.Flat (PowerSeries k) (B i)] [∀ i, Algebra k (B i)]
  [∀ i, IsScalarTower k (PowerSeries k) (B i)]
  (P : ι → Type u) [∀ i, CommRing (P i)] [∀ i, Algebra k (P i)]
  (e : ∀ i, (B i ⧸ Ideal.span {algebraMap (PowerSeries k) (B i) PowerSeries.X}) ≃ₐ[k] P i)

/-- **The formal object of `∏ Def_{P_i}` over `k⟦t⟧`** given by the family `B_i` with
`B_i / tB_i ≅ P_i`: at level `n` it is the family of the deformations `B_i / 𝔪^{n+1} B_i`. -/
def piFormalObject :
    FormalObject (piBasedCategory fun i => ringDeformationBasedCategory k k (P i)).p where
  base := powerSeriesObject k
  level n :=
    { base := (AdicTruncation.functor n).obj (powerSeriesObject k)
      x i := (formalObject k (B i) (P i) (e i)).level n
      hx _ := rfl }
  level_eq _ := rfl
  transition n :=
    { hbase := (AdicTruncation.transitionNat n).app (powerSeriesObject k)
      component i := (formalObject k (B i) (P i) (e i)).transition n
      hcomponent i := (formalObject k (B i) (P i) (e i)).transition_lift n }
  transition_lift n := by
    change (PiOver.structureFunctor fun i =>
        (ringDeformationBasedCategory k k (P i)).p).IsHomLift
      ((PiOver.structureFunctor fun i => (ringDeformationBasedCategory k k (P i)).p).map
        (X := ⟨(AdicTruncation.functor (n + 1)).obj (powerSeriesObject k),
          fun i => (formalObject k (B i) (P i) (e i)).level (n + 1), fun _ => rfl⟩)
        (Y := ⟨(AdicTruncation.functor n).obj (powerSeriesObject k),
          fun i => (formalObject k (B i) (P i) (e i)).level n, fun _ => rfl⟩)
        ⟨(AdicTruncation.transitionNat n).app (powerSeriesObject k),
          fun i => (formalObject k (B i) (P i) (e i)).transition n,
          fun i => (formalObject k (B i) (P i) (e i)).transition_lift n⟩) _
    infer_instance

/-- The level-`n` component of the formal object of `∏ Def_{P_i}` at `i` is the level-`n`
deformation of `P_i`. -/
theorem piFormalObject_level_x (n : ℕ) (i : ι) :
    ((piFormalObject k B P e).level n).x i = Over.mk (levelHom k (B i) (P i) (e i) n) := rfl

end Pi

end Deformation.Examples.Smoothing

end
