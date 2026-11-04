module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkFrobeniusCharpoly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharPowerSeriesCharpoly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveBaseFieldLisse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The geometric Frobenius on a stalk as the Frobenius on `H⁰_c` of the residue field

Let `w` be a point of a scheme `W` with finite residue field `κ = κ(w)`, and `M` an ℓ-adic sheaf on
`W`. Then the characteristic polynomial of the geometric Frobenius `π_w` on the rational stalk
`M_w̄ ⊗ ℚ_ℓ` is that of the geometric Frobenius of `κ` on `H⁰_c(Spec κ̄, i⁻¹ M ⊗ ℚ_ℓ)`, where
`i : Spec κ ⟶ W` is the canonical morphism.

All names are in the namespace `Stacks.EtaleCohomology`.

## Main definitions

* `residueFieldPointHom`: the canonical morphism `Spec κ(w) ⟶ W` of the big étale site.

## Main results

* `residueDegree_id_spec`: the closed point of `Spec κ` has degree one over `κ`.
* `LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_etale`:
  `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is finite dimensional for `X` finite étale over `k`.
* `LAdicSheaf.charpoly_rationalStalkFrobenius_eq_residueField`: the stalk Frobenius at `w` and the
  Frobenius on `H⁰_c(Spec κ̄, i⁻¹ M ⊗ ℚ_ℓ)` have the same characteristic polynomial.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-- Every point of `Spec κ` is closed, `κ` a field. -/
private theorem isClosed_singleton_spec (κ : Type u) [Field κ] (x : Spec (.of κ)) :
    IsClosed ({x} : Set (Spec (.of κ))) := by
  rw [Set.eq_univ_of_forall (fun y => Set.mem_singleton_iff.2 (Subsingleton.elim y x))]
  exact isClosed_univ

/-- An invertible linear endomorphism has nonzero determinant. -/
private theorem det_ne_zero_of_isUnit {R M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] {f : Module.End R M} (hf : IsUnit f) :
    LinearMap.det f ≠ 0 :=
  ((LinearMap.isUnit_iff_isUnit_det _).1 hf).ne_zero

/-- **The point of `Spec κ` has degree one over `κ`.** -/
theorem residueDegree_id_spec (κ : Type u) [Field κ] (x : Spec (.of κ)) :
    residueDegree (𝟙 (Spec (.of κ))) x = 1 := by
  let : Algebra κ ((Spec (.of κ)).residueField x) :=
    (fieldToResidue (𝟙 (Spec (.of κ))) x).hom.toAlgebra
  have hx := isClosed_singleton_spec κ x
  have hsurj : Function.Surjective (algebraMap κ ((Spec (.of κ)).residueField x)) := by
    have h := fieldToResidue_eq_appLE_comp_evaluation (𝟙 (Spec (.of κ))) (U := ⊤) le_top x trivial
    show Function.Surjective (fieldToResidue (𝟙 (Spec (.of κ))) x).hom
    have hid : Function.Bijective (Scheme.Hom.appLE (𝟙 (Spec (.of κ))) ⊤ ⊤ le_top).hom := by
      have : Scheme.Hom.appLE (𝟙 (Spec (.of κ))) ⊤ ⊤ le_top = 𝟙 _ := by
        simp [Scheme.Hom.appLE]
      rw [this]
      exact ConcreteCategory.bijective_of_isIso _
    rw [h, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
    exact (evaluation_surjective (isAffineOpen_top _) x trivial hx).comp
      (hid.2.comp (ConcreteCategory.bijective_of_isIso _).2)
  have hle : residueDegree (𝟙 (Spec (.of κ))) x ≤ 1 :=
    finrank_le_one (1 : (Spec (.of κ)).residueField x) fun z => by
      obtain ⟨c, rfl⟩ := hsurj z
      exact ⟨c, by rw [Algebra.smul_def, mul_one]⟩
  have := residueDegree_pos (𝟙 (Spec (.of κ))) x hx
  omega

variable (B : BigEtaleSite.{u}) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [Fact ℓ.Prime] {W : B.Scheme} [IsNoetherian W.1]

/-- **`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is finite dimensional for `X` finite étale over `k`.** -/
@[sga "4½ Rapport 2.10" "special case"]
theorem LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_etale
    (X : B.Scheme) [IsNoetherian X.1] {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [Etale f] [IsFinite f]
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
    [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ) :
    FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) :=
  LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_perfect B X ℓ f j kbar p q
    hcard F (LAdicSheaf.isPerfect_compactSupportFrobeniusCohomology_levelComplex_of_etale B X ℓ f j
      kbar F) i

/-- The canonical morphism `Spec κ(w) ⟶ W` of the big étale site, for a point `w` of `W` with
finite residue field. -/
abbrev residueFieldPointHom (w : W.1) [Finite (W.1.residueField w)] :
    BigEtaleSite.specField B W (W.1.residueField w) ⟶ W :=
  ObjectProperty.homMk (W.1.fromSpecResidueField w)

/-- **The geometric Frobenius at a point `w` with finite residue field `κ` is the geometric
Frobenius of `κ` on `H⁰_c(Spec κ̄, i⁻¹ M)`**, `i : Spec κ ⟶ W` the canonical morphism: the two
endomorphisms of `M_w̄ ⊗ ℚ_ℓ` and of `H⁰_c(Spec κ̄, i⁻¹ M ⊗ ℚ_ℓ)` have the same characteristic
polynomial. -/
theorem LAdicSheaf.charpoly_rationalStalkFrobenius_eq_residueField (M : LAdicSheaf.{u, u + 1} B W ℓ)
    (w : W.1) [Fintype (W.1.residueField w)] (hw : Finite (W.1.residueField w))
    (kbar : Type u) [Field kbar] [Algebra (W.1.residueField w) kbar] [IsAlgClosed kbar]
    (p n : ℕ) [Fact p.Prime] [CharP (W.1.residueField w) p]
    (hcard : Fintype.card (W.1.residueField w) = p ^ n)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology
      (k := W.1.residueField w) B (BigEtaleSite.specField B W (W.1.residueField w)) ℓ (𝟙 _)
      (CompactificationOf.ofProper (𝟙 _)) kbar
      (LAdicSheaf.inverseImage (residueFieldPointHom B w) M) 0)] :
    (LAdicSheaf.rationalStalkFrobenius B W ℓ M w hw).charpoly =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius (k := W.1.residueField w) B
        (BigEtaleSite.specField B W (W.1.residueField w)) ℓ (𝟙 _)
        (CompactificationOf.ofProper (𝟙 _)) kbar p n hcard
        (LAdicSheaf.inverseImage (residueFieldPointHom B w) M) 0).hom.charpoly := by
  let P := BigEtaleSite.specField B W (W.1.residueField w)
  let i := residueFieldPointHom B w
  let : Fintype (closedPoints P.1) := Fintype.ofFinite _
  let x₀ : closedPoints P.1 := ⟨default, isClosed_singleton_spec _ _⟩
  have h := LAdicSheaf.charPowerSeries_rationalGeometricCompactlySupportedFrobenius_eq_prod B P ℓ
    (𝟙 _) (CompactificationOf.ofProper (𝟙 _)) kbar p n hcard (LAdicSheaf.inverseImage i M)
  rw [Fintype.prod_subsingleton _ x₀, residueDegree_id_spec] at h
  have : Finite (P.1.residueField x₀.1) := finite_residueField (𝟙 _) x₀.1 x₀.2
  let π := LAdicSheaf.rationalGeometricCompactlySupportedFrobenius (k := W.1.residueField w) B P ℓ
    (𝟙 _) (CompactificationOf.ofProper (𝟙 _)) kbar p n hcard (LAdicSheaf.inverseImage i M) 0
  have hπ : LinearMap.det π.hom ≠ 0 :=
    det_ne_zero_of_isUnit ((Module.End.isUnit_iff _).2 (ConcreteCategory.bijective_of_isIso π))
  have hσ : LinearMap.det (LAdicSheaf.rationalStalkFrobenius B P ℓ (LAdicSheaf.inverseImage i M)
      x₀.1 (finite_residueField (𝟙 _) x₀.1 x₀.2)) ≠ 0 :=
    det_ne_zero_of_isUnit (LAdicSheaf.isUnit_rationalStalkEnd B P ℓ _ _)
  rw [charpoly_eq_of_charPowerSeries_eq _ _ hπ hσ h]
  have hbase : (B.inclusion.map i).base x₀.1 = w := Scheme.fromSpecResidueField_apply _ _
  have hcardx : Nat.card (P.1.residueField x₀.1) = Nat.card (W.1.residueField w) := by
    rw [natCard_residueField_of_residueDegree_eq_one (𝟙 _) x₀.1
      (residueDegree_id_spec (W.1.residueField w) x₀.1),
      Nat.card_eq_fintype_card]
  have := LAdicSheaf.charpoly_rationalStalkFrobenius_inverseImage B ℓ i M x₀.1
    (finite_residueField (𝟙 _) x₀.1 x₀.2) (by rw [hbase]; exact hw) (by rw [hcardx, hbase])
  have key : ∀ (y : W.1) (hy : y = w) (hy' : Finite (W.1.residueField y)),
      (LAdicSheaf.rationalStalkFrobenius B W ℓ M y hy').charpoly =
        (LAdicSheaf.rationalStalkFrobenius B W ℓ M w hw).charpoly := by
    rintro _ rfl _
    rfl
  exact (this.trans (key _ hbase _)).symm

end Stacks.EtaleCohomology
