module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCover
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverTorsor
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOnePullback
public import StacksFrontier.RingTheory.DiscreteValuationRing.GaloisTame

/-!
# Galois covers with group of invertible order are tame

Let `U ⊆ X` be open and `Z ⟶ U` a finite étale Galois cover with group `G` whose order is
invertible on `X`. Every field factor `L` of `Z` over the fraction field `K` of a local ring of `X`
is Galois over `K` of degree dividing `|G|`: the `K`-embeddings of `L` into any extension `F` of
`L` correspond to the stabiliser in `G` of the point of `Z` with residue field `L`, because the
lifts of a point through a torsor form a torsor. Hence `Z` is tamely ramified over `X` in
codimension one, by [Stacks, Tag 09EB]. This is the appeal to 09EB in the proof of
[Stacks, Tag 0EYJ].

## Main results

* `AlgebraicGeometry.isGalois_and_finrank_dvd_of_isFieldFactorAt`: field factors of a Galois cover
  are Galois of degree dividing the order of the group.
* `AlgebraicGeometry.isTamelyRamifiedInCodimensionOne_of_galoisCover`: the tameness statement.

## References

* [Stacks Project, Tag 09EB](https://stacks.math.columbia.edu/tag/09EB)
* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe v u

namespace AlgebraicGeometry

open Abhyankar

variable {T : Scheme.{u}} {G : Type v} [Group G] [Finite G] (Z : FiniteEtaleGaloisCover T G)

/-- The action of `G` on the total space of a Galois cover, as automorphisms over the base. -/
abbrev FiniteEtaleGaloisCover.overAction : Gᵐᵒᵖ →* Aut (Over.mk Z.obj.hom) :=
  ((MorphismProperty.Over.forget _ ⊤ _).mapAut Z.obj).comp Z.action

/-- The stabiliser in `G` of a point of the total space of a Galois cover. -/
def FiniteEtaleGaloisCover.stabilizer (y : Z.obj.left) : Subgroup G where
  carrier := {σ | (Z.overAction (.op σ)).hom.left y = y}
  one_mem' := by
    change (Z.overAction 1).hom.left y = y
    rw [map_one]
    rfl
  mul_mem' := by
    intro σ τ hσ hτ
    change (Z.overAction (.op (σ * τ))).hom.left y = y
    rw [MulOpposite.op_mul, map_mul, Aut.Aut_mul_def]
    change (Z.overAction (.op τ)).hom.left ((Z.overAction (.op σ)).hom.left y) = y
    rwa [show (Z.overAction (.op σ)).hom.left y = y from hσ]
  inv_mem' := by
    intro σ hσ
    change (Z.overAction (.op σ⁻¹)).hom.left y = y
    rw [MulOpposite.op_inv, map_inv, Aut.Aut_inv_def]
    have h2 : (Z.overAction (.op σ)).inv.left ((Z.overAction (.op σ)).hom.left y) = y := by
      have h3 := congrArg (fun φ : Over.mk Z.obj.hom ⟶ Over.mk Z.obj.hom ↦ φ.left y)
        (Z.overAction (.op σ)).hom_inv_id
      simp only [Over.comp_left, Over.id_left, Scheme.Hom.comp_apply] at h3
      exact h3.trans rfl
    rwa [show (Z.overAction (.op σ)).hom.left y = y from hσ] at h2

/-- A morphism out of the spectrum of a field factoring through the spectrum of another field
sends the closed point to the image of the closed point. -/
lemma Spec_comp_apply_closedPoint {F L : Type u} [Field F] [Field L] {Q : Scheme.{u}}
    (g : Spec (.of F) ⟶ Spec (.of L)) (n : Spec (.of L) ⟶ Q) :
    (g ≫ n) (closedPoint F) = n (closedPoint L) := by
  show n (g _) = _
  congr 1
  exact Subsingleton.elim _ _

section FieldFactor

variable {X : Scheme.{u}} (U : X.Opens) (Z : FiniteEtaleGaloisCover U.toScheme G) (x : X)
  (K L : Type u) [Field K] [Field L] [Algebra (X.presheaf.stalk x) K]
  [IsFractionRing (X.presheaf.stalk x) K] [Algebra K L]
  (w : Spec (.of K) ⟶ U) (v : Spec (.of L) ⟶ Z.obj.left)
  (hw : w ≫ U.ι = Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) K)) ≫
    X.fromSpecStalk x)
  (hv : v ≫ Z.obj.hom = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ w)
  (e : Z.obj.left.residueField (v (closedPoint L)) ≃+* L)
  (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Z.obj.left.fromSpecResidueField (v (closedPoint L)) = v)

include hw in
/-- Two ring maps out of `K` agree once their spectra agree over `U`. -/
lemma ringHom_eq_of_spec_map_comp_eq {F : Type u} [Field F] {ψ₁ ψ₂ : K →+* F}
    (h : Spec.map (CommRingCat.ofHom ψ₁) ≫ w = Spec.map (CommRingCat.ofHom ψ₂) ≫ w) :
    ψ₁ = ψ₂ := by
  have h2 := congrArg (· ≫ U.ι) h
  simp only [Category.assoc, hw] at h2
  rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp,
    Spec.map_inj] at h2
  apply IsLocalization.ringHom_ext (nonZeroDivisors (X.presheaf.stalk x))
  simpa [RingHom.comp_assoc] using congrArg CommRingCat.Hom.hom h2

include he in
/-- A point of `Spec F` hitting the point of `Z` with residue field `L` factors through `v`. -/
lemma exists_ringHom_spec_map_comp_eq {F : Type u} [Field F] (m : Spec (.of F) ⟶ Z.obj.left)
    (hm : m (closedPoint F) = v (closedPoint L)) :
    ∃ φ₀ : L →+* F, Spec.map (CommRingCat.ofHom φ₀) ≫ v = m := by
  let χ : Z.obj.left.residueField (v (closedPoint L)) ⟶ .of F :=
    (Z.obj.left.residueFieldCongr hm.symm).hom ≫
      Z.obj.left.descResidueField (Scheme.stalkClosedPointTo m)
  have hχ : Spec.map χ ≫ Z.obj.left.fromSpecResidueField _ = m := by
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]
  let φ₀ : L →+* F := χ.hom.comp e.symm.toRingHom
  refine ⟨φ₀, ?_⟩
  rw [← he, ← Category.assoc, ← Spec.map_comp, ← hχ]
  congr 2
  ext r
  simp [φ₀]

include hw hv he in
/-- **The embeddings of a field factor are the stabiliser.** For every extension `F` of `L`, the
`K`-embeddings `L → F` correspond to the elements of `G` fixing the point of `Z` with residue
field `L`. -/
theorem natCard_algHom_eq_card_stabilizer (F : Type u) [Field F] [Algebra K F] [Algebra L F]
    [IsScalarTower K L F] :
    Nat.card (L →ₐ[K] F) = Nat.card (Z.stabilizer (v (closedPoint L))) := by
  classical
  let π := Z.obj.hom
  let a := Z.overAction
  let y := v (closedPoint L)
  let t : (L →ₐ[K] F) → (Spec (.of F) ⟶ Z.obj.left) := fun φ ↦
    Spec.map (CommRingCat.ofHom (φ : L →+* F)) ≫ v
  have hπ : ∀ φ, t φ ≫ π = Spec.map (CommRingCat.ofHom (algebraMap K F)) ≫ w := fun φ ↦ by
    simp only [t, π, Category.assoc, hv]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]
  let sF := t (IsScalarTower.toAlgHom K L F)
  have ht : ∀ φ, t φ ≫ π = sF ≫ π := fun φ ↦ (hπ φ).trans (hπ _).symm
  have hty : ∀ φ, t φ (closedPoint F) = y := fun φ ↦
    Spec_comp_apply_closedPoint (Spec.map (CommRingCat.ofHom (φ : L →+* F))) v
  have hsy : sF (closedPoint F) = y := hty _
  have hex := fun φ ↦ existsUnique_comp_twist π a sF (t φ) (ht φ)
  let Θ : (L →ₐ[K] F) → Z.stabilizer y := fun φ ↦ ⟨(hex φ).choose, by
    have h := congrArg (· (closedPoint F)) (hex φ).choose_spec.1
    change (a _).hom.left (sF (closedPoint F)) = t φ (closedPoint F) at h
    rwa [hsy, hty φ] at h⟩
  have hΘ : ∀ φ, sF ≫ (a (.op (Θ φ : G))).hom.left = t φ := fun φ ↦ (hex φ).choose_spec.1
  refine Nat.card_congr (Equiv.ofBijective Θ ⟨fun φ φ' h ↦ ?_, fun σ ↦ ?_⟩)
  · have h1 : t φ = t φ' := by rw [← hΘ, ← hΘ, h]
    simp only [t] at h1
    rw [← he, ← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp,
      Spec.map_inj] at h1
    ext l
    simpa using congrArg (fun χ ↦ χ.hom (e.symm l)) h1
  · let m := sF ≫ (a (.op (σ : G))).hom.left
    have hm : m (closedPoint F) = y := by
      show (a (.op (σ : G))).hom.left (sF (closedPoint F)) = y
      rw [hsy]
      exact σ.2
    obtain ⟨φ₀, htφ₀⟩ := exists_ringHom_spec_map_comp_eq U Z L v e he _ hm
    have hlin : φ₀.comp (algebraMap K L) = algebraMap K F := by
      refine ringHom_eq_of_spec_map_comp_eq U x K w hw ?_
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← hv, ← Category.assoc,
        htφ₀, ← hπ (IsScalarTower.toAlgHom K L F)]
      simp only [m, π, Category.assoc]
      congr 1
      exact Over.w (a (.op (σ : G))).hom
    let φ : L →ₐ[K] F := { φ₀ with commutes' := fun r ↦ congrArg (· r) hlin }
    exact ⟨φ, Subtype.ext ((hex φ).unique (hex φ).choose_spec.1
      (show sF ≫ (a (.op (σ : G))).hom.left = t φ from htφ₀.symm))⟩

end FieldFactor

/-- **Field factors of a Galois cover are Galois of degree dividing the order of the group.** -/
theorem isGalois_and_finrank_dvd_of_isFieldFactorAt {X : Scheme.{u}} (U : X.Opens)
    (Z : FiniteEtaleGaloisCover U.toScheme G) (x : X) (K L : Type u) [Field K] [Field L]
    [Algebra (X.presheaf.stalk x) K] [IsFractionRing (X.presheaf.stalk x) K] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hFF : Stacks.FundamentalGroup.IsFieldFactorAt U.ι Z.obj.hom x K L) :
    IsGalois K L ∧ Module.finrank K L ∣ Nat.card G := by
  obtain ⟨w, v, hw, hv, e, he⟩ := hFF
  have h1 := natCard_algHom_eq_card_stabilizer U Z x K L w v hw hv e he L
  have h2 := natCard_algHom_eq_card_stabilizer U Z x K L w v hw hv e he (AlgebraicClosure L)
  have hdeg : Module.finrank K L = Nat.card (Z.stabilizer (v (closedPoint L))) := by
    rw [← Field.finSepDegree_eq_finrank_of_isSeparable, ← h2]
    rfl
  refine ⟨IsGalois.of_card_aut_eq_finrank K L ?_, ?_⟩
  · rw [hdeg, ← h1]
    exact Nat.card_congr (algEquivEquivAlgHom K L)
  · rw [hdeg]
    exact Subgroup.card_subgroup_dvd_card _

open Stacks.FundamentalGroup in
/-- **Galois covers with group of order invertible on `X` are tamely ramified in codimension
one** (the appeal to [Stacks, Tag 09EB] in the proof of [Stacks, Tag 0EYJ]). -/
theorem isTamelyRamifiedInCodimensionOne_of_finiteEtaleGaloisCover {X : Scheme.{u}}
    (U : X.Opens) (G : Type v) [Group G] [Finite G]
    (hG : ∀ x : X, IsUnit (Nat.card G : X.residueField x))
    (Z : FiniteEtaleGaloisCover U.toScheme G) :
    IsTamelyRamifiedInCodimensionOne U.ι Z.obj.hom := by
  intro Zd _ hD hV K L _ _ _ _ _ _ _ _ _ hFF
  obtain ⟨hgal, k, hk⟩ := isGalois_and_finrank_dvd_of_isFieldFactorAt U Z _ K L hFF
  have := hgal
  apply IsDiscreteValuationRing.isTamelyRamified_of_isGalois_of_isUnit_finrank
  have h := hG Zd.genericPoint
  rw [hk, Nat.cast_mul] at h
  exact isUnit_of_mul_isUnit_left h

end AlgebraicGeometry
