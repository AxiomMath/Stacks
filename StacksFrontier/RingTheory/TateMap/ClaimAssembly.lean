module

public import StacksFrontier.RingTheory.TateMap.ClaimTransfer
public import StacksFrontier.RingTheory.TateMap.ClaimSideFamily

/-!
# The Claim of Proposition 0FKD

Two classifications of a flat quasi-finite syntomic algebra over a Noetherian ring by basic
charts of the universal family give the same Tate map.

## Main results

* `Stacks.TateMap.presRel_side`: a presentation obtained from a classification is Tate-related to
  its global graph presentations.
* `Stacks.TateMap.tateOf_eq_tateOf`: the Claim.

## References

* [Stacks Project, Tag 0FKD](https://stacks.math.columbia.edu/tag/0FKD)
-/

@[expose] public noncomputable section

open MvPolynomial Stacks.Discriminant AlgebraicGeometry

universe u

namespace Stacks.TateMap

section Side

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Syntomic A B]
  [IsNoetherianRing A] [Algebra.QuasiFinite A B]

/-- **One side of the comparison.** A presentation `B ≅ A[x, 1/(φ(k) p)]/(φ(f))` coming from a
classification by a basic chart which is a domain unramified at its generic point is Tate-related
to each of its global graph presentations. -/
theorem presRel_side {n d : ℕ} [NeZero d] (k : MvPolynomial (Fin n) (univBase.{u} n d))
    [Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k)] [IsDomain (univChart n d k)]
    [Algebra.IsUnramifiedAt (univBase.{u} n d) (⊥ : Ideal (univChart n d k))]
    (φ : univBase.{u} n d →+* A) (p : MvPolynomial (Fin n) A) (H : MvPolynomial (Fin n) A)
    (f : Fin n → MvPolynomial (Fin n) A) (hH : MvPolynomial.map φ k * p = H)
    (hf : ∀ i, MvPolynomial.map φ (univPoly n d i) = f i)
    (e₁ : B ≃ₐ[A] localizedCompleteIntersection A n H f)
    {m N : ℕ} (eV : Fin (n + 1) ⊕ Fin m ≃ Fin N) (ψ : Fin m → MvPolynomial (Fin (n + 1)) A) :
    letI : Algebra (localizedCompleteIntersection A n H f) B := e₁.symm.toRingHom.toAlgebra
    letI : Algebra (localizedCompleteIntersection A N 1
        (graphRelations eV eV 1 (globalRelations H f) ψ 0)) B :=
      ((globalGraphEquiv eV _ _ ψ).symm.trans e₁.symm).toRingHom.toAlgebra
    PresRel (B := B) H f 1
      (graphRelations eV eV 1 (globalRelations H f) ψ 0) := by
  let : Algebra (localizedCompleteIntersection A n H f) B := e₁.symm.toRingHom.toAlgebra
  let : Algebra (localizedCompleteIntersection A N 1
      (graphRelations eV eV 1 (globalRelations H f) ψ 0)) B :=
    ((globalGraphEquiv eV _ _ ψ).symm.trans e₁.symm).toRingHom.toAlgebra
  set eE := p.totalDegree
  set eψ := Finset.univ.sup fun j ↦ (ψ j).totalDegree
  have hψd : ∀ j, (ψ j).totalDegree ≤ eψ := fun j ↦
    Finset.le_sup (f := fun j ↦ (ψ j).totalDegree) (Finset.mem_univ j)
  set ε := sideSpec n d eE m eψ Empty φ p ψ Empty.elim
  obtain ⟨_, _, _, _, hnice⟩ := isNiceChart_side n d k eE m eψ Empty
  have hfa : ∀ i, MvPolynomial.map ε (sideF n d eE m eψ Empty i) = f i := fun i ↦
    (map_sideSpec_paramF n d eE m eψ Empty φ p ψ Empty.elim i).trans (hf i)
  have hH : MvPolynomial.map ε (sideH n d k eE m eψ Empty) = H := by
    rw [map_mul, map_sideSpec_paramH, map_sideSpec_sideE n d eE m eψ Empty φ p ψ _ le_rfl, hH]
  have hψ' : ∀ j, MvPolynomial.map ε (sideψ n d eE m eψ Empty j) = ψ j :=
    map_sideSpec_sideψ n d eE m eψ Empty φ p ψ _ hψd
  have hgl : ∀ i, MvPolynomial.map ε (globalRelations (sideH n d k eE m eψ Empty)
      (sideF n d eE m eψ Empty) i) = globalRelations H f i := by
    intro i
    rw [map_globalRelations, hH]
    congr 1
    exact funext hfa
  have hfb : ∀ c, MvPolynomial.map ε (sideRel n d k eE m eψ Empty eV c) =
      graphRelations eV eV 1 (globalRelations H f) ψ 0 c := by
    intro c
    rw [sideRel, map_graphRelations, map_one]
    congr 1
    · exact funext hgl
    · exact funext hψ'
  have : IsScalarTower A (localizedCompleteIntersection A n H f) B :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (e₁.symm.commutes a).symm
  have : IsScalarTower A (localizedCompleteIntersection A N 1
      (graphRelations eV eV 1 (globalRelations H f) ψ 0)) B :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      (((globalGraphEquiv eV H
        f ψ).symm.trans e₁.symm).commutes a).symm
  have : Algebra.QuasiFinite A (localizedCompleteIntersection A n H f) :=
    (Algebra.QuasiFinite.iff_of_algEquiv e₁).mp inferInstance
  have : Algebra.QuasiFinite A (localizedCompleteIntersection A N 1
      (graphRelations eV eV 1 (globalRelations H f) ψ 0)) :=
    (Algebra.QuasiFinite.iff_of_algEquiv
      ((globalGraphEquiv eV H
        f ψ).symm.trans e₁.symm).symm).mp
      inferInstance
  have hka : IsUnit (algebraMap (localizedCompleteIntersection A n H f) B
      (algebraMap (MvPolynomial (Fin n) A) _
        (MvPolynomial.map ε (sideH n d k eE m eψ Empty)))) := by
    rw [hH]
    exact (isUnit_lciMk H f).map _
  refine presRel_of_transfer _ _ _ _ hnice (sideθ n d k eE m eψ Empty eV) ε H f 1 _ hfa hfb hka
    (fun j ↦ ?_)
  set χ := @algebraMap _ _ _ _ (classificationAlgebra (sideH n d k eE m eψ Empty) ε H f hfa B hka)
  have hχ : ∀ q, χ (lciMk _ _ q) = e₁.symm.toRingHom (lciMk H f (MvPolynomial.map ε q)) :=
    fun q ↦ classificationAlgebra_algebraMap _ ε H f hfa B hka q
  have hglob := lciGlobalEquiv_symm_natural' ε (sideH n d k eE m eψ Empty)
    (sideF n d eE m eψ Empty) hH hfa χ e₁.symm.toRingHom hχ
  have hgr := lciGraphEquiv_symm_natural' ε eV eV 1 (globalRelations (sideH n d k eE m eψ Empty)
    (sideF n d eE m eψ Empty)) (sideψ n d eE m eψ Empty) 0 (map_one _) hgl hψ'
    (χ.comp (lciGlobalEquiv _ _).symm.toRingEquiv.toRingHom)
    (e₁.symm.toRingHom.comp (lciGlobalEquiv H f).symm.toRingEquiv.toRingHom) hglob (X j)
  rw [MvPolynomial.map_X] at hgr
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    AlgEquiv.coe_ringEquiv] at hgr
  have hR : algebraMap (localizedCompleteIntersection A N 1
      (graphRelations eV eV 1 (globalRelations H f) ψ 0)) B (lciMk _ _ (X j)) =
      e₁.symm ((lciGlobalEquiv _ _).symm ((lciGraphEquiv eV eV 1 _ ψ 0).symm
        (lciMk _ _ (X j)))) := by
    show ((globalGraphEquiv eV _ _ ψ).symm.trans e₁.symm) (lciMk _ _ (X j)) = _
    rw [AlgEquiv.trans_apply, globalGraphEquiv_symm_lciMk]
  rw [sideθ_symm_lciMk, hR]
  exact hgr

end Side

section Claim

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Syntomic A B]
  [IsNoetherianRing A] [Algebra.QuasiFinite A B] [IsNoetherianRing B]

omit [IsNoetherianRing B] in
/-- If a basic chart classifying `A → B` is the zero ring, so is `B`. -/
theorem subsingleton_of_classification {n d : ℕ} (k : MvPolynomial (Fin n) (univBase.{u} n d))
    (jC : Algebra (univChart n d k) B) [Subsingleton (univChart n d k)] : Subsingleton B := by
  refine subsingleton_of_zero_eq_one ?_
  rw [← map_zero (@algebraMap _ _ _ _ jC), ← map_one (@algebraMap _ _ _ _ jC),
    Subsingleton.elim (0 : univChart n d k) 1]

omit [Algebra.QuasiFinite A B] [IsNoetherianRing B] in
/-- **Step 0.** A classification gives the same Tate map as the classification of the
presentation it induces. -/
theorem tateOf_eq_classificationOf_self {n d : ℕ} (k : MvPolynomial (Fin n) (univBase.{u} n d))
    [Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k)]
    (jR : Algebra (univBase.{u} n d) A) (jC : Algebra (univChart n d k) B)
    (D : ChartBaseChange (univBase.{u} n d) (univChart n d k) A B)
    (φ : univBase.{u} n d →+* A) (hφ : ∀ x, algebraMap (univBase.{u} n d) A x = φ x)
    (H : MvPolynomial (Fin n) A) (f : Fin n → MvPolynomial (Fin n) A)
    (hf : ∀ i, MvPolynomial.map φ (univPoly n d i) = f i)
    [Algebra (localizedCompleteIntersection A n H f) B]
    [IsScalarTower A (localizedCompleteIntersection A n H f) B]
    (g : MvPolynomial (Fin n) A) [IsLocalization.Away (algebraMap (MvPolynomial (Fin n) A)
      (localizedCompleteIntersection A n H f) g) B]
    (hX : ∀ i, algebraMap _ B (lciMk k (univPoly n d) (X i)) =
      algebraMap (localizedCompleteIntersection A n H f) B (lciMk H f (X i)))
    (hk : IsUnit (algebraMap (localizedCompleteIntersection A n H f) B
      (algebraMap (MvPolynomial (Fin n) A) _ (MvPolynomial.map φ k))))
    (G : FiniteOpenFactorization.{u, u, u} A B) :
    tateOf k jR jC D G =
      tateOf k φ.toAlgebra (classificationAlgebra k φ H f hf B hk)
        (classificationOf k φ H f hf g B hk) G := by
  refine tateOf_congr _ _ _ _ _ hφ (fun x ↦ ?_) _ _ G
  refine eq_classificationAlgebra k φ H f hf B hk (algebraMap _ B) (fun c ↦ ?_) hX x
  rw [D.algebraMap_comm c, hφ]

omit [Algebra.Syntomic A B] [IsNoetherianRing A] [Algebra.QuasiFinite A B] [IsNoetherianRing B] in
/-- A presentation of `B` by an isomorphism makes `B` a localization of it away from `1`. -/
theorem isLocalization_away_one_of_equiv {N : ℕ} {h : MvPolynomial (Fin N) A}
    {f : Fin N → MvPolynomial (Fin N) A} (e : localizedCompleteIntersection A N h f ≃ₐ[A] B) :
    letI := e.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (MvPolynomial (Fin N) A)
      (localizedCompleteIntersection A N h f) 1) B := by
  let := e.toRingHom.toAlgebra
  rw [map_one]
  exact IsLocalization.away_of_isUnit_of_bijective _ isUnit_one e.bijective

end Claim

end Stacks.TateMap
