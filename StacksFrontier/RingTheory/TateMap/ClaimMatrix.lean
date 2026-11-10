module

public import StacksFrontier.RingTheory.TateMap.ClaimTransfer
public import StacksFrontier.RingTheory.TateMap.ClaimSideFamily

/-!
# The matrix move of the Claim of Proposition 0FKD

Changing the relations of a global graph presentation `B = A[x, 1/D]/(r)` by a square matrix `M`
whose determinant `D` is a unit, `B = A[x, 1/(D D)]/(M r)`, gives Tate-related presentations. The
comparison is realized on a nice family: the side family with the entries of a generic matrix of
bounded degree as further parameters.

## Main definitions

* `Stacks.TateMap.matrixGen`: the generic square matrix of polynomials of degree at most `e`.

## Main results

* `Stacks.TateMap.map_sideSpec_matrixGen`: it specializes to any matrix of polynomials of degree
  at most `e`.
* `Stacks.TateMap.presRel_matrix`: the matrix move gives Tate-related presentations.

## References

* [Stacks Project, Tag 0FKD](https://stacks.math.columbia.edu/tag/0FKD)
-/

@[expose] public noncomputable section

open MvPolynomial Stacks.Discriminant AlgebraicGeometry

universe u

namespace Stacks.TateMap

variable (n d e₁ m e₂ N e : ℕ)

/-- The further parameters of the matrix family: the coefficients of the entries of a square
`N × N` matrix of polynomials of degree at most `e` in `N` variables. -/
abbrev matrixτ : Type := (Fin N × Fin N) × MultiIndex N e

/-- The generic square matrix of polynomials of degree at most `e`, over the parameter ring of the
side family with the matrix parameters. -/
noncomputable def matrixGen :
    Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) (sideBase.{u} n d e₁ m e₂ (matrixτ N e))) :=
  Matrix.of fun i j ↦ MvPolynomial.map (rename (Sum.inr ∘ Sum.inr) :
    MvPolynomial ((Fin N × Fin N) × MultiIndex N e) (univBase.{u} n d) →ₐ[_]
      sideBase.{u} n d e₁ m e₂ (matrixτ N e)).toRingHom
    (genPoly (univBase.{u} n d) (Fin N × Fin N) N e (i, j))

variable {n d e₁ m e₂ N e}

/-- The specialization of the matrix parameters to the coefficients of a matrix `M`. -/
noncomputable def matrixSpec {A : Type u} [CommRing A]
    (M : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) A)) : matrixτ N e → A :=
  fun x ↦ (M x.1.1 x.1.2).coeff (multiIndexExponent N e x.2)

/-- **The generic matrix specializes to `M`** if every entry of `M` has total degree at most
`e`. -/
theorem map_sideSpec_matrixGen {A : Type u} [CommRing A] (φ : univBase.{u} n d →+* A)
    (p : MvPolynomial (Fin n) A) (ψ : Fin m → MvPolynomial (Fin (n + 1)) A)
    (M : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) A))
    (hM : ∀ i j, (M i j).totalDegree ≤ e) (i j : Fin N) :
    MvPolynomial.map (sideSpec n d e₁ m e₂ (matrixτ N e) φ p ψ (matrixSpec M))
      (matrixGen.{u} n d e₁ m e₂ N e i j) = M i j := by
  let := φ.toAlgebra
  have : (sideSpec n d e₁ m e₂ (matrixτ N e) φ p ψ (matrixSpec M)).comp
      (rename (Sum.inr ∘ Sum.inr) :
        MvPolynomial ((Fin N × Fin N) × MultiIndex N e) (univBase.{u} n d) →ₐ[_]
          sideBase.{u} n d e₁ m e₂ (matrixτ N e)).toRingHom =
      (genSpec (e := e) (R := univBase.{u} n d) (fun ij : Fin N × Fin N ↦ M ij.1 ij.2) :
        MvPolynomial ((Fin N × Fin N) × MultiIndex N e) (univBase.{u} n d) →+* A) := by
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun iα ↦ ?_)
    · simp [sideSpec, genSpec, RingHom.algebraMap_toAlgebra]
    · simp [sideSpec, genSpec, matrixSpec]
  rw [matrixGen, Matrix.of_apply, MvPolynomial.map_map, this]
  exact map_genPoly (fun ij : Fin N × Fin N ↦ M ij.1 ij.2) (fun ij ↦ hM ij.1 ij.2) (i, j)

section Matrix

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Syntomic A B]
  [IsNoetherianRing A] [Algebra.QuasiFinite A B]

/-- The inverse of `lciMatrixEquiv` sends the class of a polynomial `q` to the class of `q`. -/
private theorem lciMatrixEquiv_symm_lciMk {S : Type u} [CommRing S] {ν : ℕ}
    (h : MvPolynomial (Fin ν) S) (f : Fin ν → MvPolynomial (Fin ν) S)
    (M : Matrix (Fin ν) (Fin ν) (MvPolynomial (Fin ν) S)) (hd : IsUnit (lciMk h f M.det))
    (q : MvPolynomial (Fin ν) S) :
    (lciMatrixEquiv h f M hd).symm (lciMk _ _ q) = lciMk h f q := by
  rw [AlgEquiv.symm_apply_eq, lciMatrixEquiv_lciMk]

/-- **The matrix move.** Let `B ≅ A[x, 1/(φ(k) p)]/(φ(f))` come from a classification by a basic
chart which is a domain unramified at its generic point, and let `B ≅ A[x, 1/D]/(r)` be one of
its global graph presentations, `D = det M` for a square matrix `M` whose determinant is a unit
in `A[x]/(r)`. Then this presentation is Tate-related to `B ≅ A[x, 1/(D D)]/(M r)`. -/
theorem presRel_matrix {n d : ℕ} [NeZero d] (k : MvPolynomial (Fin n) (univBase.{u} n d))
    [Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k)] [IsDomain (univChart n d k)]
    [Algebra.IsUnramifiedAt (univBase.{u} n d) (⊥ : Ideal (univChart n d k))]
    (φ : univBase.{u} n d →+* A) (p : MvPolynomial (Fin n) A) (H : MvPolynomial (Fin n) A)
    (f : Fin n → MvPolynomial (Fin n) A) (hH : MvPolynomial.map φ k * p = H)
    (hf : ∀ i, MvPolynomial.map φ (univPoly n d i) = f i)
    (e₂ : B ≃ₐ[A] localizedCompleteIntersection A n H f)
    {m N : ℕ} (eV : Fin (n + 1) ⊕ Fin m ≃ Fin N) (ψ : Fin m → MvPolynomial (Fin (n + 1)) A)
    (M : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) A))
    (hD : IsUnit (lciMk 1 (graphRelations eV eV 1 (globalRelations H f) ψ 0) M.det)) :
    letI : Algebra (localizedCompleteIntersection A N M.det
        (graphRelations eV eV 1 (globalRelations H f) ψ 0)) B :=
      ((lciDetEquiv M.det _ hD).trans
        ((globalGraphEquiv eV H f ψ).symm.trans e₂.symm)).toRingHom.toAlgebra
    letI : Algebra (localizedCompleteIntersection A N (M.det * M.det)
        (M.mulVec (graphRelations eV eV 1 (globalRelations H f) ψ 0))) B :=
      ((lciMatrixEquiv M.det _ M (isUnit_lciMk _ _)).symm.trans
        ((lciDetEquiv M.det _ hD).trans
          ((globalGraphEquiv eV H f ψ).symm.trans e₂.symm))).toRingHom.toAlgebra
    PresRel (B := B) M.det (graphRelations eV eV 1 (globalRelations H f) ψ 0) (M.det * M.det)
      (M.mulVec (graphRelations eV eV 1 (globalRelations H f) ψ 0)) := by
  let : Algebra (localizedCompleteIntersection A N M.det
      (graphRelations eV eV 1 (globalRelations H f) ψ 0)) B :=
    ((lciDetEquiv M.det _ hD).trans
      ((globalGraphEquiv eV H f ψ).symm.trans e₂.symm)).toRingHom.toAlgebra
  let : Algebra (localizedCompleteIntersection A N (M.det * M.det)
      (M.mulVec (graphRelations eV eV 1 (globalRelations H f) ψ 0))) B :=
    ((lciMatrixEquiv M.det _ M (isUnit_lciMk _ _)).symm.trans
      ((lciDetEquiv M.det _ hD).trans
        ((globalGraphEquiv eV H f ψ).symm.trans e₂.symm))).toRingHom.toAlgebra
  set eE := p.totalDegree
  set eψ := Finset.univ.sup fun j ↦ (ψ j).totalDegree
  have hψd : ∀ j, (ψ j).totalDegree ≤ eψ := fun j ↦
    Finset.le_sup (f := fun j ↦ (ψ j).totalDegree) (Finset.mem_univ j)
  set eM := Finset.univ.sup fun ij : Fin N × Fin N ↦ (M ij.1 ij.2).totalDegree
  have hMd : ∀ i j, (M i j).totalDegree ≤ eM := fun i j ↦
    Finset.le_sup (f := fun ij : Fin N × Fin N ↦ (M ij.1 ij.2).totalDegree)
      (Finset.mem_univ (i, j))
  set ε := sideSpec n d eE m eψ (matrixτ N eM) φ p ψ (matrixSpec M)
  -- the relations of the family specialize to those of `B`
  have hfa₀ : ∀ i, MvPolynomial.map ε (sideF n d eE m eψ (matrixτ N eM) i) = f i := fun i ↦
    (map_sideSpec_paramF n d eE m eψ (matrixτ N eM) φ p ψ (matrixSpec M) i).trans (hf i)
  have hH' : MvPolynomial.map ε (sideH n d k eE m eψ (matrixτ N eM)) = H := by
    rw [map_mul, map_sideSpec_paramH, map_sideSpec_sideE n d eE m eψ (matrixτ N eM) φ p ψ _ le_rfl,
      hH]
  have hψ' : ∀ j, MvPolynomial.map ε (sideψ n d eE m eψ (matrixτ N eM) j) = ψ j :=
    map_sideSpec_sideψ n d eE m eψ (matrixτ N eM) φ p ψ _ hψd
  have hgl : ∀ i, MvPolynomial.map ε (globalRelations (sideH n d k eE m eψ (matrixτ N eM))
      (sideF n d eE m eψ (matrixτ N eM)) i) = globalRelations H f i := by
    intro i
    rw [map_globalRelations, hH']
    congr 1
    exact funext hfa₀
  have hfa : ∀ c, MvPolynomial.map ε (sideRel n d k eE m eψ (matrixτ N eM) eV c) =
      graphRelations eV eV 1 (globalRelations H f) ψ 0 c := by
    intro c
    rw [sideRel, map_graphRelations, map_one]
    congr 1
    · exact funext hgl
    · exact funext hψ'
  -- the generic matrix specializes to `M`
  set Mg := matrixGen.{u} n d eE m eψ N eM
  have hMg : ∀ i j, MvPolynomial.map ε (Mg i j) = M i j :=
    map_sideSpec_matrixGen φ p ψ M hMd
  have hdet : MvPolynomial.map ε Mg.det = M.det := by
    rw [RingHom.map_det]
    congr 1
    exact Matrix.ext fun i j ↦ hMg i j
  have hfb : ∀ c, MvPolynomial.map ε ((Mg.mulVec (sideRel n d k eE m eψ (matrixτ N eM) eV)) c) =
      (M.mulVec (graphRelations eV eV 1 (globalRelations H f) ψ 0)) c := by
    intro c
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hMg, hfa]
  -- the family is nice
  obtain ⟨_, _, _, hft, hnice⟩ := isNiceChart_side n d k eE m eψ (matrixτ N eM)
  set S := sideBase.{u} n d eE m eψ (matrixτ N eM)
  set rel := sideRel n d k eE m eψ (matrixτ N eM) eV
  set Z₁ := localizedCompleteIntersection S N 1 rel
  set Z' := localizedCompleteIntersection S N (1 * Mg.det) rel
  set Z := localizedCompleteIntersection S N Mg.det rel
  have : Algebra.QuasiFinite S Z₁ :=
    (Algebra.QuasiFinite.iff_of_algEquiv (sideθ n d k eE m eψ (matrixτ N eM) eV)).mp
      inferInstance
  have hnice₁ : IsNiceChart S Z₁ := hnice.of_algEquiv (sideθ n d k eE m eψ (matrixτ N eM) eV)
  have : Algebra.FinitePresentation S Z₁ :=
    finitePresentation_localizedCompleteIntersection S N 1 rel
  let iZZ' : Algebra Z₁ Z' := (lciAwayHom 1 Mg.det rel).toRingHom.toAlgebra
  have := isLocalization_lciAwayHom 1 Mg.det rel
  have : @IsScalarTower S Z₁ Z' Algebra.toSMul iZZ'.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun c ↦ ((lciAwayHom 1 Mg.det rel).commutes c).symm
  have : Algebra.QuasiFinite S Z' :=
    Algebra.QuasiFinite.of_isLocalization (Submonoid.powers (lciMk 1 rel Mg.det))
  have hnice₂ : IsNiceChart S Z' := hnice₁.of_isLocalizationAway (lciMk 1 rel Mg.det)
  let eC : Z' ≃ₐ[S] Z := localizedCompleteIntersectionCongr (one_mul Mg.det) rfl
  have : Algebra.QuasiFinite S Z := (Algebra.QuasiFinite.iff_of_algEquiv eC).mp inferInstance
  have : Algebra.FinitePresentation S Z' :=
    finitePresentation_localizedCompleteIntersection S N (1 * Mg.det) rel
  have hZ : IsNiceChart S Z := hnice₂.of_algEquiv eC
  -- the transfer
  have : IsScalarTower A (localizedCompleteIntersection A N M.det
      (graphRelations eV eV 1 (globalRelations H f) ψ 0)) B :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (((lciDetEquiv M.det _ hD).trans
      ((globalGraphEquiv eV H f ψ).symm.trans e₂.symm)).commutes a).symm
  have : IsScalarTower A (localizedCompleteIntersection A N (M.det * M.det)
      (M.mulVec (graphRelations eV eV 1 (globalRelations H f) ψ 0))) B :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      (((lciMatrixEquiv M.det _ M (isUnit_lciMk _ _)).symm.trans ((lciDetEquiv M.det _ hD).trans
        ((globalGraphEquiv eV H f ψ).symm.trans e₂.symm))).commutes a).symm
  have : Algebra.QuasiFinite A (localizedCompleteIntersection A N M.det
      (graphRelations eV eV 1 (globalRelations H f) ψ 0)) :=
    (Algebra.QuasiFinite.iff_of_algEquiv ((lciDetEquiv M.det _ hD).trans
      ((globalGraphEquiv eV H f ψ).symm.trans e₂.symm)).symm).mp inferInstance
  have : Algebra.QuasiFinite A (localizedCompleteIntersection A N (M.det * M.det)
      (M.mulVec (graphRelations eV eV 1 (globalRelations H f) ψ 0))) :=
    (Algebra.QuasiFinite.iff_of_algEquiv ((lciMatrixEquiv M.det _ M (isUnit_lciMk _ _)).symm.trans
      ((lciDetEquiv M.det _ hD).trans
        ((globalGraphEquiv eV H f ψ).symm.trans e₂.symm))).symm).mp inferInstance
  have hka : IsUnit (algebraMap (localizedCompleteIntersection A N M.det
      (graphRelations eV eV 1 (globalRelations H f) ψ 0)) B
      (algebraMap (MvPolynomial (Fin N) A) _ (MvPolynomial.map ε Mg.det))) := by
    rw [hdet]
    exact (isUnit_lciMk M.det _).map _
  refine presRel_of_transfer Mg.det rel (Mg.det * Mg.det) (Mg.mulVec rel) hZ
    (lciMatrixEquiv Mg.det rel Mg (isUnit_lciMk _ _)) ε M.det
    (graphRelations eV eV 1 (globalRelations H f) ψ 0) (M.det * M.det)
    (M.mulVec (graphRelations eV eV 1 (globalRelations H f) ψ 0)) hfa hfb hka (fun j ↦ ?_)
  rw [lciMatrixEquiv_symm_lciMk, classificationAlgebra_lciMk_X]
  change _ = ((lciMatrixEquiv M.det _ M (isUnit_lciMk _ _)).symm.trans
      ((lciDetEquiv M.det _ hD).trans
        ((globalGraphEquiv eV H f ψ).symm.trans e₂.symm))) (lciMk _ _ (X j))
  rw [AlgEquiv.trans_apply, lciMatrixEquiv_symm_lciMk]
  rfl

end Matrix

end Stacks.TateMap
