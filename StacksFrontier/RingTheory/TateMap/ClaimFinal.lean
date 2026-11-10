module

public import StacksFrontier.RingTheory.TateMap.ClaimAssembly
public import StacksFrontier.RingTheory.TateMap.ClaimMatrix

/-!
# The Claim of Proposition 0FKD

Two classifications of a flat quasi-finite syntomic algebra `A → B` over a Noetherian ring by
quasi-finite basic charts of the universal family give the same Tate map
`det(NL_{B/A}) ≅ ω_{B/A}`.

The two classifications induce presentations `B ≅ A[x, 1/H₁]/(f₁) ≅ A[y, 1/H₂]/(f₂)`. Their
global graph presentations in the variables `x, t₁, y, t₂` generate the same ideal and differ by
a matrix with unit determinant. The chain

`P₁ ~ (graph of P₁) ~ (matrix times graph of P₂) ~ (graph of P₂) ~ P₂`

of Tate-related presentations is realized by nice families: the side families over the two
universal charts, and the matrix family.

## Main results

* `Stacks.TateMap.tateOf_eq_tateOf`: the Claim.

## References

* [Stacks Project, Tag 0FKD](https://stacks.math.columbia.edu/tag/0FKD)
-/

@[expose] public noncomputable section

open MvPolynomial Stacks.Discriminant AlgebraicGeometry

universe u

namespace Stacks.TateMap

section Claim

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Syntomic A B]
  [IsNoetherianRing A] [Algebra.QuasiFinite A B] [IsNoetherianRing B]

/-- Transporting along an algebra isomorphism `S ≃ₐ[R] T` makes `T` an `S`-algebra with a scalar
tower. -/
private theorem isScalarTower_toAlgebra {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (e : S ≃ₐ[R] T) :
    letI := e.toRingHom.toAlgebra
    IsScalarTower R S T :=
  letI := e.toRingHom.toAlgebra
  IsScalarTower.of_algebraMap_eq fun a ↦ (e.commutes a).symm

/-- A factor `k` of the localizing element `H = k * p` becomes a unit in any `lci` algebra. -/
private theorem isUnit_algebraMap_of_mul_eq {R T : Type u} [CommRing R] [CommRing T] {n : ℕ}
    {f : Fin n → MvPolynomial (Fin n) R} {H : MvPolynomial (Fin n) R}
    [Algebra (localizedCompleteIntersection R n H f) T] (k p : MvPolynomial (Fin n) R)
    (hH : k * p = H) :
    IsUnit (algebraMap (localizedCompleteIntersection R n H f) T
      (algebraMap (MvPolynomial (Fin n) R) _ k)) := by
  have hu := isUnit_lciMk H f
  rw [congrArg (lciMk H f) hH.symm, map_mul] at hu
  exact (isUnit_of_mul_isUnit_left hu).map _

/-- The variables of a chart presentation map to the variables of the induced presentation. -/
private theorem algebraMap_lciMk_X_eq {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra S R] [Algebra R T] {n : ℕ} {h : MvPolynomial (Fin n) S}
    {f : Fin n → MvPolynomial (Fin n) S} [Algebra (localizedCompleteIntersection S n h f) T]
    {H : MvPolynomial (Fin n) R} {g : Fin n → MvPolynomial (Fin n) R}
    (e : T ≃ₐ[R] localizedCompleteIntersection R n H g)
    (he : ∀ q : MvPolynomial (Fin n) S, e (algebraMap _ T (lciMk h f q)) =
      lciMk H g (MvPolynomial.map (algebraMap S R) q)) (i : Fin n) :
    letI := e.symm.toRingHom.toAlgebra
    algebraMap _ T (lciMk h f (X i)) =
      algebraMap (localizedCompleteIntersection R n H g) T (lciMk H g (X i)) := by
  let := e.symm.toRingHom.toAlgebra
  change _ = e.symm _
  rw [AlgEquiv.eq_symm_apply, he, MvPolynomial.map_X]

/-- **The Claim of Proposition 0FKD.** Two classifications of `A → B` by quasi-finite basic charts
of the universal family give the same Tate map. -/
theorem tateOf_eq_tateOf {n₁ d₁ : ℕ} [NeZero d₁]
    (k₁ : MvPolynomial (Fin n₁) (univBase.{u} n₁ d₁))
    [Algebra.QuasiFinite (univBase.{u} n₁ d₁) (univChart n₁ d₁ k₁)]
    (jR₁ : Algebra (univBase.{u} n₁ d₁) A) (jC₁ : Algebra (univChart n₁ d₁ k₁) B)
    (D₁ : ChartBaseChange (univBase.{u} n₁ d₁) (univChart n₁ d₁ k₁) A B)
    {n₂ d₂ : ℕ} [NeZero d₂] (k₂ : MvPolynomial (Fin n₂) (univBase.{u} n₂ d₂))
    [Algebra.QuasiFinite (univBase.{u} n₂ d₂) (univChart n₂ d₂ k₂)]
    (jR₂ : Algebra (univBase.{u} n₂ d₂) A) (jC₂ : Algebra (univChart n₂ d₂ k₂) B)
    (D₂ : ChartBaseChange (univBase.{u} n₂ d₂) (univChart n₂ d₂ k₂) A B)
    (G : FiniteOpenFactorization.{u, u, u} A B) :
    tateOf k₁ jR₁ jC₁ D₁ G = tateOf k₂ jR₂ jC₂ D₂ G := by
  classical
  have hsub : Subsingleton B → tateOf k₁ jR₁ jC₁ D₁ G = tateOf k₂ jR₂ jC₂ D₂ G := fun _ ↦ by
    have : Subsingleton (dualizingModule G) := Module.subsingleton B _
    exact LinearEquiv.ext fun _ ↦ Subsingleton.elim _ _
  rcases univChart_subsingleton_or n₁ d₁ k₁ with hs₁ | ⟨_, _⟩
  · exact hsub (subsingleton_of_classification k₁ jC₁)
  rcases univChart_subsingleton_or n₂ d₂ k₂ with hs₂ | ⟨_, _⟩
  · exact hsub (subsingleton_of_classification k₂ jC₂)
  -- the presentations induced by the two classifications
  obtain ⟨p₁, e₁, he₁⟩ := exists_presentation_of_chartBaseChange D₁
  obtain ⟨p₂, e₂, he₂⟩ := exists_presentation_of_chartBaseChange D₂
  generalize hH₁ : MvPolynomial.map (algebraMap (univBase.{u} n₁ d₁) A) k₁ * p₁ = H₁ at e₁ he₁
  generalize hf₁ : (fun i ↦ MvPolynomial.map (algebraMap (univBase.{u} n₁ d₁) A)
    (univPoly n₁ d₁ i)) = f₁ at e₁ he₁
  generalize hH₂ : MvPolynomial.map (algebraMap (univBase.{u} n₂ d₂) A) k₂ * p₂ = H₂ at e₂ he₂
  generalize hf₂ : (fun i ↦ MvPolynomial.map (algebraMap (univBase.{u} n₂ d₂) A)
    (univPoly n₂ d₂ i)) = f₂ at e₂ he₂
  have hf₁' := congrFun hf₁
  have hf₂' := congrFun hf₂
  let iP₁ : Algebra (localizedCompleteIntersection A n₁ H₁ f₁) B := e₁.symm.toRingHom.toAlgebra
  let iP₂ : Algebra (localizedCompleteIntersection A n₂ H₂ f₂) B := e₂.symm.toRingHom.toAlgebra
  have := isScalarTower_toAlgebra e₁.symm
  have := isScalarTower_toAlgebra e₂.symm
  have := isLocalization_away_one_of_equiv e₁.symm
  have := isLocalization_away_one_of_equiv e₂.symm
  have hX₁ := algebraMap_lciMk_X_eq e₁ he₁
  have hX₂ := algebraMap_lciMk_X_eq e₂ he₂
  have hk₁ := isUnit_algebraMap_of_mul_eq (T := B) (f := f₁) _ p₁ hH₁
  have hk₂ := isUnit_algebraMap_of_mul_eq (T := B) (f := f₂) _ p₂ hH₂
  rw [tateOf_eq_classificationOf_self k₁ jR₁ jC₁ D₁ _ (fun _ ↦ rfl) H₁ f₁ hf₁' 1 hX₁ hk₁ G,
    tateOf_eq_classificationOf_self k₂ jR₂ jC₂ D₂ _ (fun _ ↦ rfl) H₂ f₂ hf₂' 1 hX₂ hk₂ G]
  -- the global presentations and their decomposition
  obtain ⟨e₁g, he₁g⟩ : ∃ e : localizedCompleteIntersection A (n₁ + 1) 1 (globalRelations H₁ f₁)
      ≃ₐ[A] B, e = (lciGlobalEquiv H₁ f₁).symm.trans e₁.symm := ⟨_, rfl⟩
  obtain ⟨e₂g, he₂g⟩ : ∃ e : localizedCompleteIntersection A (n₂ + 1) 1 (globalRelations H₂ f₂)
      ≃ₐ[A] B, e = (lciGlobalEquiv H₂ f₂).symm.trans e₂.symm := ⟨_, rfl⟩
  obtain ⟨M, M', hM, -, hdetL⟩ := exists_matrix_decomp e₁g e₂g
  have hdetR : IsUnit (lciMk 1 (decompRelRight e₁g e₂g) M.det) := by
    have := hdetL.map (decompEquiv e₁g e₂g)
    rw [decompEquiv_lciMk] at this
    exact this
  -- the instances of the intermediate presentations on `B`
  set dL := decompLeft (n₁ + 1) (n₂ + 1) with hdL
  set dR := decompRight (n₁ + 1) (n₂ + 1) with hdR
  set isoL := (globalGraphEquiv dL H₁ f₁ (decompψ e₁g e₂g)).symm.trans e₁.symm with hisoL
  set isoR := (globalGraphEquiv dR H₂ f₂ (decompφ e₁g e₂g)).symm.trans e₂.symm with hisoR
  set isoL' := (localizedCompleteIntersectionCongr rfl hM).symm.trans isoL with hisoL'
  set isoRd := (lciDetEquiv M.det (decompRelRight e₁g e₂g) hdetR).trans isoR with hisoRd
  set isoMp := (lciMatrixEquiv M.det (decompRelRight e₁g e₂g) M (isUnit_lciMk _ _)).symm.trans
    isoRd with hisoMp
  let : Algebra (localizedCompleteIntersection A _ 1 (decompRelLeft e₁g e₂g)) B :=
    isoL.toRingHom.toAlgebra
  let : Algebra (localizedCompleteIntersection A _ 1 (decompRelRight e₁g e₂g)) B :=
    isoR.toRingHom.toAlgebra
  let : Algebra (localizedCompleteIntersection A _ 1 (M.mulVec (decompRelRight e₁g e₂g))) B :=
    isoL'.toRingHom.toAlgebra
  let : Algebra (localizedCompleteIntersection A _ M.det (decompRelRight e₁g e₂g)) B :=
    isoRd.toRingHom.toAlgebra
  let : Algebra (localizedCompleteIntersection A _ (M.det * M.det)
      (M.mulVec (decompRelRight e₁g e₂g))) B := isoMp.toRingHom.toAlgebra
  have := isScalarTower_toAlgebra isoL
  have := isScalarTower_toAlgebra isoR
  have := isScalarTower_toAlgebra isoL'
  have := isScalarTower_toAlgebra isoRd
  have := isScalarTower_toAlgebra isoMp
  have := (Algebra.QuasiFinite.iff_of_algEquiv isoL.symm).mp inferInstance
  have := (Algebra.QuasiFinite.iff_of_algEquiv isoR.symm).mp inferInstance
  have := (Algebra.QuasiFinite.iff_of_algEquiv isoL'.symm).mp inferInstance
  have := (Algebra.QuasiFinite.iff_of_algEquiv isoRd.symm).mp inferInstance
  have := (Algebra.QuasiFinite.iff_of_algEquiv isoMp.symm).mp inferInstance
  have := isLocalization_away_one_of_equiv isoL
  have := isLocalization_away_one_of_equiv isoR
  have := isLocalization_away_one_of_equiv isoL'
  have := isLocalization_away_one_of_equiv isoRd
  have := isLocalization_away_one_of_equiv isoMp
  -- the images of the variables
  have xL : ∀ q, isoL (lciMk _ _ q) = e₁g ((decompLeftEquiv e₁g e₂g).symm (lciMk _ _ q)) := by
    intro q
    subst he₁g
    rfl
  have xR : ∀ q, isoR (lciMk _ _ q) = e₂g ((decompRightEquiv e₁g e₂g).symm (lciMk _ _ q)) := by
    intro q
    subst he₂g
    rfl
  have xLR : ∀ q, isoL (lciMk _ _ q) = isoR (lciMk _ _ q) := by
    intro q
    rw [xL, xR, ← decompEquiv_lciMk e₁g e₂g q, decompEquiv, AlgEquiv.trans_apply,
      AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply,
      AlgEquiv.apply_symm_apply]
  have xL' : ∀ q, isoL' (lciMk _ _ q) = isoL (lciMk _ _ q) := by
    intro q
    rw [hisoL', AlgEquiv.trans_apply]
    congr 1
    rw [AlgEquiv.symm_apply_eq]
    exact (localizedCompleteIntersectionCongr_algebraMap rfl hM q).symm
  have xRd : ∀ q, isoRd (lciMk _ _ q) = isoR (lciMk _ _ q) := by
    intro q
    rw [hisoRd, AlgEquiv.trans_apply, lciDetEquiv_lciMk]
  have xMp : ∀ q, isoMp (lciMk _ _ q) = isoR (lciMk _ _ q) := by
    intro q
    rw [hisoMp, AlgEquiv.trans_apply, ← xRd]
    congr 1
    rw [AlgEquiv.symm_apply_eq, lciMatrixEquiv_lciMk]
  -- the chain of Tate-related presentations
  have c1 := presRel_side k₁ (algebraMap _ A) p₁ H₁ f₁ hH₁ hf₁' e₁ dL (decompψ e₁g e₂g)
  have c2 : PresRel (B := B) (1 : MvPolynomial (Fin _) A) (decompRelLeft e₁g e₂g) 1
      (M.mulVec (decompRelRight e₁g e₂g)) :=
    presRel_of_eqRelations (fun i ↦ congrFun hM i) fun i ↦ (xL' (X i)).symm
  have c3 : PresRel (B := B) (1 : MvPolynomial (Fin _) A) (M.mulVec (decompRelRight e₁g e₂g))
      (M.det * M.det) (M.mulVec (decompRelRight e₁g e₂g)) :=
    presRel_of_eqRelations (fun _ ↦ rfl) fun i ↦ by
      change isoL' _ = isoMp _
      rw [xL', xMp, xLR]
  have c4 := (presRel_matrix k₂ (algebraMap _ A) p₂ H₂ f₂ hH₂ hf₂' e₂ dR (decompφ e₁g e₂g) M
    hdetR).symm
  have c5 : PresRel (B := B) M.det (decompRelRight e₁g e₂g) (1 : MvPolynomial (Fin _) A)
      (decompRelRight e₁g e₂g) :=
    presRel_of_eqRelations (fun _ ↦ rfl) fun i ↦ xRd (X i)
  have c6 := (presRel_side k₂ (algebraMap _ A) p₂ H₂ f₂ hH₂ hf₂' e₂ dR (decompφ e₁g e₂g)).symm
  have hrel := ((((c1.trans 1 c2).trans 1 c3).trans 1 c4).trans 1 c5).trans 1 c6
  have : IsLocalization.Away (1 : B) B :=
    IsLocalization.away_of_isUnit_of_bijective B isUnit_one Function.bijective_id
  exact hrel 1 B 1 1 k₁ _ hf₁' hk₁ k₂ _ hf₂' hk₂ G

end Claim

end Stacks.TateMap
