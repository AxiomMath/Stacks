module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.Components
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso

/-!
# A regular model with an inseparable component: the geometry of the two components

The two components of the special fibre of the model of `Stacks.Models.InseparableModel` are the
closed subschemes `(ker jC₁)` and `(ker jE)` of `X`, isomorphic to `ℙ¹_k` and `ℙ¹_κ`. The two
curves meet in a scheme of degree at most `[κ : k] = 2` over `k`.

## Main results

* `Stacks.Models.InseparableModel.finrank_meet_le`: the scheme-theoretic intersection of the two
  components has global functions of dimension at most `2` over `k`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Stacks.Models.InseparableModel

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization Stacks.AlgebraicGeometry.ProjPolyChart

/-- A point of `ℙ¹_κ` and a point of `ℙ¹_k` with the same image in `X` lie in the standard opens
`D₊(b)` and `D₊(a)` cut out by `z₀₁`: the image lies on the strict transform, so `z₀₀` vanishes
there, and on the exceptional curve `z₀₀` and `z₀₁` do not vanish together. -/
private theorem mem_basicOpen_of_jE_eq_jC₁ (w : P1 κ) (y : P1 k) (h : jE w = jC₁ y) :
    w ∈ Proj.basicOpen (lineGrading κ) (φE (zA 1)) ∧
      y ∈ Proj.basicOpen (lineGrading k) (φC₁ (zA 1)) := by
  have hy0 : jC₁ y ∉ Proj.basicOpen grading (zA 0) := by
    show y ∉ jC₁ ⁻¹ᵁ Proj.basicOpen grading (zA 0)
    rw [jC₁, Proj.map_preimage_basicOpen, φC₁_zA]
    simp
  have hw0 : w ∉ Proj.basicOpen (lineGrading κ) (MvPolynomial.X 0) := fun hw ↦ hy0 <| by
    rw [← h]
    show w ∈ jE ⁻¹ᵁ Proj.basicOpen grading (zA 0)
    rwa [jE, Proj.map_preimage_basicOpen, φE_zA]
  have hw1 : w ∈ Proj.basicOpen (lineGrading κ) (φE (zA 1)) := by
    have hw : w ∈ (⨆ i : Fin (1 + 1),
        Proj.basicOpen (lineGrading κ) (MvPolynomial.X i)) := by
      rw [iSup_basicOpen_X_eq_top]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hw
    rw [φE_zA]
    fin_cases i
    · exact absurd hi hw0
    · exact hi
  refine ⟨hw1, ?_⟩
  show y ∈ jC₁ ⁻¹ᵁ Proj.basicOpen grading (zA 1)
  rwa [Scheme.Hom.mem_preimage, ← h, ← Scheme.Hom.mem_preimage]

/-- On the chart `D₊(b)` of `ℙ¹_κ`, any ring map killing the affine coordinate `a / b` takes every
function to the image of a constant. -/
private theorem exists_coeff_of_eq_zero (b : MvPolynomial (Fin (1 + 1)) κ)
    (hb : b = MvPolynomial.X 1)
    (hd : b ∈ lineGrading κ 1)
    (h0 : (MvPolynomial.X 0 : MvPolynomial (Fin (1 + 1)) κ) ∈ lineGrading κ (1 • 1))
    {S : Type} [CommRing S] (ψ : HomogeneousLocalization.Away (lineGrading κ) b →+* S)
    (hψ : ψ (HomogeneousLocalization.Away.mk (lineGrading κ) hd 1 (MvPolynomial.X 0) h0) = 0)
    (y : HomogeneousLocalization.Away (lineGrading κ) b) :
    ∃ c : κ, ψ y = ψ (algebraMap (lineGrading κ 0) (HomogeneousLocalization.Away (lineGrading κ) b)
      (algebraMap κ (lineGrading κ 0) c)) := by
  subst hb
  obtain ⟨P, rfl⟩ := chartHom_surjective κ 1 1 y
  refine ⟨MvPolynomial.constantCoeff P, ?_⟩
  have key : ψ.comp (chartHom κ 1 1) =
      (ψ.comp (coeffToAway κ 1 1)).comp MvPolynomial.constantCoeff := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp [chartHom_C]
    · obtain ⟨j, hj⟩ := j
      obtain rfl : j = 0 := by fin_cases j <;> simp_all
      simp only [RingHom.comp_apply, chartHom_X, MvPolynomial.constantCoeff_X, map_zero]
      exact hψ
  exact DFunLike.congr_fun key P

/-- The structure morphism of `ℙ¹_κ` on the chart `D₊(b)` is `Spec` of the inclusion of the
constants. -/
private theorem awayι_comp_P1toSpec (b : MvPolynomial (Fin (1 + 1)) κ) (hb : b = MvPolynomial.X 1)
    (hd : b ∈ lineGrading κ 1) :
    Proj.awayι (lineGrading κ) b hd Nat.one_pos ≫ P1toSpec κ =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (lineGrading κ 0) (HomogeneousLocalization.Away (lineGrading κ) b)).comp
          (algebraMap κ (lineGrading κ 0)))) := by
  subst hb
  exact Stacks.AlgebraicGeometry.ProjBaseChange.awayι_comp_projToSpecCoeff κ 1 1

/-- The ring map on global sections of a morphism to an affine scheme. -/
private def ringOfSpec {X : Scheme} {S : CommRingCat} (q : X ⟶ Spec S) : S →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso S).inv ≫ q.appTop).hom

private theorem ringOfSpec_comp {X : Scheme} {S S' : CommRingCat} (q : X ⟶ Spec S) (θ : S' ⟶ S) :
    ringOfSpec (q ≫ Spec.map θ) = (ringOfSpec q).comp θ.hom := by
  rw [ringOfSpec, ringOfSpec, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, CommRingCat.hom_comp]

/-- A morphism to the chart `D₊(b)` of `ℙ¹_κ` that agrees over the chart `D₊(z₀₁)` of `X` with a
morphism to the chart `D₊(a)` of `ℙ¹_k` kills the affine coordinate `a / b`. -/
private theorem ringOfSpec_mk_X_zero_eq_zero {Y : Scheme}
    (u' : Y ⟶ Spec (.of (HomogeneousLocalization.Away (lineGrading κ) (φE (zA 1)))))
    (v' : Y ⟶ Spec (.of (HomogeneousLocalization.Away (lineGrading k) (φC₁ (zA 1)))))
    (hsq : u' ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map φE (zA 1))) =
      v' ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map φC₁ (zA 1))))
    (h0 : (MvPolynomial.X 0 : MvPolynomial (Fin (1 + 1)) κ) ∈ lineGrading κ (1 • 1)) :
    ringOfSpec u' (HomogeneousLocalization.Away.mk (lineGrading κ) (φE.2 (zA_mem 1)) 1
      (MvPolynomial.X 0) h0) = 0 := by
  have hzA0 : zA 0 ∈ grading (1 • 1) := by
    rw [smul_eq_mul, mul_one]
    exact zA_mem 0
  let T : HomogeneousLocalization.Away grading (zA 1) :=
    HomogeneousLocalization.Away.mk grading (zA_mem 1) 1 (zA 0) hzA0
  have hTC : HomogeneousLocalization.Away.map φC₁ (zA 1) T = 0 := by
    rw [HomogeneousLocalization.Away.map_mk, HomogeneousLocalization.ext_iff_val,
      HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero]
    simp only [φC₁_zA]
    exact Localization.mk_zero _
  have hTE : HomogeneousLocalization.Away.map φE (zA 1) T =
      HomogeneousLocalization.Away.mk (lineGrading κ) (φE.2 (zA_mem 1)) 1 (MvPolynomial.X 0)
        h0 := by
    rw [HomogeneousLocalization.Away.map_mk, HomogeneousLocalization.ext_iff_val,
      HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk]
    simp [φE_zA]
  rw [← hTE, ← RingHom.comp_apply]
  have := ringOfSpec_comp u' (CommRingCat.ofHom (HomogeneousLocalization.Away.map φE (zA 1)))
  rw [CommRingCat.hom_ofHom] at this
  rw [← this, hsq, ringOfSpec_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, hTC, map_zero]

/-- A morphism `g` to `Spec k`, compatible over `Spec R` with a closed immersion into the chart
`D₊(b)` of `ℙ¹_κ` that agrees over `X` with a morphism to the chart `D₊(a)` of `ℙ¹_k`, has global
functions of dimension at most `2` over `k`. -/
private theorem finrank_le_of_chart {Y : Scheme} (g : Y ⟶ Spec (.of k))
    (u' : Y ⟶ Spec (.of (HomogeneousLocalization.Away (lineGrading κ) (φE (zA 1)))))
    (v' : Y ⟶ Spec (.of (HomogeneousLocalization.Away (lineGrading k) (φC₁ (zA 1)))))
    [IsClosedImmersion u']
    (hsq : u' ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map φE (zA 1))) =
      v' ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map φC₁ (zA 1))))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap R k)) =
      u' ≫ Proj.awayι (lineGrading κ) (φE (zA 1)) (φE.2 (zA_mem 1)) Nat.one_pos ≫ jE ≫ X_to_R) :
    Module.finrank k (cohomologyOverField k g (SheafOfModules.unit Y.ringCatSheaf) 0) ≤ 2 := by
  have hX1 : φE (zA 1) = MvPolynomial.X 1 := by
    rw [φE_zA]
    rfl
  have h0 : (MvPolynomial.X 0 : MvPolynomial (Fin (1 + 1)) κ) ∈ lineGrading κ (1 • 1) := by
    rw [smul_eq_mul, mul_one]
    exact X_mem_one κ 1 0
  have hsurj : Function.Surjective (ringOfSpec u') :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine u').2.comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (algebraMap R k))
    algebraMap_Rk_surjective
  let coeffE : κ →+* HomogeneousLocalization.Away (lineGrading κ) (φE (zA 1)) :=
    (algebraMap (lineGrading κ 0) (HomogeneousLocalization.Away (lineGrading κ) (φE (zA 1)))).comp
      (algebraMap κ (lineGrading κ 0))
  have hge : g = u' ≫ Spec.map (CommRingCat.ofHom (coeffE.comp (algebraMap k κ))) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap R k))), hg, jE_comp_X_to_R,
      reassoc_of% (awayι_comp_P1toSpec _ hX1 (φE.2 (zA_mem 1)))]
    simp only [coeffE, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hφ : ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ ⊤ (by simp)).hom =
      (ringOfSpec u').comp (coeffE.comp (algebraMap k κ)) := by
    have happ : g.appLE ⊤ ⊤ (by simp) = g.appTop := (Scheme.Hom.app_eq_appLE (U := ⊤) g).symm
    rw [happ]
    show ringOfSpec g = _
    rw [hge, ringOfSpec_comp, CommRingCat.hom_ofHom]
  let H := (restrictScalarsOverBase k g).obj
    ((SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op ⊤)).obj
      (SheafOfModules.unit Y.ringCatSheaf))
  let L : κ →ₗ[k] H :=
    { toFun := fun c => (ringOfSpec u' (coeffE c) : Γ(Y, ⊤))
      map_add' := fun c c' => by
        simp only [map_add]
        rfl
      map_smul' := fun r c => by
        show ringOfSpec u' (coeffE (r • c)) =
          ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ ⊤ (by simp)).hom r * ringOfSpec u' (coeffE c)
        rw [hφ, Algebra.smul_def, map_mul, map_mul]
        rfl }
  have hLsurj : Function.Surjective L := by
    intro z
    obtain ⟨y, rfl⟩ := hsurj z
    obtain ⟨c, hc⟩ := exists_coeff_of_eq_zero _ hX1 (φE.2 (zA_mem 1)) h0 (ringOfSpec u')
      (ringOfSpec_mk_X_zero_eq_zero u' v' hsq h0) y
    exact ⟨c, hc.symm⟩
  have hfin : Module.Finite k κ := Module.finite_of_finrank_pos (by rw [finrank_κ]; norm_num)
  refine ((cohomologyOverFieldZeroLinearIso k g _).toLinearEquiv.finrank_eq).trans_le ?_
  calc Module.finrank k H = Module.finrank k (LinearMap.range L) := by
        rw [LinearMap.range_eq_top.mpr hLsurj, finrank_top]
    _ ≤ Module.finrank k κ := LinearMap.finrank_range_le L
    _ = 2 := finrank_κ

/-- The inverse of the factorization through the image composed with a closed immersion is the
inclusion of its kernel. -/
private theorem inv_toImage_comp {A B : Scheme} (f : A ⟶ B) [IsClosedImmersion f] :
    inv f.toImage ≫ f = f.ker.subschemeι := by
  rw [IsIso.inv_comp_eq]
  exact (Scheme.Hom.toImage_imageι f).symm

/-- A morphism whose points all lie in the range of an open immersion factors through it. -/
private theorem exists_comp_eq_of_forall_mem_opensRange {Y P Q : Scheme} (ι : Q ⟶ P)
    [IsOpenImmersion ι] (u : Y ⟶ P) (h : ∀ y, u y ∈ ι.opensRange) : ∃ u' : Y ⟶ Q, u' ≫ ι = u :=
  ⟨IsOpenImmersion.lift ι u (by rintro _ ⟨y, rfl⟩; exact h y), IsOpenImmersion.lift_fac _ _ _⟩

/-- **The strict transform meets the exceptional curve in a scheme of degree at most two**: for a
morphism `g` to `Spec k` from the scheme-theoretic intersection of `(ker jE)` and `(ker jC₁)`,
compatible with `X ⟶ Spec R`, its global functions have dimension at most `2` over `k`. -/
theorem finrank_meet_le {I I' : XR.IdealSheafData} (hI : I = jE.ker) (hI' : I' = jC₁.ker)
    (g : (I'.comap I.subschemeι).subscheme ⟶ Spec (.of k))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap R k)) =
      (I'.comap I.subschemeι).subschemeι ≫ I.subschemeι ≫ X_to_R) :
    Module.finrank k (cohomologyOverField k g
      (SheafOfModules.unit (I'.comap I.subschemeι).subscheme.ringCatSheaf) 0) ≤ 2 := by
  subst hI hI'
  let u : (jC₁.ker.comap jE.ker.subschemeι).subscheme ⟶ P1 κ :=
    (jC₁.ker.comap jE.ker.subschemeι).subschemeι ≫ inv jE.toImage
  let v : (jC₁.ker.comap jE.ker.subschemeι).subscheme ⟶ P1 k :=
    (jC₁.ker.comapIso jE.ker.subschemeι).hom ≫ Limits.pullback.snd _ _ ≫ inv jC₁.toImage
  have huv : u ≫ jE = v ≫ jC₁ := by
    simp only [u, v, Category.assoc, inv_toImage_comp]
    rw [← Limits.pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  have hpt : ∀ w, u w ∈ Proj.basicOpen (lineGrading κ) (φE (zA 1)) ∧
      v w ∈ Proj.basicOpen (lineGrading k) (φC₁ (zA 1)) := fun w =>
    mem_basicOpen_of_jE_eq_jC₁ (u w) (v w)
      (by rw [← Scheme.Hom.comp_apply, huv, Scheme.Hom.comp_apply])
  let ιE := Proj.awayι (lineGrading κ) (φE (zA 1)) (φE.2 (zA_mem 1)) Nat.one_pos
  let ιC := Proj.awayι (lineGrading k) (φC₁ (zA 1)) (φC₁.2 (zA_mem 1)) Nat.one_pos
  let ιX := Proj.awayι grading (zA 1) (zA_mem 1) Nat.one_pos
  obtain ⟨u', hu'⟩ := exists_comp_eq_of_forall_mem_opensRange ιE u fun w => by
    rw [Proj.opensRange_awayι]
    exact (hpt w).1
  obtain ⟨v', hv'⟩ := exists_comp_eq_of_forall_mem_opensRange ιC v fun w => by
    rw [Proj.opensRange_awayι]
    exact (hpt w).2
  have hsq : u' ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map φE (zA 1))) =
      v' ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map φC₁ (zA 1))) := by
    rw [← cancel_mono ιX, Category.assoc, Category.assoc,
      ← Proj.awayι_comp_map φE irrelevant_le_map_φE Nat.one_pos (zA 1) (zA_mem 1),
      ← Proj.awayι_comp_map φC₁ irrelevant_le_map_φC₁ Nat.one_pos (zA 1) (zA_mem 1),
      ← Category.assoc, hu', ← Category.assoc, hv']
    exact huv
  have : IsClosedImmersion u' := by
    have : IsClosedImmersion (u' ≫ ιE) := by
      rw [hu']
      infer_instance
    exact IsClosedImmersion.of_comp u' ιE
  refine finrank_le_of_chart g u' v' hsq (hg.trans ?_)
  calc _ = u ≫ jE ≫ X_to_R := by simp only [u, Category.assoc, reassoc_of% (inv_toImage_comp jE)]
    _ = u' ≫ ιE ≫ jE ≫ X_to_R := by rw [← hu', Category.assoc]

end Stacks.Models.InseparableModel
