module

public import Mathlib.RingTheory.Localization.Ideal
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange
public import StacksFrontier.RingTheory.Smooth.Localization
public import StacksFrontier.RingTheory.Smoothing.DesingularizationLemma

/-!
# A common desingularizing factorization for two finitely presented algebras

Let `R` be Noetherian, let `Λ` be an `R`-algebra and let `π ∈ R` be an element whose
annihilator agrees with that of `π²` both in `R` and in `Λ`. Let `A` and `D` be `R`-algebras of
finite presentation mapping to `Λ`. If `π` is strictly standard in `A` over `R` and the map
`A → Λ` factors through `D` modulo `π⁴`, then both maps factor through a single `R`-algebra `B`
of finite presentation, and the singular ideal `H_{D/R}` extends into both `H_{B/D}` and
`H_{B/R}`.

The proof applies the desingularization lemma to `D → A ⊗_R D → Λ` and the image of `π` in `D`:
base change makes `π` strictly standard in `A ⊗_R D` over `D`, and the map of (2) induces the
required retraction modulo `π⁴`. The resulting `B` satisfies `𝔞 B ⊆ H_{B/D}` for
`𝔞 = Ann_D (Ann_D (π²) / Ann_D (π))`. At a prime `𝔮` of `D` at which `R → D` is smooth, `D_𝔮`
is flat over `R`, so `Ann_{D_𝔮}(π) = Ann_{D_𝔮}(π²)` by flat base change; as `D` is Noetherian
the quotient of annihilators is a finite module and its annihilator localizes, so `𝔞 ⊄ 𝔮`.
Hence `D → B` is smooth above the smooth locus of `R → D`, which gives the first inclusion, and
the second follows because smooth ring maps compose.

## Main results

* `Stacks.Smoothing.exists_finitePresentation_factorization_singularIdeal_le`: the common
  factorization together with the two singular-ideal inclusions.

## References

* [Stacks Project, Tag 07CT](https://stacks.math.columbia.edu/tag/07CT)
* [Stacks Project, Tag 07CR](https://stacks.math.columbia.edu/tag/07CR)
* [Stacks Project, Tag 07CC](https://stacks.math.columbia.edu/tag/07CC)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.Smoothing

universe u v w x

/-- Smoothness at a prime composes: if `R → S` is smooth at the contraction of `𝔮` and
`S → T` is smooth at `𝔮`, then `R → T` is smooth at `𝔮`. -/
private theorem smoothAt_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (q : Ideal T) [q.IsPrime] (p : Ideal S) [p.IsPrime] (hpq : p = q.comap (algebraMap S T))
    (hRS : Algebra.SmoothAt R S p) (hST : Algebra.SmoothAt S T q) :
    Algebra.SmoothAt R T q := by
  obtain ⟨g, hg, hgSmooth⟩ := (Algebra.smoothAt_iff R S p).mp hRS
  obtain ⟨h, hh, hhSmooth⟩ := (Algebra.smoothAt_iff S T q).mp hST
  let T₀ := Localization.Away h
  let : Algebra T T₀ := inferInstance
  let gT := algebraMap S T g
  let T₁ := Localization.Away (algebraMap T T₀ gT)
  let : Algebra T₀ T₁ := inferInstance
  have hST₁ : Algebra.Smooth S T₁ := Algebra.Smooth.localization_away (algebraMap T T₀ gT)
  let P := Localization.Away g
  have hunit : IsUnit (algebraMap S T₁ g) := by
    change IsUnit (algebraMap T T₁ gT)
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap T T₀ gT)
  let fLift : P →ₐ[S] T₁ :=
    IsLocalization.Away.liftAlgHom (x := g) (f := Algebra.ofId S T₁) hunit
  let : Algebra P T₁ := fLift.toRingHom.toAlgebra
  let : SMul S T₁ := Algebra.toSMul
  let : IsScalarTower S T T₁ := IsScalarTower.of_algebraMap_eq' (R := S) (S := T) (A := T₁) rfl
  let : IsScalarTower S P T₁ :=
    IsScalarTower.of_algebraMap_eq (R := S) (S := P) (A := T₁) fun s => (fLift.commutes s).symm
  let : IsScalarTower R P T₁ :=
    IsScalarTower.of_algebraMap_smul (R := R) (A := P) fun r z => by
      rw [show algebraMap R P r = algebraMap S P (algebraMap R S r) by rfl]
      rw [IsScalarTower.algebraMap_smul (R := S) (A := P)]
      rw [IsScalarTower.algebraMap_smul (R := R) (A := S)]
  have hPT₁ : Algebra.Smooth P T₁ := Algebra.Smooth.localization_base (Submonoid.powers g)
  have hRP : Algebra.Smooth R P := by simpa [P] using hgSmooth
  have hRT₁ : Algebra.Smooth R T₁ := Algebra.Smooth.comp R P T₁
  let : IsLocalization.Away (h * gT) T₁ := by
    simpa [gT, mul_comm] using
      (IsLocalization.Away.mul' (S := T₀) (T := T₁) (x := h) (y := gT))
  let W := Localization.Away (h * gT)
  let : Algebra T W := inferInstance
  let e : W ≃ₐ[T] T₁ := IsLocalization.algEquiv (Submonoid.powers (h * gT)) W T₁
  let eR : W ≃ₐ[R] T₁ := AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (by
    intro r
    change e (algebraMap T W (algebraMap R T r)) = algebraMap T T₁ (algebraMap R T r)
    exact e.commutes (algebraMap R T r))
  have hRW : Algebra.Smooth R W := Algebra.Smooth.of_equiv eR.symm
  have hgq : gT ∉ q := by
    intro hqg
    exact hg (hpq ▸ hqg)
  have hprod : h * gT ∉ q := by
    intro hmem
    rcases (inferInstance : q.IsPrime).mul_mem_iff_mem_or_mem.mp hmem with hc | hc
    · exact hh hc
    · exact hgq hc
  exact (Algebra.smoothAt_iff R T q).2 ⟨h * gT, hprod, hRW⟩

/-- At a prime of `D` at which `R → D` is smooth, the defect ideal of the image of `π` is not
contained in that prime, provided the annihilators of `π` and `π²` already agree in `R`. -/
private theorem annihilatorDefect_not_le_of_smoothAt {R D : Type*} [CommRing R] [CommRing D]
    [Algebra R D] [IsNoetherianRing D] (π : R)
    (hR : (Submodule.span R {π}).annihilator = (Submodule.span R {π ^ 2}).annihilator)
    (p : Ideal D) [p.IsPrime] (hp : Algebra.SmoothAt R D p) :
    ¬ annihilatorDefectIdeal D (algebraMap R D π) ≤ p := by
  obtain ⟨g, hg, hgsmooth⟩ := (Algebra.smoothAt_iff R D p).mp hp
  let S := Localization.Away g
  let : IsScalarTower R D S := IsScalarTower.of_algebraMap_smul fun r s => by
    change (algebraMap R D r) • s = r • s
    simp [Algebra.smul_def]
    rfl
  let : Algebra.Smooth R S := hgsmooth
  let : Module.Flat R S := Algebra.Smooth.flat R S
  let : Module.Flat D S := IsLocalization.flat S (Submonoid.powers g)
  let I₁ : Ideal D := (Submodule.span D {algebraMap R D π}).annihilator
  let I₂ : Ideal D := (Submodule.span D {(algebraMap R D π) ^ 2}).annihilator
  have hSann : (Submodule.span S {algebraMap R S π}).annihilator =
      (Submodule.span S {(algebraMap R S π) ^ 2}).annihilator := by
    calc
      (Submodule.span S {algebraMap R S π}).annihilator =
          Ideal.map (algebraMap R S) (Submodule.span R {π}).annihilator :=
        (map_annihilator_span_singleton_of_flat (R := R) (S := S) π).symm
      _ = Ideal.map (algebraMap R S) (Submodule.span R {π ^ 2}).annihilator :=
        congrArg (Ideal.map (algebraMap R S)) hR
      _ = (Submodule.span S {algebraMap R S (π ^ 2)}).annihilator :=
        map_annihilator_span_singleton_of_flat (R := R) (S := S) (π ^ 2)
      _ = (Submodule.span S {(algebraMap R S π) ^ 2}).annihilator := by simp
  have hmap₁ : Ideal.map (algebraMap D S) I₁ =
      (Submodule.span S {algebraMap R S π}).annihilator := by
    simpa [I₁, IsScalarTower.algebraMap_eq R D S] using
      (map_annihilator_span_singleton_of_flat (R := D) (S := S) (algebraMap R D π))
  have hmap₂ : Ideal.map (algebraMap D S) I₂ =
      (Submodule.span S {(algebraMap R S π) ^ 2}).annihilator := by
    calc
      Ideal.map (algebraMap D S) I₂ =
          (Submodule.span S {algebraMap D S ((algebraMap R D π) ^ 2)}).annihilator := by
        simpa only [I₂] using
          (map_annihilator_span_singleton_of_flat (R := D) (S := S) ((algebraMap R D π) ^ 2))
      _ = (Submodule.span S {(algebraMap R S π) ^ 2}).annihilator := by
        rw [map_pow]
        have hπ : algebraMap D S (algebraMap R D π) = algebraMap R S π :=
          (congrArg (fun f : R →+* S => f π) (IsScalarTower.algebraMap_eq R D S)).symm
        rw [hπ]
  have hmap : Ideal.map (algebraMap D S) I₁ = Ideal.map (algebraMap D S) I₂ := by
    rw [hmap₁, hmap₂, hSann]
  let : Module.Finite D I₂ := inferInstance
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := D) (M := I₂)
  have hloc : ∀ i : Fin n, ∃ k : ℕ, g ^ k * (s i : D) ∈ I₁ := by
    intro i
    have hx : algebraMap D S (s i : D) ∈ Ideal.map (algebraMap D S) I₁ := by
      rw [hmap]
      exact Ideal.mem_map_of_mem (algebraMap D S) (s i).property
    obtain ⟨m, hm, hmx⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers g) S I₁ (s i : D)).mp hx
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff m g).mp hm
    exact ⟨k, hmx⟩
  choose e he using hloc
  let N : ℕ := ∑ i : Fin n, e i
  have hgen (i : Fin n) : g ^ N * (s i : D) ∈ I₁ := by
    have hle : e i ≤ N := Finset.single_le_sum (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ i)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    have hmem := I₁.mul_mem_left (g ^ k) (he i)
    convert hmem using 1
    rw [show N = e i + k by omega, pow_add]
    ring
  have hmul (y : I₂) : g ^ N * (y : D) ∈ I₁ := by
    have hy : y ∈ Submodule.span D (Set.range s) := by
      rw [hs]
      exact Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro z hz
      obtain ⟨i, rfl⟩ := Set.mem_range.mp hz
      exact hgen i
    · simp
    · intro z₁ z₂ _ _ hz₁ hz₂
      simpa [mul_add] using I₁.add_mem hz₁ hz₂
    · intro b z _ hz
      change g ^ N * (b * (z : D)) ∈ I₁
      have hmem := I₁.mul_mem_left b hz
      convert hmem using 1
      ring
  have hN : g ^ N ∈ annihilatorDefectIdeal D (algebraMap R D π) :=
    (mem_annihilatorDefectIdeal_iff _ _).mpr fun y hy => hmul ⟨y, hy⟩
  have hNnot : g ^ N ∉ p := by
    intro h
    by_cases hzero : N = 0
    · rw [hzero] at h
      exact (inferInstance : p.IsPrime).ne_top ((Ideal.eq_top_iff_one p).mpr (by simpa using h))
    · exact hg (((inferInstance : p.IsPrime).pow_mem_iff_mem N
        (Nat.pos_of_ne_zero hzero)).mp h)
  exact fun hle => hNnot (hle hN)

/-- **Stacks 07CT.** A strictly standard element and a factorization modulo its fourth power
yield a common finitely presented factorization `A → B ← D` over `Λ` with
`H_{D/R} B ⊆ H_{B/D}` and `H_{D/R} B ⊆ H_{B/R}`. -/
@[stacks 07CT]
theorem exists_finitePresentation_factorization_singularIdeal_le
    (R : Type u) (A : Type v) (D : Type w) (Λ : Type x)
    [CommRing R] [CommRing A] [CommRing D] [CommRing Λ] [IsNoetherianRing R]
    [Algebra R A] [Algebra R D] [Algebra R Λ]
    [Algebra.FinitePresentation R A] [Algebra.FinitePresentation R D] (π : R)
    (hR : (Submodule.span R {π}).annihilator = (Submodule.span R {π ^ 2}).annihilator)
    (hΛ : (Submodule.span Λ {algebraMap R Λ π}).annihilator =
      (Submodule.span Λ {(algebraMap R Λ π) ^ 2}).annihilator)
    (fA : A →ₐ[R] Λ) (fD : D →ₐ[R] Λ)
    (hπ : IsStrictlyStandard (R := R) (A := A) (algebraMap R A π))
    (bar : (A ⧸ Ideal.span {(algebraMap R A π) ^ 4}) →ₐ[R]
      D ⧸ Ideal.span {(algebraMap R D π) ^ 4})
    (hbar : ∀ (a : A) (y : D),
      bar (Ideal.Quotient.mk (Ideal.span {(algebraMap R A π) ^ 4}) a) =
          Ideal.Quotient.mk (Ideal.span {(algebraMap R D π) ^ 4}) y →
        Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (fA a) =
          Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (fD y)) :
    ∃ (B : Type w) (_ : CommRing B) (_ : Algebra D B) (_ : Algebra R B)
      (_ : IsScalarTower R D B) (_ : Algebra.FinitePresentation R B)
      (a : A →ₐ[R] B) (g : B →ₐ[R] Λ),
      g.comp a = fA ∧ g.comp (IsScalarTower.toAlgHom R D B) = fD ∧
        (singularIdeal R D).map (algebraMap D B) ≤ singularIdeal D B ∧
        (singularIdeal R D).map (algebraMap D B) ≤ singularIdeal R B := by
  let C := D ⊗[R] A
  let : Algebra D C := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower R D C := IsScalarTower.of_algebraMap_smul fun r c => by
    induction c using TensorProduct.inductionOn with
    | add u y hu hy => simp [hu, hy]
    | tmul d a => simp [Algebra.algebraMap_eq_smul_one]
  let : Algebra.FinitePresentation D C := Algebra.FinitePresentation.baseChange D
  let : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing R D
  let : Algebra D Λ := fD.toAlgebra
  let : IsScalarTower R D Λ := IsScalarTower.of_algebraMap_smul fun r z => by
    change (algebraMap D Λ (algebraMap R D r)) • z = _
    rw [IsScalarTower.algebraMap_smul]
    simp
  let fC : C →ₐ[D] Λ :=
    Algebra.TensorProduct.lift (Algebra.ofId D Λ) fA (fun d a => Commute.all _ _)
  have hCstd : IsStrictlyStandard (R := D) (algebraMap D C (algebraMap R D π)) := by
    simpa [C] using
      (isStrictlyStandard_basechange (R := R) (R' := D) (A := A) (algebraMap R A π) hπ)
  let IA := Ideal.span {(algebraMap R A π) ^ 4}
  let ID := Ideal.span {(algebraMap R D π) ^ 4}
  let IC := Ideal.span {(algebraMap D C (algebraMap R D π)) ^ 4}
  let IL := Ideal.span {(algebraMap R Λ π) ^ 4}
  let qA : A →ₐ[R] D ⧸ ID := bar.comp (Ideal.Quotient.mkₐ R IA)
  let liftC : C →ₐ[D] D ⧸ ID :=
    Algebra.TensorProduct.lift (Algebra.ofId D (D ⧸ ID)) qA (fun d a => Commute.all _ _)
  have hIC : IC ≤ RingHom.ker liftC.toRingHom := by
    change Ideal.span {(algebraMap D C (algebraMap R D π)) ^ 4} ≤ RingHom.ker liftC.toRingHom
    rw [Ideal.span_le]
    rintro _ ⟨z, rfl⟩
    apply RingHom.mem_ker.mpr
    rw [map_pow]
    change (liftC (algebraMap D C (algebraMap R D π))) ^ 4 = 0
    rw [liftC.commutes, ← map_pow, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  let qΛ : Λ →ₐ[R] Λ ⧸ IL := Ideal.Quotient.mkₐ R IL
  let qDB : D →ₐ[R] Λ ⧸ IL := qΛ.comp fD
  let qFA : A →ₐ[R] Λ ⧸ IL := qΛ.comp fA
  have hID' : ID ≤ IL.comap fD.toRingHom := by
    change Ideal.span {(algebraMap R D π) ^ 4} ≤ IL.comap fD.toRingHom
    rw [Ideal.span_le]
    rintro _ ⟨z, rfl⟩
    change fD.toRingHom ((algebraMap R D π) ^ 4) ∈ IL
    rw [map_pow]
    change (fD (algebraMap R D π)) ^ 4 ∈ IL
    rw [fD.commutes π]
    exact Ideal.subset_span (by simp)
  let qMap : (D ⧸ ID) →ₐ[R] (Λ ⧸ IL) := Ideal.quotientMapₐ IL fD hID'
  let ρ : (C ⧸ IC) →ₐ[D] (D ⧸ ID) :=
    Ideal.Quotient.liftₐ (R₁ := D) IC liftC (fun z hz => RingHom.mem_ker.mp (hIC hz))
  have hqMap : qMap.comp (Ideal.Quotient.mkₐ R ID) = qDB := by
    simpa [qMap, qDB, qΛ] using (Ideal.quotient_map_comp_mkₐ (R₁ := R) (I := ID) IL fD hID')
  let left : C →ₐ[R] (Λ ⧸ IL) := qΛ.comp (AlgHom.restrictScalars R fC)
  let right : C →ₐ[R] (Λ ⧸ IL) :=
    qMap.comp ((AlgHom.restrictScalars R ρ).comp (Ideal.Quotient.mkₐ R IC))
  have hbar' : qMap.comp qA = qFA := by
    refine AlgHom.ext fun a => ?_
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (bar (Ideal.Quotient.mk IA a))
    have h := hbar a y hy.symm
    change qMap (bar (Ideal.Quotient.mk IA a)) = qΛ (fA a)
    rw [← hy, show qMap (Ideal.Quotient.mk ID y) = qDB y from DFunLike.congr_fun hqMap y]
    exact h.symm
  have hfLeft : fC.comp Algebra.TensorProduct.includeLeft = Algebra.ofId D Λ := by
    simpa only [fC] using
      (Algebra.TensorProduct.lift_comp_includeLeft (Algebra.ofId D Λ) fA
        (fun _ _ => Commute.all _ _))
  have hfRight : (AlgHom.restrictScalars R fC).comp Algebra.TensorProduct.includeRight = fA := by
    simpa only [fC] using
      (Algebra.TensorProduct.lift_comp_includeRight (Algebra.ofId D Λ) fA
        (fun _ _ => Commute.all _ _))
  have hLiftLeft : liftC.comp Algebra.TensorProduct.includeLeft = Algebra.ofId D (D ⧸ ID) := by
    simpa only [liftC] using
      (Algebra.TensorProduct.lift_comp_includeLeft (Algebra.ofId D (D ⧸ ID)) qA
        (fun _ _ => Commute.all _ _))
  have hLiftRight :
      (AlgHom.restrictScalars R liftC).comp Algebra.TensorProduct.includeRight = qA := by
    simpa only [liftC] using
      (Algebra.TensorProduct.lift_comp_includeRight (Algebra.ofId D (D ⧸ ID)) qA
        (fun _ _ => Commute.all _ _))
  have hρAt (c : C) : ρ (Ideal.Quotient.mk IC c) = liftC c := rfl
  have hρLeftPoint (d : D) :
      ρ (Ideal.Quotient.mk IC (d ⊗ₜ[R] (1 : A))) = Ideal.Quotient.mk ID d := by
    rw [hρAt]
    change (liftC.comp Algebra.TensorProduct.includeLeft) d = _
    rw [hLiftLeft]
    rfl
  have hρRightPoint (a : A) : ρ (Ideal.Quotient.mk IC ((1 : D) ⊗ₜ[R] a)) = qA a := by
    rw [hρAt]
    change ((AlgHom.restrictScalars R liftC).comp Algebra.TensorProduct.includeRight) a = _
    rw [hLiftRight]
  have hbridge : left = right := by
    apply AlgHom.toRingHom_injective
    apply Algebra.TensorProduct.ringHom_ext
    · ext d
      change qΛ ((fC.comp Algebra.TensorProduct.includeLeft) d) =
        qMap (ρ (Ideal.Quotient.mk IC (d ⊗ₜ[R] (1 : A))))
      rw [hfLeft, hρLeftPoint]
      exact (DFunLike.congr_fun hqMap d).symm
    · ext a
      change qΛ (((AlgHom.restrictScalars R fC).comp Algebra.TensorProduct.includeRight) a) =
        qMap (ρ (Ideal.Quotient.mk IC ((1 : D) ⊗ₜ[R] a)))
      rw [hfRight, hρRightPoint]
      exact (DFunLike.congr_fun hbar' a).symm
  have hIL : IL = Ideal.span {(algebraMap D Λ (algebraMap R D π)) ^ 4} :=
    (congrArg (fun z : Λ => Ideal.span {z ^ 4}) (fD.commutes π)).symm
  have hρSection : ∀ (y : C) (z : D),
      ρ (Ideal.Quotient.mk IC y) = Ideal.Quotient.mk ID z →
        Ideal.Quotient.mk (Ideal.span {(algebraMap D Λ (algebraMap R D π)) ^ 4}) (fC y) =
          Ideal.Quotient.mk (Ideal.span {(algebraMap D Λ (algebraMap R D π)) ^ 4})
            (algebraMap D Λ z) := by
    intro y z hz
    have hbridgeAt := DFunLike.congr_fun hbridge y
    have hcomp : qΛ (fC y) = qMap (ρ (Ideal.Quotient.mk IC y)) := by
      simpa [left, right] using hbridgeAt
    have hq : qΛ (fC y) = qΛ (algebraMap D Λ z) := calc
      qΛ (fC y) = qMap (ρ (Ideal.Quotient.mk IC y)) := hcomp
      _ = qMap (Ideal.Quotient.mk ID z) := congrArg qMap hz
      _ = qDB z := DFunLike.congr_fun hqMap z
      _ = qΛ (algebraMap D Λ z) := rfl
    rw [← hIL]
    change Ideal.Quotient.mk IL (fC y) = Ideal.Quotient.mk IL (algebraMap D Λ z)
    simpa [qΛ] using hq
  have hAnnΛ : (Submodule.span Λ {algebraMap D Λ (algebraMap R D π)}).annihilator =
      (Submodule.span Λ {(algebraMap D Λ (algebraMap R D π)) ^ 2}).annihilator := by
    rw [show algebraMap D Λ (algebraMap R D π) = algebraMap R Λ π from fD.commutes π]
    exact hΛ
  obtain ⟨B, instB, algDB, fpDB, gC, hB, hfact, hdefect⟩ :=
    exists_finitePresentation_factorization_singularIdeal D C Λ (algebraMap R D π) fC hAnnΛ
      hCstd ρ hρSection
  let : CommRing B := instB
  let : Algebra D B := algDB
  let : Algebra.FinitePresentation D B := fpDB
  let : Algebra R B := Algebra.compHom B (algebraMap R D)
  let : IsScalarTower R D B := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Algebra.FinitePresentation R B := Algebra.FinitePresentation.trans R D B
  let a : A →ₐ[R] B :=
    (AlgHom.restrictScalars R gC).comp Algebra.TensorProduct.includeRight
  let d : D →ₐ[R] B := IsScalarTower.toAlgHom R D B
  let g : B →ₐ[R] Λ := AlgHom.restrictScalars R hB
  have hmapA : g.comp a = fA := calc
    g.comp a = (AlgHom.restrictScalars R (hB.comp gC)).comp
        Algebra.TensorProduct.includeRight := AlgHom.ext fun _ => rfl
    _ = (AlgHom.restrictScalars R fC).comp Algebra.TensorProduct.includeRight := by rw [hfact]
    _ = fA := hfRight
  have hmapD : g.comp d = fD := AlgHom.ext fun z => hB.commutes z
  have hDB (q : PrimeSpectrum B)
      (hp : Algebra.SmoothAt R D (q.asIdeal.comap (algebraMap D B))) :
      Algebra.SmoothAt D B q.asIdeal := by
    by_contra hnot
    have hsing : singularIdeal D B ≤ q.asIdeal :=
      (singularIdeal_le_iff_not_smoothAt D B q.asIdeal).mpr hnot
    have hmap : Ideal.map (algebraMap D B) (annihilatorDefectIdeal D (algebraMap R D π)) ≤
        q.asIdeal := hdefect.trans hsing
    exact annihilatorDefect_not_le_of_smoothAt π hR _ hp (Ideal.map_le_iff_le_comap.mp hmap)
  have hpnot (q : PrimeSpectrum B) (hq : ¬ Algebra.SmoothAt R B q.asIdeal) :
      ¬ Algebra.SmoothAt R D (q.asIdeal.comap (algebraMap D B)) := by
    intro hp
    let : (q.asIdeal.comap (algebraMap D B)).IsPrime := Ideal.IsPrime.comap _
    exact hq (smoothAt_comp q.asIdeal _ rfl hp (hDB q hp))
  refine ⟨B, instB, algDB, inferInstance, inferInstance, inferInstance, a, g, hmapA, hmapD,
    ?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, singularIdeal, PrimeSpectrum.mem_vanishingIdeal]
    intro q hq
    let : (q.asIdeal.comap (algebraMap D B)).IsPrime := Ideal.IsPrime.comap _
    rw [singularIdeal, PrimeSpectrum.mem_vanishingIdeal] at hy
    exact hy ⟨q.asIdeal.comap (algebraMap D B), inferInstance⟩ fun hp => hq (hDB q hp)
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, singularIdeal, PrimeSpectrum.mem_vanishingIdeal]
    intro q hq
    let : (q.asIdeal.comap (algebraMap D B)).IsPrime := Ideal.IsPrime.comap _
    rw [singularIdeal, PrimeSpectrum.mem_vanishingIdeal] at hy
    exact hy ⟨q.asIdeal.comap (algebraMap D B), inferInstance⟩ (hpnot q hq)

end Stacks.Smoothing

end
