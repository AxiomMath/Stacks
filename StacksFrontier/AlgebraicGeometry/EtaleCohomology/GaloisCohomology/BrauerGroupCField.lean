module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksCore.Algebra.BrauerGroup.AlgClosed
public import StacksCore.Algebra.BrauerGroup.Basic
public import StacksCore.Algebra.Split.DivisionRing
public import StacksCore.RingTheory.SkolemNoether
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.CFields

/-!
# The Brauer group of a \(C_1\) field is trivial

A finite central division algebra over a \(C_1\) field has degree one, so it is the field
itself; since every finite central simple algebra is a matrix algebra over such a division
algebra, every Brauer class is the class of a matrix algebra over the field, which is trivial.

## Main results

* `brauerGroup_eq_one_of_isCField` says that every Brauer class over a \(C_1\) field is the
  identity class.

## Implementation notes

The vanishing of the Brauer group is expressed multiplicatively: every element of
`BrauerGroup K` is equal to `1`. The degree-one step is where the \(C_1\) hypothesis enters.
For a division algebra `D` of degree `d` split by a finite Galois extension `E/K`, the reduced
norm is realised as the determinant of a matrix of linear forms in a `K`-basis of `D`; it is
Galois invariant by Skolem–Noether, hence descends to a homogeneous degree-`d` form over `K` in
`d ^ 2` variables. If `d > 1` then `d < d ^ 2`, so the \(C_1\) condition produces a nonzero
zero of that form, contradicting that every nonzero element of a division ring is a unit.

## References

* [Stacks Project, Tag 03RC](https://stacks.math.columbia.edu/tag/03RC)
-/

@[expose] public noncomputable section

universe u v w

open scoped TensorProduct


private noncomputable def matrixPoly {K D E : Type*} [Field K] [Field E] [DivisionRing D]
    [Algebra K D] [Algebra K E] {n d : ℕ} (b : Module.Basis (Fin n) K D)
    (f : D →ₐ[K] Matrix (Fin d) (Fin d) E) :
    Matrix (Fin d) (Fin d) (MvPolynomial (Fin n) E) :=
  fun i j => ∑ k : Fin n, MvPolynomial.X k * MvPolynomial.C (f (b k) i j)

private theorem matrixPoly_entry_homogeneous {K D E : Type*} [Field K] [Field E]
    [DivisionRing D] [Algebra K D] [Algebra K E] {n d : ℕ}
    (b : Module.Basis (Fin n) K D) (f : D →ₐ[K] Matrix (Fin d) (Fin d) E)
    (i j : Fin d) : (matrixPoly b f i j).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro k hk
  simpa using (MvPolynomial.isHomogeneous_X E k).mul
    (MvPolynomial.isHomogeneous_C (Fin n) (f (b k) i j))

private theorem matrixPoly_det_homogeneous {K D E : Type*} [Field K] [Field E]
    [DivisionRing D] [Algebra K D] [Algebra K E] {n d : ℕ}
    (b : Module.Basis (Fin n) K D) (f : D →ₐ[K] Matrix (Fin d) (Fin d) E) :
    (Matrix.det (matrixPoly b f)).IsHomogeneous d := by
  classical
  rw [Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum
  intro σ hσ
  apply MvPolynomial.IsHomogeneous.C_mul
  convert MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i : Fin d => matrixPoly b f (σ i) i) (fun _ => 1) ?_ using 1
  · simp
  · intro i hi
    simpa using matrixPoly_entry_homogeneous b f (σ i) i

private theorem matrixPoly_as_sum {K D E : Type*} [Field K] [Field E] [DivisionRing D]
    [Algebra K D] [Algebra K E] {n d : ℕ} (b : Module.Basis (Fin n) K D)
    (f : D →ₐ[K] Matrix (Fin d) (Fin d) E) :
    matrixPoly b f = ∑ k : Fin n, (MvPolynomial.X (R := E) k) •
      (RingHom.mapMatrix (MvPolynomial.C : E →+* MvPolynomial (Fin n) E) (f (b k))) := by
  ext i j
  simp only [matrixPoly, RingHom.mapMatrix_apply, Matrix.sum_apply, Matrix.smul_apply]
  rfl

/-- The `K`-algebra map `D → Mₙ(E)` induced by a splitting `E ⊗[K] D ≃ₐ[E] Mₙ(E)`. -/
private noncomputable def splitHom {K D E : Type*} [Field K] [Field E] [DivisionRing D]
    [Algebra K D] [Algebra K E] {d : ℕ} (e : E ⊗[K] D ≃ₐ[E] Matrix (Fin d) (Fin d) E) :
    D →ₐ[K] Matrix (Fin d) (Fin d) E :=
  (e.toAlgHom.restrictScalars K).comp Algebra.TensorProduct.includeRight

private theorem galois_fixed_det {K : Type u} {D : Type v} {Ω : Type (max u v)} [Field K]
    [DivisionRing D] [Algebra K D] [Module.Finite K D] [Algebra.IsCentral K D] [Field Ω]
    [Algebra K Ω]
    (E : IntermediateField K Ω) [IsGalois K E] [FiniteDimensional K E]
    (σ : Gal(E/K)) {d : ℕ} [NeZero d]
    (e : E ⊗[K] D ≃ₐ[E] Matrix (Fin d) (Fin d) E)
    (b : Module.Basis (Fin (Module.finrank K D)) K D) :
    MvPolynomial.map σ.toRingEquiv.toRingHom (Matrix.det (matrixPoly b (splitHom (K := K) e))) =
      Matrix.det (matrixPoly b (splitHom (K := K) e)) := by
  classical
  let fD := splitHom (K := K) e
  let matσ : Matrix (Fin d) (Fin d) E →ₐ[K] Matrix (Fin d) (Fin d) E := {
    toRingHom := RingHom.mapMatrix σ.toRingEquiv.toRingHom
    commutes' := by
      intro k
      simp [RingHom.mapMatrix_apply, Matrix.algebraMap_eq_diagonal, σ.commutes] }
  let gD := matσ.comp fD
  let hcomm : ∀ x : E, ∀ y : D, Commute ((algebraMap E (Matrix (Fin d) (Fin d) E)) x) (gD y) := by
    intro x y
    exact Algebra.commutes x (gD y)
  let g : E ⊗[K] D →ₐ[E] Matrix (Fin d) (Fin d) E :=
    Algebra.TensorProduct.lift (Algebra.ofId E _) gD hcomm
  let : IsSimpleRing (E ⊗[K] D) := IsSimpleRing.of_ringEquiv e.toRingEquiv.symm inferInstance
  obtain ⟨u, hu⟩ := skolemNoether E (Matrix (Fin d) (Fin d) E) (E ⊗[K] D)
    e.toAlgHom g
  have hconj (k : Fin (Module.finrank K D)) :
      gD (b k) = (u : Matrix (Fin d) (Fin d) E) * fD (b k) *
        ((u⁻¹ : (Matrix (Fin d) (Fin d) E)ˣ) : Matrix (Fin d) (Fin d) E) := by
    have h := hu (Algebra.TensorProduct.includeRight (b k))
    simpa [g, Algebra.TensorProduct.lift_tmul, gD, fD, splitHom] using h
  let uP : Matrix (Fin d) (Fin d) (MvPolynomial (Fin (Module.finrank K D)) E) :=
    RingHom.mapMatrix MvPolynomial.C (u : Matrix (Fin d) (Fin d) E)
  let vP : Matrix (Fin d) (Fin d) (MvPolynomial (Fin (Module.finrank K D)) E) :=
    RingHom.mapMatrix MvPolynomial.C (↑(u⁻¹) : Matrix (Fin d) (Fin d) E)
  have hpoly : matrixPoly b gD = uP * matrixPoly b fD * vP := by
    rw [matrixPoly_as_sum, matrixPoly_as_sum]
    calc
      (∑ k : Fin (Module.finrank K D), MvPolynomial.X k •
          RingHom.mapMatrix MvPolynomial.C (gD (b k))) =
          ∑ k : Fin (Module.finrank K D), MvPolynomial.X k •
            (uP * RingHom.mapMatrix MvPolynomial.C (fD (b k)) * vP) := by
        congr 1
        funext k
        simp [uP, vP, RingHom.mapMatrix_apply, hconj k]
        rfl
      _ = uP * (∑ k : Fin (Module.finrank K D), MvPolynomial.X k •
            RingHom.mapMatrix MvPolynomial.C (fD (b k))) * vP := by
        rw [Matrix.mul_sum (s := Finset.univ), Matrix.sum_mul (s := Finset.univ)]
        congr 1
        funext k
        rw [Matrix.mul_smul, Matrix.smul_mul]
  have huv : uP * vP = 1 := by
    simp [uP, vP, RingHom.mapMatrix_apply]
  have hdetuv : uP.det * vP.det = 1 := by
    calc
      uP.det * vP.det = (uP * vP).det := (Matrix.det_mul uP vP).symm
      _ = 1 := by rw [huv, Matrix.det_one]
  have hdet : (Matrix.det (matrixPoly b gD)) = Matrix.det (matrixPoly b fD) := by
    rw [hpoly, Matrix.det_mul, Matrix.det_mul]
    calc
      uP.det * (matrixPoly b fD).det * vP.det =
          (uP.det * vP.det) * (matrixPoly b fD).det := by ring
      _ = (matrixPoly b fD).det := by rw [hdetuv, one_mul]
  show MvPolynomial.map σ.toRingEquiv.toRingHom (Matrix.det (matrixPoly b fD)) =
    Matrix.det (matrixPoly b fD)
  rw [RingHom.map_det, show (RingHom.mapMatrix (MvPolynomial.map σ.toRingEquiv.toRingHom)
      (matrixPoly b fD)) = matrixPoly b gD by
        ext i j
        simp [matrixPoly, gD, matσ, fD, RingHom.mapMatrix_apply]]
  exact hdet

private theorem descendMvPolynomial {F E ι : Type*} [Field F] [Field E] [Algebra F E]
    [IsGalois F E] [FiniteDimensional F E] (p : MvPolynomial ι E)
    (hp : ∀ g : Gal(E/F), MvPolynomial.map g.toRingEquiv.toRingHom p = p) :
    ∃ q : MvPolynomial ι F, MvPolynomial.map (algebraMap F E) q = p := by
  classical
  have hfixed (m : ι →₀ ℕ) :
      MvPolynomial.coeff m p ∈ Set.range (algebraMap F E) :=
    (IsGalois.mem_range_algebraMap_iff_fixed (F := F) (E := E) _).2
      (fun g => by
        show g.toRingEquiv.toRingHom (MvPolynomial.coeff m p) = _
        simpa only [MvPolynomial.coeff_map] using
          congrArg (MvPolynomial.coeff m) (hp g))
  let c : (ι →₀ ℕ) → F := fun m => Classical.choose (hfixed m)
  have hc (m : ι →₀ ℕ) : algebraMap F E (c m) = MvPolynomial.coeff m p :=
    Classical.choose_spec (hfixed m)
  refine ⟨∑ m ∈ p.support, MvPolynomial.monomial m (c m), ?_⟩
  calc
    MvPolynomial.map (algebraMap F E) (∑ m ∈ p.support, MvPolynomial.monomial m (c m))
      = ∑ m ∈ p.support, MvPolynomial.monomial m (algebraMap F E (c m)) := by simp
    _ = ∑ m ∈ p.support, MvPolynomial.monomial m (MvPolynomial.coeff m p) := by
      simp_rw [hc]
    _ = p := MvPolynomial.support_sum_monomial_coeff p

private theorem cOne_degree_eq_one {K : Type u} {D : Type v} [Field K] [DivisionRing D]
    [Algebra K D] [Module.Finite K D] [Algebra.IsCentral K D]
    (hK : IsCField K 1) : Algebra.IsCentralSimple.degree K D = 1 := by
  classical
  let d := Algebra.IsCentralSimple.degree K D
  have hdpos : 0 < d := by simpa [d] using Algebra.IsCentralSimple.degree_pos K D
  by_contra hd
  have hdgt : 1 < d := by omega
  let Ω := ULift.{max u v} (AlgebraicClosure K)
  let down : Ω ≃+* AlgebraicClosure K := ULift.ringEquiv
  let downPoly : Polynomial Ω ≃+* Polynomial (AlgebraicClosure K) :=
    RingEquiv.ofBijective (Polynomial.mapRingHom down.toRingHom)
      ⟨Polynomial.map_injective _ down.injective,
        fun p => ⟨Polynomial.map down.symm.toRingHom p, by simp [Polynomial.map_map]⟩⟩
  have : IsAlgClosed Ω := IsAlgClosed.of_exists_root (k := Ω)
    (fun (p : Polynomial Ω) (hp : p.Monic) (hpi : Irreducible p) => by
      let q := downPoly p
      have hqmonic : q.Monic := by simpa [q, downPoly] using hp.map down.toRingHom
      have hqirr : Irreducible q := Irreducible.map downPoly hpi
      obtain ⟨a, ha⟩ := IsAlgClosed.exists_root q
        (ne_of_gt (Polynomial.degree_pos_of_irreducible hqirr))
      refine ⟨down.symm a, ?_⟩
      have hmap : Polynomial.map down.symm.toRingHom q = p := by
        apply downPoly.injective
        simp [q, downPoly, Polynomial.map_map]
      have hroot : Polynomial.eval (down.symm a) p = 0 := by
        calc
          Polynomial.eval (down.symm a) p =
              Polynomial.eval (down.symm a) (Polynomial.map down.symm.toRingHom q) := by rw [hmap]
          _ = Polynomial.eval₂ down.symm (down.symm a) q :=
              Polynomial.eval_map down.symm.toRingHom (down.symm a)
          _ = down.symm (Polynomial.eval a q) := Polynomial.eval₂_at_apply down.symm.toRingHom a
          _ = 0 := by rw [ha]; simp
      exact hroot)
  let eK : Ω ≃ₐ[K] AlgebraicClosure K := ULift.algEquiv (R := K) (A := AlgebraicClosure K)
  have : Algebra.IsAlgebraic K Ω :=
    Algebra.IsAlgebraic.of_injective (A := Ω) (B := AlgebraicClosure K) eK eK.injective
  obtain ⟨E, hEfin, hEg, hEsplit⟩ :=
    Algebra.IsCentralSimple.exists_finite_galois_split (k := K) (A := D) (k_bar := Ω)
  obtain ⟨m, hm, ⟨e⟩⟩ := hEsplit
  have hdimD : Module.finrank K D = d ^ 2 := by
    simpa [d] using (Algebra.IsCentralSimple.degree_sq_eq_finrank K D).symm
  have hdimM : Module.finrank K D = m ^ 2 := by
    have he := e.toLinearEquiv.finrank_eq
    rw [Module.finrank_baseChange] at he
    simpa [Module.finrank_matrix, pow_two] using he
  have hmd : m = d := by
    apply (pow_left_inj₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2 ≠ 0)).1
    exact hdimM.symm.trans hdimD
  subst m
  let : FiniteDimensional K E := hEfin
  let : IsGalois K E := hEg
  let : NeZero d := ⟨by omega⟩
  let b : Module.Basis (Fin (Module.finrank K D)) K D :=
    Module.finBasisOfFinrankEq K D rfl
  let fD := splitHom (K := K) e
  let pE : MvPolynomial (Fin (Module.finrank K D)) E := Matrix.det (matrixPoly b fD)
  have hpE : pE.IsHomogeneous d := matrixPoly_det_homogeneous b fD
  have hfixed : ∀ σ : Gal(E/K), MvPolynomial.map σ.toRingEquiv.toRingHom pE = pE := by
    intro σ
    simpa [pE, fD] using galois_fixed_det (K := K) (D := D) (Ω := Ω) E σ e b
  obtain ⟨q, hqmap⟩ := descendMvPolynomial (F := K) (E := E) pE hfixed
  have hqhom : q.IsHomogeneous d := by
    apply MvPolynomial.IsHomogeneous.of_map (RingHom.injective (algebraMap K E))
    rw [hqmap]
    exact hpE
  have hdlt : d < Module.finrank K D := by
    rw [hdimD]
    nlinarith
  have hcond : 0 < d ∧ d ^ 1 < Module.finrank K D := by simpa using ⟨hdpos, hdlt⟩
  obtain ⟨α, hα, hqzero⟩ := hK d (Module.finrank K D) hcond q hqhom
  let αE : Fin (Module.finrank K D) → E := fun i => algebraMap K E (α i)
  have hevalmap : MvPolynomial.eval αE pE = algebraMap K E (MvPolynomial.eval α q) := by
    rw [← hqmap]
    exact (MvPolynomial.map_eval (algebraMap K E) α q).symm
  have hevalzero : MvPolynomial.eval αE pE = 0 := by rw [hevalmap, hqzero, map_zero]
  let x : D := ∑ i, α i • b i
  let z : E ⊗[K] D := ∑ i, αE i • Algebra.TensorProduct.includeRight (b i)
  have hxLC : x = Finsupp.linearCombination K b (Finsupp.equivFunOnFinite.symm α) := by
    simp [x, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
  have hxrepr : b.repr x = Finsupp.equivFunOnFinite.symm α := by
    rw [hxLC]
    simp
  let inc : D →ₐ[K] E ⊗[K] D := Algebra.TensorProduct.includeRight
  have hterm (a : K) (y : D) :
      (algebraMap K E a : E) • (inc y : E ⊗[K] D) =
        inc ((a : K) • y) := by
    have hs : algebraMap E (E ⊗[K] D) (algebraMap K E a) =
        inc (algebraMap K D a) := by
      rw [AlgHom.commutes inc a]
      simp
    rw [Algebra.smul_def (R := E) (A := E ⊗[K] D)]
    rw [Algebra.smul_def (R := K) (A := D)]
    rw [hs, map_mul]
  have hz : z = inc x := by
    simp only [z, x, αE]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm (α i) (b i)
  have hevaldet : MvPolynomial.eval αE pE = (e z).det := by
    dsimp [pE]
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [matrixPoly, z, fD, splitHom, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X, Algebra.TensorProduct.includeRight_apply,
      Matrix.sum_apply, Matrix.smul_apply]
  have hx : x ≠ 0 := by
    intro hx0
    apply hα
    have hcoeff : Finsupp.equivFunOnFinite.symm α = 0 := by
      simpa [hxrepr] using congrArg b.repr hx0
    have h := congrArg Finsupp.equivFunOnFinite hcoeff
    funext i
    simpa using congrFun h i
  have hunitdet : IsUnit (e (inc x)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (IsUnit.map (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
        (isUnit_iff_ne_zero.mpr hx))
  apply hunitdet.ne_zero
  rw [← hz, ← hevaldet]
  exact hevalzero


/-- Every Brauer class over a C₁ field is trivial. -/
@[stacks 03RC, sga "4½ Arcata 3.2.2"]
theorem brauerGroup_eq_one_of_isCField (K : Type u) [Field K]
    (hK : IsCField K 1) (x : BrauerGroup K) : x = 1 := by
  induction x using BrauerGroup.induction with
  | h A =>
    have : IsArtinianRing A := IsArtinianRing.of_finite K A
    obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ :=
      IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
    have : Algebra.IsCentral K D := .of_matrix (h := .of_algEquiv K _ _ e)
    have hdim : Module.finrank K D = 1 := by
      rw [← Algebra.IsCentralSimple.degree_sq_eq_finrank K D, cOne_degree_eq_one hK, one_pow]
    have hbij : Function.Bijective (algebraMap K D) :=
      (Algebra.finrank_eq_one_iff_bijective_algebraMap (F := K) (E := D)).mp hdim
    let ed : K ≃ₐ[K] D := AlgEquiv.ofBijective (Algebra.ofId K D) hbij
    calc
      BrauerGroup.mk K A = BrauerGroup.mk K (Matrix (Fin n) (Fin n) D) :=
        BrauerGroup.mk_congr e
      _ = BrauerGroup.mk K (Matrix (Fin n) (Fin n) K) :=
        BrauerGroup.mk_congr (AlgEquiv.mapMatrix ed.symm)
      _ = 1 := BrauerGroup.mk_matrix_eq_one (k := K) (Fin n)

