module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.GRing.Defs
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.Henselian.Pair.Henselization
public import StacksFrontier.RingTheory.Rig.AdicCompletionMap
public import StacksFrontier.RingTheory.Rig.Henselization
public import StacksFrontier.RingTheory.Smoothing.ApproximationHenselianGRing
public import StacksFrontier.RingTheory.Smoothing.ApproximationHenselianPair

/-!
# Approximating a map of adic completions by a map into an étale neighbourhood

Let `A` be a Noetherian G-ring, let `I ⊆ A` be an ideal and let `B` and `C` be finite type
`A`-algebras. Given an `A`-algebra map `ψ : B^ → C^` between the `I`-adic completions and an
integer `N ≥ 1`, there is an étale `C`-algebra `C'` inducing an isomorphism `C / IC ≅ C' / IC'`
and an `A`-algebra map `φ : B → C'` which agrees with `ψ` modulo `I ^ N`.

The proof follows the source. The henselization `C^h` of the pair `(C, IC)` is a filtered
colimit of such étale `C`-algebras and has the same completion as `C` (Stacks 0A02, 0AGU,
0AGV), so it is enough to produce an `A`-algebra map `B → C^h` agreeing with `ψ` modulo
`I ^ N`; writing `B = A[x₁, …, x_n] / (f₁, …, f_m)` turns `ψ` into a solution of the system
`f₁ = ⋯ = f_m = 0` in `C^`, and the approximation lemma Stacks 0AH5 moves that solution into
`C^h`. Finally Stacks 0AKJ factors the resulting map `B → C^h` through a single étale stage
with the right closed fibre.

## Main results

* `Stacks.Smoothing.exists_etale_neighbourhood_algHom_approximation`: **Stacks 0AK4**, the étale
  neighbourhood and the approximating algebra map.

## Implementation notes

*Nothing is granted.* Stacks 0AH5 itself is available, as
`Stacks.Smoothing.exists_solution_of_henselianPair` in
`StacksFrontier.RingTheory.Smoothing.ApproximationHenselianPair`, and is used here rather than
assumed. It does not, however, carry the source's hypothesis that the ring is a Noetherian
G-ring: in its place it carries `Stacks.Smoothing.IsIndSmoothAdicCompletion A I`, the conclusion
of Popescu's Theorem (Stacks 07GC) for the map `A → A^∧`. Popescu's Theorem is itself proved in
this library, as `Stacks.Smoothing.indSmooth_of_isRegularRingMap`, so the bridge from a G-ring
to that hypothesis is proved as well, as
`Stacks.Smoothing.isIndSmoothAdicCompletion_of_isGRing`.

The bridge is used exactly once, on the henselization `C^h` of `(C, IC)`, and every step of it
is in the library: `C^h` is a G-ring by Stacks 0AH3 (`isGRing_henselization`), its completion
map is therefore regular by Stacks 0AH2 (`isRegularRingHom_algebraMap_adicCompletion`) — the
source's own reduction of its hypothesis to regularity — and Popescu's Theorem turns that
regularity into the required ind-smooth presentation. So this theorem carries no hypothesis
beyond the source's own.

*How agreement modulo `I ^ N` is expressed.* Rather than choosing an inverse of the canonical
isomorphism `C^ ≅ (C')^`, the congruence is stated inside `C' / (IC) ^ N`: the completed map is
evaluated in `C / (IC) ^ N` and then transported along the canonical quotient map. Since
`(IC) ^ N = I ^ N C`, this is the source's congruence modulo `I ^ N`. Bijectivity of the
quotient map for *every* power is also returned; it is what identifies the two completions, and
the case `n = 1` is the isomorphism `C / IC ≅ C' / IC'` of the source.

## References

* [Stacks Project, Tag 0AK4](https://stacks.math.columbia.edu/tag/0AK4)
* [Stacks Project, Tag 0AH5](https://stacks.math.columbia.edu/tag/0AH5)
* [Stacks Project, Tag 0AKJ](https://stacks.math.columbia.edu/tag/0AKJ)
* [Stacks Project, Tag 07GC](https://stacks.math.columbia.edu/tag/07GC)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Smoothing

universe u v w

/-- An element of `R^` congruent to `c` modulo `I ^ N` evaluates to the class of `c` in
`R / I ^ N`. -/
private theorem _root_.AdicCompletion.evalₐ_eq_mk_of_sub_mem {R : Type*} [CommRing R] (I : Ideal R)
    (N : ℕ) {x : AdicCompletion I R} {c : R}
    (h : x - algebraMap R (AdicCompletion I R) c ∈
      (I ^ N).map (algebraMap R (AdicCompletion I R))) :
    AdicCompletion.evalₐ I N x = Ideal.Quotient.mk (I ^ N) c := by
  have hker : (I ^ N).map (algebraMap R (AdicCompletion I R)) ≤
      RingHom.ker (AdicCompletion.evalₐ I N).toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro z hz
    show AdicCompletion.evalₐ I N (AdicCompletion.of I R z) = 0
    rw [AdicCompletion.evalₐ_of]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
  have hdiff := RingHom.mem_ker.mp (hker h)
  simp only [map_sub] at hdiff
  exact sub_eq_zero.mp hdiff

/-- A solution `c` of the relations of a presentation `q` of `B` defines an `A`-algebra map
`φ : B → H` with `φ ∘ q = aeval c`. -/
private theorem exists_algHom_comp_eq_aeval {A B H : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [CommRing H] [Algebra A H] {n : ℕ} (q : MvPolynomial (Fin n) A →ₐ[A] B)
    (hq : Function.Surjective q) (c : Fin n → H)
    (hc : ∀ p ∈ RingHom.ker q.toRingHom, MvPolynomial.aeval c p = 0) :
    ∃ φ : B →ₐ[A] H, φ.comp q = MvPolynomial.aeval c := by
  refine ⟨(Ideal.Quotient.liftₐ _ (MvPolynomial.aeval c) hc).comp
    (Ideal.quotientKerAlgEquivOfSurjective hq).symm.toAlgHom, AlgHom.ext fun p => ?_⟩
  show Ideal.Quotient.liftₐ _ (MvPolynomial.aeval c) hc
    ((Ideal.quotientKerAlgEquivOfSurjective hq).symm (q p)) = MvPolynomial.aeval c p
  rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply hq p]
  rfl

/-- If `q r = 0` for a presentation `q` of `B`, then `r`, mapped to `H`, vanishes at the images
of the generators under any `A`-algebra map `θ : B → D`. -/
private theorem aeval_map_eq_zero_of_apply_eq_zero {A B H D : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [CommRing H] [Algebra A H] [CommRing D] [Algebra H D] [Algebra A D]
    [IsScalarTower A H D] {n : ℕ} (q : MvPolynomial (Fin n) A →ₐ[A] B) (θ : B →ₐ[A] D)
    {r : MvPolynomial (Fin n) A} (hr : q r = 0) :
    MvPolynomial.aeval (fun i => θ (q (MvPolynomial.X i)))
      (MvPolynomial.map (algebraMap A H) r) = 0 := by
  have h : MvPolynomial.aeval (fun i => θ (q (MvPolynomial.X i))) = θ.comp q :=
    MvPolynomial.algHom_ext fun i => by simp
  rw [MvPolynomial.aeval_map_algebraMap, h, AlgHom.comp_apply, hr, map_zero]

/-- **Stacks 0AH5 for algebra maps.** Over a henselian pair `(H, J)` with `H` a Noetherian
G-ring, an `A`-algebra map from a finitely presented `A`-algebra `B` to the `J`-adic completion
of `H` agrees modulo `J ^ N` with an `A`-algebra map `B → H`. -/
private theorem exists_algHom_evalₐ_comp_eq_of_isGRing {A B H : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.FinitePresentation A B] [CommRing H] [Algebra A H] {J : Ideal H}
    (hG : IsGRing H) (hpair : HenselianPair H J) (θ : B →ₐ[A] AdicCompletion J H) {N : ℕ}
    (hN : N ≠ 0) :
    ∃ φ : B →ₐ[A] H, ((AdicCompletion.evalₐ J N).restrictScalars A).comp θ =
      (Ideal.Quotient.mkₐ A (J ^ N)).comp φ := by
  classical
  -- Present `B` by generators and relations over `A`.
  obtain ⟨n, q, hq, hqker⟩ := Algebra.FinitePresentation.out (R := A) (A := B)
  obtain ⟨m, rels, hrels'⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hqker
  have hrels : Ideal.span (Set.range rels) = RingHom.ker q.toRingHom := hrels'
  have hK : ∀ j, rels j ∈ RingHom.ker q.toRingHom := by
    intro j
    rw [← hrels]
    exact Ideal.subset_span ⟨j, rfl⟩
  -- `θ` is a solution of the relations in the completion of `H`.
  obtain ⟨c, happrox, hsol⟩ := exists_solution_of_henselianPair_of_isGRing hG hpair
    (fun j => MvPolynomial.map (algebraMap A H) (rels j)) (fun i => θ (q (MvPolynomial.X i)))
    (fun j => aeval_map_eq_zero_of_apply_eq_zero q θ (RingHom.mem_ker.mp (hK j))) hN
  have hKle : RingHom.ker q.toRingHom ≤ RingHom.ker (MvPolynomial.aeval (R := A) c).toRingHom := by
    rw [← hrels, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    simpa [MvPolynomial.aeval_def, MvPolynomial.eval₂_map] using hsol j
  obtain ⟨φ, hφ⟩ := exists_algHom_comp_eq_aeval q hq c fun p hp => RingHom.mem_ker.mp (hKle hp)
  refine ⟨φ, (AlgHom.cancel_right hq).mp (MvPolynomial.algHom_ext fun i => ?_)⟩
  have hφgen := DFunLike.congr_fun hφ (MvPolynomial.X i)
  change φ (q (MvPolynomial.X i)) = MvPolynomial.aeval c (MvPolynomial.X i) at hφgen
  show AdicCompletion.evalₐ J N (θ (q (MvPolynomial.X i))) =
    Ideal.Quotient.mk (J ^ N) (φ (q (MvPolynomial.X i)))
  rw [hφgen]
  simpa using AdicCompletion.evalₐ_eq_mk_of_sub_mem J N (happrox i)

/-- If `f` induces an injection `R / I ^ n → S / (I ^ n) S`, it induces an injection
`R / I ^ n → S / (I S) ^ n`. -/
private theorem quotientMap_map_pow_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (I : Ideal R) (n : ℕ)
    (h : Function.Injective (Ideal.quotientMap ((I ^ n).map f) f Ideal.le_comap_map))
    (hle : I ^ n ≤ ((I.map f) ^ n).comap f) :
    Function.Injective (Ideal.quotientMap ((I.map f) ^ n) f hle) := by
  apply Ideal.quotientMap_injective'
  intro z hz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply h
  simpa only [Ideal.quotientMap_mk, map_zero] using
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.map_pow f I n ▸ hz : f z ∈ (I ^ n).map f)

/-- **Stacks 0AK4.** Let `A` be a Noetherian G-ring, `I ⊆ A` an ideal and `B`, `C` finite type
`A`-algebras. Every `A`-algebra map `ψ` between the `I`-adic completions of `B` and `C` is
approximated, to every positive order `N`, by an `A`-algebra map `φ : B → C'` into an étale
`C`-algebra `C'` whose closed fibre agrees with that of `C`. -/
@[stacks 0AK4 "the full conclusion with NO carried hypotheses, for every `N ≥ 1`: an étale \
`C`-algebra `C'` inducing an isomorphism `C / IC ≅ C' / IC'` (indeed `C / (IC)^n ≅ C' / (IC)^n \
C'` for every `n`), and an `A`-algebra map `B → C'` agreeing modulo `I ^ N` with the given map \
of `I`-adic completions. Stacks 0AH5 is used, not assumed, and the \
`IsIndSmoothAdicCompletion` hypothesis it carries in place of the source's G-ring is \
discharged by Popescu's Theorem 07GC (`indSmooth_of_isRegularRingMap`) through \
`isIndSmoothAdicCompletion_of_isGRing`, applied once to the henselization of (C, IC), which is \
a G-ring by 0AH3 and whose completion map is regular by 0AH2. Stacks \
0AKJ supplies the single étale stage."]
public theorem exists_etale_neighbourhood_algHom_approximation
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] (hA : IsGRing A)
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (I : Ideal A)
    (ψ : AdicCompletion (I.map (algebraMap A B)) B →ₐ[A]
      AdicCompletion (I.map (algebraMap A C)) C)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ (C' : Type (max u v w)) (_ : CommRing C') (_ : Algebra C C')
      (_ : Algebra A C') (_ : IsScalarTower A C C') (_ : Algebra.Etale C C')
      (φ : B →ₐ[A] C'),
      (∀ n : ℕ, Function.Bijective
          (Ideal.quotientMap (((I.map (algebraMap A C)) ^ n).map (algebraMap C C'))
            (algebraMap C C') Ideal.le_comap_map)) ∧
      Function.Bijective
          (Ideal.quotientMap ((I.map (algebraMap A C)).map (algebraMap C C'))
            (algebraMap C C') Ideal.le_comap_map) ∧
      ∀ b : B,
        Ideal.quotientMap (((I.map (algebraMap A C)) ^ N).map (algebraMap C C'))
            (algebraMap C C') Ideal.le_comap_map
            (AdicCompletion.evalₐ (I.map (algebraMap A C)) N
              (ψ (algebraMap B (AdicCompletion (I.map (algebraMap A B)) B) b))) =
          Ideal.Quotient.mk (((I.map (algebraMap A C)) ^ N).map (algebraMap C C')) (φ b) := by
  classical
  let : IsNoetherianRing A := hA.1
  let : Algebra.EssFiniteType A C := inferInstance
  have hGC : IsGRing C := isGRing_of_essFiniteType hA
  let : IsNoetherianRing C := hGC.1
  let J : Ideal C := I.map (algebraMap A C)
  -- The henselization `C^h` of the pair `(C, IC)` (Stacks 0A02).
  obtain ⟨H₀, hH₀, ι, hpair₀, hι₀⟩ := exists_henselization.{w, w} C J
  let : CommRing H₀ := hH₀
  let : Algebra C H₀ := ι.toAlgebra
  let : Algebra A H₀ := (ι.comp (algebraMap A C)).toAlgebra
  let : IsScalarTower A C H₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hιeq : algebraMap C H₀ = ι := rfl
  let JH : Ideal H₀ := J.map (algebraMap C H₀)
  have hpair : HenselianPair H₀ JH := by simpa [JH, hιeq] using hpair₀
  have hι : ∀ (T : Type w) (_ : CommRing T) (K : Ideal T), HenselianPair T K →
      ∀ f : C →+* T, J ≤ K.comap f →
        ∃! g : H₀ →+* T, g.comp (algebraMap C H₀) = f ∧ JH ≤ K.comap g :=
    fun T hT K hTpair f hf => by simpa [hιeq, JH] using hι₀ T hT K hTpair f hf
  -- The completion of `C^h` receives the completion of `C` (Stacks 0AGV).
  let D := AdicCompletion JH H₀
  let : Algebra C D := inferInstance
  let : Algebra A D := inferInstance
  let : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcompletion := henselization_isNoetherian_and_completion_equiv C J H₀ hpair hι
  let uRing := adicCompletionMap (algebraMap C H₀) J JH (by rfl)
  let uC : AdicCompletion J C →ₐ[C] D :=
    { toRingHom := uRing
      commutes' :=
        RingHom.congr_fun (adicCompletionMap_comp_algebraMap (algebraMap C H₀) J JH (by rfl)) }
  let uA := uC.restrictScalars A
  let θ : B →ₐ[A] D := uA.comp (ψ.comp (IsScalarTower.toAlgHom A B
    (AdicCompletion (I.map (algebraMap A B)) B)))
  let : IsNoetherianRing H₀ := hcompletion.2.1
  have hGH₀ : IsGRing H₀ := isGRing_henselization hGC J H₀ hpair hι
  let : Algebra.FinitePresentation A B :=
    (Algebra.FinitePresentation.of_finiteType (R := A) (A := B)).mp inferInstance
  -- Approximate it by a solution in `C^h` (Stacks 0AH5), whose `IsIndSmoothAdicCompletion`
  -- hypothesis is supplied by Popescu's Theorem 07GC from 0AH3 and 0AH2.
  obtain ⟨φH₀, hquotB⟩ :=
    exists_algHom_evalₐ_comp_eq_of_isGRing hGH₀ hpair θ (N := N) (by omega)
  -- Factor `B → C^h` through a single étale stage (Stacks 0AKJ).
  let : CommRing (henselization C J : Type w) := CommAlgCat.instCommRingObjForgetAlgHomCarrier
  let : Algebra C (henselization C J : Type w) := CommAlgCat.instAlgebraObjForgetAlgHomCarrier
  let : Algebra A (henselization C J : Type w) :=
    ((algebraMap C (henselization C J : Type w)).comp (algebraMap A C)).toAlgebra
  let : IsScalarTower A C (henselization C J : Type w) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e : (henselization C J : Type w) ≃ₐ[C] H₀ :=
    (nonempty_algEquiv_henselization (R := C) (I := J) H₀ hpair hι).some
  let φH : B →ₐ[A] (henselization C J : Type w) :=
    e.symm.restrictScalars A |>.toAlgHom.comp φH₀
  obtain ⟨Cp, hCpRing, hCpC, hCpA, hCpTower, hEtale, φ, k, hclosed, hfactor⟩ :=
    Rig.exists_etale_factorization_algHom_henselization A B C I φH
  let k0 : Cp →ₐ[C] H₀ := e.toAlgHom.comp k
  have hfactor0 : (k0.restrictScalars A).comp φ = φH₀ := by
    have h := congrArg (fun f : B →ₐ[A] (henselization C J : Type w) =>
      (e.restrictScalars A).toAlgHom.comp f) hfactor
    apply AlgHom.ext
    intro b
    show e (k (φ b)) = φH₀ b
    have hb := congrArg (fun f : B →ₐ[A] H₀ => f b) h
    simpa [φH] using hb
  let : CommRing Cp := hCpRing
  let : Algebra C Cp := hCpC
  let : Algebra A Cp := hCpA
  let : IsScalarTower A C Cp := hCpTower
  let JpN : Ideal Cp := (J ^ N).map (algebraMap C Cp)
  have hleι : J ^ N ≤ (JH ^ N).comap ι :=
    Ideal.map_le_iff_le_comap.mp (Ideal.map_pow ι J N).le
  have hleJpN : JpN ≤ (JH ^ N).comap k0.toRingHom := by
    apply (Ideal.map_le_iff_le_comap (f := k0.toRingHom)).mp
    have hkcomp : k0.toRingHom.comp (algebraMap C Cp) = algebraMap C H₀ :=
      RingHom.ext k0.commutes
    show (((J ^ N).map (algebraMap C Cp)).map k0.toRingHom) ≤ JH ^ N
    rw [Ideal.map_map, hkcomp, Ideal.map_pow]
  let qH : Cp ⧸ JpN →ₐ[A] H₀ ⧸ JH ^ N :=
    Ideal.quotientMapₐ (JH ^ N) (k0.restrictScalars A) hleJpN
  have hIndCp : (CommAlgCat.etale.{max u v w} C).ind (CommAlgCat.of C Cp) :=
    (CommAlgCat.etale C).le_ind _ hEtale
  have hpowCp := flat_and_bijective_quotientMap_pow_of_ind_etale C J Cp hIndCp hclosed
  have hpowH := flat_henselization_and_bijective_quotientMap C J H₀ hpair hι
  have hquotcomp :
      (Ideal.quotientMap (JH ^ N) k0.toRingHom hleJpN).comp
        (Ideal.quotientMap JpN (algebraMap C Cp) Ideal.le_comap_map) =
        Ideal.quotientMap (JH ^ N) ι hleι := by
    ext x
    simp [RingHom.comp_apply, hιeq]
  have hqHinj : Function.Injective qH := by
    have hqH' : Function.Injective (Ideal.quotientMap (JH ^ N) ι hleι) :=
      quotientMap_map_pow_injective (algebraMap C H₀) J N (hpowH.2 N).injective hleι
    refine Function.Injective.of_comp_right ?_ (hpowCp.2 N).surjective
    show Function.Injective ((Ideal.quotientMap (JH ^ N) k0.toRingHom hleJpN).comp
      (Ideal.quotientMap JpN (algebraMap C Cp) Ideal.le_comap_map))
    rw [hquotcomp]
    exact hqH'
  refine ⟨Cp, hCpRing, hCpC, hCpA, hCpTower, hEtale, φ, hpowCp.2, hclosed, ?_⟩
  intro b
  apply hqHinj
  calc
    qH ((Ideal.quotientMap JpN (algebraMap C Cp) Ideal.le_comap_map)
        (AdicCompletion.evalₐ J N (ψ (algebraMap B _ b)))) =
      (Ideal.quotientMap (JH ^ N) ι hleι)
        (AdicCompletion.evalₐ J N (ψ (algebraMap B _ b))) := by
          show (((Ideal.quotientMap (JH ^ N) k0.toRingHom hleJpN).comp
            (Ideal.quotientMap JpN (algebraMap C Cp) Ideal.le_comap_map)) _) = _
          rw [hquotcomp]
    _ = Ideal.Quotient.mk (JH ^ N) (k0 (φ b)) := by
      have happroxB := DFunLike.congr_fun hquotB b
      change AdicCompletion.evalₐ JH N (uRing (ψ (algebraMap B _ b))) =
        Ideal.Quotient.mk (JH ^ N) (φH₀ b) at happroxB
      rw [adicCompletionMap_evalₐ (algebraMap C H₀) J JH (by rfl) N (ψ (algebraMap B _ b))]
        at happroxB
      simp only [hιeq] at happroxB
      rwa [← DFunLike.congr_fun hfactor0 b] at happroxB

end Stacks.Smoothing

end
