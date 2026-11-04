module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute

/-!
# An affine-space bundle over a quasi-affine scheme

A quasi-affine scheme `X` is a quasi-compact open of the spectrum of its ring `A` of global
sections, so finitely many standard opens `D(f_1), …, D(f_n)` cover it. The affine scheme

`T = Spec (A[x_1, …, x_n] / (f_1 x_1 + ⋯ + f_n x_n - 1))`

maps to `Spec A` through `X`, and after base change along any morphism `X' → X` with `X'`
affine it becomes affine `n`-space over `X'`: the coefficients `f_i` generate the unit ideal
in `Γ(X', 𝒪_{X'})`, and a choice `∑ f_i a_i = 1` of a partition of unity turns the relation
`∑ f_i x_i = 1` into a change of coordinates.

In particular every quasi-affine scheme is covered by an affine scheme through a morphism
whose affine base changes are all affine spaces of one fixed dimension.

## Main results

* `AlgebraicGeometry.exists_affine_pullback_iso_affineSpace`: a quasi-affine scheme admits a
  morphism from an affine scheme whose base change along every affine scheme over it is affine
  `n`-space over that scheme, for one fixed `n`.

## Implementation notes

The isomorphism with affine space is stated in the category of schemes over the affine base, so
that it includes compatibility with the two structure morphisms. Mathlib indexes affine space by
an arbitrary type, so affine `n`-space is affine space indexed by `ULift (Fin n)`.

The algebraic heart is `hyperplanePolynomialEquiv`, an explicit isomorphism between a polynomial
ring in `n` variables and the quotient of a polynomial ring in `n + 1` variables by one linear
relation whose coefficients generate the unit ideal; the extra variable is indexed by `none` and
the original ones by `some i`.

## References

* [Stacks Project, Tag 0F82](https://stacks.math.columbia.edu/tag/0F82)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace AlgebraicGeometry

/-- In the quotient of a polynomial ring by the relation `∑ f i * X (some i) = 1`, the images of
the variables `X (some i)` are coefficients of a representation of `1` by the `f i`. -/
private lemma quotient_hyperplane_eq_one {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] (f : ι → R) :
    ∑ i, algebraMap R (MvPolynomial (Option ι) R ⧸
      Ideal.span ({∑ i, MvPolynomial.C (f i) * MvPolynomial.X (some i) - 1} :
        Set (MvPolynomial (Option ι) R))) (f i) *
        Ideal.Quotient.mk _ (MvPolynomial.X (some i)) = 1 := by
  classical
  let I : Ideal (MvPolynomial (Option ι) R) :=
    Ideal.span {∑ i, MvPolynomial.C (f i) * MvPolynomial.X (some i) - 1}
  have hrel : Ideal.Quotient.mk I
      (∑ i, MvPolynomial.C (f i) * MvPolynomial.X (some i) - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  rw [map_sub, map_one, sub_eq_zero] at hrel
  change ∑ i, algebraMap R (MvPolynomial (Option ι) R ⧸ I) (f i) *
    Ideal.Quotient.mk I (MvPolynomial.X (some i)) = 1
  simpa only [map_sum, map_mul, MvPolynomial.C_eq_algebraMap,
    Ideal.Quotient.mk_algebraMap] using hrel

/-- If `∑ f i * a i = 1` in `R`, then the quotient of the polynomial ring on `Option ι` by the
single relation `∑ f i * X (some i) = 1` is a polynomial ring on `ι`.

The isomorphism sends `X i` to `C (a i) * X none + X (some i)`; its inverse sends `X none` to
`-1 + ∑ C (f i) * X i` and `X (some i)` to `X i + C (a i) - C (a i) * ∑ C (f j) * X j`. -/
private noncomputable def hyperplanePolynomialEquiv {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] (f a : ι → R)
    (h : ∑ i, f i * a i = 1) :
    MvPolynomial ι R ≃ₐ[R]
      (MvPolynomial (Option ι) R ⧸
        Ideal.span ({∑ i, MvPolynomial.C (f i) * MvPolynomial.X (some i) - 1} :
          Set (MvPolynomial (Option ι) R))) := by
  classical
  let rel : MvPolynomial (Option ι) R :=
    ∑ i, MvPolynomial.C (f i) * MvPolynomial.X (some i) - 1
  let I : Ideal (MvPolynomial (Option ι) R) := Ideal.span {rel}
  let s : MvPolynomial ι R := ∑ i, MvPolynomial.C (f i) * MvPolynomial.X i
  have hmapsum {S : Type _} [CommRing S] (g : R →+* S) : ∑ i, g (f i) * g (a i) = 1 := by
    simpa using congrArg g h
  have hcoef : ∑ i, MvPolynomial.C (f i) * MvPolynomial.C (a i) =
      (1 : MvPolynomial ι R) :=
    hmapsum (MvPolynomial.C : R →+* MvPolynomial ι R)
  have hrelcalc : ∑ i, MvPolynomial.C (f i) *
      (MvPolynomial.X i + MvPolynomial.C (a i) - MvPolynomial.C (a i) * s) =
        s + (∑ i, MvPolynomial.C (f i) * MvPolynomial.C (a i)) -
          (∑ i, MvPolynomial.C (f i) * MvPolynomial.C (a i)) * s := by
    calc
      _ = ∑ i, (MvPolynomial.C (f i) * MvPolynomial.X i +
          MvPolynomial.C (f i) * MvPolynomial.C (a i) -
          (MvPolynomial.C (f i) * MvPolynomial.C (a i)) * s) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [← Finset.sum_mul]
  let φ : MvPolynomial ι R →ₐ[R]
      (MvPolynomial (Option ι) R ⧸ I) :=
    MvPolynomial.aeval fun i : ι =>
      Ideal.Quotient.mk I
        (MvPolynomial.C (a i) * MvPolynomial.X none + MvPolynomial.X (some i))
  let ψ₀ : MvPolynomial (Option ι) R →ₐ[R] MvPolynomial ι R :=
    MvPolynomial.aeval fun j : Option ι => match j with
      | none => -1 + s
      | some i => MvPolynomial.X i + MvPolynomial.C (a i) -
          MvPolynomial.C (a i) * s
  have hrel : ψ₀ rel = 0 := by
    simp [ψ₀, rel, s, hrelcalc, hcoef]
  let ψ : (MvPolynomial (Option ι) R ⧸ I) →ₐ[R] MvPolynomial ι R :=
    Ideal.Quotient.liftₐ I ψ₀ fun _ hp =>
      (show I ≤ RingHom.ker ψ₀.toRingHom from
        Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hrel)) hp
  have hψφ : ψ.comp φ = AlgHom.id R (MvPolynomial ι R) := by
    apply MvPolynomial.algHom_ext
    intro i
    change ψ (φ (MvPolynomial.X i)) = MvPolynomial.X i
    rw [show φ (MvPolynomial.X i) = Ideal.Quotient.mk I
        (MvPolynomial.C (a i) * MvPolynomial.X none + MvPolynomial.X (some i)) by simp [φ]]
    simp only [ψ]
    change ψ₀ (MvPolynomial.C (a i) * MvPolynomial.X none +
      MvPolynomial.X (some i)) = MvPolynomial.X i
    simp [ψ₀, s]
    ring
  have hmkC (r : R) : Ideal.Quotient.mk I (MvPolynomial.C r) =
      algebraMap R (MvPolynomial (Option ι) R ⧸ I) r := by
    change Ideal.Quotient.mk I
      (algebraMap R (MvPolynomial (Option ι) R) r) = _
    rw [Ideal.Quotient.mk_algebraMap]
  have hcoefQ : ∑ i,
      (algebraMap R (MvPolynomial (Option ι) R ⧸ I)) (f i) *
        (algebraMap R (MvPolynomial (Option ι) R ⧸ I)) (a i) = 1 :=
    hmapsum (algebraMap R (MvPolynomial (Option ι) R ⧸ I))
  have hsumXQ : ∑ i,
      (algebraMap R (MvPolynomial (Option ι) R ⧸ I)) (f i) *
        Ideal.Quotient.mk I (MvPolynomial.X (some i)) = 1 :=
    quotient_hyperplane_eq_one f
  have hterm : ∀ i : ι,
      algebraMap R (MvPolynomial (Option ι) R ⧸ I) (f i) *
          Ideal.Quotient.mk I
            (MvPolynomial.C (a i) * MvPolynomial.X none + MvPolynomial.X (some i)) =
        algebraMap R (MvPolynomial (Option ι) R ⧸ I) (f i) *
            algebraMap R (MvPolynomial (Option ι) R ⧸ I) (a i) *
            Ideal.Quotient.mk I (MvPolynomial.X none) +
          algebraMap R (MvPolynomial (Option ι) R ⧸ I) (f i) *
            Ideal.Quotient.mk I (MvPolynomial.X (some i)) := by
    intro i
    rw [map_add, map_mul, hmkC]
    ring
  have hφs : φ s = ∑ i, algebraMap R (MvPolynomial (Option ι) R ⧸ I) (f i) *
      Ideal.Quotient.mk I
        (MvPolynomial.C (a i) * MvPolynomial.X none + MvPolynomial.X (some i)) := by
    simp only [s, φ, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  have hsφ : φ s = Ideal.Quotient.mk I (MvPolynomial.X none) + 1 := by
    rw [hφs, Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_add_distrib,
      ← Finset.sum_mul, hcoefQ, quotient_hyperplane_eq_one f, one_mul]
  have hh : φ.comp ψ₀ = Ideal.Quotient.mkₐ R I := by
    apply MvPolynomial.algHom_ext
    intro j
    change φ (ψ₀ (MvPolynomial.X j)) =
      (Ideal.Quotient.mkₐ R I) (MvPolynomial.X j)
    simp only [ψ₀, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    cases j with
    | none =>
        change φ (-1 + s) = Ideal.Quotient.mk I (MvPolynomial.X none)
        rw [map_add, map_neg, map_one, hsφ]
        ring
    | some i =>
        change φ (MvPolynomial.X i + MvPolynomial.C (a i) -
          MvPolynomial.C (a i) * s) = Ideal.Quotient.mk I (MvPolynomial.X (some i))
        rw [map_sub, map_add, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
        rw [map_add, map_mul, hmkC, hsφ]
        ring
  have hφψ : φ.comp ψ = AlgHom.id R (MvPolynomial (Option ι) R ⧸ I) := by
    apply AlgHom.ext
    intro q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    change φ (ψ (Ideal.Quotient.mk I p)) = Ideal.Quotient.mk I p
    simp only [ψ]
    exact (AlgHom.ext_iff.mp hh) p
  exact AlgEquiv.ofAlgHom φ ψ hφψ hψφ

/-- Base change of `hyperplanePolynomialEquiv`: if the images of the `f i` in a base ring `B`
admit coefficients `a i` with `∑ f i * a i = 1`, then the base change to `B` of the quotient by
the relation `∑ C (f i) * X (some i) = 1` is a polynomial ring over `B`. -/
private noncomputable def baseChangeHyperplaneEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Fintype ι]
    (f : ι → A) (a : ι → B)
    (h : ∑ i, algebraMap A B (f i) * a i = 1) :
    B ⊗[A] (MvPolynomial (Option ι) A ⧸
      Ideal.span ({∑ i, MvPolynomial.C (f i) * MvPolynomial.X (some i) - 1} :
        Set (MvPolynomial (Option ι) A))) ≃ₐ[B] MvPolynomial ι B := by
  classical
  let relA : MvPolynomial (Option ι) A :=
    ∑ i, MvPolynomial.C (f i) * MvPolynomial.X (some i) - 1
  let relB : MvPolynomial (Option ι) B :=
    ∑ i, MvPolynomial.C (algebraMap A B (f i)) * MvPolynomial.X (some i) - 1
  let J : Ideal (MvPolynomial (Option ι) A) := Ideal.span {relA}
  let K : Ideal (MvPolynomial (Option ι) B) := Ideal.span {relB}
  let e := MvPolynomial.scalarRTensorAlgEquiv (R := A) (N := B) (σ := Option ι)
  have hJ : K = (J.map (Algebra.TensorProduct.includeRight (A := B)
      (R := A))).map (e : B ⊗[A] MvPolynomial (Option ι) A →+* MvPolynomial (Option ι) B) := by
    have hmap : e (1 ⊗ₜ[A] relA) = relB := by
      calc
        e (1 ⊗ₜ[A] relA) =
            MvPolynomial.algebraTensorAlgEquiv A B (1 ⊗ₜ[A] relA) := rfl
        _ = 1 • MvPolynomial.map (algebraMap A B) relA := by
          rw [MvPolynomial.algebraTensorAlgEquiv_tmul]
          simp
        _ = relB := by
          simp [relA, relB, MvPolynomial.map_C, MvPolynomial.map_X]
    have hmap' : e (Algebra.TensorProduct.includeRight relA) = relB := by
      simpa using hmap
    rw [show J = Ideal.span {relA} by rfl, show K = Ideal.span {relB} by rfl,
      Ideal.map_span, Ideal.map_span]
    simp only [Set.image_singleton]
    change Ideal.span {relB} = Ideal.span {e (Algebra.TensorProduct.includeRight relA)}
    rw [hmap']
  have hquot :
      B ⊗[A] (MvPolynomial (Option ι) A ⧸ J) ≃ₐ[B]
        (B ⊗[A] MvPolynomial (Option ι) A) ⧸
          J.map (Algebra.TensorProduct.includeRight (A := B)
            (R := A)) :=
    Algebra.TensorProduct.tensorQuotientEquiv (R := A) B
      (MvPolynomial (Option ι) A) B J
  have hquot' :
      ((B ⊗[A] MvPolynomial (Option ι) A) ⧸
          J.map (Algebra.TensorProduct.includeRight (A := B)
            (R := A))) ≃ₐ[B] MvPolynomial (Option ι) B ⧸ K :=
    Ideal.quotientEquivAlg _ _ e hJ
  exact hquot.trans (hquot'.trans (hyperplanePolynomialEquiv
    (fun i => algebraMap A B (f i)) a h).symm)

/-- `baseChangeHyperplaneEquiv` with the polynomial variables indexed by `ULift (Fin n)`, which
is the index type of affine `n`-space over a scheme. -/
private noncomputable def baseChangeHyperplaneEquivULift
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} (f : Fin n → A) (a : Fin n → B)
    (h : ∑ i, algebraMap A B (f i) * a i = 1) :
    B ⊗[A] (MvPolynomial (Option (Fin n)) A ⧸
      Ideal.span ({∑ i, MvPolynomial.C (f i) * MvPolynomial.X (some i) - 1} :
        Set (MvPolynomial (Option (Fin n)) A))) ≃ₐ[B]
      MvPolynomial (ULift.{u} (Fin n)) B :=
  (baseChangeHyperplaneEquiv f a h).trans
    (MvPolynomial.renameEquiv B Equiv.ulift).symm

/-- A quasi-affine scheme is covered by finitely many standard opens of the spectrum of its ring
of global sections which are contained in its image there. -/
private lemma exists_basicOpen_finite_cover_range_toSpecΓ (X : Scheme) [X.IsQuasiAffine] :
    ∃ (n : ℕ) (f : Fin n → Γ(X, ⊤)),
      (∀ i, (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum ↑Γ(X, ⊤))) ⊆
        (Set.range X.toSpecΓ : Set (PrimeSpectrum ↑Γ(X, ⊤)))) ∧
      (Set.range X.toSpecΓ : Set (PrimeSpectrum ↑Γ(X, ⊤))) ⊆
        ⋃ i, (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum ↑Γ(X, ⊤))) := by
  let b : Set Γ(X, ⊤) :=
    {r | (PrimeSpectrum.basicOpen r : Set _) ⊆ (Set.range X.toSpecΓ : Set (PrimeSpectrum _))}
  have hUcover : (Set.range X.toSpecΓ : Set (PrimeSpectrum ↑Γ(X, ⊤))) ⊆
      ⋃ r ∈ b, (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum ↑Γ(X, ⊤))) := by
    intro x hx
    rcases (PrimeSpectrum.isBasis_basic_opens (R := Γ(X, ⊤))).exists_subset_of_mem_open hx
      X.toSpecΓ.isOpenEmbedding.isOpen_range with ⟨v, ⟨_, ⟨r, rfl⟩, rfl⟩, hxv, hvu⟩
    exact Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hvu, hxv⟩⟩
  obtain ⟨t, ht, htfin, htcov⟩ :=
    (isCompact_range X.toSpecΓ.continuous).elim_finite_subcover_image
      (b := b)
      (c := fun r : Γ(X, ⊤) => (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum ↑Γ(X, ⊤))))
      (fun r _ => (PrimeSpectrum.basicOpen r).isOpen) hUcover
  obtain ⟨n, e, he⟩ := htfin.fin_embedding
  refine ⟨n, ⇑e, fun i => ht (he ▸ Set.mem_range_self i), htcov.trans ?_⟩
  rw [← he, Set.biUnion_range]

/-- If the image of `Spec B → Spec A` is covered by the standard opens of `f_1, …, f_n`, then the
images of the `f i` in `B` generate the unit ideal, so `1 = ∑ f i * a i` for some `a i ∈ B`. -/
private lemma exists_unit_coefficients_of_specMap_range
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} (f : Fin n → A)
    (h : Set.range (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⊆
      ⋃ i, (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum A))) :
    ∃ a : Fin n → B, ∑ i, algebraMap A B (f i) * a i = 1 := by
  classical
  let I : Ideal B := Ideal.span (Set.range fun i => algebraMap A B (f i))
  have hI : I = ⊤ := by
    by_contra hI
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
    let x : PrimeSpectrum B := ⟨m, hm.isPrime⟩
    rcases Set.mem_iUnion.mp (h ⟨x, rfl⟩) with ⟨i, hi⟩
    change PrimeSpectrum.comap (algebraMap A B) x ∈ PrimeSpectrum.basicOpen (f i) at hi
    rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hi
    exact hi (hIm (Ideal.subset_span ⟨i, rfl⟩))
  obtain ⟨a, ha⟩ := (Ideal.mem_span_range_iff_exists_fun (x := (1 : B))
    (v := fun i : Fin n => algebraMap A B (f i))).mp ((Ideal.eq_top_iff_one I).mp hI)
  exact ⟨a, (Finset.sum_congr rfl fun _ _ => mul_comm _ _).trans ha⟩

/-- Assembly of the base change: given an identification of the fibre product with a pullback of
spectra over an affine base, an isomorphism of the base-changed algebra with a polynomial algebra,
and the comparison of affine space over `X'` with affine space over the spectrum of its global
sections, the fibre product is affine space over `X'` compatibly with the projections. -/
private lemma exists_iso_affineSpace_of_baseChange
    {X X' : Scheme.{u}} [IsAffine X']
    {A Q : Type u} [CommRing A] [CommRing Q] [Algebra A Q]
    [Algebra A Γ(X', ⊤)] (idx : Type u)
    (f : Spec (.of Q) ⟶ X) (g : X' ⟶ X)
    (g₀ : X' ⟶ Spec (.of A))
    (ePoly : Γ(X', ⊤) ⊗[A] Q ≃ₐ[Γ(X', ⊤)]
      MvPolynomial idx Γ(X', ⊤))
    (eOpen : pullback g f ≅ pullback g₀
      (Spec.map (CommRingCat.ofHom (algebraMap A Q))))
    (eAffineBase : AffineSpace idx (Spec (.of Γ(X', ⊤))) ≅ AffineSpace idx X')
    (gmap : pullback g₀ (Spec.map (CommRingCat.ofHom (algebraMap A Q))) ⟶ pullback
      (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X', ⊤))) :
        Spec (.of Γ(X', ⊤)) ⟶ Spec (.of A))
      (Spec.map (CommRingCat.ofHom (algebraMap A Q))))
    (hgmapIso : IsIso gmap)
    (hgmapfst : gmap ≫ pullback.fst
        (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X', ⊤))))
        (Spec.map (CommRingCat.ofHom (algebraMap A Q))) =
      pullback.fst g₀ (Spec.map (CommRingCat.ofHom (algebraMap A Q))) ≫
        X'.isoSpec.hom)
    (hAffineBaseOver : eAffineBase.hom ≫ (AffineSpace idx X' ↘ X') =
      (AffineSpace idx (Spec (.of Γ(X', ⊤))) ↘ Spec (.of Γ(X', ⊤))) ≫
        X'.isoSpec.inv)
    (heOpen : eOpen.hom ≫
      pullback.fst g₀ (Spec.map (CommRingCat.ofHom (algebraMap A Q))) =
        pullback.fst g f) :
    ∃ e : pullback g f ≅ AffineSpace idx X',
      e.hom ≫ (AffineSpace idx X' ↘ X') = pullback.fst g f := by
  let q : Spec (.of Q) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A Q))
  let eSpec : pullback g₀ q ≅ Spec (.of (Γ(X', ⊤) ⊗[A] Q)) :=
    asIso gmap ≪≫ pullbackSpecIso A Γ(X', ⊤) Q
  let eTotal : pullback g f ≅ AffineSpace idx X' :=
    eOpen ≪≫ eSpec ≪≫
      Scheme.Spec.mapIso ePoly.symm.toRingEquiv.toCommRingCatIso.op ≪≫
      (AffineSpace.SpecIso idx (.of Γ(X', ⊤))).symm ≪≫ eAffineBase
  have hcoeff' :
      CommRingCat.ofHom
          (MvPolynomial.C : Γ(X', ⊤) →+* MvPolynomial idx Γ(X', ⊤)) ≫
        ePoly.symm.toRingEquiv.toCommRingCatIso.hom =
      CommRingCat.ofHom (algebraMap Γ(X', ⊤)
        (Γ(X', ⊤) ⊗[A] Q)) := by
    ext r
    change ePoly.symm (algebraMap Γ(X', ⊤) (MvPolynomial idx Γ(X', ⊤)) r) = _
    rw [AlgEquiv.commutes]
    rfl
  have hSpecBase :
      (AffineSpace.SpecIso idx (CommRingCat.of Γ(X', ⊤))).inv ≫
        (AffineSpace idx (Spec (.of Γ(X', ⊤))) ↘ Spec (.of Γ(X', ⊤))) =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : Γ(X', ⊤) →+* MvPolynomial idx Γ(X', ⊤))) :=
    AffineSpace.SpecIso_inv_over (CommRingCat.of Γ(X', ⊤))
  have hSpecBase' := hSpecBase =≫ X'.isoSpec.inv
  have hPolyCoeff :
      Spec.map ePoly.symm.toRingEquiv.toCommRingCatIso.hom.op.unop ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : Γ(X', ⊤) →+* MvPolynomial idx Γ(X', ⊤))) =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X', ⊤)
        (Γ(X', ⊤) ⊗[A] Q))) := by
    rw [← Spec.map_comp]
    simpa only [Quiver.Hom.unop_op] using
      congrArg (fun f : CommRingCat.Hom _ _ => Spec.map f) hcoeff'
  have hPolyCoeff'' := hPolyCoeff =≫ X'.isoSpec.inv
  have hPBBase := pullbackSpecIso_hom_fst' A Γ(X', ⊤) Q =≫ X'.isoSpec.inv
  have hgmapfst' := hgmapfst =≫ X'.isoSpec.inv
  simp only [RingEquiv.toCommRingCatIso_hom, Category.assoc]
    at hSpecBase' hPolyCoeff'' hPBBase hgmapfst'
  refine ⟨eTotal, ?_⟩
  simp only [eTotal, eSpec, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
    RingEquiv.toCommRingCatIso_hom,
    Iso.symm_hom, Scheme.Spec_map, asIso_hom, Category.assoc]
  rw [hAffineBaseOver, hSpecBase', hPolyCoeff'', hPBBase, hgmapfst']
  simpa only [X'.isoSpec.hom_inv_id, Category.comp_id] using heOpen

/-- **Stacks Project, Tag 0F82.** A quasi-affine scheme `X` admits an integer `n`, an affine
scheme `T` and a morphism `T ⟶ X` such that for every morphism `X' ⟶ X` with `X'` affine the
fibre product `X' ×_X T` is isomorphic to affine `n`-space over `X'`, as a scheme over `X'`. -/
@[stacks 0F82]
theorem exists_affine_pullback_iso_affineSpace (X : Scheme.{u}) [X.IsQuasiAffine] :
    ∃ (n : ℕ) (T : Scheme.{u}), IsAffine T ∧
      ∃ f : T ⟶ X, ∀ (X' : Scheme.{u}) (_ : IsAffine X') (g : X' ⟶ X),
        Nonempty (Over.mk (pullback.fst g f) ≅
          Over.mk (AffineSpace.over (ULift.{u} (Fin n)) X').hom) := by
  classical
  obtain ⟨n, s, hs, hcover⟩ := exists_basicOpen_finite_cover_range_toSpecΓ X
  let A : Type u := ↑(Γ(X, ⊤))
  let P := MvPolynomial (Option (Fin n)) A
  let I : Ideal P := Ideal.span {∑ i, MvPolynomial.C (s i) * MvPolynomial.X (some i) - 1}
  let Q := P ⧸ I
  let T : Scheme.{u} := Spec (.of Q)
  let q : T ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A Q))
  have hqsum : ∑ i, algebraMap A Q (s i) *
      Ideal.Quotient.mk I (MvPolynomial.X (some i)) = 1 :=
    quotient_hyperplane_eq_one s
  have hqopens : Set.range q ⊆
      ⋃ i, (PrimeSpectrum.basicOpen (s i) : Set (PrimeSpectrum A)) := by
    rintro _ ⟨x, rfl⟩
    let x' : PrimeSpectrum Q := x
    obtain ⟨i, hi⟩ : ∃ i, algebraMap A Q (s i) ∉ x.asIdeal := by
      by_contra! hall
      have hmem : (∑ i, algebraMap A Q (s i) *
          Ideal.Quotient.mk I (MvPolynomial.X (some i))) ∈ x'.asIdeal :=
        Submodule.sum_mem _ fun i _ => x'.asIdeal.mul_mem_right _ (hall i)
      rw [hqsum] at hmem
      exact x'.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hmem)
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    change PrimeSpectrum.comap (algebraMap A Q) x' ∈ PrimeSpectrum.basicOpen (s i)
    rwa [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  have hqrange : Set.range q ⊆ Set.range X.toSpecΓ := hqopens.trans (Set.iUnion_subset hs)
  let f : T ⟶ X := IsOpenImmersion.lift X.toSpecΓ q hqrange
  refine ⟨n, T, inferInstance, f, fun X' _ g => ?_⟩
  let g₀ : X' ⟶ Spec (.of A) := g ≫ X.toSpecΓ
  let β : CommRingCat.of A ⟶ CommRingCat.of Γ(X', ⊤) :=
    (Scheme.ΓSpecIso (.of A)).inv ≫ g₀.appTop
  let : Algebra A Γ(X', ⊤) := β.hom.toAlgebra
  have hβspec : Spec.map β = X'.isoSpec.inv ≫ g₀ := by
    calc
      Spec.map β = Spec.map g₀.appTop ≫
          Spec.map (Scheme.ΓSpecIso (.of A)).inv := by
        simp [β, ← Spec.map_comp]
      _ = Spec.map g₀.appTop ≫ (Spec (.of A)).isoSpec.inv := by
        rw [Scheme.isoSpec_Spec_inv]
      _ = X'.isoSpec.inv ≫ g₀ := Scheme.isoSpec_inv_naturality g₀
  have hβrange : Set.range (Spec.map β) ⊆
      (Set.range X.toSpecΓ : Set (PrimeSpectrum A)) := by
    rw [hβspec]
    rintro y ⟨z, rfl⟩
    exact ⟨g (X'.isoSpec.inv z), rfl⟩
  obtain ⟨a, ha⟩ := exists_unit_coefficients_of_specMap_range s (hβrange.trans hcover)
  have hfq : f ≫ X.toSpecΓ = q := IsOpenImmersion.lift_fac X.toSpecΓ q hqrange
  have hopen : pullback.fst g f ≫ g₀ = pullback.snd g f ≫ q := by
    calc
      pullback.fst g f ≫ g₀ = (pullback.fst g f ≫ g) ≫ X.toSpecΓ := by
        simp only [g₀, Category.assoc]
      _ = (pullback.snd g f ≫ f) ≫ X.toSpecΓ := by
        rw [pullback.condition]
      _ = pullback.snd g f ≫ q := by rw [Category.assoc, hfq]
  let gcomp : pullback g f ⟶ pullback g₀ q :=
    pullback.lift (pullback.fst g f) (pullback.snd g f) hopen
  have hcomp : pullback.fst g₀ q ≫ g = pullback.snd g₀ q ≫ f := by
    apply (cancel_mono X.toSpecΓ).mp
    calc
      pullback.fst g₀ q ≫ g ≫ X.toSpecΓ = pullback.fst g₀ q ≫ g₀ := by
        simp [g₀]
      _ = pullback.snd g₀ q ≫ q := pullback.condition
      _ = pullback.snd g₀ q ≫ f ≫ X.toSpecΓ := by rw [← hfq]
  let gcompInv : pullback g₀ q ⟶ pullback g f :=
    pullback.lift (pullback.fst g₀ q) (pullback.snd g₀ q) hcomp
  let eOpen : pullback g f ≅ pullback g₀ q :=
    { hom := gcomp, inv := gcompInv,
      hom_inv_id := by apply pullback.hom_ext <;>
        simp only [Category.assoc, gcomp, gcompInv, pullback.lift_fst,
          pullback.lift_snd, Category.id_comp]
      inv_hom_id := by apply pullback.hom_ext <;>
        simp only [Category.assoc, gcomp, gcompInv, pullback.lift_fst,
          pullback.lift_snd, Category.id_comp] }
  let gspec : Spec (.of Γ(X', ⊤)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A Γ(X', ⊤)))
  have hgspec : g₀ = X'.isoSpec.hom ≫ gspec := by
    rw [show gspec = Spec.map β from rfl, hβspec, Iso.hom_inv_id_assoc]
  let gmap : pullback g₀ q ⟶ pullback gspec q :=
    pullback.map g₀ q gspec q X'.isoSpec.hom (𝟙 T) (𝟙 (Spec (.of A))) hgspec (by simp)
  have hgmapIso : IsIso gmap :=
    pullback.map_isIso g₀ q gspec q X'.isoSpec.hom
      (𝟙 T) (𝟙 (Spec (.of A))) hgspec (by simp)
  let idx := ULift.{u} (Fin n)
  let eAffineBase : AffineSpace idx (Spec (.of Γ(X', ⊤))) ≅ AffineSpace idx X' :=
    (AffineSpace.functor.obj (.op idx)).mapIso X'.isoSpec.symm
  obtain ⟨eTotal, hOver⟩ := exists_iso_affineSpace_of_baseChange idx f g g₀
    (baseChangeHyperplaneEquivULift s a ha) eOpen eAffineBase gmap hgmapIso
    (by dsimp [gmap, pullback.map]; exact pullback.lift_fst _ _ _)
    (AffineSpace.map_over X'.isoSpec.inv) (pullback.lift_fst _ _ _)
  exact ⟨Over.isoMk eTotal hOver⟩

end AlgebraicGeometry

end
