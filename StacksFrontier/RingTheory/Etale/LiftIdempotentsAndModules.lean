module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.RingTheory.Etale.Basic
public import StacksFrontier.RingTheory.Etale.LiftFactorization
public import StacksFrontier.RingTheory.Idempotents.Lifting

/-!
# Lifting idempotents of an integral algebra and finite projective modules

Let `A` be a commutative ring and `I` an ideal. Two pieces of data over `A ⧸ I` are lifted here,
each after an étale base change `A → A'` that leaves the quotient by `I` unchanged: an idempotent
of `B ⧸ IB` for `B` an integral `A`-algebra, and a finite projective `A ⧸ I`-module.

## Main results

* `exists_etale_baseChange_idempotent_lift`: an idempotent of `B ⧸ IB`, for `B` integral over
  `A`, lifts to `B ⊗[A] A'`.
* `exists_etale_baseChange_finite_projective_lift`: a finite projective `A ⧸ I`-module lifts to a
  finite projective `A'`-module.

## Implementation notes

For the idempotent, Stacks 09XG (`exists_monic_aeval_eq_zero_map_eq_of_sq_sub_mem_map`) gives a
monic `f ∈ A[X]` killing a lift `y` of the idempotent and reducing to `Xᵈ (X - 1)ᵈ` modulo `I`.
Lifting that coprime factorization by `exists_etale_lift_of_isCoprime_factorization` yields
`f = g h` over an étale `A'` with `g` and `h` coprime, so `g(y) h(y) = 0` while a Bézout identity
`k g + l h = 1` makes `g(y) k(y)` an idempotent lifting the given one.

For the module, a finite projective `A ⧸ I`-module is the image of an idempotent matrix
`p` over `A ⧸ I`. Lifting the matrix arbitrarily to `φ` over `A` and taking its characteristic
polynomial `f`, the algebra `A[X] ⧸ (f)` maps to the matrix algebra by Cayley–Hamilton, and
`X(1 - X)` is nilpotent in its reduction modulo `I`; the resulting idempotent of that reduction
lifts by the previous result, and its image under the matrix representation is an idempotent over
`A'` lifting `p`.

The two halves use different `open` groups and the second needs the `RingHomInvPair` instances for
semilinear transport, so each is kept in its own section.

## References

* [Stacks Project, Tag 07M4](https://stacks.math.columbia.edu/tag/07M4)
* [Stacks Project, Tag 07M5](https://stacks.math.columbia.edu/tag/07M5)
-/

universe u v

@[expose] public section

section Idempotents

open Polynomial

private lemma isCoprime_X_pow_X_sub_one_pow {R : Type*} [CommRing R] (d : ℕ) :
    IsCoprime (X ^ d : R[X]) ((X - 1) ^ d) :=
  IsCoprime.pow ⟨1, -1, by ring⟩

private lemma idempotent_of_bezout_of_mul_eq_zero {R : Type*} [CommRing R]
    (G H K L : R) (hzero : G * H = 0) (hbez : K * G + L * H = 1) :
    IsIdempotentElem (G * K) := by
  show (G * K) * (G * K) = G * K
  linear_combination (G * K) * hbez - K * L * hzero

private lemma eq_mul_of_bezout {R : Type*} [CommRing R] (e G H K L : R)
    (he : IsIdempotentElem e) (hG : G = e) (hHe : H * e = 0)
    (hbez : K * G + L * H = 1) : e = G * K := by
  subst G
  linear_combination K * he.eq - e * hbez + L * hHe

private lemma map_eval_map {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (p : Polynomial S) (x : R) :
    g (p.eval (f x)) = (p.map g).eval (g (f x)) := by
  simp [Polynomial.eval_map, Polynomial.eval₂_at_apply]

/-- **Stacks 07M4.** An idempotent of `B ⧸ IB`, for an integral `A`-algebra `B`, lifts to
`B ⊗[A] A'` after an étale base change `A → A'` which induces an isomorphism modulo `I`. -/
@[stacks 07M4]
theorem exists_etale_baseChange_idempotent_lift
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B]
    (I : Ideal A) (e : B ⧸ I.map (algebraMap A B)) (he : IsIdempotentElem e) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A'),
      let T := TensorProduct A B A'
      let ι : B →+* T :=
        Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := A')
      let J : Ideal T := (I.map (algebraMap A B)).map ι
      let q : (B ⧸ I.map (algebraMap A B)) →+* T ⧸ J :=
        Ideal.quotientMap J ι Ideal.le_comap_map
      ∃ e' : T,
      Algebra.Etale A A' ∧
      Function.Bijective
        (Ideal.quotientMap (I.map (algebraMap A A')) (algebraMap A A')
          Ideal.le_comap_map) ∧
      IsIdempotentElem e' ∧
      q e = Ideal.Quotient.mk J e' := by
  classical
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective e
  have hb : b ^ 2 - b ∈ I.map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, pow_two]
    exact sub_eq_zero.mpr he
  obtain ⟨d, hd, f, hf, hfb, hfbar⟩ :=
    exists_monic_aeval_eq_zero_map_eq_of_sq_sub_mem_map I b hb
  obtain ⟨A', _, _, g, h, hEt, hbij, hgmon, hhmon, hcop, hfac, hgbar, hhbar⟩ :=
    exists_etale_lift_of_isCoprime_factorization I f (X ^ d) ((X - 1) ^ d) hf
      (monic_X.pow d) ((monic_X_sub_C 1).pow d) hfbar
      (isCoprime_X_pow_X_sub_one_pow d)
  let T := TensorProduct A B A'
  let ι : B →+* T :=
    Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := A')
  let ρ : A' →+* T :=
    (Algebra.TensorProduct.includeRight : A' →ₐ[A] T).toRingHom
  have hρι (a : A) : ρ (algebraMap A A' a) = ι (algebraMap A B a) := by
    rw [show ρ (algebraMap A A' a) = algebraMap A T a from
      Algebra.TensorProduct.includeRight.commutes a]
    exact Algebra.TensorProduct.includeLeft.commutes a
  obtain ⟨k, l, hbez⟩ := hcop
  let z : T := ι b
  let G : T := (g.map ρ).eval z
  let H : T := (h.map ρ).eval z
  let K : T := (k.map ρ).eval z
  let L : T := (l.map ρ).eval z
  have hGH : G * H = 0 := by
    show (g.map ρ).eval z * (h.map ρ).eval z = 0
    rw [← Polynomial.eval_mul, ← Polynomial.map_mul, ← hfac, Polynomial.map_map]
    have hscalar : ρ.comp (algebraMap A A') = ι.comp (algebraMap A B) := RingHom.ext hρι
    rw [hscalar, ← Polynomial.map_map, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      Polynomial.eval_map, ← Polynomial.aeval_def]
    show ι ((aeval b) f) = 0
    rw [hfb, map_zero]
  have hKL : K * G + L * H = 1 := by
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_one] using congrArg (fun p => (p.map ρ).eval z) hbez
  refine ⟨A', inferInstance, inferInstance, G * K, hEt, hbij,
    idempotent_of_bezout_of_mul_eq_zero G H K L hGH hKL, ?_⟩
  let J : Ideal T := (I.map (algebraMap A B)).map ι
  let qB : (B ⧸ I.map (algebraMap A B)) →+* T ⧸ J :=
    Ideal.quotientMap J ι Ideal.le_comap_map
  let qT : T →+* T ⧸ J := Ideal.Quotient.mk J
  have hker : I.map (algebraMap A A') ≤ RingHom.ker (qT.comp ρ) :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr <| by
      show ρ (algebraMap A A' a) ∈ J
      rw [hρι a]
      exact Ideal.mem_map_of_mem ι (Ideal.mem_map_of_mem (algebraMap A B) ha)
  let s : A' ⧸ I.map (algebraMap A A') →+* T ⧸ J :=
    Ideal.Quotient.lift _ (qT.comp ρ) hker
  have hGbar : qT G = qB (Ideal.Quotient.mk _ b) := by
    show qT ((g.map ρ).eval z) = _
    rw [map_eval_map, Polynomial.map_map]
    have hρ : qT.comp ρ = s.comp (Ideal.Quotient.mk _) := by ext; rfl
    rw [hρ, ← Polynomial.map_map, ← hgbar]
    simp only [Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_pow, Polynomial.eval_X]
    rw [show qT z = qB (Ideal.Quotient.mk _ b) from rfl]
    simpa only [map_pow] using congrArg qB (he.pow_eq (Nat.ne_of_gt hd))
  have hHbar_mul_e : qT H * qB (Ideal.Quotient.mk _ b) = 0 := by
    rw [← hGbar, ← map_mul, mul_comm H G, hGH, map_zero]
  have hKLG : qT K * qT G + qT L * qT H = 1 := by
    simpa only [map_add, map_mul, map_one] using congrArg qT hKL
  show qB (Ideal.Quotient.mk _ b) = qT (G * K)
  rw [map_mul]
  exact eq_mul_of_bezout _ _ _ _ _ (he.map qB) hGbar hHbar_mul_e hKLG

end Idempotents

section FiniteProjective

open Matrix Polynomial

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-! Stacks 07M5 needs four matrix-flavoured support lemmas that PR901 proved alongside Stacks
0D47. Current main reaches 0D47 through module endomorphisms instead
(`StacksFrontier/RingTheory/Module/Projective/Lifting.lean`), so it does not have them. They carry
no Stacks tag, so they are replayed here as private helpers rather than published as a second
provider of anything. -/

/-- A finite projective module `M` over a commutative ring `S` is isomorphic to the range of
an idempotent square matrix over `S`.

Being finite projective, `M` is a direct summand of a finite free module `S^n = (Fin n → S)`:
there are `S`-linear maps `i : M → S^n` and `r : S^n → M` with `r ∘ i = id`. Then
`f := i ∘ r : S^n → S^n` is an idempotent endomorphism, since
`f ∘ f = i ∘ (r ∘ i) ∘ r = i ∘ r = f`, and its range is `i '' M ≅ M`, because `i` is a split
injection, hence injective, and `range f = range i`. Transporting `f` across `Matrix.toLin'`
gives a matrix `pbar := toLin'.symm f` with `IsIdempotentElem pbar` and
`range (toLin' pbar) = range f ≅ M`. -/
private theorem exists_isIdempotentElem_matrix_of_finiteProjective
    (S : Type*) [CommRing S] (M : Type*) [AddCommGroup M] [Module S M]
    [Module.Finite S M] [Module.Projective S M] :
    ∃ (n : ℕ) (pbar : Matrix (Fin n) (Fin n) S),
      IsIdempotentElem pbar ∧
      Nonempty (LinearMap.range (Matrix.toLin' pbar) ≃ₗ[S] M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' S M
  obtain ⟨i, hi⟩ := LinearMap.exists_rightInverse_of_surjective f
    (LinearMap.range_eq_top.mpr hf)
  set e : (Fin n → S) →ₗ[S] (Fin n → S) := i ∘ₗ f with he_def
  have he_idem : e ∘ₗ e = e := by
    rw [he_def, LinearMap.comp_assoc, ← LinearMap.comp_assoc f i f, hi, LinearMap.id_comp]
  have hsymm : Matrix.toLin' (Matrix.toLin'.symm e) = e := LinearEquiv.apply_symm_apply _ _
  refine ⟨n, Matrix.toLin'.symm e, ?_, ?_⟩
  · show Matrix.toLin'.symm e * Matrix.toLin'.symm e = Matrix.toLin'.symm e
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, hsymm, he_idem]
  · rw [hsymm, he_def]
    have hli : Function.LeftInverse f i := fun x => by
      simpa using LinearMap.congr_fun hi x
    have hrange : (i ∘ₗ f).range = i.range := by
      rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hf, Submodule.map_top]
    exact ⟨(LinearEquiv.ofEq _ _ hrange).trans (LinearEquiv.ofInjective i hli.injective).symm⟩

/-- The range of an idempotent matrix over a commutative ring is a projective module.

An idempotent endomorphism `f := toLin' e` of the free, hence projective, module `Fin n → R`
is a projection onto its range (`LinearMap.IsProj f.range f`). This exhibits `range f` as a
direct summand of `Fin n → R`: the inclusion `range f ↪ (Fin n → R)` is split by the
corestriction of `f`, whose composite with the inclusion is the identity on the range. -/
private theorem Module.Projective_range_toLin'_of_isIdempotentElem
    {R : Type*} [CommRing R] {n : ℕ} (e : Matrix (Fin n) (Fin n) R)
    (he : IsIdempotentElem e) :
    Module.Projective R (LinearMap.range (Matrix.toLin' e)) := by
  have hf : IsIdempotentElem (Matrix.toLin' e) := by
    show Matrix.toLin' e * Matrix.toLin' e = Matrix.toLin' e
    rw [show Matrix.toLin' e * Matrix.toLin' e = Matrix.toLin' e ∘ₗ Matrix.toLin' e from rfl,
        ← Matrix.toLin'_mul, he]
  have hproj := LinearMap.IsIdempotentElem.isProj_range (Matrix.toLin' e) hf
  exact Module.Projective.of_split (LinearMap.range (Matrix.toLin' e)).subtype
    hproj.codRestrict (LinearMap.ext fun x => Subtype.ext (hproj.map_id x x.property))

/-- The reduction isomorphism. Let `e : Matrix (Fin n) (Fin n) R` be idempotent and let
`pbar := e.map (Ideal.Quotient.mk I)` be its reduction, which is again idempotent. Then there
is an `R/I`-linear isomorphism
`(range (toLin' e)) ⧸ (I • ⊤) ≃ₗ[R/I] range (toLin' pbar)`.

This is base change. The submodule `range (toLin' e)` is the direct summand of `R^n` cut out by
the projector `e`, and reducing modulo `I` commutes with the idempotent decomposition: from
`R^n = Im(e) ⊕ Ker(e)` one gets `(R/I)^n = Im(e)/I·Im(e) ⊕ Ker(e)/I·Ker(e)`, and the reduced
projector is exactly `pbar`, whose image is `Im(e)/I·Im(e)`. Equivalently
`Im(e)/I·Im(e) ≅ (R/I) ⊗_R Im(e)`, and tensoring the split idempotent `e` with `R/I` gives the
split idempotent `pbar` over `R/I`, with matching ranges. -/
private theorem quotient_range_toLin'_equiv_of_map
    {R : Type*} [CommRing R] (I : Ideal R) {n : ℕ}
    (e : Matrix (Fin n) (Fin n) R) (he : IsIdempotentElem e)
    (pbar : Matrix (Fin n) (Fin n) (R ⧸ I)) (hpe : e.map (Ideal.Quotient.mk I) = pbar) :
    Nonempty
      ((LinearMap.range (Matrix.toLin' e) ⧸
          (I • (⊤ : Submodule R (LinearMap.range (Matrix.toLin' e)))))
        ≃ₗ[R ⧸ I]
        LinearMap.range (Matrix.toLin' pbar)) := by
  classical
  have hmk_smul : ∀ (c x : R), c • (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (c * x) :=
    fun c x => by simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
  -- entrywise reduction map
  let red : (Fin n → R) →ₗ[R] (Fin n → R ⧸ I) :=
    { toFun := fun v i => Ideal.Quotient.mk I (v i)
      map_add' a b := funext fun i => map_add (Ideal.Quotient.mk I) (a i) (b i)
      map_smul' c a := funext fun i => (hmk_smul c (a i)).symm }
  have hred_apply : ∀ (v : Fin n → R) (i : Fin n), red v i = Ideal.Quotient.mk I (v i) := by
    intro v i; rfl
  -- commutation
  have hcomm : ∀ v, red (Matrix.toLin' e v) = Matrix.toLin' pbar (red v) := by
    intro v
    ext i
    rw [hred_apply, ← hpe]
    show Ideal.Quotient.mk I ((Matrix.toLin' e) v i)
      = (Matrix.toLin' (e.map (Ideal.Quotient.mk I))) (red v) i
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply,
        Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, Matrix.map_apply, hred_apply]
  -- membership: red sends range(toLin' e) into range(toLin' pbar)
  have hmem : ∀ x : LinearMap.range (Matrix.toLin' e),
      red (x : Fin n → R) ∈ LinearMap.range (Matrix.toLin' pbar) := by
    rintro ⟨x, v, rfl⟩
    exact ⟨red v, (hcomm v).symm⟩
  -- the R-linear map φ
  let φ : LinearMap.range (Matrix.toLin' e) →ₗ[R] LinearMap.range (Matrix.toLin' pbar) :=
    { toFun := fun x => ⟨red (x : Fin n → R), hmem x⟩
      map_add' x y := Subtype.ext (map_add red (x : Fin n → R) y)
      map_smul' c x := Subtype.ext (map_smul red c (x : Fin n → R)) }
  have hφ_apply : ∀ (x : LinearMap.range (Matrix.toLin' e)),
      (φ x : Fin n → R ⧸ I) = red (x : Fin n → R) := fun x => rfl
  -- I • ⊤ ≤ ker φ
  have hker : (I • (⊤ : Submodule R (LinearMap.range (Matrix.toLin' e)))) ≤ LinearMap.ker φ := by
    rw [Submodule.smul_le]
    intro r hr x _
    rw [LinearMap.mem_ker, map_smul]
    apply Subtype.ext
    rw [Submodule.coe_smul_of_tower]
    show r • (φ x : Fin n → R ⧸ I) = (0 : LinearMap.range (Matrix.toLin' pbar))
    ext i
    rw [hφ_apply]
    show (r • red (x : Fin n → R)) i = 0
    rw [Pi.smul_apply, hred_apply, hmk_smul]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ hr
  -- lift φ through the quotient
  let liftφ : (LinearMap.range (Matrix.toLin' e) ⧸
      (I • (⊤ : Submodule R (LinearMap.range (Matrix.toLin' e)))))
        →ₗ[R] LinearMap.range (Matrix.toLin' pbar) :=
    Submodule.liftQ _ φ hker
  have hlift_mk : ∀ (x : LinearMap.range (Matrix.toLin' e)),
      liftφ (Submodule.Quotient.mk x) = φ x := fun x => rfl
  -- surjectivity
  have hsurj : Function.Surjective liftφ := by
    rintro ⟨z, w, rfl⟩
    -- lift w : Fin n → R ⧸ I to v : Fin n → R with red v = w
    choose v hv using fun i => Ideal.Quotient.mk_surjective (w i)
    have hredv : red v = w := by ext i; rw [hred_apply]; exact hv i
    refine ⟨Submodule.Quotient.mk ⟨Matrix.toLin' e v, ⟨v, rfl⟩⟩, ?_⟩
    rw [hlift_mk]
    apply Subtype.ext
    rw [hφ_apply]
    show red (Matrix.toLin' e v) = Matrix.toLin' pbar w
    rw [hcomm, hredv]
  -- injectivity
  -- key: ker φ ≤ I • ⊤
  have hkerle : LinearMap.ker φ ≤ (I • (⊤ : Submodule R (LinearMap.range (Matrix.toLin' e)))) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    -- each coordinate of ↑x lies in I
    have hxI : ∀ i, (x : Fin n → R) i ∈ I := by
      intro i
      have hr0 : red (x : Fin n → R) = 0 := by
        have := Subtype.ext_iff.mp hx
        rwa [hφ_apply] at this
      have h2 : red (x : Fin n → R) i = 0 := by rw [hr0]; rfl
      rw [hred_apply] at h2
      rwa [Ideal.Quotient.eq_zero_iff_mem] at h2
    -- x is fixed by toLin' e
    have hfix : Matrix.toLin' e (x : Fin n → R) = (x : Fin n → R) := by
      obtain ⟨v, hv⟩ := x.property
      have heq : Matrix.toLin' e (Matrix.toLin' e v) = Matrix.toLin' (e * e) v := by
        rw [Matrix.toLin'_mul]; rfl
      rw [← hv, heq, show e * e = e from he]
    -- decompose x as a sum over the standard basis applied to toLin' e
    have hgen : ∀ j, Matrix.toLin' e (Pi.single j 1) ∈ LinearMap.range (Matrix.toLin' e) :=
      fun j => ⟨Pi.single j 1, rfl⟩
    have hxsum : x = ∑ j, (x : Fin n → R) j •
        (⟨Matrix.toLin' e (Pi.single j 1), hgen j⟩ : LinearMap.range (Matrix.toLin' e)) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul_of_tower, ← map_smul, ← map_sum]
      conv_lhs => rw [← hfix]
      congr 1
      ext i
      simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
    rw [hxsum]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem_smul (hxI j) Submodule.mem_top
  have hinj : Function.Injective liftφ := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ φ hker hkerle
  exact ⟨(LinearEquiv.ofBijective liftφ ⟨hinj, hsurj⟩).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective⟩

variable {A : Type u} [CommRing A] {n : ℕ}

private lemma matrix_detects_quotient_nilpotence
    {S : Type u} [CommRing S] [Algebra A S]
    (I : Ideal A) (ι : S →ₐ[A] Matrix (Fin n) (Fin n) A)
    (hι : Function.Injective ι) (s : S)
    (hs : (ι s).map (Ideal.Quotient.mk I) = 0) :
    IsNilpotent (Ideal.Quotient.mk (I.map (algebraMap A S)) s) := by
  let J : Ideal S := I.map (algebraMap A S)
  let q : S →+* S ⧸ J := Ideal.Quotient.mk J
  let p : A[X] := Matrix.charpoly (ι s)
  have hpmap : p.map (Ideal.Quotient.mk I) = X ^ n := by
    rw [← Matrix.charpoly_map, hs, Matrix.charpoly_zero]
    simp
  have hpS : aeval s p = 0 := by
    apply hι
    rw [← Polynomial.aeval_algHom_apply ι s p, Matrix.aeval_self_charpoly, map_zero]
  let qA : (A ⧸ I) →+* (S ⧸ J) :=
    Ideal.quotientMap J (algebraMap A S) Ideal.le_comap_map
  have hcomp : q.comp (algebraMap A S) = qA.comp (Ideal.Quotient.mk I) := by
    ext a
    rfl
  have hpqmap : p.map (q.comp (algebraMap A S)) = X ^ n := by
    rw [hcomp, ← Polynomial.map_map, hpmap, Polynomial.map_pow, Polynomial.map_X]
  have hpq : q s ^ n = 0 := by
    have heval : (p.map (q.comp (algebraMap A S))).eval (q s) = 0 := by
      rw [← Polynomial.eval₂_eq_eval_map, ← Polynomial.hom_eval₂]
      simpa [Polynomial.aeval_def] using congrArg q hpS
    simpa [hpqmap] using heval
  exact ⟨n, hpq⟩
set_option synthInstance.maxHeartbeats 1000000 in
-- The tensor quotient comparison requires a larger instance search budget.
private theorem etale_lift_matrix
    (I : Ideal A) {n : ℕ}
    (pbar : Matrix (Fin n) (Fin n) (A ⧸ I))
    (hpbar : IsIdempotentElem pbar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A'),
      let J := I.map (algebraMap A A')
      let q : (A ⧸ I) →+* (A' ⧸ J) :=
        Ideal.quotientMap J (algebraMap A A') Ideal.le_comap_map
      Algebra.Etale A A' ∧ Function.Bijective q ∧
      ∃ e : Matrix (Fin n) (Fin n) A',
        IsIdempotentElem e ∧ e.map (Ideal.Quotient.mk J) = pbar.map q := by
  classical
  let φ : Matrix (Fin n) (Fin n) A :=
    Matrix.of (fun i j => (Ideal.Quotient.mk_surjective (pbar i j)).choose)
  have hφ : φ.map (Ideal.Quotient.mk I) = pbar := by
    ext i j
    exact (Ideal.Quotient.mk_surjective (pbar i j)).choose_spec
  let B := Algebra.adjoin A {φ}
  let : CommRing B := Algebra.instCommRingAdjoinSingleton φ
  let b : B := ⟨φ, Algebra.subset_adjoin rfl⟩
  let ι : B →ₐ[A] Matrix (Fin n) (Fin n) A := B.val
  have hred : (ι (b - b ^ 2)).map (Ideal.Quotient.mk I) = 0 := by
    show ((Ideal.Quotient.mk I).mapMatrix) (φ - φ ^ 2) = 0
    rw [map_sub, map_pow]
    show φ.map (Ideal.Quotient.mk I) - (φ.map (Ideal.Quotient.mk I)) ^ 2 = 0
    rw [hφ, pow_two, hpbar.eq, sub_self]
  let J : Ideal B := I.map (algebraMap A B)
  let qb : B →+* B ⧸ J := Ideal.Quotient.mk J
  obtain ⟨k, hk⟩ := matrix_detects_quotient_nilpotence I ι
    (show Function.Injective ι from Subtype.val_injective) (b - b ^ 2) hred
  let m := k + 1
  have hm : (qb b - (qb b) ^ 2) ^ m = 0 := by
    rw [show qb b - (qb b) ^ 2 = qb (b - b ^ 2) by simp, pow_succ, hk, zero_mul]
  let eb : B ⧸ J := 1 - (1 - (qb b) ^ m) ^ m
  have heb : IsIdempotentElem eb := isIdempotentElem_one_sub_one_sub_pow_pow (qb b) m hm
  let : Module.Finite A B := Algebra.finite_adjoin_simple_of_isIntegral (Matrix.isIntegral φ)
  let : Algebra.IsIntegral A B := inferInstance
  obtain ⟨A', instA', algA', e', hetale, hq, he', heq⟩ :=
    exists_etale_baseChange_idempotent_lift I eb heb
  let : CommRing A' := instA'
  let : Algebra A A' := algA'
  let T := TensorProduct A B A'
  let ιT : B →+* T := Algebra.TensorProduct.includeLeftRingHom
  let JT : Ideal T := J.map ιT
  let qT : B ⧸ J →+* T ⧸ JT := Ideal.quotientMap JT ιT Ideal.le_comap_map
  have heq' : qT eb = Ideal.Quotient.mk JT e' := heq
  let incA' : B →ₐ[A] Matrix (Fin n) (Fin n) A' :=
    (AlgHom.mapMatrix (Algebra.ofId A A')).comp ι
  let ψ' : TensorProduct A A' B →ₐ[A'] Matrix (Fin n) (Fin n) A' :=
    (AlgHom.liftEquiv A A' B (Matrix (Fin n) (Fin n) A')) incA'
  let ψ : T →ₐ[A] Matrix (Fin n) (Fin n) A' :=
    (ψ'.restrictScalars A).comp (Algebra.TensorProduct.comm A B A').toAlgHom
  let e : Matrix (Fin n) (Fin n) A' := ψ e'
  have he : IsIdempotentElem e := he'.map ψ
  let JA' : Ideal A' := I.map (algebraMap A A')
  let redT : T →+* Matrix (Fin n) (Fin n) (A' ⧸ JA') :=
    ((Ideal.Quotient.mk JA').mapMatrix).comp ψ.toRingHom
  have hJTeq : JT = I.map (algebraMap A T) := by
    dsimp [JT, J, ιT]
    rw [Ideal.map_map]
    congr 1
  have hkill : JT ≤ RingHom.ker redT := by
    rw [hJTeq, Ideal.map_le_iff_le_comap]
    intro a ha
    show redT (algebraMap A T a) = 0
    show ((Ideal.Quotient.mk JA').mapMatrix) (ψ (algebraMap A T a)) = 0
    rw [AlgHom.commutes]
    -- scalar matrices of elements of I reduce to zero.
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    split
    · rw [show Ideal.Quotient.mk JA' ((algebraMap A A') a) = 0 by
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem (algebraMap A A') ha]
      rfl
    · simp
  let redQ : T ⧸ JT →+* Matrix (Fin n) (Fin n) (A' ⧸ JA') :=
    Ideal.Quotient.lift JT redT hkill
  let qA : (A ⧸ I) →+* (A' ⧸ JA') :=
    Ideal.quotientMap JA' (algebraMap A A') Ideal.le_comap_map
  have hbase : redQ (qT (qb b)) = pbar.map qA := by
    have hψ : ψ (ιT b) = φ.map (algebraMap A A') := by
      show ψ' ((Algebra.TensorProduct.comm A B A') (b ⊗ₜ (1 : A'))) = _
      rw [Algebra.TensorProduct.comm_tmul, show ψ' (1 ⊗ₜ[A] b) = (1 : A') • incA' b from
        AlgHom.liftEquiv_tmul incA' 1 b, one_smul]
      rfl
    show redT (ιT b) = pbar.map qA
    show (ψ (ιT b)).map (Ideal.Quotient.mk JA') = pbar.map qA
    rw [hψ, ← hφ]
    ext i j
    simp [qA, Matrix.map_apply]
  have hpb : IsIdempotentElem (pbar.map qA) :=
    hpbar.map qA.mapMatrix
  have hcorr : 1 - (1 - (pbar.map qA) ^ m) ^ m = pbar.map qA := by
    rw [hpb.pow_succ_eq k, hpb.one_sub.pow_succ_eq k, sub_sub_cancel]
  have hmap_eb : redQ (qT eb) = pbar.map qA := by
    show redQ (qT (1 - (1 - (qb b) ^ m) ^ m)) = _
    simpa only [map_sub, map_one, map_pow, hbase] using hcorr
  have hmap_e : e.map (Ideal.Quotient.mk JA') = pbar.map
      (Ideal.quotientMap JA' (algebraMap A A') Ideal.le_comap_map) := by
    show redT e' = pbar.map qA
    calc
      redT e' = redQ (Ideal.Quotient.mk JT e') := rfl
      _ = redQ (qT eb) := congrArg redQ heq'.symm
      _ = pbar.map qA := hmap_eb
  exact ⟨A', instA', algA', hetale, hq, e, he, hmap_e⟩
private lemma matrix_map_mulVec
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {n : ℕ} (p : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    Matrix.toLin' (p.map f) (fun j => f (v j)) =
      fun i => f (Matrix.toLin' p v i) := by
  ext i
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]

/-- Applying a ring map entrywise sends the range of `toLin' p` into that of `toLin' (p.map f)`. -/
private lemma map_mem_range_toLin'
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (p : Matrix (Fin n) (Fin n) R) (x : Fin n → R) (hx : x ∈ LinearMap.range (Matrix.toLin' p)) :
    (fun i => f (x i)) ∈ LinearMap.range (Matrix.toLin' (p.map f)) := by
  obtain ⟨v, rfl⟩ := hx
  exact ⟨fun i => f (v i), matrix_map_mulVec f p v⟩

private noncomputable abbrev range_equiv_map
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R ≃+* S) {n : ℕ} (p : Matrix (Fin n) (Fin n) R) :
    LinearMap.range (Matrix.toLin' p) ≃ₛₗ[(f : R →+* S)]
      LinearMap.range (Matrix.toLin' (p.map f)) := by
  let F : LinearMap.range (Matrix.toLin' p) →
      LinearMap.range (Matrix.toLin' (p.map f)) := fun x =>
    ⟨_, map_mem_range_toLin' (f : R →+* S) p x x.property⟩
  let G : LinearMap.range (Matrix.toLin' (p.map f)) →
      LinearMap.range (Matrix.toLin' p) := fun x => by
    refine ⟨(fun i => f.symm ((x : Fin n → S) i)), ?_⟩
    have hc : (p.map f).map (f.symm : S →+* R) = p := by
      ext i j
      exact f.symm_apply_apply _
    have := map_mem_range_toLin' (f.symm : S →+* R) (p.map f) x x.property
    rwa [hc] at this
  refine { toFun := F, invFun := G,
           left_inv := fun x => Subtype.ext (funext fun _ => f.symm_apply_apply _),
           right_inv := fun x => Subtype.ext (funext fun _ => f.apply_symm_apply _),
           map_add' := ?_, map_smul' := ?_ }
  · intro x y
    apply Subtype.ext
    ext i
    simp [F]
  · intro a x
    apply Subtype.ext
    ext i
    simp [F, map_mul]

/-- **Stacks 07M5.** A finite projective module over `A ⧸ I` lifts after an étale base change
`A → A'` which induces an isomorphism `A ⧸ I ≃+* A' ⧸ I A'`. -/
@[stacks 07M5]
theorem exists_etale_baseChange_finite_projective_lift
    {A : Type u} [CommRing A] (I : Ideal A)
    (Pbar : Type v) [AddCommGroup Pbar] [Module (A ⧸ I) Pbar]
    [Module.Finite (A ⧸ I) Pbar] [Module.Projective (A ⧸ I) Pbar] :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A'),
      let J := I.map (algebraMap A A')
      let q : (A ⧸ I) →+* (A' ⧸ J) :=
        Ideal.quotientMap J (algebraMap A A') Ideal.le_comap_map
      Algebra.Etale A A' ∧
      ∃ hq : Function.Bijective q,
      ∃ (P' : Type (max u v)) (_ : AddCommGroup P') (_ : Module A' P')
        (_ : Module.Finite A' P') (_ : Module.Projective A' P'),
        Nonempty
          (Pbar ≃ₛₗ[RingHomClass.toRingHom (RingEquiv.ofBijective q hq)]
            TensorProduct A' (A' ⧸ J) P') := by
  classical
  obtain ⟨n, pbar, hpbar, ⟨ePbar⟩⟩ :=
    exists_isIdempotentElem_matrix_of_finiteProjective (A ⧸ I) Pbar
  obtain ⟨A', cA', aA', hetale, hq, e, he, hmap⟩ :=
    etale_lift_matrix I pbar hpbar
  let J : Ideal A' := I.map (algebraMap A A')
  let q : (A ⧸ I) →+* (A' ⧸ J) :=
    Ideal.quotientMap J (algebraMap A A') Ideal.le_comap_map
  let qr : (A ⧸ I) ≃+* (A' ⧸ J) := RingEquiv.ofBijective q hq
  let E := LinearMap.range (Matrix.toLin' e)
  let P' := ULift.{v} E
  have hfinE : Module.Finite A' E :=
    Module.Finite.range _
  have hprojE : Module.Projective A' E :=
    Module.Projective_range_toLin'_of_isIdempotentElem e he
  have hfin : Module.Finite A' P' :=
    Module.Finite.equiv (ULift.moduleEquiv (R := A') (M := E)).symm
  have hproj : Module.Projective A' P' :=
    Module.Projective.of_equiv (ULift.moduleEquiv (R := A') (M := E)).symm
  obtain ⟨eRed⟩ := quotient_range_toLin'_equiv_of_map J e he (pbar.map q) hmap
  let eRange : LinearMap.range (Matrix.toLin' pbar) ≃ₛₗ[(qr : (A ⧸ I) →+* (A' ⧸ J))]
      LinearMap.range (Matrix.toLin' (pbar.map q)) :=
    range_equiv_map qr pbar
  let eQuot : (E ⧸ (J • (⊤ : Submodule A' E))) ≃ₗ[A' ⧸ J]
      TensorProduct A' (A' ⧸ J) E :=
    (TensorProduct.quotTensorEquivQuotSMul E J).symm.extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let eLift : TensorProduct A' (A' ⧸ J) P' ≃ₗ[A' ⧸ J]
      TensorProduct A' (A' ⧸ J) E :=
    (LinearEquiv.lTensor (A' ⧸ J) (ULift.moduleEquiv (R := A') (M := E))).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let eFinal : Pbar ≃ₛₗ[(qr : (A ⧸ I) →+* (A' ⧸ J))]
      TensorProduct A' (A' ⧸ J) P' :=
    ePbar.symm.trans (eRange.trans (eRed.symm.trans (eQuot.trans eLift.symm)))
  exact ⟨A', cA', aA', hetale, hq, P', inferInstance, inferInstance, hfin, hproj, ⟨eFinal⟩⟩

end FiniteProjective
