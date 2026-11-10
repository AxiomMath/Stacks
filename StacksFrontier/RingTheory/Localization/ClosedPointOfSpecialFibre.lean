module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.LocalSubring
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Localization at a closed point of the special fibre

Let `φ : R → S` be a ring map between local rings that is essentially of finite type; `φ` is not
assumed to be a local ring homomorphism. Then there are a natural number `n` and a maximal ideal
`𝔪 ⊆ R[x_1, …, x_n]` lying over the maximal ideal `𝔪_R` of `R` such that `S` is a localization of
a quotient of the local ring `R[x_1, …, x_n]_𝔪`, compatibly with the `R`-algebra structures.

## Conventions

"Localization" means inverting some multiplicatively closed subset, not just the complement of a
prime. Accordingly "essentially of finite type" means that `S` is isomorphic, as an `R`-algebra,
to a localization of a finite-type `R`-algebra, which is `Algebra.EssFiniteType R S`. "`S` is a
localization of a quotient of `B`" means that there are an ideal `I ⊆ B` and a multiplicative
subset `T ⊆ B ⧸ I` with `S ≅ T⁻¹(B ⧸ I)`, the given ring map `B → S` factoring as the quotient map
`B → B ⧸ I` followed by the localization map; this is `IsLocalizationOfQuotientMap`.

The `R`-algebra structure on `R[x_1, …, x_n]_𝔪` is the composite
`R → R[x_1, …, x_n] → R[x_1, …, x_n]_𝔪`, so the condition
`g.comp (algebraMap R _) = algebraMap R S` says that `g` is compatible with the `R`-algebra
structures.

A prime `q ⊆ R[x_1, …, x_n]` is in *good position* if `q ⊔ 𝔪_R R[x_1, …, x_n] ≠ ⊤`.

## Main definitions

* `IsLocalizationOfQuotientMap`: the ring map `g : B →+* S` exhibits `S` as a localization of a
  quotient of `B`.

## Main results

* `exists_isLocalizationOfQuotientMap_mvPolynomial_atMaximal`: the statement above.
* `exists_isLocalizationOfQuotientMap`: `S` is a localization of a quotient of `R[x_1, …, x_n]_q`
  for some `n` and some prime `q`.
* `exists_prime_goodPosition_isLocalizationOfQuotient`: for every prime `q ⊆ R[x_1, …, x_n]` the
  ring `R[x_1, …, x_n]_q` is a localization of a quotient of `R[x_1, …, x_{n'}]_{q'}` for a prime
  `q'` in good position.
* `exists_maximalIdeal_liesOver_of_sup_ne_top`: for a prime `q` in good position, there is a
  maximal ideal `𝔪` lying over `𝔪_R` such that `R[x_1, …, x_n]_q` is a localization of a quotient
  of `R[x_1, …, x_n]_𝔪`.

## References

* [Stacks Project, Tag 0AUG](https://stacks.math.columbia.edu/tag/0AUG)
-/

@[expose] public section
-- needed file-wide: `isLocalizationOfQuotientMap_comp`, `quotKerAlgEquivOfSurjective_mk`,
-- `loc_of_quot_of_lift` and `exists_isLocalizationOfQuotientMap` all rewrite through the
-- `Ideal.Quotient`/`Localization` `IsScalarTower` coercions, which only unfold with defeq
-- transparency relaxed.
set_option backward.isDefEq.respectTransparency false

universe u v

/-! ### Localizations of quotients -/

/-- A ring homomorphism `g : B →+* S` exhibits `S` as a localization of a quotient of `B` if there
are an ideal `I ⊆ B`, a ring homomorphism `f : B ⧸ I →+* S` and a submonoid `T` of `B ⧸ I` such
that `g` is the composite `B → B ⧸ I → S` and, with `S` regarded as a `(B ⧸ I)`-algebra via `f`,
`S` is the localization of `B ⧸ I` at `T`. -/
def IsLocalizationOfQuotientMap {B S : Type*} [CommRing B] [CommRing S]
    (g : B →+* S) : Prop :=
  ∃ (I : Ideal B) (f : (B ⧸ I) →+* S) (T : Submonoid (B ⧸ I)),
    g = f.comp (Ideal.Quotient.mk I) ∧
      (letI : Algebra (B ⧸ I) S := f.toAlgebra; IsLocalization T S)

/-! ### Basic properties of `IsLocalizationOfQuotientMap` -/

/-- A localization map is a localization of a quotient map, with the zero ideal. -/
theorem isLocalizationOfQuotientMap_of_isLocalization
    {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    (T : Submonoid B) [IsLocalization T S] :
    IsLocalizationOfQuotientMap (algebraMap B S) := by
  refine ⟨⊥, (algebraMap B S).comp (RingEquiv.quotientBot B).toRingHom,
    Submonoid.map (RingEquiv.quotientBot B).symm.toMonoidHom T, ?_, ?_⟩
  · ext b
    simp [RingEquiv.quotientBot_mk]
  · let : Algebra (B ⧸ (⊥ : Ideal B)) S :=
      ((algebraMap B S).comp (RingEquiv.quotientBot B).toRingHom).toAlgebra
    have := IsLocalization.isLocalization_of_base_ringEquiv T S
      (RingEquiv.quotientBot B).symm
    convert this using 2
    · rfl
    · rw [RingEquiv.symm_symm]

/-- `IsLocalizationOfQuotientMap` is closed under composition: if `g : B →+* C` exhibits `C` as a
localization of a quotient of `B`, and `h : C →+* S` exhibits `S` as a localization of a quotient
of `C`, then `h.comp g` exhibits `S` as a localization of a quotient of `B`. -/
theorem isLocalizationOfQuotientMap_comp
    {B C S : Type*} [CommRing B] [CommRing C] [CommRing S]
    (g : B →+* C) (h : C →+* S)
    (hg : IsLocalizationOfQuotientMap g) (hh : IsLocalizationOfQuotientMap h) :
    IsLocalizationOfQuotientMap (h.comp g) := by
  obtain ⟨I, f, T, hgeq, hgloc⟩ := hg
  obtain ⟨J, f', T', hheq, hhloc⟩ := hh
  let algC : Algebra (B ⧸ I) C := f.toAlgebra
  let algS : Algebra (C ⧸ J) S := f'.toAlgebra
  have hfC : algebraMap (B ⧸ I) C = f := rfl
  have hfS : algebraMap (C ⧸ J) S = f' := rfl
  set J₀ : Ideal (B ⧸ I) := Ideal.comap f J with hJ₀
  have heqJ : Ideal.map (algebraMap (B ⧸ I) C) J₀ = J := by
    rw [hfC]; exact IsLocalization.map_under T C J
  have key := IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap
    (R := B ⧸ I) T C (I := J₀)
  let algR₀C : Algebra ((B ⧸ I) ⧸ J₀) (C ⧸ J) :=
    ((Ideal.quotEquivOfEq heqJ).toRingHom.comp
      (algebraMap ((B ⧸ I) ⧸ J₀) (C ⧸ Ideal.map (algebraMap (B ⧸ I) C) J₀))).toAlgebra
  have part1 : IsLocalization (Algebra.algebraMapSubmonoid ((B ⧸ I) ⧸ J₀) T) (C ⧸ J) :=
    (IsLocalization.isLocalization_iff_of_ringEquiv
      (Algebra.algebraMapSubmonoid ((B ⧸ I) ⧸ J₀) T) (Ideal.quotEquivOfEq heqJ)).mp key
  let algR₀S : Algebra ((B ⧸ I) ⧸ J₀) S :=
    ((algebraMap (C ⧸ J) S).comp (algebraMap ((B ⧸ I) ⧸ J₀) (C ⧸ J))).toAlgebra
  have tower : IsScalarTower ((B ⧸ I) ⧸ J₀) (C ⧸ J) S :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have part2 : IsLocalization
      (IsLocalization.localizationLocalizationSubmodule
        (Algebra.algebraMapSubmonoid ((B ⧸ I) ⧸ J₀) T) T') S :=
    IsLocalization.localization_localization_isLocalization
      (Algebra.algebraMapSubmonoid ((B ⧸ I) ⧸ J₀) T) T' S
  set K : Ideal B := Ideal.comap (Ideal.Quotient.mk I) J₀ with hK
  set I' : Ideal B := I ⊔ K with hI'
  have hmapK : Ideal.map (Ideal.Quotient.mk I) K = J₀ :=
    Ideal.map_comap_of_surjective _ (Ideal.Quotient.mk_surjective) J₀
  let e : B ⧸ I' ≃+* (B ⧸ I) ⧸ J₀ :=
    (DoubleQuot.quotQuotEquivQuotSup I K).symm.trans (Ideal.quotEquivOfEq hmapK)
  have part3 : let _ : Algebra (B ⧸ I') S :=
        ((algebraMap ((B ⧸ I) ⧸ J₀) S).comp e.toRingHom).toAlgebra
      IsLocalization (Submonoid.map e.symm
        (IsLocalization.localizationLocalizationSubmodule
          (Algebra.algebraMapSubmonoid ((B ⧸ I) ⧸ J₀) T) T')) S := by
    have := IsLocalization.isLocalization_of_base_ringEquiv
      (IsLocalization.localizationLocalizationSubmodule
        (Algebra.algebraMapSubmonoid ((B ⧸ I) ⧸ J₀) T) T') S e.symm
    convert this using 2
  refine ⟨I', (algebraMap ((B ⧸ I) ⧸ J₀) S).comp e.toRingHom,
    Submonoid.map e.symm.toMonoidHom
      (IsLocalization.localizationLocalizationSubmodule
        (Algebra.algebraMapSubmonoid ((B ⧸ I) ⧸ J₀) T) T'), ?_, ?_⟩
  · ext b
    rw [hgeq, hheq]
    change f' (Ideal.Quotient.mk J (f (Ideal.Quotient.mk I b))) =
      f' ((algebraMap ((B ⧸ I) ⧸ J₀) (C ⧸ J)) (e (Ideal.Quotient.mk I' b)))
    congr 1
  · exact part3

/-! ### Reduction to a localization of a quotient of `R[x]_q` -/

/-- If `A` is the localization of `P` at `S` and `B` is the localization of `P` at `T` with
`S ≤ T`, then `B` is the localization of `A` at the image of `T`. -/
theorem isLocalization_algebraMapSubmonoid_of_le_aux
    {P : Type*} [CommRing P] {S T : Submonoid P} {A B : Type*} [CommRing A] [CommRing B]
    [Algebra P A] [Algebra P B] [Algebra A B] [IsScalarTower P A B]
    [IsLocalization S A] [IsLocalization T B] (hST : S ≤ T) :
    IsLocalization (Algebra.algebraMapSubmonoid A T) B := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, t, ht, rfl⟩
    rw [← IsScalarTower.algebraMap_apply P A B t]
    exact IsLocalization.map_units B ⟨t, ht⟩
  · intro z
    obtain ⟨⟨p, t⟩, hpt⟩ := IsLocalization.surj T z
    refine ⟨⟨algebraMap P A p, ⟨algebraMap P A t.val, ⟨t.val, t.property, rfl⟩⟩⟩, ?_⟩
    simp only
    rw [← IsScalarTower.algebraMap_apply P A B p, ← IsScalarTower.algebraMap_apply P A B t.val]
    exact hpt
  · intro x y h
    obtain ⟨⟨nx, sx⟩, hx⟩ := IsLocalization.surj S x
    obtain ⟨⟨ny, sy⟩, hy⟩ := IsLocalization.surj S y
    have hxB := congrArg (algebraMap A B) hx
    have hyB := congrArg (algebraMap A B) hy
    simp only [map_mul, ← IsScalarTower.algebraMap_apply P A B] at hxB hyB
    have key : algebraMap P B (nx * sy) = algebraMap P B (ny * sx) := by
      rw [map_mul, map_mul, ← hxB, ← hyB, h]; ring
    rw [IsLocalization.eq_iff_exists T B] at key
    obtain ⟨t, ht⟩ := key
    refine ⟨⟨algebraMap P A (t * sx.val * sy.val), ⟨t * sx.val * sy.val, ?_, rfl⟩⟩, ?_⟩
    · exact mul_mem (mul_mem t.property (hST sx.property)) (hST sy.property)
    · change algebraMap P A (↑t * sx.val * sy.val) * x = algebraMap P A (↑t * sx.val * sy.val) * y
      have ht' := congrArg (algebraMap P A) ht
      simp only [map_mul] at ht' ⊢
      linear_combination (algebraMap P A t * algebraMap P A sy) * hx -
        (algebraMap P A t * algebraMap P A sx) * hy + ht'

/-- Applying `Ideal.quotientKerAlgEquivOfSurjective` to a class `Ideal.Quotient.mk … p`
recovers `f p`. -/
@[sga "3 VIIB 1.3.1" "partial"]
lemma quotKerAlgEquivOfSurjective_mk {R A B : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [CommRing B] [Algebra R B] {f : A →ₐ[R] B} (hf : Function.Surjective f)
    (p : A) :
    (Ideal.quotientKerAlgEquivOfSurjective hf) (Ideal.Quotient.mk (RingHom.ker f.toRingHom) p)
      = f p := by
  rw [Ideal.quotientKerAlgEquivOfSurjective, Ideal.quotientKerAlgEquivOfRightInverse_apply]
  simp [RingHom.kerLift]

/-- Let `B` be a localization of `P` at `M`, and let `ψ : P →+* S` send every element of `M` to a
unit. If `S` is a localization of `P ⧸ ker ψ` at a submonoid `M'`, for the algebra structure
induced by `ψ`, then the lift `B →+* S` of `ψ` exhibits `S` as a localization of a quotient
of `B`. -/
lemma loc_of_quot_of_lift {P S : Type*} [CommRing P] [CommRing S]
    (M : Submonoid P) (B : Type*) [CommRing B] [Algebra P B] [IsLocalization M B]
    (ψ : P →+* S) (hM : ∀ y : M, IsUnit (ψ ↑y))
    (M' : Submonoid (P ⧸ RingHom.ker ψ))
    (hloc' : letI : Algebra (P ⧸ RingHom.ker ψ) S :=
        (Ideal.Quotient.lift (RingHom.ker ψ) ψ (fun _ ha => ha)).toAlgebra
      IsLocalization M' S) :
    IsLocalizationOfQuotientMap (IsLocalization.lift (S := B) hM : B →+* S) := by
  let algQS : Algebra (P ⧸ RingHom.ker ψ) S :=
    (Ideal.Quotient.lift (RingHom.ker ψ) ψ (fun a ha ↦ ha)).toAlgebra
  have hcompat : (algebraMap (P ⧸ RingHom.ker ψ) S)
      = Ideal.Quotient.lift (RingHom.ker ψ) ψ (fun a ha ↦ ha) := rfl
  have : IsLocalization M' S := hloc'
  set g : B →+* S := IsLocalization.lift (S := B) hM with hg
  have hgcomp : g.comp (algebraMap P B) = ψ := IsLocalization.lift_comp hM
  set I : Ideal B := Ideal.map (algebraMap P B) (RingHom.ker ψ) with hI
  have hIleker : I ≤ RingHom.ker g := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro p hp
    exact RingHom.mem_ker.mpr ((RingHom.congr_fun hgcomp p).trans (RingHom.mem_ker.mp hp))
  set f : B ⧸ I →+* S := Ideal.Quotient.lift I g hIleker with hf
  have hgfact : g = f.comp (Ideal.Quotient.mk I) := by rw [hf]; ext b; simp
  have htower : f.comp (algebraMap (P ⧸ RingHom.ker ψ) (B ⧸ I))
      = algebraMap (P ⧸ RingHom.ker ψ) S := by
    ext x
    change f ((algebraMap (P ⧸ RingHom.ker ψ) (B ⧸ I)) (Ideal.Quotient.mk _ x))
        = (algebraMap (P ⧸ RingHom.ker ψ) S) (Ideal.Quotient.mk _ x)
    rw [hcompat, Ideal.Quotient.lift_mk]
    have hAM : algebraMap (P ⧸ RingHom.ker ψ) (B ⧸ I) (Ideal.Quotient.mk _ x)
        = Ideal.Quotient.mk I (algebraMap P B x) := rfl
    rw [hAM, hf, Ideal.Quotient.lift_mk]
    exact RingHom.congr_fun hgcomp x
  set N : Submonoid (P ⧸ RingHom.ker ψ) := Algebra.algebraMapSubmonoid (P ⧸ RingHom.ker ψ) M with hN
  refine ⟨I, f, Algebra.algebraMapSubmonoid (B ⧸ I) (M' ⊔ N), hgfact, ?_⟩
  let algBIS : Algebra (B ⧸ I) S := f.toAlgebra
  have hlocBI : IsLocalization N (B ⧸ I) :=
    IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap M B (RingHom.ker ψ)
  have tower : IsScalarTower (P ⧸ RingHom.ker ψ) (B ⧸ I) S := by
    apply IsScalarTower.of_algebraMap_eq'
    change algebraMap (P ⧸ RingHom.ker ψ) S
        = (algebraMap (B ⧸ I) S).comp (algebraMap (P ⧸ RingHom.ker ψ) (B ⧸ I))
    have hAB : (algebraMap (B ⧸ I) S) = f := rfl
    rw [hAB, htower]
  have hNunit : ∀ x ∈ N, IsUnit (algebraMap (P ⧸ RingHom.ker ψ) S x) := by
    rintro _ ⟨m, hm, rfl⟩
    have heq : algebraMap (P ⧸ RingHom.ker ψ) S (algebraMap P (P ⧸ RingHom.ker ψ) m) = ψ m := by
      rw [hcompat]
      change Ideal.Quotient.lift (RingHom.ker ψ) ψ _ (Ideal.Quotient.mk (RingHom.ker ψ) m) = ψ m
      rw [Ideal.Quotient.lift_mk]
    rw [heq]
    exact hM ⟨m, hm⟩
  have hsub : M' ⊔ N ≤ (IsUnit.submonoid S).comap (algebraMap (P ⧸ RingHom.ker ψ) S) :=
    sup_le (fun x hx ↦ IsLocalization.map_units S ⟨x, hx⟩) (fun x hx ↦ hNunit x hx)
  have hlocS : IsLocalization (M' ⊔ N) S :=
    IsLocalization.of_le M' (M' ⊔ N) le_sup_left fun _ hr ↦ hsub hr
  exact isLocalization_algebraMapSubmonoid_of_le_aux
    (P := P ⧸ RingHom.ker ψ) (S := N) (T := M' ⊔ N) (A := B ⧸ I) (B := S) le_sup_right

/-- If the local ring `S` is essentially of finite type over the local ring `R`, then there are
`n`, a prime `q ⊆ R[x_1, …, x_n]`, and a ring map `g : R[x_1, …, x_n]_q →+* S` compatible with the
`R`-algebra structures exhibiting `S` as a localization of a quotient of `R[x_1, …, x_n]_q`. -/
theorem exists_isLocalizationOfQuotientMap
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [Algebra.EssFiniteType R S] :
    ∃ (n : ℕ) (q : Ideal (MvPolynomial (Fin n) R)) (_ : q.IsPrime)
      (g : Localization.AtPrime q →+* S),
        g.comp (algebraMap R (Localization.AtPrime q)) = algebraMap R S ∧
        IsLocalizationOfQuotientMap g := by
  classical
  obtain ⟨S₀, M, hft, hloc⟩ := (Algebra.essFiniteType_iff_exists_subalgebra R S).mp inferInstance
  obtain ⟨n, φ, hφsurj⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := S₀)).mp
      hft
  set ι : S₀ →+* S := S₀.subtype with hι
  set ψ : MvPolynomial (Fin n) R →+* S := ι.comp φ.toRingHom with hψ
  set q : Ideal (MvPolynomial (Fin n) R) := Ideal.comap ψ (IsLocalRing.maximalIdeal S) with hq
  have hqp : q.IsPrime := Ideal.IsPrime.comap _
  have hunits : ∀ y : q.primeCompl, IsUnit (ψ ↑y) := fun y ↦
    IsLocalRing.notMem_maximalIdeal.mp y.property
  set g : Localization.AtPrime q →+* S :=
    IsLocalization.lift (S := Localization.AtPrime q) hunits with hg
  have hgcomp : g.comp (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime q)) = ψ :=
    IsLocalization.lift_comp hunits
  refine ⟨n, q, hqp, g, ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_eq R (MvPolynomial (Fin n) R) (Localization.AtPrime q),
        ← RingHom.comp_assoc, hgcomp, hψ, RingHom.comp_assoc,
        show φ.toRingHom.comp (algebraMap R (MvPolynomial (Fin n) R)) = algebraMap R S₀ from
          φ.comp_algebraMap, hι]
    ext r
    exact (IsScalarTower.algebraMap_apply R S₀ S r).symm
  · have hkereq : RingHom.ker ψ = RingHom.ker φ.toRingHom := by
      ext x; simp only [RingHom.mem_ker, hψ, RingHom.comp_apply]
      exact ⟨fun h ↦ Subtype.ext h, fun h ↦ by rw [h, map_zero]⟩
    set Q := MvPolynomial (Fin n) R ⧸ RingHom.ker ψ with hQ
    set equivφ : (MvPolynomial (Fin n) R ⧸ RingHom.ker φ.toRingHom) ≃ₐ[R] S₀ :=
      Ideal.quotientKerAlgEquivOfSurjective hφsurj with hequivφ
    set eqQ : Q ≃+* (MvPolynomial (Fin n) R ⧸ RingHom.ker φ.toRingHom) :=
      Ideal.quotEquivOfEq hkereq with heqQ
    set e' : Q ≃+* S₀ := eqQ.trans equivφ.toRingEquiv with he'
    set kl : Q →+* S := Ideal.Quotient.lift (RingHom.ker ψ) ψ (fun a ha ↦ ha) with hkl
    have hcompat : kl = ι.comp e'.toRingHom := by
      refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p ↦ ?_)
      change kl (Ideal.Quotient.mk _ p) = ι (e' (Ideal.Quotient.mk _ p))
      rw [hkl, Ideal.Quotient.lift_mk]
      change ψ p = ι (equivφ (eqQ (Ideal.Quotient.mk (RingHom.ker ψ) p)))
      have hinner : equivφ (eqQ (Ideal.Quotient.mk (RingHom.ker ψ) p)) = φ p := by
        rw [show eqQ (Ideal.Quotient.mk (RingHom.ker ψ) p)
              = Ideal.Quotient.mk (RingHom.ker φ.toRingHom) p from rfl, hequivφ]
        exact quotKerAlgEquivOfSurjective_mk hφsurj p
      rw [hinner]
      rfl
    let algQS : Algebra Q S := kl.toAlgebra
    have hloc' : IsLocalization (Submonoid.map (e'.symm : S₀ →+* Q).toMonoidHom M) S := by
      have := IsLocalization.isLocalization_of_base_ringEquiv M S (e'.symm)
      convert this using 2
      · rfl
      · rw [RingEquiv.symm_symm, hcompat, hι]; rfl
    exact loc_of_quot_of_lift q.primeCompl (Localization.AtPrime q) ψ hunits
      (Submonoid.map (e'.symm : S₀ →+* Q).toMonoidHom M) hloc'

/-! ### Reduction to a prime in good position -/

/-- Let `A` be a valuation subring of a field `κ` and `lam : Fin m → κ` a family with some
`lam i ∉ A`. Then there is an index `i` of maximal valuation, and for it `lam i ≠ 0`,
`(lam i)⁻¹ ∈ A` and `lam j * (lam i)⁻¹ ∈ A` for every `j`. -/
lemma pick_max_val (κ : Type u) [Field κ] (A : ValuationSubring κ) (m : ℕ)
    (lam : Fin m → κ) (hne : ∃ i, lam i ∉ A) :
    ∃ i, (∀ j, A.valuation (lam j) ≤ A.valuation (lam i)) ∧ lam i ≠ 0 ∧ (lam i)⁻¹ ∈ A
      ∧ ∀ j, lam j * (lam i)⁻¹ ∈ A := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin m))
    (fun j ↦ A.valuation (lam j)) ⟨hne.choose, Finset.mem_univ _⟩
  simp only [Finset.mem_univ, true_implies] at hi
  obtain ⟨k, hk⟩ := hne
  have hlt : (1 : A.ValueGroup) < A.valuation (lam i) :=
    not_le.mp fun hmem ↦ hk ((A.valuation_le_one_iff _).mp ((hi k).trans hmem))
  have hne0 : lam i ≠ 0 := by
    rintro h
    simp [h] at hlt
  have hpos : (0 : A.ValueGroup) < A.valuation (lam i) := by
    rw [zero_lt_iff]; simpa using hne0
  refine ⟨i, hi, hne0, ?_, ?_⟩
  · rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, inv_le_one₀ hpos]
    exact hlt.le
  · intro j
    rw [← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀,
        ← div_eq_mul_inv, div_le_one₀ hpos]
    exact hi j

/-- If `f : R →+* κ` is a ring map from a local ring to a field and `f r * f s = 1`, then `r` is
a unit. -/
theorem isUnit_of_mul_map_eq_one_local_aux {R κ : Type*} [CommRing R] [IsLocalRing R]
    [Field κ] (f : R →+* κ) (r s : R) (h : f r * f s = 1) : IsUnit r := by
  have hmem : 1 - r * s ∈ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
      (by rw [RingHom.mem_ker, map_sub, map_one, map_mul, h, sub_self])
  exact isUnit_of_mul_isUnit_left ((IsLocalRing.isUnit_or_isUnit_one_sub_self (r * s)).resolve_right
    ((IsLocalRing.mem_maximalIdeal _).mp hmem))

/-- If a ring map `σ : R[x_1, …, x_n] →+* κ` to a field sends `R` and all variables into a valuation
subring `A` dominating the image of `R`, then every ideal inside `ker σ` is in good position. -/
private theorem sup_maximalIdeal_ne_top_of_valuationSubring
    {R : Type u} [CommRing R] [IsLocalRing R] {n : ℕ} {κ : Type*} [Field κ]
    (A : ValuationSubring κ) (σ : MvPolynomial (Fin n) R →+* κ)
    (hArange : LocalSubring.range (σ.comp (algebraMap R (MvPolynomial (Fin n) R)))
      ≤ A.toLocalSubring)
    (hmemX : ∀ j, σ (MvPolynomial.X j) ∈ A)
    (q : Ideal (MvPolynomial (Fin n) R)) (hq : ∀ p ∈ q, σ p = 0) :
    q ⊔ (IsLocalRing.maximalIdeal R).map (algebraMap R (MvPolynomial (Fin n) R)) ≠ ⊤ := by
  set P := MvPolynomial (Fin n) R with hP
  set f : R →+* κ := σ.comp (algebraMap R P) with hf
  obtain ⟨hsubA, hinclLocal⟩ := LocalSubring.le_def.mp hArange
  have hmemC : ∀ r : R, σ (algebraMap R P r) ∈ A := fun r ↦
    hsubA (⟨r, rfl⟩ : f r ∈ (LocalSubring.range f).toSubring)
  set gR : R →+* A := (σ.comp (algebraMap R P)).codRestrict A.toSubring hmemC with hgR
  set wA : Fin n → A := fun j ↦ ⟨σ (MvPolynomial.X j), hmemX j⟩ with hwA
  set τ : P →+* A := MvPolynomial.eval₂Hom gR wA with hτ
  have hsubtypeτ : (A.toSubring.subtype).comp τ = σ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change A.toSubring.subtype (τ (MvPolynomial.C r)) = σ (MvPolynomial.C r)
      rw [hτ, MvPolynomial.eval₂Hom_C]
      change (gR r : κ) = σ (MvPolynomial.C r)
      rw [hgR]
      change σ (algebraMap R P r) = σ (MvPolynomial.C r)
      rw [MvPolynomial.algebraMap_eq]
    · intro j
      change A.toSubring.subtype (τ (MvPolynomial.X j)) = σ (MvPolynomial.X j)
      rw [hτ, MvPolynomial.eval₂Hom_X']
      rfl
  have hsubtypeτ' : ∀ p : P, (τ p : κ) = σ p := fun p ↦ RingHom.congr_fun hsubtypeτ p
  have hgRlocal : ∀ r : R, IsUnit (gR r) → IsUnit r := by
    intro r hur
    have hmemf : f r ∈ (LocalSubring.range f).toSubring := ⟨r, rfl⟩
    have hval : (gR r : κ) = f r := by rw [hgR]; rfl
    have hinclpt : (Subring.inclusion hsubA ⟨f r, hmemf⟩ : A) = gR r := by
      apply Subtype.ext; rw [hval]; rfl
    have hunitincl : IsUnit (Subring.inclusion hsubA ⟨f r, hmemf⟩) := by rw [hinclpt]; exact hur
    have hunitrange : IsUnit (⟨f r, hmemf⟩ : (LocalSubring.range f).toSubring) :=
      hinclLocal.map_nonunit _ hunitincl
    obtain ⟨u, hu⟩ := hunitrange
    obtain ⟨s, hs⟩ := (↑u⁻¹ : ↥(LocalSubring.range f).toSubring).property
    have hmul1 : f r * f s = 1 := by
      simpa only [Subring.coe_mul, Subring.coe_one, hu, ← hs] using congrArg Subtype.val u.mul_inv
    exact isUnit_of_mul_map_eq_one_local_aux f r s hmul1
  set mA := IsLocalRing.maximalIdeal A with hmA
  set I : Ideal P := Ideal.comap τ mA with hI
  have hqleI : q ≤ I := fun p hp ↦ by
    rw [hI, Ideal.mem_comap,
      show τ p = 0 from Subtype.ext ((hsubtypeτ' p).trans (hq p hp))]
    exact Ideal.zero_mem _
  have hMleI : (IsLocalRing.maximalIdeal R).map (algebraMap R P) ≤ I := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, hI, Ideal.mem_comap]
    have hτeq : τ (algebraMap R P r) = gR r := by
      apply Subtype.ext
      rw [hsubtypeτ' (algebraMap R P r), hgR]; rfl
    rw [hτeq, hmA, IsLocalRing.mem_maximalIdeal]
    intro hu
    exact ((IsLocalRing.mem_maximalIdeal r).mp hr) (hgRlocal r hu)
  have hIne : I ≠ ⊤ := by
    rw [Ne, Ideal.eq_top_iff_one, hI, Ideal.mem_comap, map_one, hmA, IsLocalRing.mem_maximalIdeal]
    simp
  exact fun htop ↦ hIne (eq_top_iff.mpr (htop.symm.trans_le (sup_le hqleI hMleI)))

/-- Let `q ⊆ R[x_1, …, x_n]` be a prime with `q ⊔ 𝔪_R R[x_1, …, x_n] = ⊤`, and let `A` be a
valuation subring of the fraction field `κ(q)` of `R[x_1, …, x_n] ⧸ q` dominating the image of `R`.
Then some variable `X i` maps outside `A`. -/
lemma exists_var_notMem_valuationSubring
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ)
    (q : Ideal (MvPolynomial (Fin n) R)) (hq : q.IsPrime)
    (hbad : q ⊔ (IsLocalRing.maximalIdeal R).map (algebraMap R (MvPolynomial (Fin n) R)) = ⊤) :
    haveI : q.IsPrime := hq
    haveI : IsDomain (MvPolynomial (Fin n) R ⧸ q) := Ideal.Quotient.isDomain q
    ∀ (A : ValuationSubring (FractionRing (MvPolynomial (Fin n) R ⧸ q))),
      LocalSubring.range
          (((algebraMap (MvPolynomial (Fin n) R ⧸ q)
              (FractionRing (MvPolynomial (Fin n) R ⧸ q))).comp
            (Ideal.Quotient.mk q)).comp (algebraMap R (MvPolynomial (Fin n) R)))
          ≤ A.toLocalSubring →
      ∃ i, ((algebraMap (MvPolynomial (Fin n) R ⧸ q)
              (FractionRing (MvPolynomial (Fin n) R ⧸ q))).comp
            (Ideal.Quotient.mk q)) (MvPolynomial.X i) ∉ A := by
  have := hq
  have : IsDomain (MvPolynomial (Fin n) R ⧸ q) := Ideal.Quotient.isDomain q
  intro A hArange
  by_contra hcon
  push Not at hcon
  exact sup_maximalIdeal_ne_top_of_valuationSubring A _ hArange hcon q
    (fun p hp ↦ by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]) hbad

/-- The localization lift `g : R[x]_{q'} →+* L` of a ring map `Φ : R[x] →+* L`
into a local ring `L`, where `q' = comap Φ (maximalIdeal L)`, is a *local* ring
homomorphism. -/
theorem lift_isLocalHom_of_comap {P L : Type*} [CommRing P] [CommRing L] [IsLocalRing L]
    (Φ : P →+* L) (q' : Ideal P) [hq'p : q'.IsPrime]
    (hq' : q' = Ideal.comap Φ (IsLocalRing.maximalIdeal L))
    (hu : ∀ y : q'.primeCompl, IsUnit (Φ ↑y)) :
    IsLocalHom (IsLocalization.lift (S := Localization.AtPrime q') hu) := by
  set g := IsLocalization.lift (S := Localization.AtPrime q') hu with hg
  have hgcomp : ∀ z : P, g (algebraMap P (Localization.AtPrime q') z) = Φ z := fun z ↦
    RingHom.congr_fun (IsLocalization.lift_comp (S := Localization.AtPrime q') hu) z
  constructor
  intro a hua
  obtain ⟨⟨num, den⟩, hd⟩ := IsLocalization.surj q'.primeCompl a
  have key : g a * Φ den.val = Φ num := by rw [← hgcomp, ← hgcomp, ← map_mul, hd]
  have hnum : IsUnit (Φ num) := by rw [← key]; exact hua.mul (hu den)
  have hnotmem : num ∉ q' := by
    rw [hq']
    exact IsLocalRing.notMem_maximalIdeal.mpr hnum
  have hanum : IsUnit (algebraMap P (Localization.AtPrime q') num) :=
    IsLocalization.map_units _ (⟨num, hnotmem⟩ : q'.primeCompl)
  rw [← hd] at hanum
  exact isUnit_of_mul_isUnit_left hanum

/-- A bijective ring homomorphism exhibits its target as a localization of a quotient of its
source. -/
theorem bij_isLocOfQuot {B S : Type*} [CommRing B] [CommRing S]
    (g : B →+* S) (hg : Function.Bijective g) :
    IsLocalizationOfQuotientMap g := by
  let : Algebra B S := g.toAlgebra
  have hga : g = algebraMap B S := rfl
  have : IsLocalization (⊥ : Submonoid B) S := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, hm⟩
      rw [Submonoid.mem_bot] at hm
      subst hm
      simp
    · intro z
      obtain ⟨b, rfl⟩ := hg.surjective z
      exact ⟨⟨b, 1⟩, by simp [hga]⟩
    · exact fun h ↦ ⟨1, hg.injective (by simpa [hga] using h)⟩
  exact isLocalizationOfQuotientMap_of_isLocalization (⊥ : Submonoid B)

/-- If `f : R →+* κ` is a ring map from a local ring to a field and `f r * f s = 1`, then `r` is
a unit. -/
alias isUnit_of_mul_map_eq_one_local := isUnit_of_mul_map_eq_one_local_aux

/-- Let `q ⊆ R[x_1, …, x_n]` be a prime and `A` a valuation subring of the fraction field `κ(q)` of
`R[x_1, …, x_n] ⧸ q` dominating the image of `R`. Let `i` be an index with `X i ∉ q` such that,
writing `λ_j` for the image of `X j` in `κ(q)`, `λ_i⁻¹ ∈ A` and `λ_j λ_i⁻¹ ∈ A` for all `j`. Then
there are `n'`, a prime `q' ⊆ R[x_1, …, x_{n'}]` in good position, and a ring map
`R[x_1, …, x_{n'}]_{q'} →+* R[x_1, …, x_n]_q` compatible with the `R`-algebra structures
exhibiting `R[x_1, …, x_n]_q` as a localization of a quotient of `R[x_1, …, x_{n'}]_{q'}`. -/
lemma exists_goodPosition_isLocalizationOfQuotientMap
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ)
    (q : Ideal (MvPolynomial (Fin n) R)) (hq : q.IsPrime)
    (i : Fin n)
    (hxi : MvPolynomial.X i ∉ q)
    (A : (haveI : q.IsPrime := hq
          haveI : IsDomain (MvPolynomial (Fin n) R ⧸ q) := Ideal.Quotient.isDomain q
          ValuationSubring (FractionRing (MvPolynomial (Fin n) R ⧸ q))))
    (hArange :
      haveI : q.IsPrime := hq
      haveI : IsDomain (MvPolynomial (Fin n) R ⧸ q) := Ideal.Quotient.isDomain q
      LocalSubring.range
          (((algebraMap (MvPolynomial (Fin n) R ⧸ q)
              (FractionRing (MvPolynomial (Fin n) R ⧸ q))).comp
            (Ideal.Quotient.mk q)).comp (algebraMap R (MvPolynomial (Fin n) R)))
          ≤ A.toLocalSubring)
    (hAvars :
      haveI : q.IsPrime := hq
      haveI : IsDomain (MvPolynomial (Fin n) R ⧸ q) := Ideal.Quotient.isDomain q
      ∀ j, ((algebraMap (MvPolynomial (Fin n) R ⧸ q)
              (FractionRing (MvPolynomial (Fin n) R ⧸ q))).comp
            (Ideal.Quotient.mk q)) (MvPolynomial.X j)
          * (((algebraMap (MvPolynomial (Fin n) R ⧸ q)
              (FractionRing (MvPolynomial (Fin n) R ⧸ q))).comp
            (Ideal.Quotient.mk q)) (MvPolynomial.X i))⁻¹ ∈ A)
    (hAinv :
      haveI : q.IsPrime := hq
      haveI : IsDomain (MvPolynomial (Fin n) R ⧸ q) := Ideal.Quotient.isDomain q
      (((algebraMap (MvPolynomial (Fin n) R ⧸ q)
          (FractionRing (MvPolynomial (Fin n) R ⧸ q))).comp
        (Ideal.Quotient.mk q)) (MvPolynomial.X i))⁻¹ ∈ A) :
    ∃ (n' : ℕ) (q' : Ideal (MvPolynomial (Fin n') R)) (_ : q'.IsPrime),
      q' ⊔ (IsLocalRing.maximalIdeal R).map (algebraMap R (MvPolynomial (Fin n') R)) ≠ ⊤ ∧
      ∃ (g : Localization.AtPrime q' →+* Localization.AtPrime q),
        g.comp (algebraMap R (Localization.AtPrime q')) = algebraMap R (Localization.AtPrime q) ∧
        IsLocalizationOfQuotientMap g := by
  classical
  have : q.IsPrime := hq
  have : IsDomain (MvPolynomial (Fin n) R ⧸ q) := Ideal.Quotient.isDomain q
  set P := MvPolynomial (Fin n) R with hP
  set Lq := Localization.AtPrime q with hLq
  set aq := algebraMap P Lq with haq
  have hxiU : IsUnit (aq (MvPolynomial.X i)) :=
    IsLocalization.map_units Lq (⟨MvPolynomial.X i, hxi⟩ : q.primeCompl)
  set xiI : Lq := ↑hxiU.unit⁻¹ with hxiI
  have hxiIU : IsUnit xiI := (hxiU.unit⁻¹).isUnit
  have hmul : aq (MvPolynomial.X i) * xiI = 1 := hxiU.mul_val_inv
  have hmul' : xiI * aq (MvPolynomial.X i) = 1 := hxiU.val_inv_mul
  set v : Fin n → Lq := fun j ↦ if j = i then xiI else aq (MvPolynomial.X j) * xiI with hv
  have hvi : v i = xiI := by rw [hv]; simp
  have hvj : ∀ j, j ≠ i → v j = aq (MvPolynomial.X j) * xiI := fun j hj ↦ by rw [hv]; simp [hj]
  set Φ : P →ₐ[R] Lq := MvPolynomial.aeval v with hΦ
  have hΦX : ∀ j, Φ (MvPolynomial.X j) = v j := fun j ↦ by rw [hΦ, MvPolynomial.aeval_X]
  set q' : Ideal P := Ideal.comap Φ.toRingHom (IsLocalRing.maximalIdeal Lq) with hq'
  have hq'p : q'.IsPrime := Ideal.IsPrime.comap _
  set Lq' := Localization.AtPrime q' with hLq'
  set aq' := algebraMap P Lq' with haq'
  have hunits_g : ∀ y : q'.primeCompl, IsUnit (Φ.toRingHom ↑y) := fun y ↦
    IsLocalRing.notMem_maximalIdeal.mp y.property
  set g : Lq' →+* Lq := IsLocalization.lift hunits_g with hg
  have hgcomp' : ∀ z : P, g (aq' z) = Φ z := fun z ↦
    RingHom.congr_fun (IsLocalization.lift_comp (S := Lq') hunits_g) z
  have hglocal : IsLocalHom g := lift_isLocalHom_of_comap Φ.toRingHom q' hq' hunits_g
  have hxi' : MvPolynomial.X i ∉ q' := by
    intro hmem
    have hh : Φ (MvPolynomial.X i) ∈ IsLocalRing.maximalIdeal Lq := hmem
    rw [hΦX, hvi] at hh; exact (IsLocalRing.notMem_maximalIdeal.mpr hxiIU) hh
  have huxi' : IsUnit (aq' (MvPolynomial.X i)) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff Lq' q' (MvPolynomial.X i)).mpr hxi'
  set yiI : Lq' := ↑huxi'.unit⁻¹ with hyiI
  have hyiIU : IsUnit yiI := (huxi'.unit⁻¹).isUnit
  have hmulY : aq' (MvPolynomial.X i) * yiI = 1 := huxi'.mul_val_inv
  have hmulY' : yiI * aq' (MvPolynomial.X i) = 1 := huxi'.val_inv_mul
  set w : Fin n → Lq' := fun j ↦ if j = i then yiI else aq' (MvPolynomial.X j) * yiI with hw
  have hwi : w i = yiI := by rw [hw]; simp
  have hwj : ∀ j, j ≠ i → w j = aq' (MvPolynomial.X j) * yiI := fun j hj ↦ by rw [hw]; simp [hj]
  set Ψ : P →ₐ[R] Lq' := MvPolynomial.aeval w with hΨ
  have hΨX : ∀ j, Ψ (MvPolynomial.X j) = w j := fun j ↦ by rw [hΨ, MvPolynomial.aeval_X]
  have hgyiI : g yiI = aq (MvPolynomial.X i) := by
    have h1 : g yiI * g (aq' (MvPolynomial.X i)) = 1 := by rw [← map_mul, hmulY', map_one]
    rw [hgcomp', hΦX, hvi] at h1
    have h2 : g yiI * xiI = aq (MvPolynomial.X i) * xiI := by rw [h1, hmul]
    exact IsUnit.mul_right_cancel hxiIU h2
  have hgΨ : g.comp Ψ.toRingHom = aq := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change g (Ψ (MvPolynomial.C r)) = aq (MvPolynomial.C r)
      rw [hΨ, MvPolynomial.aeval_C,
        show algebraMap R Lq' r = aq' (MvPolynomial.C r) by
          rw [IsScalarTower.algebraMap_apply R P Lq', MvPolynomial.algebraMap_eq],
        hgcomp', hΦ, MvPolynomial.aeval_C,
        show algebraMap R Lq r = aq (MvPolynomial.C r) by
          rw [IsScalarTower.algebraMap_apply R P Lq, MvPolynomial.algebraMap_eq]]
    · intro j
      change g (Ψ (MvPolynomial.X j)) = aq (MvPolynomial.X j)
      rw [hΨX]
      by_cases hj : j = i
      · subst hj; rw [hwi, hgyiI]
      · rw [hwj j hj, map_mul, hgcomp', hΦX, hvj j hj, hgyiI, mul_assoc, hmul', mul_one]
  have hgΨ' : ∀ z : P, g (Ψ z) = aq z := fun z ↦ RingHom.congr_fun hgΨ z
  have hΨunits : ∀ y : q.primeCompl, IsUnit (Ψ.toRingHom ↑y) := by
    intro y
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hmem
    have hgmem : g (Ψ ↑y) ∈ IsLocalRing.maximalIdeal Lq := by
      by_contra hu
      have hu' : IsUnit (g (Ψ ↑y)) := IsLocalRing.notMem_maximalIdeal.mp hu
      exact (IsLocalRing.notMem_maximalIdeal.mpr (hglocal.map_nonunit _ hu')) hmem
    rw [hgΨ'] at hgmem
    exact y.property ((IsLocalization.AtPrime.to_map_mem_maximal_iff Lq q ↑y).mp hgmem)
  set g' : Lq →+* Lq' := IsLocalization.lift hΨunits with hg'
  have hg'comp : ∀ z : P, g' (aq z) = Ψ z := fun z ↦
    RingHom.congr_fun (IsLocalization.lift_comp (S := Lq) hΨunits) z
  have hg'xiI : g' xiI = aq' (MvPolynomial.X i) := by
    have h1 : g' xiI * g' (aq (MvPolynomial.X i)) = 1 := by rw [← map_mul, hmul', map_one]
    rw [hg'comp, hΨX, hwi] at h1
    have h2 : g' xiI * yiI = aq' (MvPolynomial.X i) * yiI := by rw [h1, hmulY]
    exact IsUnit.mul_right_cancel hyiIU h2
  have hg'Φ : g'.comp Φ.toRingHom = aq' := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change g' (Φ (MvPolynomial.C r)) = aq' (MvPolynomial.C r)
      rw [hΦ, MvPolynomial.aeval_C,
        show algebraMap R Lq r = aq (MvPolynomial.C r) by
          rw [IsScalarTower.algebraMap_apply R P Lq, MvPolynomial.algebraMap_eq],
        hg'comp, hΨ, MvPolynomial.aeval_C,
        show algebraMap R Lq' r = aq' (MvPolynomial.C r) by
          rw [IsScalarTower.algebraMap_apply R P Lq', MvPolynomial.algebraMap_eq]]
    · intro j
      change g' (Φ (MvPolynomial.X j)) = aq' (MvPolynomial.X j)
      rw [hΦX]
      by_cases hj : j = i
      · subst hj; rw [hvi, hg'xiI]
      · rw [hvj j hj, map_mul, hg'comp, hΨX, hwj j hj, hg'xiI, mul_assoc, hmulY', mul_one]
  have hgg' : g.comp g' = RingHom.id Lq := by
    apply IsLocalization.ringHom_ext q.primeCompl
    change (g.comp g').comp aq = (RingHom.id Lq).comp aq
    rw [RingHom.comp_assoc]
    have : g'.comp aq = Ψ.toRingHom := RingHom.ext (fun z ↦ hg'comp z)
    rw [this, hgΨ, RingHom.id_comp]
  have hg'g : g'.comp g = RingHom.id Lq' := by
    apply IsLocalization.ringHom_ext q'.primeCompl
    change (g'.comp g).comp aq' = (RingHom.id Lq').comp aq'
    rw [RingHom.comp_assoc]
    have : g.comp aq' = Φ.toRingHom := RingHom.ext (fun z ↦ hgcomp' z)
    rw [this, hg'Φ, RingHom.id_comp]
  have hbij : Function.Bijective g :=
    ⟨Function.LeftInverse.injective (g := g') fun a ↦ RingHom.congr_fun hg'g a,
      Function.RightInverse.surjective (g := g') fun y ↦ RingHom.congr_fun hgg' y⟩
  refine ⟨n, q', hq'p, ?_, g, ?_, ?_⟩
  · set κ := FractionRing (MvPolynomial (Fin n) R ⧸ q) with hκ
    set toκ : P →+* κ := ((algebraMap (MvPolynomial (Fin n) R ⧸ q) κ).comp (Ideal.Quotient.mk q))
        with htoκ
    have hkill : ∀ p : P, toκ p = 0 ↔ p ∈ q := fun p ↦ by
      rw [htoκ, RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff]
      exact Ideal.Quotient.eq_zero_iff_mem
    have hru : ∀ y : q.primeCompl, IsUnit (toκ ↑y) := by
      intro y; rw [isUnit_iff_ne_zero]; intro h; exact y.property ((hkill _).mp h)
    set ρ : Lq →+* κ := IsLocalization.lift (S := Lq) hru with hρ
    have hρaq : ∀ p : P, ρ (aq p) = toκ p := fun p ↦
      RingHom.congr_fun (IsLocalization.lift_comp (S := Lq) hru) p
    have hkerρ : ∀ x : Lq, ρ x = 0 ↔ x ∈ IsLocalRing.maximalIdeal Lq := by
      intro x
      obtain ⟨⟨a, s⟩, hx⟩ := IsLocalization.mk'_surjective q.primeCompl x
      simp only at hx
      subst hx
      rw [hρ, IsLocalization.lift_mk', IsLocalization.AtPrime.mk'_mem_maximal_iff Lq q a s, ← hkill
          a]
      exact mul_eq_zero_iff_right (Units.ne_zero _)
    set σ : P →+* κ := ρ.comp Φ.toRingHom with hσ
    have hσX : ∀ j, σ (MvPolynomial.X j) = ρ (v j) := fun j ↦ by
      rw [hσ, RingHom.comp_apply]; congr 1; exact hΦX j
    have hρxiI : ρ xiI = (toκ (MvPolynomial.X i))⁻¹ := by
      have h1 : ρ (aq (MvPolynomial.X i)) * ρ xiI = 1 := by rw [← map_mul, hmul, map_one]
      rw [hρaq] at h1
      exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1)
    have hσXi : σ (MvPolynomial.X i) = (toκ (MvPolynomial.X i))⁻¹ := by
      rw [hσX, hvi, hρxiI]
    have hσXj : ∀ j, j ≠ i →
        σ (MvPolynomial.X j) = toκ (MvPolynomial.X j) * (toκ (MvPolynomial.X i))⁻¹ := by
      intro j hj
      rw [hσX, hvj j hj, map_mul, hρaq, hρxiI]
    have hσC : ∀ r : R, σ (algebraMap R P r) = toκ (algebraMap R P r) := by
      intro r
      rw [hσ, RingHom.comp_apply]
      rw [show Φ.toRingHom (algebraMap R P r) = aq (algebraMap R P r) from ?_, hρaq]
      · change Φ (algebraMap R P r) = aq (algebraMap R P r)
        rw [show aq (algebraMap R P r) = algebraMap R Lq r from
          (IsScalarTower.algebraMap_apply R P Lq r).symm, Φ.commutes]
    have hmemX : ∀ j, σ (MvPolynomial.X j) ∈ A := by
      intro j
      by_cases hj : j = i
      · subst hj; rw [hσXi]; exact hAinv
      · rw [hσXj j hj]; exact hAvars j
    have hkerσ : ∀ p : P, p ∈ q' ↔ σ p = 0 := by
      intro p
      rw [hq']
      change Φ.toRingHom p ∈ IsLocalRing.maximalIdeal Lq ↔ σ p = 0
      rw [← hkerρ (Φ.toRingHom p), hσ]; rfl
    have hσf : σ.comp (algebraMap R P) = toκ.comp (algebraMap R P) := RingHom.ext hσC
    exact fun htop ↦ sup_maximalIdeal_ne_top_of_valuationSubring A σ (hσf ▸ hArange) hmemX q'
      (fun p hp ↦ (hkerσ p).mp hp) htop
  · change g.comp (algebraMap R Lq') = algebraMap R Lq
    rw [IsScalarTower.algebraMap_eq R P Lq', ← RingHom.comp_assoc,
      show g.comp aq' = Φ.toRingHom from RingHom.ext hgcomp']
    exact AlgHom.comp_algebraMap Φ
  · exact bij_isLocOfQuot g hbij

open MvPolynomial in
/-- If the prime `q ⊆ R[x_1, …, x_n]` is not in good position, i.e. `q ⊔ 𝔪_R R[x_1, …, x_n] = ⊤`,
then there are `n'`, a prime `q' ⊆ R[x_1, …, x_{n'}]` in good position, and a ring map
`R[x_1, …, x_{n'}]_{q'} →+* R[x_1, …, x_n]_q` compatible with the `R`-algebra structures
exhibiting `R[x_1, …, x_n]_q` as a localization of a quotient of `R[x_1, …, x_{n'}]_{q'}`. -/
theorem exists_goodPosition_prime_localization
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ)
    (q : Ideal (MvPolynomial (Fin n) R)) (hq : q.IsPrime)
    (hbad : q ⊔ (IsLocalRing.maximalIdeal R).map (algebraMap R (MvPolynomial (Fin n) R)) = ⊤) :
    ∃ (n' : ℕ) (q' : Ideal (MvPolynomial (Fin n') R)) (_ : q'.IsPrime),
      q' ⊔ (IsLocalRing.maximalIdeal R).map (algebraMap R (MvPolynomial (Fin n') R)) ≠ ⊤ ∧
      ∃ (g : Localization.AtPrime q' →+* Localization.AtPrime q),
        g.comp (algebraMap R (Localization.AtPrime q')) = algebraMap R (Localization.AtPrime q) ∧
        IsLocalizationOfQuotientMap g := by
  have : q.IsPrime := hq
  have : IsDomain (MvPolynomial (Fin n) R ⧸ q) := Ideal.Quotient.isDomain q
  set κ := FractionRing (MvPolynomial (Fin n) R ⧸ q) with hκ
  set toκ : MvPolynomial (Fin n) R →+* κ :=
    (algebraMap (MvPolynomial (Fin n) R ⧸ q) κ).comp (Ideal.Quotient.mk q) with htoκ
  set RtoκRingHom : R →+* κ := toκ.comp (algebraMap R (MvPolynomial (Fin n) R)) with hRtoκ
  obtain ⟨A, hA⟩ := (LocalSubring.range RtoκRingHom).exists_le_valuationSubring
  obtain ⟨i, hi⟩ := exists_var_notMem_valuationSubring R n q hq hbad A hA
  obtain ⟨i₀, _, hlamne, hinv, hvars⟩ :=
    pick_max_val κ A n (fun j ↦ toκ (MvPolynomial.X j)) ⟨i, hi⟩
  have hxi : MvPolynomial.X i₀ ∉ q := fun hmem ↦ hlamne <| by
    change toκ (MvPolynomial.X i₀) = 0
    rw [htoκ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
  exact exists_goodPosition_isLocalizationOfQuotientMap R n q hq i₀ hxi A hA hvars hinv

/-- For every prime `q ⊆ R[x_1, …, x_n]` there are `n'`, a prime `q' ⊆ R[x_1, …, x_{n'}]` in good
position, i.e. `q' ⊔ 𝔪_R R[x_1, …, x_{n'}] ≠ ⊤`, and a ring map
`R[x_1, …, x_{n'}]_{q'} →+* R[x_1, …, x_n]_q` compatible with the `R`-algebra structures
exhibiting `R[x_1, …, x_n]_q` as a localization of a quotient of `R[x_1, …, x_{n'}]_{q'}`. -/
theorem exists_prime_goodPosition_isLocalizationOfQuotient
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ)
    (q : Ideal (MvPolynomial (Fin n) R)) (hq : q.IsPrime) :
    ∃ (n' : ℕ) (q' : Ideal (MvPolynomial (Fin n') R)) (_ : q'.IsPrime),
      q' ⊔ (IsLocalRing.maximalIdeal R).map (algebraMap R (MvPolynomial (Fin n') R)) ≠ ⊤ ∧
      ∃ (g : Localization.AtPrime q' →+* Localization.AtPrime q),
        g.comp (algebraMap R (Localization.AtPrime q')) = algebraMap R (Localization.AtPrime q) ∧
        IsLocalizationOfQuotientMap g := by
  by_cases hgood : q ⊔ (IsLocalRing.maximalIdeal R).map
      (algebraMap R (MvPolynomial (Fin n) R)) = ⊤
  · exact exists_goodPosition_prime_localization R n q hq hgood
  · exact ⟨n, q, hq, hgood, RingHom.id _, by simp, bij_isLocOfQuot _ Function.bijective_id⟩

/-! ### The good case -/

/-- If `A` is the localization of `P` at `S` and `B` is the localization of `P` at `T` with
`S ≤ T`, then `B` is the localization of `A` at the image of `T`. -/
@[ega "0 1.4.6" "special case", ega "0 7.6.8" "partial"]
alias isLocalization_algebraMapSubmonoid_of_le := isLocalization_algebraMapSubmonoid_of_le_aux

/-- If a prime `q ⊆ R[x_1, …, x_n]` is in good position, i.e. `q ⊔ 𝔪_R R[x_1, …, x_n] ≠ ⊤`, then
there are a maximal ideal `𝔪 ⊆ R[x_1, …, x_n]` lying over `𝔪_R` and a ring map
`g : R[x_1, …, x_n]_𝔪 →+* R[x_1, …, x_n]_q` compatible with the `R`-algebra structures exhibiting
`R[x_1, …, x_n]_q` as a localization of a quotient of `R[x_1, …, x_n]_𝔪`. -/
theorem exists_maximalIdeal_liesOver_of_sup_ne_top
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ)
    (q : Ideal (MvPolynomial (Fin n) R)) (hq : q.IsPrime)
    (hgood : q ⊔ (IsLocalRing.maximalIdeal R).map (algebraMap R (MvPolynomial (Fin n) R)) ≠ ⊤) :
    ∃ (𝔪 : Ideal (MvPolynomial (Fin n) R)) (_ : 𝔪.IsMaximal),
      haveI : 𝔪.IsPrime := (‹𝔪.IsMaximal›).isPrime
      𝔪.comap (algebraMap R (MvPolynomial (Fin n) R)) = IsLocalRing.maximalIdeal R ∧
      ∃ (g : Localization.AtPrime 𝔪 →+* Localization.AtPrime q),
        g.comp (algebraMap R (Localization.AtPrime 𝔪)) = algebraMap R (Localization.AtPrime q) ∧
        IsLocalizationOfQuotientMap g := by
  set P := MvPolynomial (Fin n) R
  obtain ⟨𝔪, h𝔪max, h𝔪le⟩ := Ideal.exists_le_maximal _ hgood
  have hqm : q ≤ 𝔪 := le_trans le_sup_left h𝔪le
  have hmRm : (IsLocalRing.maximalIdeal R).map (algebraMap R P) ≤ 𝔪 := le_trans le_sup_right h𝔪le
  have : 𝔪.IsPrime := h𝔪max.isPrime
  refine ⟨𝔪, h𝔪max, ?_, ?_⟩
  · exact le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ h𝔪max.ne_top))
      (Ideal.map_le_iff_le_comap.mp hmRm)
  · have hcompl : 𝔪.primeCompl ≤ q.primeCompl := fun _ hx hh ↦ hx (hqm hh)
    have hunits : ∀ y : 𝔪.primeCompl, IsUnit (algebraMap P (Localization.AtPrime q) y) := fun y ↦
      IsLocalization.map_units (Localization.AtPrime q) (⟨y.val, hcompl y.property⟩ : q.primeCompl)
    let g : Localization.AtPrime 𝔪 →+* Localization.AtPrime q := IsLocalization.lift hunits
    have hgcomp : g.comp (algebraMap P (Localization.AtPrime 𝔪))
        = algebraMap P (Localization.AtPrime q) := IsLocalization.lift_comp hunits
    let algMq : Algebra (Localization.AtPrime 𝔪) (Localization.AtPrime q) := g.toAlgebra
    have tower : IsScalarTower P (Localization.AtPrime 𝔪) (Localization.AtPrime q) :=
      IsScalarTower.of_algebraMap_eq' hgcomp.symm
    have isLoc : IsLocalization
        (Algebra.algebraMapSubmonoid (Localization.AtPrime 𝔪) q.primeCompl)
          (Localization.AtPrime q) :=
      isLocalization_algebraMapSubmonoid_of_le hcompl
    refine ⟨g, ?_, ?_⟩
    · rw [show algebraMap R (Localization.AtPrime 𝔪)
            = (algebraMap P (Localization.AtPrime 𝔪)).comp (algebraMap R P) from
          IsScalarTower.algebraMap_eq R P (Localization.AtPrime 𝔪),
        ← RingHom.comp_assoc, hgcomp,
        ← IsScalarTower.algebraMap_eq R P (Localization.AtPrime q)]
    · exact isLocalizationOfQuotientMap_of_isLocalization
        (Algebra.algebraMapSubmonoid (Localization.AtPrime 𝔪) q.primeCompl)

/-! ### Main statement -/

/-- Let `R → S` be a ring map of local rings, not necessarily local, that is essentially of finite
type. Then there are `n : ℕ` and a maximal ideal `𝔪 ⊆ R[x_1, …, x_n]` lying over the maximal ideal
of `R` such that `S` is a localization of a quotient of the local ring `R[x_1, …, x_n]_𝔪`,
compatibly with the `R`-algebra structures. -/
@[stacks 0AUG]
theorem exists_isLocalizationOfQuotientMap_mvPolynomial_atMaximal
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [Algebra.EssFiniteType R S] :
    ∃ (n : ℕ) (𝔪 : Ideal (MvPolynomial (Fin n) R)) (_ : 𝔪.IsMaximal),
      haveI : 𝔪.IsPrime := (‹𝔪.IsMaximal›).isPrime
      𝔪.comap (algebraMap R (MvPolynomial (Fin n) R)) = IsLocalRing.maximalIdeal R ∧
      ∃ (g : Localization.AtPrime 𝔪 →+* S),
        g.comp (algebraMap R (Localization.AtPrime 𝔪)) = algebraMap R S ∧
        IsLocalizationOfQuotientMap g := by
  obtain ⟨n, q, hq, g₀, hg₀comp, hg₀loc⟩ := exists_isLocalizationOfQuotientMap R S
  obtain ⟨n', q', hq', hq'good, g₁, hg₁comp, hg₁loc⟩ :=
    exists_prime_goodPosition_isLocalizationOfQuotient R n q hq
  obtain ⟨𝔪, h𝔪max, h𝔪over, g₂, hg₂comp, hg₂loc⟩ := exists_maximalIdeal_liesOver_of_sup_ne_top R n'
    q' hq' hq'good
  refine ⟨n', 𝔪, h𝔪max, h𝔪over, g₀.comp (g₁.comp g₂), ?_, ?_⟩
  · rw [RingHom.comp_assoc, RingHom.comp_assoc, hg₂comp, hg₁comp, hg₀comp]
  · exact isLocalizationOfQuotientMap_comp _ g₀
      (isLocalizationOfQuotientMap_comp g₂ g₁ hg₂loc hg₁loc) hg₀loc

/-- `g : B →+* S` exhibits `S` as a localization of a quotient of `B` if and only if there are an
ideal `I`, a ring map `f : B ⧸ I →+* S` and a submonoid `T` of `B ⧸ I` such that
`g = f.comp (Ideal.Quotient.mk I)` and, with the algebra structure induced by `f`, `S` is the
localization of `B ⧸ I` at `T`. -/
theorem isLocalizationOfQuotientMap_iff {B S : Type*} [CommRing B] [CommRing S]
    (g : B →+* S) :
    IsLocalizationOfQuotientMap g ↔
      ∃ (I : Ideal B) (f : (B ⧸ I) →+* S) (T : Submonoid (B ⧸ I)),
        g = f.comp (Ideal.Quotient.mk I) ∧
          (letI : Algebra (B ⧸ I) S := f.toAlgebra; IsLocalization T S) :=
  Iff.rfl
