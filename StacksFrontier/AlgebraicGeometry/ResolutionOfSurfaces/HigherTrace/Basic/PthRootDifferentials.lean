module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Tactic.Abel
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.HigherTrace.Basic.ExteriorProductComponent
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.TraceMapPositive.Basic
public import StacksFrontier.RingTheory.Kaehler.Basic
public import StacksFrontier.RingTheory.Kaehler.JacobiZariski

/-!
# Absolute differentials of a `p`-th root extension

The splitting of the differentials of a polynomial ring and of its base changes, and, for `S`
obtained from `R` by adjoining a root of `X ^ p - C a`, the splitting of `Ω_{S/Λ}` as the quotient
of `S ⊗[R] Ω_{R/Λ}` by the span of `da` plus a free summand spanned by `dx`, with the induced
top-degree component of the exterior powers.
-/

public noncomputable section

namespace KaehlerDifferential

open Polynomial
open scoped TensorProduct
open scoped KaehlerDifferential

variable {p t : ℕ} {Λ R S : Type*} [CommRing Λ] [CommRing R] [CommRing S]
  [Algebra Λ R] [Algebra Λ S] [Algebra R S] [IsScalarTower Λ R S]

/-- The differentials of a polynomial ring over `Lambda` split as the differentials of the base
together with a free rank-one summand spanned by `dX`. -/
private noncomputable def polynomialAbsoluteDifferentialEquiv {Λ R : Type*} [CommRing Λ]
    [CommRing R] [Algebra Λ R] :
    Ω[Polynomial R⁄Λ] ≃ₗ[Polynomial R]
      (Polynomial R ⊗[R] Ω[R⁄Λ]) × Polynomial R := by
  let P := Polynomial R
  let c : P ⊗[R] Ω[R⁄Λ] →ₗ[P] Ω[P⁄Λ] :=
    KaehlerDifferential.mapBaseChange Λ R P
  let q : Ω[P⁄Λ] →ₗ[P] Ω[P⁄R] := KaehlerDifferential.map Λ R P P
  let e : Ω[P⁄R] ≃ₗ[P] P := KaehlerDifferential.polynomialEquiv R
  let g : Ω[P⁄Λ] →ₗ[P] P := e.toLinearMap.comp q
  let s : P →ₗ[P] Ω[P⁄Λ] :=
    { toFun := fun z => z • KaehlerDifferential.D Λ P Polynomial.X
      map_add' := by intro x y; simp [add_smul]
      map_smul' := by intro a x; simp [smul_smul] }
  let F : (P ⊗[R] Ω[R⁄Λ]) × P →ₗ[P] Ω[P⁄Λ] :=
    { toFun := fun z => c z.1 + s z.2
      map_add' := by
        intro x y
        change c (x.1 + y.1) + s (x.2 + y.2) = _
        rw [map_add, map_add]
        abel
      map_smul' := by
        intro a x
        change c (a • x.1) + s (a • x.2) = a • (c x.1 + s x.2)
        rw [map_smul, map_smul]
        simp [smul_add] }
  have hg_c : g.comp c = 0 := by
    apply LinearMap.ext
    intro z
    have hqc : q (c z) = 0 :=
      (KaehlerDifferential.exact_mapBaseChange_map Λ R P (c z)).2 ⟨z, rfl⟩
    change e (q (c z)) = 0
    rw [hqc]
    simp
  have hg_s : g.comp s = LinearMap.id := by
    apply LinearMap.ext
    intro z
    change e (q (z • KaehlerDifferential.D Λ P Polynomial.X)) = z
    rw [map_smul, KaehlerDifferential.map_D Λ R P P]
    rw [map_smul, KaehlerDifferential.polynomialEquiv_D]
    simp
  have hc_inj : Function.Injective c :=
    KaehlerDifferential.mapBaseChange_injective Λ R P
  have hF_inj : Function.Injective F := by
    intro x y hxy
    have hp : x.2 = y.2 := by
      have hgF (w : (P ⊗[R] Ω[R⁄Λ]) × P) : g (F w) = w.2 := by
        change g (c w.1 + s w.2) = w.2
        rw [map_add]
        change (g.comp c) w.1 + (g.comp s) w.2 = w.2
        rw [hg_c, hg_s]
        simp
      exact (hgF x).symm.trans ((congrArg g hxy).trans (hgF y))
    have hc : c x.1 = c y.1 := by
      change c x.1 + s x.2 = c y.1 + s y.2 at hxy
      rw [hp] at hxy
      exact add_right_cancel hxy
    exact Prod.ext (hc_inj hc) hp
  have hF_surj : Function.Surjective F := by
    intro z
    let u := g z
    have hz0 : z - s u ∈ LinearMap.ker q := by
      change q (z - s u) = 0
      have hq : q (s u) = (e.symm u) := by
        calc
          q (s u) = e.symm (e (q (s u))) := by simp
          _ = e.symm (g (s u)) := rfl
          _ = e.symm u := congrArg e.symm (LinearMap.congr_fun hg_s u)
      have hzq : q z = e.symm u := (e.symm_apply_apply (q z)).symm
      rw [map_sub, hzq, hq, sub_self]
    have hzc : z - s u ∈ LinearMap.range c :=
      (KaehlerDifferential.exact_mapBaseChange_map Λ R P (z - s u)).1 hz0
    obtain ⟨v, hv⟩ := hzc
    refine ⟨(v, u), ?_⟩
    change c v + s u = z
    rw [hv, sub_add_cancel]
  exact (LinearEquiv.ofBijective F ⟨hF_inj, hF_surj⟩).symm

/-- The inverse of the splitting of the differentials of a polynomial ring, on a pair. -/
private theorem polynomialAbsoluteDifferentialEquiv_symm_apply {Λ R : Type*} [CommRing Λ]
    [CommRing R] [Algebra Λ R] (u : Polynomial R ⊗[R] Ω[R⁄Λ]) (v : Polynomial R) :
    (polynomialAbsoluteDifferentialEquiv (Λ := Λ) (R := R)).symm (u, v) =
      KaehlerDifferential.mapBaseChange Λ R (Polynomial R) u +
        v • KaehlerDifferential.D Λ (Polynomial R) Polynomial.X := by
  simp [polynomialAbsoluteDifferentialEquiv]

/-- The base change along an algebra map of the splitting of the differentials of a polynomial
ring. -/
private noncomputable def polynomialBaseChangeAbsoluteDifferentialEquiv
    {Λ R A : Type*} [CommRing Λ] [CommRing R] [CommRing A]
    [Algebra Λ R] [Algebra R A] [Algebra (Polynomial R) A]
    [IsScalarTower R (Polynomial R) A] :
    A ⊗[Polynomial R] Ω[Polynomial R⁄Λ] ≃ₗ[A]
      (A ⊗[R] Ω[R⁄Λ]) × A := by
  let e := LinearEquiv.baseChange (Polynomial R) A
    (Ω[Polynomial R⁄Λ]) ((Polynomial R ⊗[R] Ω[R⁄Λ]) × Polynomial R)
    (polynomialAbsoluteDifferentialEquiv (Λ := Λ) (R := R))
  let e₁ : A ⊗[Polynomial R] (Polynomial R ⊗[R] Ω[R⁄Λ]) ≃ₗ[A]
      A ⊗[R] Ω[R⁄Λ] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R (Polynomial R) A A
      (Ω[R⁄Λ])
  let e₂ : A ⊗[Polynomial R] Polynomial R ≃ₗ[A] A :=
    TensorProduct.AlgebraTensorModule.rid (Polynomial R) A A
  exact e.trans <| (TensorProduct.prodRight (Polynomial R) A A
      (Polynomial R ⊗[R] Ω[R⁄Λ]) (Polynomial R)).trans (e₁.prodCongr e₂)

/-- The splitting sends a differential pulled back from the base to the corresponding element of
the first summand. -/
private theorem polynomialAbsoluteDifferentialEquiv_apply_base
    {Λ R : Type*} [CommRing Λ] [CommRing R] [Algebra Λ R]
    (η : Ω[R⁄Λ]) :
    polynomialAbsoluteDifferentialEquiv
        (KaehlerDifferential.map Λ Λ R (Polynomial R) η) =
      ((1 : Polynomial R) ⊗ₜ[R] η, 0) := by
  have h := polynomialAbsoluteDifferentialEquiv_symm_apply
    (Λ := Λ) ((1 : Polynomial R) ⊗ₜ[R] η) (0 : Polynomial R)
  simp only [KaehlerDifferential.mapBaseChange_tmul, one_smul,
    zero_smul, add_zero] at h
  exact ((polynomialAbsoluteDifferentialEquiv (Λ := Λ) (R := R)).symm_apply_eq.mp h).symm

/-- The splitting sends `dX` to the generator of the free summand. -/
private theorem polynomialAbsoluteDifferentialEquiv_apply_X
    {Λ R : Type*} [CommRing Λ] [CommRing R] [Algebra Λ R] :
    polynomialAbsoluteDifferentialEquiv
        (KaehlerDifferential.D Λ (Polynomial R) Polynomial.X) =
      (0, 1) := by
  have h := polynomialAbsoluteDifferentialEquiv_symm_apply
    (Λ := Λ) (0 : Polynomial R ⊗[R] Ω[R⁄Λ]) (1 : Polynomial R)
  simp only [map_zero, one_smul, zero_add] at h
  exact ((polynomialAbsoluteDifferentialEquiv (Λ := Λ) (R := R)).symm_apply_eq.mp h).symm

/-- The base-changed splitting on a differential pulled back from the base. -/
private theorem polynomialBaseChangeAbsoluteDifferentialEquiv_apply_base
    {Λ R A : Type*} [CommRing Λ] [CommRing R] [CommRing A]
    [Algebra Λ R] [Algebra R A] [Algebra (Polynomial R) A]
    [IsScalarTower R (Polynomial R) A] (η : Ω[R⁄Λ]) :
    polynomialBaseChangeAbsoluteDifferentialEquiv
        ((1 : A) ⊗ₜ[Polynomial R]
          KaehlerDifferential.map Λ Λ R (Polynomial R) η) =
      ((1 : A) ⊗ₜ[R] η, 0) := by
  simp [polynomialBaseChangeAbsoluteDifferentialEquiv,
    polynomialAbsoluteDifferentialEquiv_apply_base]

/-- The base-changed splitting on `dX`. -/
private theorem polynomialBaseChangeAbsoluteDifferentialEquiv_apply_X
    {Λ R A : Type*} [CommRing Λ] [CommRing R] [CommRing A]
    [Algebra Λ R] [Algebra R A] [Algebra (Polynomial R) A]
    [IsScalarTower R (Polynomial R) A] :
    polynomialBaseChangeAbsoluteDifferentialEquiv
        ((1 : A) ⊗ₜ[Polynomial R]
          KaehlerDifferential.D Λ (Polynomial R) Polynomial.X) =
      (0, 1) := by
  simp [polynomialBaseChangeAbsoluteDifferentialEquiv,
    polynomialAbsoluteDifferentialEquiv_apply_X]

/-- Compatibility of the splitting of polynomial differentials with the map induced by an algebra
map on the base. -/
private theorem polynomialDifferential_map_comp
    {Λ R A : Type*} [CommRing Λ] [CommRing R] [CommRing A]
    [Algebra Λ R] [Algebra R A] [Algebra Λ A]
    [Algebra (Polynomial R) A]
    [IsScalarTower Λ R A] [IsScalarTower R (Polynomial R) A]
    [IsScalarTower Λ (Polynomial R) A] (η : Ω[R⁄Λ]) :
    KaehlerDifferential.map Λ Λ (Polynomial R) A
        (KaehlerDifferential.map Λ Λ R (Polynomial R) η) =
      KaehlerDifferential.map Λ Λ R A η := by
  have h : ((KaehlerDifferential.map Λ Λ (Polynomial R) A).restrictScalars R).comp
      (KaehlerDifferential.map Λ Λ R (Polynomial R)) =
        KaehlerDifferential.map Λ Λ R A := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro r
    change KaehlerDifferential.map Λ Λ (Polynomial R) A
      (KaehlerDifferential.map Λ Λ R (Polynomial R)
        (KaehlerDifferential.D Λ R r)) =
      KaehlerDifferential.map Λ Λ R A (KaehlerDifferential.D Λ R r)
    rw [KaehlerDifferential.map_D, KaehlerDifferential.map_D,
      KaehlerDifferential.map_D]
    congr 1
    exact (IsScalarTower.algebraMap_apply R (Polynomial R) A r).symm
  exact LinearMap.congr_fun h η

/-- The differential of `X ^ p - C a` in characteristic `p`, read through the splitting of the
differentials of the polynomial ring. -/
private theorem pthPolynomial_differential {Λ R : Type*} [CommRing Λ] [CommRing R]
    [Algebra Λ R] (p : ℕ) [CharP R p] (a : R) :
    KaehlerDifferential.D Λ (Polynomial R) (Polynomial.X ^ p - Polynomial.C a) =
      -KaehlerDifferential.mapBaseChange Λ R (Polynomial R)
        (1 ⊗ₜ[R] KaehlerDifferential.D Λ R a) := by
  let P := Polynomial R
  have hp0 : (p : P) = 0 := by
    calc
      (p : P) = algebraMap R P (p : R) := (map_natCast (algebraMap R P) p).symm
      _ = algebraMap R P 0 := by rw [CharP.cast_eq_zero R p]
      _ = 0 := map_zero _
  have hpow : KaehlerDifferential.D Λ P (Polynomial.X ^ p) = 0 := by
    rw [Derivation.leibniz_pow]
    rw [← Nat.cast_smul_eq_nsmul P p, hp0, zero_smul]
  have hC : KaehlerDifferential.D Λ P (Polynomial.C a) =
      KaehlerDifferential.map Λ Λ R P (KaehlerDifferential.D Λ R a) := by
    calc
      KaehlerDifferential.D Λ P (Polynomial.C a) =
          KaehlerDifferential.D Λ P (algebraMap R P a) :=
            congrArg (KaehlerDifferential.D Λ P) (Polynomial.C_eq_algebraMap a)
      _ = KaehlerDifferential.map Λ Λ R P (KaehlerDifferential.D Λ R a) :=
        (KaehlerDifferential.map_D Λ Λ R P a).symm
  rw [map_sub, hpow, hC]
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul]
  simp [P]

/-- The image of the relation `X ^ p - C a` under the conormal map, read through the splitting. -/
private theorem polynomialRelation_differential {Λ R : Type*} [CommRing Λ] [CommRing R]
    [Algebra Λ R] (p : ℕ) [CharP R p] (a : R) :
    (polynomialAbsoluteDifferentialEquiv (Λ := Λ) (R := R)).symm
      (-((1 : Polynomial R) ⊗ₜ[R] KaehlerDifferential.D Λ R a), 0) =
        KaehlerDifferential.D Λ (Polynomial R) (Polynomial.X ^ p - Polynomial.C a) := by
  rw [polynomialAbsoluteDifferentialEquiv_symm_apply, pthPolynomial_differential]
  simp [KaehlerDifferential.mapBaseChange_tmul]

/-- The base change of the conormal image of the relation `X ^ p - C a`. -/
private theorem polynomialBaseChange_relation_apply {Λ R A : Type*} [CommRing Λ]
    [CommRing R] [CommRing A] [Algebra Λ R] [Algebra R A]
    [Algebra (Polynomial R) A] [IsScalarTower R (Polynomial R) A]
    (p : ℕ) [CharP R p] (a : R) :
    polynomialBaseChangeAbsoluteDifferentialEquiv (Λ := Λ) (R := R) (A := A)
      (1 ⊗ₜ[Polynomial R]
        KaehlerDifferential.D Λ (Polynomial R) (Polynomial.X ^ p - Polynomial.C a)) =
      (-((1 : A) ⊗ₜ[R] KaehlerDifferential.D Λ R a), 0) := by
  have hrel := polynomialRelation_differential (Λ := Λ) p a
  have hmap :
      polynomialAbsoluteDifferentialEquiv (Λ := Λ) (R := R)
        (KaehlerDifferential.D Λ (Polynomial R) (Polynomial.X ^ p - Polynomial.C a)) =
        (-((1 : Polynomial R) ⊗ₜ[R] KaehlerDifferential.D Λ R a), 0) := by
    exact ((polynomialAbsoluteDifferentialEquiv (Λ := Λ) (R := R)).symm_apply_eq.mp hrel).symm
  simp only [polynomialBaseChangeAbsoluteDifferentialEquiv, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, hmap, TensorProduct.prodRight_tmul,
    LinearEquiv.prodCongr_apply,
    TensorProduct.AlgebraTensorModule.rid_tmul]
  rw [show -((1 : Polynomial R) ⊗ₜ[R] KaehlerDifferential.D Λ R a) =
      (-1 : Polynomial R) ⊗ₜ[R] KaehlerDifferential.D Λ R a by rfl]
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  simp only [neg_smul, one_smul, zero_smul,
    TensorProduct.neg_tmul]

/-- The cotangent module of a principal ideal is spanned by the class of its generator. -/
private theorem cotangent_span_generator {A : Type*} [CommRing A] (I : Ideal A) (f : A)
    (hI : I = Ideal.span {f}) :
    Submodule.span A
      ({(Ideal.toCotangent I) ⟨f, by rw [hI]; exact Ideal.subset_span (Set.mem_singleton f)⟩} :
        Set I.Cotangent) = ⊤ := by
  let fI : I := ⟨f, hI ▸ Ideal.mem_span_singleton_self f⟩
  rw [Submodule.eq_top_iff']
  intro z
  obtain ⟨y, rfl⟩ := I.toCotangent_surjective z
  have hyspan : (y : A) ∈ Ideal.span {f} := hI ▸ y.property
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hyspan
  have hy : y = c • fI := Subtype.ext <| hc.trans (mul_comm _ _)
  rw [hy, map_smul]
  exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))

/-- The range of the conormal map of a principal ideal is spanned by the image of its generator. -/
private theorem conormalMap_range_span_generator {P A Λ : Type*} [CommRing P] [CommRing A]
    [CommRing Λ] [Algebra Λ P] [Algebra P A] [Algebra Λ A] [IsScalarTower Λ P A]
    (hsurj : Function.Surjective (algebraMap P A)) (f : P)
    (hI : RingHom.ker (algebraMap P A) = Ideal.span {f}) :
    let I := RingHom.ker (algebraMap P A)
    letI : Module A I.Cotangent := ConormalSeq.cotangentModule hsurj
    LinearMap.range (ConormalSeq.conormalMap Λ hsurj) =
      Submodule.span A (singleton (ConormalSeq.conormalMap Λ hsurj
        (Ideal.toCotangent I ⟨f, show f ∈ RingHom.ker (algebraMap P A) from
          hI ▸ Ideal.subset_span (Set.mem_singleton f)⟩))) := by
  let I : Ideal P := RingHom.ker (algebraMap P A)
  let : Module A I.Cotangent := ConormalSeq.cotangentModule hsurj
  let : IsScalarTower P A I.Cotangent :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      change (RingHom.quotientKerEquivOfSurjective hsurj).symm
          (algebraMap P A r) • x = r • x
      rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
      rfl
  let fI : I := ⟨f, by simp [I, hI]⟩
  have hspanA : Submodule.span A ({I.toCotangent fI} : Set I.Cotangent) = ⊤ := by
    rw [← Submodule.restrictScalars_eq_top_iff P,
      Submodule.restrictScalars_span P A hsurj]
    exact cotangent_span_generator I f hI
  rw [LinearMap.range_eq_map, ← hspanA, Submodule.map_span]
  simp only [Set.image_singleton]
  congr 1

/-- The kernel of the base-changed differential map of a presentation with principal relation ideal
is spanned by the conormal image of the generator. -/
private theorem mapBaseChange_ker_of_principal {Λ P A : Type*}
    [CommRing Λ] [CommRing P] [CommRing A]
    [Algebra Λ P] [Algebra Λ A] [Algebra P A] [IsScalarTower Λ P A]
    (hsurj : Function.Surjective (algebraMap P A)) (f : P)
    (hker : RingHom.ker (algebraMap P A) = Ideal.span {f}) :
    LinearMap.ker (KaehlerDifferential.mapBaseChange Λ P A) =
      Submodule.span A {(1 : A) ⊗ₜ[P] KaehlerDifferential.D Λ P f} := by
  let I := RingHom.ker (algebraMap P A)
  let : Module A I.Cotangent := ConormalSeq.cotangentModule hsurj
  have h := ConormalSeq.conormalMap_range_eq_ker_mapBaseChange Λ P A hsurj
  have h' := conormalMap_range_span_generator (P := P) (A := A) (Λ := Λ)
    hsurj f hker
  ext z
  change z ∈ (LinearMap.ker (KaehlerDifferential.mapBaseChange Λ P A)).restrictScalars A ↔ _
  rw [← h, h', ConormalSeq.conormalMap_toCotangent]

/-- Two surjections out of a module with the same kernel have isomorphic targets. -/
private noncomputable def equivOfSurjectiveSameKer {K M N P : Type*}
    [CommRing K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup P] [Module K P]
    (f : M →ₗ[K] N) (g : M →ₗ[K] P)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : LinearMap.ker f = LinearMap.ker g) : N ≃ₗ[K] P := by
  let E : (M ⧸ LinearMap.ker f) ≃ₗ[K] (M ⧸ LinearMap.ker g) :=
    Submodule.quotEquivOfEq _ _ hker
  exact ((f.quotKerEquivOfSurjective hf).symm.trans E).trans
    (g.quotKerEquivOfSurjective hg)

/-- The kernel of the quotient map on the first factor of a product is spanned by the quotiented
vector. -/
private theorem quotientProd_ker {K M : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] (v : M) :
    LinearMap.ker (LinearMap.prodMap
      (Submodule.span K {v}).mkQ (LinearMap.id : K →ₗ[K] K)) =
      Submodule.span K {(v, (0 : K))} := by
  ext ⟨m, r⟩
  simp only [LinearMap.mem_ker, LinearMap.prodMap_apply, LinearMap.id_apply,
    Prod.mk_eq_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨⟨c, hc⟩, hr⟩
    refine ⟨c, ?_⟩
    ext
    · simpa using hc
    · simp [hr]
  · rintro ⟨c, hc⟩
    exact ⟨⟨c, congrArg Prod.fst hc⟩, by simpa using (congrArg Prod.snd hc).symm⟩

/-- Tensoring with a quotient by a span of one element, as an isomorphism onto the quotient of the
tensor product. -/
noncomputable def tensorQuotientSpanEquiv
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (v : M) :
    ((S ⊗[R] M) ⧸ Submodule.span S {(1 : S) ⊗ₜ[R] v}) ≃ₗ[S]
      S ⊗[R] (M ⧸ Submodule.span R {v}) := by
  let N : Submodule R M := Submodule.span R {v}
  let F : S ⊗[R] N →ₗ[S] S ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.lTensor S S (N.subtype.restrictScalars R)
  have hrange : F.range = Submodule.span S {(1 : S) ⊗ₜ[R] v} := by
    apply le_antisymm
    · rintro z ⟨x, rfl⟩
      induction x with
      | add x y hx hy =>
          rw [map_add]
          exact (Submodule.span S _).add_mem hx hy
      | tmul s n =>
          change s ⊗ₜ[R] (n : M) ∈ _
          obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp n.property
          convert (Submodule.span S _).smul_mem (s * algebraMap R S r)
            (Submodule.mem_span_singleton_self ((1 : S) ⊗ₜ[R] v)) using 1
          simp [← hr, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
            Algebra.smul_def, mul_comm]
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨(1 : S) ⊗ₜ[R] (⟨v, Submodule.mem_span_singleton_self v⟩ : N), rfl⟩
  exact (Submodule.quotEquivOfEq _ _ hrange.symm).trans
    (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv S R S N).symm

/-- The value of that isomorphism on a pure tensor. -/
theorem tensorQuotientSpanEquiv_apply_tmul
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (v m : M) (s : S) :
    tensorQuotientSpanEquiv (S := S) v
      ((Submodule.span S {(1 : S) ⊗ₜ[R] v}).mkQ (s ⊗ₜ[R] m)) =
      s ⊗ₜ[R] (Submodule.span R {v}).mkQ m := by
  rfl

/-- The differentials of a surjective base change, identified with the quotient of the split
differentials by the span of the image of the relation. -/
private noncomputable def differentialQuotientEquiv
    {Λ P A B : Type*} [CommRing Λ] [CommRing P] [CommRing A]
    [Algebra Λ P] [Algebra Λ A] [Algebra P A] [IsScalarTower Λ P A]
    [AddCommGroup B] [Module A B]
    (h : Function.Surjective (algebraMap P A))
    (E : A ⊗[P] Ω[P⁄Λ] ≃ₗ[A] B × A)
    (u : A ⊗[P] Ω[P⁄Λ]) (v : B)
    (hu : LinearMap.ker (KaehlerDifferential.mapBaseChange Λ P A) =
      Submodule.span A {u})
    (hEu : E u = (v, 0)) :
    Ω[A⁄Λ] ≃ₗ[A] (B ⧸ Submodule.span A {v}) × A := by
  let f := KaehlerDifferential.mapBaseChange Λ P A
  let q : B × A →ₗ[A] (B ⧸ Submodule.span A {v}) × A :=
    LinearMap.prodMap (Submodule.span A {v}).mkQ LinearMap.id
  let g := q.comp E.toLinearMap
  have hf : Function.Surjective f :=
    KaehlerDifferential.mapBaseChange_surjective (R := Λ) (A := P) (B := A) h
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨b, hb⟩ := (Submodule.span A {v}).mkQ_surjective z.1
    obtain ⟨x, hx⟩ := E.surjective (b, z.2)
    refine ⟨x, ?_⟩
    change q (E x) = z
    rw [hx]
    exact Prod.ext hb rfl
  have hker : LinearMap.ker f = LinearMap.ker g := by
    rw [hu]
    ext x
    change x ∈ Submodule.span A {u} ↔ g x = 0
    rw [Submodule.mem_span_singleton]
    change (∃ c : A, c • u = x) ↔ E x ∈ LinearMap.ker q
    rw [show LinearMap.ker q = Submodule.span A {(v, (0 : A))} from quotientProd_ker v,
      Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, by rw [map_smul, hEu]⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, E.injective (by rwa [map_smul, hEu])⟩
  exact equivOfSurjectiveSameKer f g hf hg hker

/-- The value of that identification on a base-changed differential. -/
private theorem differentialQuotientEquiv_apply_mapBaseChange
    {Λ P A B : Type*} [CommRing Λ] [CommRing P] [CommRing A]
    [Algebra Λ P] [Algebra Λ A] [Algebra P A] [IsScalarTower Λ P A]
    [AddCommGroup B] [Module A B]
    (h : Function.Surjective (algebraMap P A))
    (E : A ⊗[P] Ω[P⁄Λ] ≃ₗ[A] B × A)
    (u : A ⊗[P] Ω[P⁄Λ]) (v : B)
    (hu : LinearMap.ker (KaehlerDifferential.mapBaseChange Λ P A) =
      Submodule.span A {u})
    (hEu : E u = (v, 0)) (x : A ⊗[P] Ω[P⁄Λ]) :
    differentialQuotientEquiv h E u v hu hEu
        (KaehlerDifferential.mapBaseChange Λ P A x) =
      ((Submodule.span A {v}).mkQ (E x).1, (E x).2) := by
  have hmk : ∀ hf : Function.Surjective (KaehlerDifferential.mapBaseChange Λ P A),
      ((KaehlerDifferential.mapBaseChange Λ P A).quotKerEquivOfSurjective hf).symm
        (KaehlerDifferential.mapBaseChange Λ P A x) = Submodule.Quotient.mk x :=
    fun hf => (LinearEquiv.symm_apply_eq _).mpr
      (LinearMap.quotKerEquivOfSurjective_apply_mk _ hf x).symm
  simp only [differentialQuotientEquiv, equivOfSurjectiveSameKer, LinearEquiv.trans_apply,
    hmk, Submodule.quotEquivOfEq_mk]
  rfl

/-- For `S` obtained from `R` by adjoining a `p`-th root, the absolute differentials of `S` split
as the quotient of the differentials of `R` by the span of `da`, together with a free rank-one
summand spanned by `dx`. -/
noncomputable def pthRootAbsoluteDifferentialEquiv
    [CharP R p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) :
    Ω[S⁄Λ] ≃ₗ[S]
      ((S ⊗[R] Ω[R⁄Λ]) ⧸
        Submodule.span S {(1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a}) × S := by
  let P := Polynomial R
  let f : P := X ^ p - C a
  letI : Algebra P S := (e.toRingHom.comp (AdjoinRoot.mk f)).toAlgebra
  letI : IsScalarTower R P S := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R S r = e (AdjoinRoot.mk f (C r))
    rw [AdjoinRoot.mk_C]
    exact (e.commutes r).symm
  letI : IsScalarTower Λ P S := IsScalarTower.of_algebraMap_eq fun l => by
    change algebraMap Λ S l = e (AdjoinRoot.mk f (C (algebraMap Λ R l)))
    rw [AdjoinRoot.mk_C]
    change algebraMap Λ S l = e (algebraMap R (AdjoinRoot f) (algebraMap Λ R l))
    rw [e.commutes]
    exact IsScalarTower.algebraMap_apply Λ R S l
  have hsurj : Function.Surjective (algebraMap P S) := by
    intro s
    obtain ⟨x, rfl⟩ := e.surjective s
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
    exact ⟨g, rfl⟩
  have hker : RingHom.ker (algebraMap P S) = Ideal.span {f} := by
    ext g
    change e (AdjoinRoot.mk f g) = 0 ↔ g ∈ Ideal.span {f}
    rw [← map_zero e]
    rw [e.injective.eq_iff, AdjoinRoot.mk_eq_zero, Ideal.mem_span_singleton]
  let E := polynomialBaseChangeAbsoluteDifferentialEquiv
    (Λ := Λ) (R := R) (A := S)
  have hu : LinearMap.ker (KaehlerDifferential.mapBaseChange Λ P S) =
      Submodule.span S
        {(1 : S) ⊗ₜ[P] KaehlerDifferential.D Λ P f} :=
    mapBaseChange_ker_of_principal hsurj f hker
  have hEu : E ((1 : S) ⊗ₜ[P] KaehlerDifferential.D Λ P f) =
      (-((1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a), 0) :=
    polynomialBaseChange_relation_apply p a
  let E' := differentialQuotientEquiv hsurj E
    ((1 : S) ⊗ₜ[P] KaehlerDifferential.D Λ P f)
    (-((1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a)) hu hEu
  have hspan : Submodule.span S
      {(-((1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a))} =
      Submodule.span S {(1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a} := by
    simpa only [Set.neg_singleton] using
      (Submodule.span_neg (R := S)
        ({(1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a} :
          Set (S ⊗[R] Ω[R⁄Λ])))
  exact E'.trans ((Submodule.quotEquivOfEq _ _ hspan).prodCongr
    (LinearEquiv.refl S S))

/-- The `Polynomial R`-algebra structure on `S` given by `e` is compatible with the actions of `R`
and `Λ`. -/
private theorem pthRoot_isScalarTower [Algebra (Polynomial R) S] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S)
    (halg : algebraMap (Polynomial R) S = e.toRingHom.comp (AdjoinRoot.mk (X ^ p - C a))) :
    IsScalarTower R (Polynomial R) S ∧ IsScalarTower Λ (Polynomial R) S := by
  have hR : IsScalarTower R (Polynomial R) S := IsScalarTower.of_algebraMap_eq fun r => by
    rw [halg]
    change algebraMap R S r = e (AdjoinRoot.mk _ (C r))
    rw [AdjoinRoot.mk_C]
    exact (e.commutes r).symm
  exact ⟨hR, IsScalarTower.of_algebraMap_eq fun l => by
    rw [IsScalarTower.algebraMap_apply Λ R S, IsScalarTower.algebraMap_apply R (Polynomial R) S,
      ← IsScalarTower.algebraMap_apply Λ R (Polynomial R)]⟩

/-- The splitting of the absolute differentials of the `p`-th root extension on the image of an
element of `S ⊗[Polynomial R] Ω[Polynomial R⁄Λ]`, read through the base-changed splitting. -/
private theorem pthRootAbsoluteDifferentialEquiv_apply_aux
    [CharP R p] (a : R) (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S)
    [inst : Algebra (Polynomial R) S]
    (hinst : inst = (e.toRingHom.comp (AdjoinRoot.mk (X ^ p - C a))).toAlgebra)
    [IsScalarTower R (Polynomial R) S] [IsScalarTower Λ (Polynomial R) S]
    (z : S ⊗[Polynomial R] Ω[Polynomial R⁄Λ]) (v : S ⊗[R] Ω[R⁄Λ]) (c : S)
    (hz : polynomialBaseChangeAbsoluteDifferentialEquiv z = (v, c)) :
    pthRootAbsoluteDifferentialEquiv (Λ := Λ) a e
        (KaehlerDifferential.mapBaseChange Λ (Polynomial R) S z) =
      ((Submodule.span S {(1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a}).mkQ v, c) := by
  have halg : algebraMap (Polynomial R) S = e.toRingHom.comp (AdjoinRoot.mk (X ^ p - C a)) := by
    rw [hinst]
    rfl
  have hsurj : Function.Surjective (algebraMap (Polynomial R) S) := by
    rw [halg]
    exact e.surjective.comp (AdjoinRoot.mk_surjective)
  have hker : RingHom.ker (algebraMap (Polynomial R) S) = Ideal.span {X ^ p - C a} := by
    ext g
    rw [RingHom.mem_ker, halg, RingHom.comp_apply, Ideal.mem_span_singleton,
      ← AdjoinRoot.mk_eq_zero, ← e.injective.eq_iff]
    simp
  have hu := mapBaseChange_ker_of_principal (Λ := Λ) hsurj _ hker
  have hEu := polynomialBaseChange_relation_apply (Λ := Λ) (A := S) p a
  have key := differentialQuotientEquiv_apply_mapBaseChange hsurj _ _ _ hu hEu z
  subst hinst
  unfold pthRootAbsoluteDifferentialEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  rw [key, hz]
  exact congrArg (·, c) (Submodule.quotEquivOfEq_mk _ _ _ _)

/-- The splitting of the absolute differentials of the `p`-th root extension on a differential
pulled back from `R`. -/
theorem pthRootAbsoluteDifferentialEquiv_apply_base
    [CharP R p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) (η : Ω[R⁄Λ]) :
    pthRootAbsoluteDifferentialEquiv (Λ := Λ) a e
        (KaehlerDifferential.map Λ Λ R S η) =
      ((Submodule.span S {(1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a}).mkQ
        ((1 : S) ⊗ₜ[R] η), 0) := by
  let : Algebra (Polynomial R) S := (e.toRingHom.comp (AdjoinRoot.mk (X ^ p - C a))).toAlgebra
  obtain ⟨_, _⟩ := pthRoot_isScalarTower (Λ := Λ) a e rfl
  have hz : KaehlerDifferential.mapBaseChange Λ (Polynomial R) S
      ((1 : S) ⊗ₜ[Polynomial R] KaehlerDifferential.map Λ Λ R (Polynomial R) η) =
        KaehlerDifferential.map Λ Λ R S η := by
    simpa only [KaehlerDifferential.mapBaseChange_tmul, one_smul] using
      polynomialDifferential_map_comp η
  rw [← hz]
  exact pthRootAbsoluteDifferentialEquiv_apply_aux a e rfl _ _ _
    (polynomialBaseChangeAbsoluteDifferentialEquiv_apply_base η)

/-- The splitting of the absolute differentials of the `p`-th root extension on `dx`. -/
theorem pthRootAbsoluteDifferentialEquiv_apply_root
    [CharP R p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) :
    pthRootAbsoluteDifferentialEquiv (Λ := Λ) a e
        (KaehlerDifferential.D Λ S (e (AdjoinRoot.root (X ^ p - C a)))) =
      (0, 1) := by
  let : Algebra (Polynomial R) S := (e.toRingHom.comp (AdjoinRoot.mk (X ^ p - C a))).toAlgebra
  obtain ⟨_, _⟩ := pthRoot_isScalarTower (Λ := Λ) a e rfl
  have hz : KaehlerDifferential.mapBaseChange Λ (Polynomial R) S
      ((1 : S) ⊗ₜ[Polynomial R] KaehlerDifferential.D Λ (Polynomial R) X) =
        KaehlerDifferential.D Λ S (e (AdjoinRoot.root (X ^ p - C a))) := by
    simp only [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
    rfl
  rw [← hz]
  simpa only [map_zero] using pthRootAbsoluteDifferentialEquiv_apply_aux a e rfl _ _ _
    (polynomialBaseChangeAbsoluteDifferentialEquiv_apply_X (Λ := Λ) (R := R) (A := S))

/-- The top-degree component of the exterior power of the split absolute differentials of the
`p`-th root extension. -/
noncomputable def rootExteriorComponent
    [CharP R p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) :
    (⋀[S]^(t + 1) Ω[S⁄Λ]) →ₗ[S]
      (⋀[S]^t ((S ⊗[R] Ω[R⁄Λ]) ⧸
        Submodule.span S {(1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a})) ⊗[S]
        (⋀[S]^1 S) :=
  (exteriorProductComponent (K := S)
    (M := (S ⊗[R] Ω[R⁄Λ]) ⧸
      Submodule.span S {(1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a})
    (N := S) t 1).comp
      (exteriorPower.map (t + 1)
        (pthRootAbsoluteDifferentialEquiv (Λ := Λ) a e).toLinearMap)

/-- The value of the top-degree component on a wedge of base differentials with `dx` appended. -/
theorem rootExteriorComponent_apply_snoc
    [CharP R p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S)
    (s : S) (η : Fin t → Ω[R⁄Λ]) :
    rootExteriorComponent (t := t) (Λ := Λ) a e
      (exteriorPower.ιMulti S (t + 1)
        (Fin.snoc (fun j => KaehlerDifferential.map Λ Λ R S (η j))
          (s • KaehlerDifferential.D Λ S
            (e (AdjoinRoot.root (X ^ p - C a)))))) =
    exteriorPower.ιMulti S t
        (fun j => (Submodule.span S
          {(1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a}).mkQ
            ((1 : S) ⊗ₜ[R] η j)) ⊗ₜ[S]
      exteriorPower.ιMulti S 1 (fun _ => s) := by
  let E := pthRootAbsoluteDifferentialEquiv (Λ := Λ) a e
  have hb (j : Fin t) :
      E (KaehlerDifferential.map Λ Λ R S (η j)) =
        ((Submodule.span S
          {(1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a}).mkQ
          ((1 : S) ⊗ₜ[R] η j), 0) :=
    pthRootAbsoluteDifferentialEquiv_apply_base a e (η j)
  have hr : E (s • KaehlerDifferential.D Λ S
      (e (AdjoinRoot.root (X ^ p - C a)))) = (0, s) := by
    rw [map_smul, pthRootAbsoluteDifferentialEquiv_apply_root]
    simp
  have htuple : E ∘
      Fin.snoc (fun j => KaehlerDifferential.map Λ Λ R S (η j))
        (s • KaehlerDifferential.D Λ S
          (e (AdjoinRoot.root (X ^ p - C a)))) =
      Fin.snoc (fun j => ((Submodule.span S
          {(1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a}).mkQ
          ((1 : S) ⊗ₜ[R] η j), (0 : S))) (0, s) := by
    rw [Fin.comp_snoc]
    rw [hr]
    congr 1
    funext j
    exact hb j
  simp only [rootExteriorComponent, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti]
  have htuple' : (pthRootAbsoluteDifferentialEquiv (Λ := Λ) a e).toLinearMap ∘
      Fin.snoc (fun j => KaehlerDifferential.map Λ Λ R S (η j))
        (s • KaehlerDifferential.D Λ S
          (e (AdjoinRoot.root (X ^ p - C a)))) =
      Fin.snoc (fun j => ((Submodule.span S
          {(1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a}).mkQ
          ((1 : S) ⊗ₜ[R] η j), (0 : S))) (0, s) := htuple
  rw [htuple']
  exact exteriorProductComponent_apply_snoc t _ s

/-- The top-degree component annihilates a wedge of differentials all pulled back from the base. -/
theorem rootExteriorComponent_apply_baseForm
    [CharP R p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S)
    (η : Fin (t + 1) → Ω[R⁄Λ]) :
    rootExteriorComponent (t := t) (Λ := Λ) a e
      (exteriorPower.ιMulti S (t + 1)
        (fun j => KaehlerDifferential.map Λ Λ R S (η j))) = 0 := by
  have htuple : (pthRootAbsoluteDifferentialEquiv (Λ := Λ) a e).toLinearMap ∘
      (fun j : Fin (t + 1) => KaehlerDifferential.map Λ Λ R S (η j)) =
      LinearMap.inl S
        ((S ⊗[R] Ω[R⁄Λ]) ⧸
          Submodule.span S {(1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a}) S ∘
        (fun j => (Submodule.span S
          {(1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R a}).mkQ
            ((1 : S) ⊗ₜ[R] η j)) := by
    funext j
    exact pthRootAbsoluteDifferentialEquiv_apply_base a e (η j)
  simp only [rootExteriorComponent, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti]
  rw [htuple]
  exact exteriorProductComponent_apply_inl t _
end KaehlerDifferential

end
