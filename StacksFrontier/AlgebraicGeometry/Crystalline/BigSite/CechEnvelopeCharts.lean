module

public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeObjects
public import StacksFrontier.RingTheory.Etale.Lifting

/-!
# Smooth lifts with global étale coordinates

Fix a global crystalline situation `(p, (S, I, γ), X)` with `S` affine, `A = Γ(S, ⊤)`, and assume
`X ⟶ S₀` smooth.  Every point of `X` has an affine open neighbourhood `U` with a smooth lift `B`
(`Crystalline.GlobalCrystallineSituation.CechEnvelope.SmoothLift`) carrying *global étale
coordinates*: elements `t₁, …, t_d ∈ B` such that `A[T₁, …, T_d] → B`, `Tᵢ ↦ tᵢ`, is étale.

## The proof

A smooth algebra over `A₀ = A/I` is, Zariski locally, étale over a polynomial ring
(`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`, Stacks 00TA): around every point of an
affine open `V` of `X` there is a basic open `U = D(f)` of `V` and an étale map
`A₀[T₁, …, T_d] → Γ(U, 𝒪)`.  Étale algebras lift along the surjection
`A[T₁, …, T_d] → A₀[T₁, …, T_d]` (`etale_lift_along_surjection`, Stacks 04D1): there is an étale
`A[T]`-algebra `B` with `B / I B ≅ Γ(U, 𝒪)`.  It is smooth over `A`, being étale over a polynomial
ring, so it *is* a smooth lift of `U`, and the images `tᵢ ∈ B` of the variables are global étale
coordinates on it.

## Main results

* `Crystalline.GlobalCrystallineSituation.CechEnvelope.exists_smooth_etale_lift_mvPolynomial` —
  the algebraic core: an étale algebra over `A₀[T]` lifts to a smooth `A`-algebra with étale
  coordinates.
* `Crystalline.GlobalCrystallineSituation.CechEnvelope.exists_smoothLift_etaleCoordinates` —
  **every point of `X` has an affine open neighbourhood with a smooth lift with global étale
  coordinates.**
* `Crystalline.GlobalCrystallineSituation.CechEnvelope.exists_finite_smoothLift_etaleCoordinates`
  — when `X` is quasi-compact, finitely many such charts cover `X`.

## References

* [Stacks Project, Tag 00TA](https://stacks.math.columbia.edu/tag/00TA)
* [Stacks Project, Tag 04D1](https://stacks.math.columbia.edu/tag/04D1)
* [Stacks Project, Tag 07MV](https://stacks.math.columbia.edu/tag/07MV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry
open TopologicalSpace

universe u

namespace Crystalline.GlobalCrystallineSituation.CechEnvelope

/-- **An étale algebra over a polynomial ring over `A₀ = A / J` lifts to a smooth `A`-algebra with
étale coordinates.**  Let `R` be an `A₀`-algebra and `A₀[T₁, …, T_d] → R` an étale map over `A₀`.
Then there are a smooth `A`-algebra `C`, elements `t₁, …, t_d ∈ C` such that `A[T] → C`,
`Tᵢ ↦ tᵢ`, is étale, and a surjection of `A`-algebras `C → R` with kernel `J C`. -/
theorem exists_smooth_etale_lift_mvPolynomial {A A₀ R : Type u} [CommRing A] [CommRing A₀]
    [CommRing R] [Algebra A A₀] [Algebra A₀ R] [Algebra A R] [IsScalarTower A A₀ R]
    (hA : Function.Surjective (algebraMap A A₀)) {d : ℕ}
    [Algebra (MvPolynomial (Fin d) A₀) R] [IsScalarTower A₀ (MvPolynomial (Fin d) A₀) R]
    [Algebra.Etale (MvPolynomial (Fin d) A₀) R] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C), Algebra.Smooth A C ∧
      ∃ t : Fin d → C, (MvPolynomial.aeval (R := A) t).toRingHom.Etale ∧
        ∃ ψ : C →ₐ[A] R, Function.Surjective ψ ∧
          RingHom.ker (ψ : C →+* R) = (RingHom.ker (algebraMap A A₀)).map (algebraMap A C) := by
  let P := MvPolynomial (Fin d) A
  let P₀ := MvPolynomial (Fin d) A₀
  let π : P →+* P₀ := MvPolynomial.map (algebraMap A A₀)
  have hπ : Function.Surjective π := MvPolynomial.map_surjective _ hA
  let : Algebra P P₀ := π.toAlgebra
  let : Algebra P R := ((algebraMap P₀ R).comp π).toAlgebra
  have : IsScalarTower P P₀ R := .of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨C, _, _, hC, ψ, hψ, hker⟩ := etale_lift_along_surjection P P₀ R hπ
  let : Algebra A C := ((algebraMap P C).comp MvPolynomial.C).toAlgebra
  have : IsScalarTower A P C := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.Smooth A P := {}
  have hAR : ∀ a : A, algebraMap P R (MvPolynomial.C a) = algebraMap A R a := fun a ↦ by
    show algebraMap P₀ R (π (MvPolynomial.C a)) = _
    rw [MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply A₀ P₀ R, ← IsScalarTower.algebraMap_apply A A₀ R]
  let ψA : C →ₐ[A] R :=
    { (ψ : C →+* R) with
      commutes' := fun a ↦ by
        show ψ (algebraMap P C (MvPolynomial.C a)) = _
        rw [ψ.commutes, hAR] }
  refine ⟨C, inferInstance, inferInstance, Algebra.Smooth.comp A P C,
    fun i ↦ algebraMap P C (MvPolynomial.X i), ?_, ψA, hψ, ?_⟩
  · have h : (MvPolynomial.aeval (R := A) fun i ↦ algebraMap P C (MvPolynomial.X i)).toRingHom =
        algebraMap P C := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
      · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]
        rfl
      · simp
    rw [h]
    exact RingHom.etale_algebraMap.2 hC
  · show RingHom.ker (ψ : C →+* R) = _
    rw [hker]
    have hπker : RingHom.ker (algebraMap P P₀) =
        (RingHom.ker (algebraMap A A₀)).map (MvPolynomial.C : A →+* P) :=
      MvPolynomial.ker_map _
    rw [hπker, Ideal.map_map]
    rfl

variable {S : GlobalCrystallineSituation.{u}} {U : Scheme.{u}} (j : U ⟶ S.X)

/-- **A smooth lift with global étale coordinates from étale coordinates on `U`.**  Let
`φ : A₀[T₁, …, T_d] → Γ(U, 𝒪)` be an étale map over `A₀ = Γ(S₀, 𝒪)`.  Then `U` has a smooth lift
`B` with elements `t₁, …, t_d ∈ B` such that `A[T] → B`, `Tᵢ ↦ tᵢ`, is étale: the étale lift of
`Γ(U, 𝒪)` along `A[T] → A₀[T]` of
`Crystalline.GlobalCrystallineSituation.CechEnvelope.exists_smooth_etale_lift_mvPolynomial`. -/
theorem exists_smoothLift_etale_of_etale [IsAffine S.S.scheme] {d : ℕ}
    (φ : MvPolynomial (Fin d) Γ(DividedPowerScheme.closedFiber S.S, ⊤) →+* Γ(U, ⊤))
    (hφC : φ.comp MvPolynomial.C = (j ≫ S.toClosedFiber).appTop.hom) (hφ : φ.Etale) :
    ∃ (L : SmoothLift S j) (t : Fin d → L.ring),
      (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale := by
  let A := ↥(baseSectionsRing S)
  let A₀ := Γ(DividedPowerScheme.closedFiber S.S, ⊤)
  let : Algebra A A₀ := (DividedPowerScheme.closedFiberι S.S).appTop.hom.toAlgebra
  let : Algebra A₀ Γ(U, ⊤) := (j ≫ S.toClosedFiber).appTop.hom.toAlgebra
  let : Algebra A Γ(U, ⊤) := ((algebraMap A₀ Γ(U, ⊤)).comp (algebraMap A A₀)).toAlgebra
  have : IsScalarTower A A₀ Γ(U, ⊤) := .of_algebraMap_eq fun _ ↦ rfl
  let : Algebra (MvPolynomial (Fin d) A₀) Γ(U, ⊤) := φ.toAlgebra
  have : IsScalarTower A₀ (MvPolynomial (Fin d) A₀) Γ(U, ⊤) :=
    .of_algebraMap_eq fun a ↦ (RingHom.congr_fun hφC a).symm
  have : Algebra.Etale (MvPolynomial (Fin d) A₀) Γ(U, ⊤) := hφ
  have hA : Function.Surjective (algebraMap A A₀) :=
    (DividedPowerScheme.closedFiberι S.S).app_surjective ⊤ (isAffineOpen_top _)
  have hker : RingHom.ker (algebraMap A A₀) = (baseSectionsRing S).ideal :=
    ((DividedPowerScheme.ideal_obj_eq_ker_ideal_closedFiberι S.S
      ⟨⊤, isAffineOpen_top _⟩).trans (Scheme.Hom.ker_apply _ _)).symm
  obtain ⟨C, _, _, hCsm, t, ht, ψ, hψ, hψker⟩ :=
    exists_smooth_etale_lift_mvPolynomial (A := A) (A₀ := A₀) (R := Γ(U, ⊤)) hA (d := d)
  let e := RingHom.quotientKerEquivOfSurjective hψ
  have hk : RingHom.ker (ψ : C →+* Γ(U, ⊤)) =
      (baseSectionsRing S).ideal.map (algebraMap (baseSectionsRing S) C) := by
    rw [hψker, hker]
  refine ⟨{
    ring := C
    smooth := hCsm
    equiv := e.symm.trans (Ideal.quotEquivOfEq hk)
    equiv_sourceToBase := fun a ↦ ?_ }, t, ht⟩
  have h1 : (sourceToBase (SmallSite.overSituation S j)).appTop.hom a = ψ (algebraMap A C a) := by
    rw [ψ.commutes]
    rfl
  have h2 : e.symm (ψ (algebraMap A C a)) = Ideal.Quotient.mk _ (algebraMap A C a) :=
    e.symm_apply_eq.2 (RingHom.quotientKerEquivOfSurjective_apply_mk hψ _).symm
  rw [RingEquiv.trans_apply, h1, h2]
  exact Ideal.quotEquivOfEq_mk hk _

variable (S) in
/-- **Every point of `X` has an affine open neighbourhood with a smooth lift with global étale
coordinates**, when `S` is affine and `X ⟶ S₀` is smooth: there are an affine scheme `U`, an open
immersion `j : U ⟶ X` whose image contains the point, a smooth lift `B` of `U` over `A = Γ(S, 𝒪)`
and `t₁, …, t_d ∈ B` with `A[T₁, …, T_d] → B`, `Tᵢ ↦ tᵢ`, étale.

The open `U` is a basic open of an affine open of `X` on which `X ⟶ S₀` is étale over affine
space (Stacks 00TA), and `B` is the étale lift of the coordinates, by
`Crystalline.GlobalCrystallineSituation.CechEnvelope.exists_smoothLift_etale_of_etale`. -/
theorem exists_smoothLift_etaleCoordinates [IsAffine S.S.scheme] (hsm : Smooth S.toClosedFiber)
    (x : S.X) :
    ∃ (U : Scheme.{u}) (j : U ⟶ S.X), IsOpenImmersion j ∧ IsAffine U ∧ x ∈ Set.range j.base ∧
      ∃ (L : SmoothLift S j) (d : ℕ) (t : Fin d → L.ring),
        (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale := by
  have : IsAffine (DividedPowerScheme.closedFiber S.S) :=
    isAffine_of_isAffineHom (DividedPowerScheme.closedFiberι S.S)
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  have : IsAffine W.toScheme := hW
  let A₀ := Γ(DividedPowerScheme.closedFiber S.S, ⊤)
  let : Algebra A₀ Γ(W.toScheme, ⊤) := (W.ι ≫ S.toClosedFiber).appTop.hom.toAlgebra
  have : Algebra.Smooth A₀ Γ(W.toScheme, ⊤) :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp
      (inferInstance : Smooth (W.ι ≫ S.toClosedFiber))
  let y : W.toScheme := ⟨x, hxW⟩
  let q : PrimeSpectrum Γ(W.toScheme, ⊤) := W.toScheme.isoSpec.hom y
  have : q.asIdeal.IsPrime := q.isPrime
  have : Algebra.IsSmoothAt A₀ q.asIdeal :=
    (by rw [Algebra.smoothLocus_eq_univ]; trivial : q ∈ Algebra.smoothLocus A₀ Γ(W.toScheme, ⊤))
  obtain ⟨f, hfq, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A₀) (S := Γ(W.toScheme, ⊤))
      (p := q.asIdeal)
  have : Algebra.Etale (MvPolynomial (Fin n) A₀) (Localization.Away f) :=
    Algebra.Etale.of_formallyUnramified_of_flat
  have hy : y ∈ W.toScheme.basicOpen f := by
    rwa [← Scheme.map_PrimeSpectrum_basicOpen_of_affine]
  let V := W.toScheme.basicOpen f
  have : IsAffine V.toScheme := (isAffineOpen_top W.toScheme).basicOpen f
  let j : V.toScheme ⟶ S.X := V.ι ≫ W.ι
  let e : Localization.Away f ≃ₐ[Γ(W.toScheme, ⊤)] Γ(V.toScheme, ⊤) :=
    IsLocalization.algEquiv (Submonoid.powers f) _ _
  let φ : MvPolynomial (Fin n) A₀ →+* Γ(V.toScheme, ⊤) :=
    (e : Localization.Away f →+* Γ(V.toScheme, ⊤)).comp
      (algebraMap (MvPolynomial (Fin n) A₀) (Localization.Away f))
  have hφ : φ.Etale := by
    let : Algebra (MvPolynomial (Fin n) A₀) Γ(V.toScheme, ⊤) := φ.toAlgebra
    let e' : Localization.Away f ≃ₐ[MvPolynomial (Fin n) A₀] Γ(V.toScheme, ⊤) :=
      { e.toRingEquiv with commutes' := fun _ ↦ rfl }
    exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_equiv e')
  have hφC : φ.comp MvPolynomial.C = (j ≫ S.toClosedFiber).appTop.hom := by
    refine RingHom.ext fun a ↦ ?_
    have h₁ : algebraMap (MvPolynomial (Fin n) A₀) (Localization.Away f) (MvPolynomial.C a) =
        algebraMap Γ(W.toScheme, ⊤) (Localization.Away f) (algebraMap A₀ Γ(W.toScheme, ⊤) a) := by
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
    show e (algebraMap (MvPolynomial (Fin n) A₀) (Localization.Away f) (MvPolynomial.C a)) = _
    rw [h₁, AlgEquiv.commutes]
    simp only [j, Category.assoc, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.coe_comp, Function.comp_apply]
    rfl
  obtain ⟨L, t, ht⟩ := exists_smoothLift_etale_of_etale j φ hφC hφ
  exact ⟨V.toScheme, j, inferInstance, inferInstance, ⟨⟨y, hy⟩, rfl⟩, L, n, t, ht⟩

variable (S) in
/-- **A quasi-compact `X` smooth over `S₀` is covered by finitely many charts with smooth lifts
with global étale coordinates**, those of
`Crystalline.GlobalCrystallineSituation.CechEnvelope.exists_smoothLift_etaleCoordinates`. -/
theorem exists_finite_smoothLift_etaleCoordinates [IsAffine S.S.scheme] [CompactSpace S.X]
    (hsm : Smooth S.toClosedFiber) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → Scheme.{u}) (j : ∀ i, U i ⟶ S.X),
      (∀ i, IsOpenImmersion (j i)) ∧ (∀ i, IsAffine (U i)) ∧
        (⋃ i, Set.range (j i).base) = Set.univ ∧
        ∀ i, ∃ (L : SmoothLift S (j i)) (d : ℕ) (t : Fin d → L.ring),
          (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale := by
  choose U j hj hU hx hL using exists_smoothLift_etaleCoordinates S hsm
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ Set.range (j x).base)
    (fun x ↦ (hj x).base_open.isOpen_range) fun x _ ↦ Set.mem_iUnion.2 ⟨x, hx x⟩
  refine ⟨s, inferInstance, fun i ↦ U i.1, fun i ↦ j i.1, fun i ↦ hj i.1, fun i ↦ hU i.1,
    Set.eq_univ_of_forall fun x ↦ ?_, fun i ↦ hL i.1⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxy⟩

end Crystalline.GlobalCrystallineSituation.CechEnvelope
