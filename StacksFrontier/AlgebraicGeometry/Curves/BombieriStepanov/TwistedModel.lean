module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.DedekindPlaces
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.PlaceTransport
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.Twisted
public import StacksFrontier.NumberTheory.BombieriStepanov.TwistedIdentities
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Twisted points of a Dedekind model, bounded through a proper model

Let `M` be a proper curve over a finite field `F` with discrete valuation rings at its places
and a rational place `P₀`, and let `A` be a Dedekind domain with fraction field `R(M)`
containing `F`. For a ring automorphism `σ` of `A` of finite order fixing `F` and an embedding
`ι : F → Ω` into a field, consider the `σ`-twisted points: the ring homomorphisms `φ : A → Ω`
over `ι` with `φ(σ a) = φ(a) ^ Q`. Then, for `Q = r²` a power of `#F` with `r` large,

`#{σ-twisted points} ≤ Q + (2γ + 1) r`.

The kernel `P` of a twisted point is a nonzero maximal ideal, whose localization is the local
ring at a place `x_P` of `M` (`Stacks.BombieriStepanov.exists_curvePlace_eq_localization`). The
point factors through `A / P = κ(x_P)` as an `F`-embedding, so at most `deg x_P` twisted points
have kernel `P`. At `x_P` the extension `τ` of `σ` to `R(M)` satisfies the congruence
`τ y ≡ y ^ Q` for regular `y`: write `y = a / t` with `t ∉ P`; the numerator of `τ y - y ^ Q` is
killed by the twisted point. Since `τ` carries `L(n P₀)` into `L(n τ(P₀))` with `τ(P₀)` rational
(`Stacks.BombieriStepanov.exists_mapsTo_poleSpace`), the twisted Stepanov bound
`Stacks.BombieriStepanov.exists_sum_curveDeg_add_one_le_twisted` applies to these places.

## Main results

* `Stacks.BombieriStepanov.ncard_twisted_le`: the bound above.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace Stacks.BombieriStepanov

variable {F : Type u} [Field F] {M : Scheme.{u}} (p : M ⟶ Spec (.of F)) [IsIntegral M]
  [IsLocallyNoetherian M]
  (hdvr : ∀ x : M, coheight x = 1 → IsDiscreteValuationRing (M.presheaf.stalk x))
  {A : Type u} [CommRing A] [IsDedekindDomain A] [Algebra A M.functionField]
  [IsFractionRing A M.functionField] [Algebra F A]
  (hFA : ∀ c : F, algebraMap A M.functionField (algebraMap F A c) =
    (fieldToStalk p (genericPoint M)).hom c)

omit [IsDedekindDomain A] in
/-- A twisted point of an automorphism of finite order takes values in a finite field. -/
theorem pow_pow_eq_of_twisted {Ω : Type*} [Field Ω] (σ : A ≃+* A) {N : ℕ}
    (hN : ∀ a, (⇑σ)^[N] a = a) (Q : ℕ) (φ : A →+* Ω) (hφ : ∀ a, φ (σ a) = φ a ^ Q) (a : A) :
    φ a ^ (Q ^ N) = φ a := by
  have key : ∀ j a, φ ((⇑σ)^[j] a) = φ a ^ (Q ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro a
      rw [Function.iterate_succ_apply', hφ, ih, ← pow_mul, pow_succ]
  rw [← key N a, hN]

include hdvr in
omit [IsDedekindDomain A] in
/-- **The congruence at the place of a twisted point.** If `φ` is `σ`-twisted with kernel `P`
and `x` is a place with `𝒪_{M,x} = A_P`, then `τ y ≡ y ^ Q` at `x` for every regular `y`, where
`τ` extends `σ` to the function field. -/
theorem one_le_curveVal_sub_pow_of_twisted {Ω : Type*} [Field Ω] (σ : A ≃+* A) (Q : ℕ)
    (φ : A →+* Ω) (hφ : ∀ a, φ (σ a) = φ a ^ Q) [(RingHom.ker φ).IsMaximal]
    (x : CurvePlace M)
    (hx : ∀ f : M.functionField,
      (∃ s : M.presheaf.stalk x.1, algebraMap _ M.functionField s = f) ↔
        ∃ a t : A, t ∉ RingHom.ker φ ∧ f = algebraMap A M.functionField a *
          (algebraMap A _ t)⁻¹)
    (y : M.functionField) (hy : 0 ≤ curveVal hdvr x y) :
    ((1 : ℤ) : WithTop ℤ) ≤ curveVal hdvr x
      (IsFractionRing.ringEquivOfRingEquiv (K := M.functionField) (L := M.functionField) σ y -
        y ^ Q) := by
  have := hdvr x.1 x.2
  set τ : M.functionField ≃+* M.functionField :=
    IsFractionRing.ringEquivOfRingEquiv (K := M.functionField) (L := M.functionField) σ
  have hτ : ∀ a, τ (algebraMap A M.functionField a) = algebraMap A M.functionField (σ a) :=
    IsFractionRing.ringEquivOfRingEquiv_algebraMap σ
  obtain ⟨a, t, ht, rfl⟩ := (hx y).1 ((zero_le_curveVal_iff hdvr x y).1 hy)
  have hinjA := IsFractionRing.injective A M.functionField
  have hne : ∀ b : A, b ∉ RingHom.ker φ → algebraMap A M.functionField b ≠ 0 := by
    intro b hb h
    exact hb ((map_eq_zero_iff _ hinjA).1 h ▸ (RingHom.ker φ).zero_mem)
  -- numerator and denominator
  set N := σ a * t ^ Q - a ^ Q * σ t
  set D := σ t * t ^ Q
  have hN : N ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker]
    simp only [N, map_sub, map_mul, map_pow, hφ, sub_self]
  have hD : D ∉ RingHom.ker φ := by
    rw [RingHom.mem_ker]
    simp only [D, map_mul, map_pow, hφ]
    have ht' : φ t ≠ 0 := by simpa [RingHom.mem_ker] using ht
    exact mul_ne_zero (pow_ne_zero _ ht') (pow_ne_zero _ ht')
  have hσt : σ t ∉ RingHom.ker φ := by
    rw [RingHom.mem_ker, hφ]
    exact pow_ne_zero _ (by simpa [RingHom.mem_ker] using ht)
  have heq : τ (algebraMap A M.functionField a * (algebraMap A _ t)⁻¹) -
      (algebraMap A M.functionField a * (algebraMap A _ t)⁻¹) ^ Q =
      algebraMap A M.functionField N * (algebraMap A M.functionField D)⁻¹ := by
    have h1 := hne t ht
    have h2 := hne (σ t) hσt
    have hT : (algebraMap A M.functionField t) ^ Q * ((algebraMap A M.functionField t)⁻¹) ^ Q =
        1 := by rw [← mul_pow, mul_inv_cancel₀ h1, one_pow]
    simp only [map_mul, map_inv₀, hτ, N, D, map_sub, map_pow]
    field_simp
    linear_combination (-(algebraMap A M.functionField (σ t)) *
      (algebraMap A M.functionField a) ^ Q) * hT
  rw [heq]
  obtain ⟨sD, hsD⟩ := exists_algebraMap_eq_inv hx hD
  have hNm := (toStalk_mem_maximalIdeal_iff hx N).2 hN
  rw [← algebraMap_toStalk x (forall_exists_algebraMap_eq hx) N, ← hsD, ← map_mul,
    one_le_curveVal_algebraMap_iff hdvr x]
  exact Ideal.mul_mem_right _ _ hNm

include hFA in
omit [IsLocallyNoetherian M] [IsDedekindDomain A] [IsFractionRing A M.functionField] in
/-- The inclusion `A → 𝒪_{M,x}` carries the constants of `A` to those of the local ring. -/
theorem toStalk_algebraMap (x : M)
    (hA : ∀ a : A, ∃ s : M.presheaf.stalk x,
      algebraMap (M.presheaf.stalk x) M.functionField s = algebraMap A M.functionField a)
    (c : F) : toStalk x hA (algebraMap F A c) = (fieldToStalk p x).hom c := by
  refine IsFractionRing.injective (M.presheaf.stalk x) M.functionField ?_
  rw [algebraMap_toStalk, hFA]
  exact algebraMap_functionFieldAlgebra p x c

/-- A surjective `F`-algebra map onto a field induces an `F`-algebra isomorphism from the quotient
by its kernel. -/
private theorem exists_algEquiv_quotient_ker {R κ : Type*} [CommRing R] [Field κ]
    [Algebra F R] [Algebra F κ] (θ : R →+* κ)
    (hθc : ∀ c : F, θ (algebraMap F R c) = algebraMap F κ c) (hθs : Function.Surjective θ) :
    ∃ eF : (R ⧸ RingHom.ker θ) ≃ₐ[F] κ, ∀ a, eF (Ideal.Quotient.mk _ a) = θ a :=
  ⟨AlgEquiv.ofRingEquiv (f := RingHom.quotientKerEquivOfSurjective hθs) fun c => by
      change RingHom.quotientKerEquivOfSurjective hθs (Ideal.Quotient.mk _ (algebraMap F R c)) = _
      rw [RingHom.quotientKerEquivOfSurjective_apply_mk, hθc],
    fun _ => RingHom.quotientKerEquivOfSurjective_apply_mk hθs _⟩

/-- A surjective `F`-algebra map from a finite type `F`-algebra onto a field, with maximal kernel,
exhibits the target as the quotient by that kernel, hence as a finite `F`-module. -/
private theorem module_finite_of_surjective_of_ker_isMaximal {R κ : Type*} [CommRing R] [Field κ]
    [Algebra F R] [Algebra F κ] [Algebra.FiniteType F R] (θ : R →+* κ)
    (hθc : ∀ c : F, θ (algebraMap F R c) = algebraMap F κ c) (hθs : Function.Surjective θ)
    [(RingHom.ker θ).IsMaximal] : Module.Finite F κ := by
  obtain ⟨eF, -⟩ := exists_algEquiv_quotient_ker θ hθc hθs
  let : Field (R ⧸ RingHom.ker θ) := Ideal.Quotient.field _
  have : Module.Finite F (R ⧸ RingHom.ker θ) :=
    finite_of_finite_type_of_isJacobsonRing F (R ⧸ RingHom.ker θ)
  exact Module.Finite.equiv eF.toLinearEquiv

/-- A surjective `F`-algebra map onto a field is universal among the `F`-algebra maps killing its
kernel: every such map factors through it. -/
private theorem exists_algHom_comp_eq_of_surjective {R κ Ω : Type*} [CommRing R] [Field κ]
    [Field Ω] [Algebra F R] [Algebra F κ] [Algebra F Ω] (θ : R →+* κ)
    (hθc : ∀ c : F, θ (algebraMap F R c) = algebraMap F κ c) (hθs : Function.Surjective θ)
    (φ : R →ₐ[F] Ω) (hφ : ∀ a ∈ RingHom.ker θ, φ a = 0) :
    ∃ ψ : κ →ₐ[F] Ω, ∀ a, ψ (θ a) = φ a := by
  obtain ⟨eF, heF⟩ := exists_algEquiv_quotient_ker θ hθc hθs
  let ψ₀ : R ⧸ RingHom.ker θ →ₐ[F] Ω := Ideal.Quotient.liftₐ _ φ hφ
  refine ⟨ψ₀.comp eF.symm.toAlgHom, fun a => ?_⟩
  have h1 : eF.symm (θ a) = Ideal.Quotient.mk _ a := by
    rw [AlgEquiv.symm_apply_eq, heF]
  change ψ₀ (eF.symm (θ a)) = φ a
  rw [h1]
  rfl

include hFA in
omit [IsLocallyNoetherian M] [IsDedekindDomain A] in
/-- **The fibre of the place map.** The ring homomorphisms `φ : A → Ω` over `ι` whose kernel has
`A_P = 𝒪_{M,x}` number at most `deg x`: each factors through `κ(x) = A / P` as an `F`-embedding. -/
theorem ncard_le_curveDeg {Ω : Type*} [Field Ω] (ι : F →+* Ω) [Algebra.FiniteType F A]
    (x : CurvePlace M)
    (hA : ∀ a : A, ∃ s : M.presheaf.stalk x.1,
      algebraMap (M.presheaf.stalk x.1) M.functionField s = algebraMap A M.functionField a)
    (T : Set (PointsOver A ι))
    (hT : ∀ φ ∈ T, ∃ _ : (RingHom.ker φ.1).IsMaximal, ∀ f : M.functionField,
      (∃ s : M.presheaf.stalk x.1, algebraMap _ M.functionField s = f) ↔
        ∃ a t : A, t ∉ RingHom.ker φ.1 ∧ f = algebraMap A M.functionField a *
          (algebraMap A _ t)⁻¹) :
    T.Finite ∧ T.ncard ≤ curveDeg F p x := by
  classical
  let : Algebra F Ω := ι.toAlgebra
  let : Algebra F (M.presheaf.stalk x.1) :=
    ((M.presheaf.germ ⊤ x.1 (by simp)).hom.comp
      ((Scheme.ΓSpecIso (.of F)).inv ≫ p.appTop).hom).toAlgebra
  set θ : A →+* IsLocalRing.ResidueField (M.presheaf.stalk x.1) :=
    (IsLocalRing.residue (M.presheaf.stalk x.1)).comp (toStalk x.1 hA)
  have hθc : ∀ c : F, θ (algebraMap F A c) =
      algebraMap F (IsLocalRing.ResidueField (M.presheaf.stalk x.1)) c := by
    intro c
    change IsLocalRing.residue _ (toStalk x.1 hA (algebraMap F A c)) = _
    rw [toStalk_algebraMap p hFA]
    rfl
  -- the kernel of every point of `T` is the kernel of `θ`, and `θ` is onto
  have hker : ∀ φ ∈ T, RingHom.ker φ.1 = RingHom.ker θ := by
    intro φ hφ
    obtain ⟨_, hx⟩ := hT φ hφ
    exact (ker_residue_comp_toStalk hx).symm
  by_cases hTne : T.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hTne
    subst hTne
    simp
  obtain ⟨φ₀, hφ₀⟩ := hTne
  obtain ⟨hmax, hx₀⟩ := hT φ₀ hφ₀
  have hθs : Function.Surjective θ := surjective_residue_comp_toStalk hx₀
  -- the residue field is finite over `F`
  have : (RingHom.ker θ).IsMaximal := hker φ₀ hφ₀ ▸ hmax
  have : Module.Finite F (IsLocalRing.ResidueField (M.presheaf.stalk x.1)) :=
    module_finite_of_surjective_of_ker_isMaximal θ hθc hθs
  -- a point of `T` factors through `θ`
  have hfac : ∀ φ ∈ T, ∃ ψ : IsLocalRing.ResidueField (M.presheaf.stalk x.1) →ₐ[F] Ω,
      ∀ a, ψ (θ a) = φ.1 a := fun φ hφ =>
    exists_algHom_comp_eq_of_surjective θ hθc hθs
      { φ.1 with commutes' := fun c => congrArg (fun g : F →+* Ω => g c) φ.2 }
      (fun a ha => by rw [← hker φ hφ] at ha; exact ha)
  have : Nonempty (IsLocalRing.ResidueField (M.presheaf.stalk x.1) →ₐ[F] Ω) :=
    ⟨(hfac φ₀ hφ₀).choose⟩
  choose! Ψ hΨ using hfac
  have hinj : Set.InjOn Ψ T := by
    intro φ hφ φ' hφ' h
    refine Subtype.ext (RingHom.ext fun a => ?_)
    rw [← hΨ φ hφ a, ← hΨ φ' hφ' a, h]
  have : Finite (IsLocalRing.ResidueField (M.presheaf.stalk x.1) →ₐ[F] Ω) := inferInstance
  have hfin : T.Finite := Set.Finite.of_finite_image (Set.toFinite _) hinj
  refine ⟨hfin, ?_⟩
  rw [← hinj.ncard_image]
  refine (Set.ncard_le_ncard (Set.subset_univ _)).trans ?_
  rw [Set.ncard_univ]
  refine (card_algHom_le_finrank F _ Ω).trans_eq ?_
  unfold curveDeg
  rw [Stacks.Chow.residueDegree_eq_finrank_residueField F p x.1]

include hdvr in
omit [IsDedekindDomain A] in
/-- An element of `A` lies in `P` exactly when it vanishes at the place `x_P`. -/
theorem mem_iff_one_le_curveVal {P : Ideal A} [P.IsMaximal] {x : CurvePlace M}
    (hx : ∀ f : M.functionField,
      (∃ s : M.presheaf.stalk x.1, algebraMap _ M.functionField s = f) ↔
        ∃ a t : A, t ∉ P ∧ f = algebraMap A M.functionField a * (algebraMap A _ t)⁻¹) (a : A) :
    a ∈ P ↔ ((1 : ℤ) : WithTop ℤ) ≤ curveVal hdvr x (algebraMap A M.functionField a) := by
  rw [← algebraMap_toStalk x.1 (forall_exists_algebraMap_eq hx) a,
    one_le_curveVal_algebraMap_iff hdvr x, toStalk_mem_maximalIdeal_iff hx]

omit [IsLocallyNoetherian M] [IsIntegral M] in
/-- A place of a curve is a closed point: its coheight is one, while the generic point, the only
other possibility in dimension one, is maximal. -/
private theorem isClosed_singleton_curvePlace [IsCurve F p] (P₀ : CurvePlace M) :
    IsClosed ({P₀.1} : Set M) := by
  refine Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint M
    (IsCurve.topologicalKrullDim_eq_one p) fun h => ?_
  have hmax : IsMax (genericPoint M) := fun y _ => genericPoint_specializes y
  have := P₀.2
  rw [h, Order.coheight_eq_zero.mpr hmax] at this
  exact zero_ne_one this

omit [IsDedekindDomain A] in
/-- The kernel of a twisted point is maximal: its values are roots of `z ^ Q ^ N = z`, so its
range is finite. -/
private theorem isMaximal_ker_of_twisted {Ω : Type*} [Field Ω] (σ : A ≃+* A) {N Q : ℕ}
    (hN : ∀ a, (⇑σ)^[N] a = a) (hRfin : {z : Ω | z ^ (Q ^ N) = z}.Finite) (φ : A →+* Ω)
    (hφ : ∀ a, φ (σ a) = φ a ^ Q) : (RingHom.ker φ).IsMaximal := by
  refine isMaximal_ker_of_finite_range φ (hRfin.subset ?_)
  rintro _ ⟨a, rfl⟩
  exact pow_pow_eq_of_twisted σ hN Q φ hφ a

include hdvr in
omit [IsDedekindDomain A] in
/-- The kernel of a twisted point is nonzero: were it trivial, `A` and with it the function field
of `M` would be finite, whereas a place of `M` carries an element of valuation one. -/
private theorem ker_ne_bot_of_twisted {Ω : Type*} [Field Ω] (σ : A ≃+* A) {N Q : ℕ}
    (hN : ∀ a, (⇑σ)^[N] a = a) (P₀ : CurvePlace M)
    (hRfin : {z : Ω | z ^ (Q ^ N) = z}.Finite) (φ : A →+* Ω)
    (hφ : ∀ a, φ (σ a) = φ a ^ Q) : RingHom.ker φ ≠ ⊥ := by
  intro hker
  have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot _).2 hker
  have : Finite A := by
    refine Finite.of_injective (β := hRfin.toFinset) (fun a => ⟨φ a, ?_⟩) fun a b h => ?_
    · rw [Set.Finite.mem_toFinset]
      exact pow_pow_eq_of_twisted σ hN Q φ hφ a
    · exact hinj (congrArg Subtype.val h)
  have : Finite M.functionField := by
    refine Finite.of_surjective (fun ab : A × A => algebraMap A M.functionField ab.1 /
      algebraMap A M.functionField ab.2) fun f => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) f
    exact ⟨(a, b), rfl⟩
  let : Fintype M.functionField := Fintype.ofFinite _
  obtain ⟨π, hπ⟩ := exists_curveVal_eq_one hdvr P₀
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at hπ
  have h0 := val_algebraMap (k := M.functionField) (curveVal hdvr P₀) hπ0
  rw [Algebra.algebraMap_self, RingHom.id_apply, hπ] at h0
  exact absurd h0 (by decide)

include hdvr hFA in
omit [IsDedekindDomain A] in
/-- **Counting the twisted points through their places.** A finite set `s` of twisted points maps
to places with fibres of size at most the degree, and the twisted Stepanov bound `hγ` limits the
total degree of the places other than `P₀`. -/
private theorem card_le_of_subset_twisted {Ω : Type*} [Field Ω] (ι : F →+* Ω)
    [Algebra.FiniteType F A] (P₀ : CurvePlace M) (hP₀ : curveDeg F p P₀ = 1) (Q c : ℕ)
    (T : Set (PointsOver A ι)) (hmax : ∀ φ ∈ T, (RingHom.ker φ.1).IsMaximal)
    (X : PointsOver A ι → CurvePlace M)
    (hX : ∀ φ ∈ T, ∀ f : M.functionField,
      (∃ s : M.presheaf.stalk (X φ).1, algebraMap _ M.functionField s = f) ↔
        ∃ a t : A, t ∉ RingHom.ker φ.1 ∧ f = algebraMap A M.functionField a *
          (algebraMap A _ t)⁻¹)
    (τ : M.functionField → M.functionField)
    (hcong : ∀ φ ∈ T, ∀ y, 0 ≤ curveVal hdvr (X φ) y →
      ((1 : ℤ) : WithTop ℤ) ≤ curveVal hdvr (X φ) (τ y - y ^ Q))
    (hγ : ∀ S : Finset (CurvePlace M), P₀ ∉ S →
      (∀ P ∈ S, ∀ y : M.functionField, 0 ≤ curveVal hdvr P y →
        ((1 : ℤ) : WithTop ℤ) ≤ curveVal hdvr P (τ y - y ^ Q)) →
      ∑ P ∈ S, curveDeg F p P + 1 ≤ c)
    (s : Finset (PointsOver A ι)) (hs : ↑s ⊆ T) : s.card ≤ c := by
  classical
  set S := s.image X
  have h2 : ∀ x ∈ S, (s.filter fun φ => X φ = x).card ≤ curveDeg F p x := by
    intro x hxS
    obtain ⟨φ₀, hφ₀s, rfl⟩ := Finset.mem_image.1 hxS
    have hφ₀ := hs hφ₀s
    have := hmax φ₀ hφ₀
    rw [← Set.ncard_coe_finset]
    exact (ncard_le_curveDeg p hFA ι (X φ₀) (forall_exists_algebraMap_eq (hX φ₀ hφ₀))
      (↑(s.filter fun φ => X φ = X φ₀)) fun φ hφ => by
        have hφ' : φ ∈ s ∧ X φ = X φ₀ := by simpa using hφ
        have hφT := hs hφ'.1
        refine ⟨hmax φ hφT, fun f => ?_⟩
        rw [← hφ'.2]
        exact hX φ hφT f).2
  calc s.card = ∑ x ∈ S, (s.filter fun φ => X φ = x).card :=
        Finset.card_eq_sum_card_image X s
    _ ≤ ∑ x ∈ S, curveDeg F p x := Finset.sum_le_sum h2
    _ ≤ ∑ x ∈ S.erase P₀, curveDeg F p x + 1 := by
        by_cases hP : P₀ ∈ S
        · rw [← Finset.add_sum_erase S _ hP, hP₀, add_comm]
        · rw [Finset.erase_eq_of_notMem hP]
          omega
    _ ≤ c := hγ (S.erase P₀) (Finset.notMem_erase P₀ S) fun x hx y hy => by
        obtain ⟨φ, hφs, rfl⟩ := Finset.mem_image.1 (Finset.mem_of_mem_erase hx)
        exact hcong φ (hs hφs) y hy

/-- A set all of whose finite subsets have at most `n` elements is finite with at most `n`
elements. -/
private theorem finite_and_ncard_le_of_card_le {α : Type*} (T : Set α) (n : ℕ)
    (h : ∀ s : Finset α, ↑s ⊆ T → s.card ≤ n) : T.Finite ∧ T.ncard ≤ n := by
  classical
  have hTfin : T.Finite := by
    by_contra hinf
    obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (n + 1)
    have := h s hs
    omega
  refine ⟨hTfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hTfin]
  exact h _ (by simp)

include hdvr hFA in
/-- **The twisted points of a Dedekind model are bounded by Stepanov's method.** Let `σ` be a
ring automorphism of finite order of `A` fixing `F`. There is `γ` such that for `Q = r²`,
`r = p ^ e > γ² + 3γ + 1`, the `σ`-twisted points `φ : A → Ω` over `ι`
(`φ(σ a) = φ(a) ^ Q`) number at most `Q + (2γ + 1) r`. -/
theorem ncard_twisted_le [Finite F] (pr : ℕ) [Fact pr.Prime] [CharP F pr] [IsProper p]
    [IsCurve F p] [Algebra.FiniteType F A] (P₀ : CurvePlace M)
    (hsurj : Function.Surjective fun c : F =>
      IsLocalRing.residue (M.presheaf.stalk P₀.1) ((fieldToStalk p P₀.1).hom c))
    (σ : A ≃+* A) (hσF : ∀ c, σ (algebraMap F A c) = algebraMap F A c) {N : ℕ} (hN0 : N ≠ 0)
    (hN : ∀ a, (⇑σ)^[N] a = a) {Ω : Type*} [Field Ω] (ι : F →+* Ω) :
    ∃ γ : ℕ, ∀ e : ℕ, γ ^ 2 + 3 * γ + 1 < pr ^ e →
      {φ : PointsOver A ι | ∀ a, φ.1 (σ a) = φ.1 a ^ (pr ^ e * pr ^ e)}.Finite ∧
      {φ : PointsOver A ι | ∀ a, φ.1 (σ a) = φ.1 a ^ (pr ^ e * pr ^ e)}.ncard ≤
        pr ^ e * pr ^ e + (2 * γ + 1) * pr ^ e := by
  classical
  have := Fintype.ofFinite F
  set τ : M.functionField ≃+* M.functionField :=
    IsFractionRing.ringEquivOfRingEquiv (K := M.functionField) (L := M.functionField) σ
  have hτ : ∀ a, τ (algebraMap A M.functionField a) = algebraMap A M.functionField (σ a) :=
    IsFractionRing.ringEquivOfRingEquiv_algebraMap σ
  have hτF : ∀ c : F, τ ((fieldToStalk p (genericPoint M)).hom c) =
      (fieldToStalk p (genericPoint M)).hom c := by
    intro c
    rw [← hFA, hτ, hσF]
  obtain ⟨P₁, hP₁val, hmaps⟩ := exists_mapsTo_poleSpace p hdvr τ hτF P₀
  have hP₀ : curveDeg F p P₀ = 1 := curveDeg_eq_one_of_surjective p P₀ hsurj
  have hP₁ : curveDeg F p P₁ = 1 := curveDeg_eq_one_of_surjective p P₁
    (surjective_residue_of_curveVal_ringEquiv p hdvr τ hτF hP₁val hsurj)
  have hcl : IsClosed ({P₀.1} : Set M) := isClosed_singleton_curvePlace p P₀
  obtain ⟨γ, hγ⟩ := exists_sum_curveDeg_add_one_le_twisted p hdvr pr P₀ P₁ hcl hP₀ hP₁ hsurj τ
    hmaps
  refine ⟨γ, fun e he => ?_⟩
  set Q := pr ^ e * pr ^ e with hQ
  set T := {φ : PointsOver A ι | ∀ a, φ.1 (σ a) = φ.1 a ^ Q} with hTdef
  have hF : ∀ c : F, ∃ a : A, algebraMap A M.functionField a =
      (fieldToStalk p (genericPoint M)).hom c := fun c => ⟨_, hFA c⟩
  -- the kernel of a twisted point is a nonzero maximal ideal
  have hQN : 1 < Q ^ N := Nat.one_lt_pow hN0 (by
    have := (Fact.out : pr.Prime).one_lt
    have h1 : 1 ≤ pr ^ e := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 < pr ^ e := lt_of_le_of_lt (by omega) he
    nlinarith)
  obtain ⟨hRfin, -⟩ := setOf_pow_eq_self_finite_ncard_le (Ω := Ω) hQN
  have hmax : ∀ φ ∈ T, (RingHom.ker φ.1).IsMaximal :=
    fun φ hφ => isMaximal_ker_of_twisted σ hN hRfin φ.1 hφ
  have hbot : ∀ φ ∈ T, RingHom.ker φ.1 ≠ ⊥ :=
    fun φ hφ => ker_ne_bot_of_twisted hdvr σ hN P₀ hRfin φ.1 hφ
  have hplace : ∀ φ ∈ T, ∃ x : CurvePlace M, ∀ f : M.functionField,
      (∃ s : M.presheaf.stalk x.1, algebraMap _ M.functionField s = f) ↔
        ∃ a t : A, t ∉ RingHom.ker φ.1 ∧ f = algebraMap A M.functionField a *
          (algebraMap A _ t)⁻¹ := by
    intro φ hφ
    have := hmax φ hφ
    exact exists_curvePlace_eq_localization p hdvr hF _ (hbot φ hφ)
  have : Nonempty (CurvePlace M) := ⟨P₀⟩
  choose! X hX using hplace
  -- the congruence at the place of a twisted point
  have hcong : ∀ φ ∈ T, ∀ y, 0 ≤ curveVal hdvr (X φ) y →
      ((1 : ℤ) : WithTop ℤ) ≤ curveVal hdvr (X φ) (τ y - y ^ Q) := by
    intro φ hφ y hy
    have := hmax φ hφ
    exact one_le_curveVal_sub_pow_of_twisted hdvr σ Q φ.1 hφ (X φ) (hX φ hφ) y hy
  -- the bound for finite sets of twisted points, hence for all of `T`
  exact finite_and_ncard_le_of_card_le T _ fun s hs =>
    card_le_of_subset_twisted p hdvr hFA ι P₀ hP₀ Q _ T hmax X hX τ hcong (hγ e he) s hs

end Stacks.BombieriStepanov

end
