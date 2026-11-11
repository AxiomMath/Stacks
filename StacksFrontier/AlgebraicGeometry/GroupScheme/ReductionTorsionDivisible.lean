module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.ReductionTorsionBound
public import StacksFrontier.RingTheory.Jacobson.FiniteTypeIntMaximal
public import StacksFrontier.RingTheory.NoetherNormalization.BoundedDegreePoints.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Torsion points divisible by points of bounded degree

Let `𝒜` be a commutative group scheme over `Spec R`, separated and of finite type, and `k` a
field containing `R`. For an `R`-subalgebra `S ⊆ k` write `𝒜(S)` for the group of morphisms
`Spec S ⟶ 𝒜` over `Spec R`; restriction to `k` is injective
(`AlgebraicGeometry.specOverMap_comp_injective`).

Fix `0 ≠ f ∈ R`, a subalgebra `S₁ ⊆ k` of finite type over `ℤ` containing `1/f`, a maximal
ideal `𝔫` of `S₁` and `d ∈ ℕ`. This file shows that there is `N` such that the following holds.
Let `S ⊆ k` be a subalgebra with elements `v₁, …, v_d ∈ S` such that `S[1/f]` is spanned by
the `vᵢ` over `R[1/f]`, and `w ∈ 𝒜(S)` a point killed by a power of a prime `ℓ`. If
`z ∈ 𝒜(S₁)` agrees with `ℓ ^ N w` on `k`, then `z` is trivial at `𝔫`
(`AlgebraicGeometry.specOverMap_mk_comp_eq_one_of_eq_pow`).

The proof: `𝔪 = 𝔫 ∩ R` is maximal, as `S₁ / 𝔫` is finite. Let `F` be a finite field containing
every extension of `R / 𝔪` of degree at most `d`, and `N = #𝒜(F)`. The ring `T = S₁[S] ⊆ k` is
integral over `S₁` (`isIntegral_of_forall_pow_smul_mem_span`), so `𝔫` is the trace of a maximal
ideal `𝔑` of `T`. The trace `𝔮` of `𝔑` on `S` lies over `𝔪`, so `S / 𝔮` is a field of degree at
most `d` over `R / 𝔪` (`Ideal.Quotient.finite_and_finrank_le_of_forall_pow_smul_mem_span`) and
embeds into `F`. The image of `w` in `𝒜(S / 𝔮) ⊆ 𝒜(F)` is a point of `ℓ`-power order of a
group with `N` elements, hence is killed by `ℓ ^ N`; so the image of `z` in `𝒜(T / 𝔑)` is
trivial, and so is its image in `𝒜(S₁ / 𝔫) ⊆ 𝒜(T / 𝔑)`.

Together with the fact that a point over the spectrum of a reduced Jacobson ring which is trivial
at every closed point is trivial (`AlgebraicGeometry.eq_of_forall_isMaximal`), this rules out a
nonzero point of `𝒜(k)` which is `ℓ ^ N`-divisible by `ℓ`-power torsion points of bounded degree
for every `N`; no analysis of the kernel of reduction at a single place is needed.

## Main results

* `AlgebraicGeometry.ext_of_forall_isMaximal_of_isSeparated` and
  `AlgebraicGeometry.eq_of_forall_isMaximal`: morphisms out of the spectrum of a reduced Jacobson
  ring are determined by their restrictions to the closed points.
* `AlgebraicGeometry.isIntegral_of_forall_pow_smul_mem_span`.
* `AlgebraicGeometry.specOverMap_mk_comp_eq_one_of_eq_pow`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- **Two morphisms out of the spectrum of a reduced Jacobson ring which agree on the closed
points are equal**, if they agree after a separated morphism. The fibre product of `(a, b)` with
the diagonal contains every closed point, which are dense, so it maps dominantly to `Spec S`. -/
theorem ext_of_forall_isMaximal_of_isSeparated {S : Type u} [CommRing S] [IsJacobsonRing S]
    [_root_.IsReduced S] {Y Z : Scheme.{u}} (s : Y ⟶ Z) [IsSeparated s] {a b : Spec (.of S) ⟶ Y}
    (hab : a ≫ s = b ≫ s)
    (h : ∀ 𝔫 : Ideal S, 𝔫.IsMaximal → Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔫)) ≫ a =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔫)) ≫ b) : a = b := by
  let j := pullback.fst (pullback.lift a b hab) (pullback.diagonal s)
  have ha : j ≫ a = pullback.snd _ _ := by
    have := pullback.condition (f := pullback.lift a b hab) (g := pullback.diagonal s) =≫
      pullback.fst s s
    rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst,
      Category.comp_id] at this
    exact this
  have hb : j ≫ b = pullback.snd _ _ := by
    have := pullback.condition (f := pullback.lift a b hab) (g := pullback.diagonal s) =≫
      pullback.snd s s
    rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd,
      Category.comp_id] at this
    exact this
  have : IsDominant j := by
    rw [isDominant_iff, DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff,
      ← closure_closedPoints]
    refine closure_mono fun x hx => ?_
    have hmax : x.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hx
    let := Ideal.Quotient.field x.asIdeal
    let q : Spec (.of (S ⧸ x.asIdeal)) ⟶ Spec (.of S) :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk x.asIdeal))
    have hq : q ≫ a = q ≫ b := h x.asIdeal hmax
    let l := pullback.lift (f := pullback.lift a b hab) (g := pullback.diagonal s) q (q ≫ a)
      (by
        apply pullback.hom_ext <;>
          simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
            pullback.diagonal_snd, Category.comp_id, hq])
    have hl : l ≫ j = q := pullback.lift_fst _ _ _
    refine ⟨l (IsLocalRing.closedPoint _), ?_⟩
    change (l ≫ j) _ = x
    rw [hl]
    have hq' : (q (IsLocalRing.closedPoint (S ⧸ x.asIdeal))).asIdeal = x.asIdeal := by
      change Ideal.comap (Ideal.Quotient.mk x.asIdeal) (IsLocalRing.maximalIdeal _) = _
      rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact PrimeSpectrum.ext hq'
  exact ext_of_isDominant_of_isSeparated s hab j (ha.trans hb.symm)

variable {R : Type u} [CommRing R]

/-- **Points over a reduced Jacobson ring are determined at the closed points.** Two morphisms
`Spec S ⟶ 𝒜` over `Spec R` into a separated scheme over `Spec R`, with `S` reduced and Jacobson,
which agree on `Spec (S / 𝔫)` for every maximal ideal `𝔫`, are equal. -/
theorem eq_of_forall_isMaximal (𝒜 : Over (Spec (.of R))) [IsSeparated 𝒜.hom] {S : Type u}
    [CommRing S] [Algebra R S] [IsJacobsonRing S] [_root_.IsReduced S] {a b : specOver R S ⟶ 𝒜}
    (h : ∀ 𝔫 : Ideal S, 𝔫.IsMaximal →
      specOverMap (Ideal.Quotient.mkₐ R 𝔫) ≫ a = specOverMap (Ideal.Quotient.mkₐ R 𝔫) ≫ b) :
    a = b := by
  apply Over.OverMorphism.ext
  refine ext_of_forall_isMaximal_of_isSeparated 𝒜.hom ((Over.w a).trans (Over.w b).symm)
    fun 𝔫 h𝔫 => ?_
  exact congrArg CommaMorphism.left (h 𝔫 h𝔫)

/-- Restriction of points along an `R`-algebra map of fields is injective. -/
theorem specOverMap_comp_injective_of_field (𝒜 : Over (Spec (.of R))) {K L : Type u} [Field K]
    [Field L] [Algebra R K] [Algebra R L] (φ : K →ₐ[R] L) :
    Function.Injective (fun a : specOver R K ⟶ 𝒜 => specOverMap φ ≫ a) := by
  intro a b h
  apply Over.OverMorphism.ext
  have h' := congrArg CommaMorphism.left h
  simp only [Over.comp_left, specOverMap_left] at h'
  exact specMap_comp_injective_of_field (X := 𝒜.left) φ.toRingHom h'

/-- **Integrality of a subring of bounded degree.** Let `S₁, S ⊆ k` be `R`-subalgebras of a field,
`0 ≠ f ∈ R` with `1/f ∈ S₁`, and `v₁, …, v_d ∈ S` such that every `s ∈ S` has
`f ^ M • s ∈ span R {vᵢ}` for some `M`. Then every element of `S` is integral over `S₁`: it
stabilizes the finitely generated `S₁`-module `span S₁ {vᵢ} ⊇ S`. -/
theorem isIntegral_of_forall_pow_smul_mem_span {k : Type*} [Field k] [Algebra R k]
    (S₁ : Subalgebra R k) {f : R} (hf0 : algebraMap R k f ≠ 0) (hf : (algebraMap R k f)⁻¹ ∈ S₁)
    (S : Subalgebra R k) {d : ℕ} (v : Fin d → k) (hv : ∀ i, v i ∈ S)
    (hS : ∀ s ∈ S, ∃ M : ℕ, f ^ M • s ∈ Submodule.span R (Set.range v)) {s : k} (hs : s ∈ S) :
    _root_.IsIntegral S₁ s := by
  let N : Submodule S₁ k := Submodule.span S₁ (Set.range v)
  have hsub : ∀ x ∈ S, x ∈ N := by
    intro x hx
    obtain ⟨M, hM⟩ := hS x hx
    have h1 : f ^ M • x ∈ N := Submodule.span_le_restrictScalars R S₁ _ hM
    have h2 : x = (⟨(algebraMap R k f)⁻¹, hf⟩ : S₁) ^ M • (f ^ M • x) := by
      simp only [Algebra.smul_def, map_pow]
      rw [← mul_assoc, ← mul_pow]
      change x = ((algebraMap R k f)⁻¹ * algebraMap R k f) ^ M * x
      rw [inv_mul_cancel₀ hf0, one_pow, one_mul]
    rw [h2]
    exact N.smul_mem _ h1
  refine isIntegral_of_smul_mem_submodule N ?_ (Submodule.fg_span (Set.finite_range v)) s ?_
  · intro hN
    have h1 : (1 : k) ∈ N := hsub 1 S.one_mem
    rw [hN] at h1
    exact one_ne_zero ((Submodule.mem_bot S₁).mp h1)
  · intro n hn
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hsub _ (S.mul_mem hs (hv i))
    | zero => simp
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact N.add_mem hx hy
    | smul c x _ hx =>
      rw [smul_comm]
      exact N.smul_mem c hx

/-- In a finite group, an element killed by a power of a prime `ℓ` is killed by `ℓ ^ #G`. -/
theorem pow_prime_pow_natCard_eq_one {G : Type*} [Group G] [Finite G] {ℓ : ℕ} (hℓ : ℓ.Prime)
    {x : G} {e : ℕ} (hx : x ^ (ℓ ^ e) = 1) : x ^ (ℓ ^ Nat.card G) = 1 := by
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hℓ).mp (orderOf_dvd_of_pow_eq_one hx)
  rw [← orderOf_dvd_iff_pow_eq_one, ha]
  refine Nat.pow_dvd_pow ℓ ((Nat.lt_pow_self hℓ.one_lt).le.trans ?_)
  rw [← ha]
  exact orderOf_le_card

/-- **A point `ℓ ^ N`-divisible by an `ℓ`-power torsion point of bounded degree is trivial at a
closed point.** Let `S₁ ⊆ k` be an `R`-subalgebra of finite type over `ℤ` containing `1/f` for
some `0 ≠ f ∈ R`, `𝔫` a maximal ideal of `S₁`, `d ∈ ℕ` and `ℓ` a prime. There is `N` such that,
for every `R`-subalgebra `S ⊆ k` with elements `v₁, …, v_d ∈ S` such that every `s ∈ S` has
`f ^ M • s ∈ span R {vᵢ}` for some `M`, every `w ∈ 𝒜(S)` killed by a power of `ℓ` and every
`z ∈ 𝒜(S₁)` which agrees on `k` with `ℓ ^ N w`, the restriction of `z` to `Spec (S₁ / 𝔫)` is
trivial. One can take `N = #𝒜(F)` for a finite field `F` containing every extension of degree at
most `d` of `R / (𝔫 ∩ R)`. -/
theorem specOverMap_mk_comp_eq_one_of_eq_pow (𝒜 : Over (Spec (.of R))) [GrpObj 𝒜]
    [IsCommMonObj 𝒜] [LocallyOfFiniteType 𝒜.hom] [QuasiCompact 𝒜.hom] [IsSeparated 𝒜.hom]
    {k : Type u} [Field k] [Algebra R k] (S₁ : Subalgebra R k) [Algebra.FiniteType ℤ S₁] {f : R}
    (hf0 : algebraMap R k f ≠ 0) (hf : (algebraMap R k f)⁻¹ ∈ S₁) (𝔫 : Ideal S₁) [h𝔫 : 𝔫.IsMaximal]
    (d : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ N : ℕ, ∀ (S : Subalgebra R k) (v : Fin d → k), (∀ i, v i ∈ S) →
      (∀ s ∈ S, ∃ M : ℕ, f ^ M • s ∈ Submodule.span R (Set.range v)) →
      ∀ (z : specOver R S₁ ⟶ 𝒜) (w : specOver R S ⟶ 𝒜) (e : ℕ), w ^ (ℓ ^ e) = 1 →
        specOverMap S₁.val ≫ z = (specOverMap S.val ≫ w) ^ (ℓ ^ N) →
        specOverMap (Ideal.Quotient.mkₐ R 𝔫) ≫ z = 1 := by
  -- the maximal ideal `𝔪 = 𝔫 ∩ R`
  set 𝔪 : Ideal R := 𝔫.comap (algebraMap R S₁)
  have : Finite (S₁ ⧸ 𝔫) := finite_quotient_of_isMaximal_of_finiteType_int 𝔫
  have : Finite (R ⧸ 𝔪) :=
    Finite.of_injective _ (Ideal.quotientMap_injective (I := 𝔫) (f := algebraMap R S₁))
  have h𝔪 : 𝔪.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
  have hf𝔪 : f ∉ 𝔪 := by
    intro h
    have hu : IsUnit (algebraMap R S₁ f) := by
      refine IsUnit.of_mul_eq_one ⟨(algebraMap R k f)⁻¹, hf⟩ (Subtype.ext ?_)
      change algebraMap R k f * (algebraMap R k f)⁻¹ = 1
      exact mul_inv_cancel₀ hf0
    exact h𝔫.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  let := Ideal.Quotient.field 𝔪
  obtain ⟨F, _, _, _, hF⟩ := FiniteField.exists_algHom_of_finrank_le (R ⧸ 𝔪) d
  let : Algebra R F := ((algebraMap (R ⧸ 𝔪) F).comp (Ideal.Quotient.mk 𝔪)).toAlgebra
  have : IsScalarTower R (R ⧸ 𝔪) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Finite (specOver R F ⟶ 𝒜) := by
    have := finite_sections_of_finite 𝒜.hom F
    exact Finite.of_injective (fun x : specOver R F ⟶ 𝒜 =>
      (⟨x.left, Over.w x⟩ : {p : Spec (.of F) ⟶ 𝒜.left //
        p ≫ 𝒜.hom = Spec.map (CommRingCat.ofHom (algebraMap R F))})) fun x y h =>
      Over.OverMorphism.ext (congrArg Subtype.val h)
  refine ⟨Nat.card (specOver R F ⟶ 𝒜), fun S v hv hS z w e hw hz => ?_⟩
  set N := Nat.card (specOver R F ⟶ 𝒜)
  -- the ring `T = S₁[S]`, integral over `S₁`
  let T : Subalgebra R k := S₁ ⊔ S
  let i₁ : S₁ →ₐ[R] T := Subalgebra.inclusion le_sup_left
  let i₂ : S →ₐ[R] T := Subalgebra.inclusion le_sup_right
  let : Algebra S₁ T := i₁.toRingHom.toAlgebra
  have : Algebra.IsIntegral S₁ T := by
    have hle : T ≤ (integralClosure S₁ k).restrictScalars R := by
      refine sup_le (fun x hx => ?_) (fun x hx =>
        isIntegral_of_forall_pow_smul_mem_span S₁ hf0 hf S v hv hS hx)
      exact isIntegral_algebraMap (R := S₁) (x := (⟨x, hx⟩ : S₁))
    refine ⟨fun t => ?_⟩
    let φ : T →ₐ[S₁] k := { T.val.toRingHom with commutes' := fun _ => rfl }
    exact (isIntegral_algHom_iff φ Subtype.val_injective).mp (hle t.2)
  have hinj : Function.Injective (algebraMap S₁ T) :=
    Subalgebra.inclusion_injective (le_sup_left : S₁ ≤ T)
  obtain ⟨𝔑, h𝔑, hcomap⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := T) 𝔫 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le)
  -- the residue field of `S` at `𝔮 = 𝔑 ∩ S`
  let 𝔮 : Ideal S := 𝔑.comap i₂
  have : 𝔮.LiesOver 𝔪 := by
    constructor
    change 𝔫.comap (algebraMap R S₁) = (𝔑.comap i₂.toRingHom).comap (algebraMap R S)
    rw [← hcomap, Ideal.comap_comap, Ideal.comap_comap]
    rfl
  let e' : Fin d → S := fun i => ⟨v i, hv i⟩
  have he' : ∀ a : S, ∃ M : ℕ, f ^ M • a ∈ Submodule.span R (Set.range e') := by
    intro a
    obtain ⟨M, hM⟩ := hS a a.2
    refine ⟨M, ?_⟩
    have hmap : Submodule.span R (Set.range v) =
        (Submodule.span R (Set.range e')).map S.val.toLinearMap := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hmap] at hM
    obtain ⟨y, hy, hya⟩ := hM
    have : y = f ^ M • a := Subtype.val_injective hya
    exact this ▸ hy
  have : 𝔮.IsMaximal := Ideal.isMaximal_of_liesOver_of_forall_pow_smul_mem_span e' he' 𝔪 𝔮 hf𝔪
  obtain ⟨hfinq, hrank⟩ :=
    Ideal.Quotient.finite_and_finrank_le_of_forall_pow_smul_mem_span e' he' 𝔪 𝔮 hf𝔪
  let := Ideal.Quotient.field 𝔮
  obtain ⟨τ⟩ := hF (S ⧸ 𝔮) hrank
  -- the image of `w` over `S / 𝔮` is killed by `ℓ ^ N`
  let wL := specOverMap (Ideal.Quotient.mkₐ R 𝔮) ≫ w
  have hwL : wL ^ (ℓ ^ N) = 1 := by
    have hwF : (specOverMap (τ.restrictScalars R) ≫ wL) ^ (ℓ ^ e) = 1 := by
      rw [← MonObj.comp_pow, ← MonObj.comp_pow, hw, MonObj.comp_one, MonObj.comp_one]
    apply specOverMap_comp_injective_of_field 𝒜 (τ.restrictScalars R)
    simp only
    rw [MonObj.comp_one, MonObj.comp_pow]
    exact pow_prime_pow_natCard_eq_one hℓ hwF
  -- the relation over `T`
  have hzT : specOverMap i₁ ≫ z = (specOverMap i₂ ≫ w) ^ (ℓ ^ N) := by
    apply specOverMap_comp_injective 𝒜 T.val Subtype.val_injective
    simp only
    rw [MonObj.comp_pow, ← Category.assoc, ← Category.assoc, specOverMap_comp,
      specOverMap_comp]
    exact hz
  -- the image in `T / 𝔑`
  let := Ideal.Quotient.field 𝔑
  let q₁ : S₁ ⧸ 𝔫 →ₐ[R] T ⧸ 𝔑 := Ideal.quotientMapₐ 𝔑 i₁ hcomap.ge
  let q₂ : S ⧸ 𝔮 →ₐ[R] T ⧸ 𝔑 := Ideal.quotientMapₐ 𝔑 i₂ le_rfl
  have h1 : (Ideal.Quotient.mkₐ R 𝔑).comp i₁ = q₁.comp (Ideal.Quotient.mkₐ R 𝔫) := by
    ext; rfl
  have h2 : (Ideal.Quotient.mkₐ R 𝔑).comp i₂ = q₂.comp (Ideal.Quotient.mkₐ R 𝔮) := by
    ext; rfl
  let := Ideal.Quotient.field 𝔫
  apply specOverMap_comp_injective_of_field 𝒜 q₁
  simp only
  rw [MonObj.comp_one, ← Category.assoc, specOverMap_comp, ← h1, ← specOverMap_comp,
    Category.assoc, hzT, MonObj.comp_pow, ← Category.assoc, specOverMap_comp, h2,
    ← specOverMap_comp, Category.assoc, ← MonObj.comp_pow, hwL, MonObj.comp_one]

end AlgebraicGeometry

end
