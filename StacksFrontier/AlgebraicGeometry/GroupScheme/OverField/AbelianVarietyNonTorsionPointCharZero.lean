module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyNonTorsionPoint
public import StacksFrontier.AlgebraicGeometry.GroupScheme.PointsOverBaseChange
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ReductionTorsionBound
public import StacksFrontier.AlgebraicGeometry.GroupScheme.SpreadingOut.Model
public import StacksFrontier.RingTheory.Jacobson.FiniteTypeIntMaximal
public import StacksFrontier.RingTheory.NoetherNormalization.BoundedDegreePoints.Main

/-!
# Points of infinite order on an abelian variety in characteristic zero

Let `k` be an algebraically closed field of characteristic `0` and `A` an abelian variety over `k`
of positive dimension. Then `A(k)` has a point of infinite order.

The proof is by specialization. `A` and its group law are the base change of a commutative group
scheme `𝒜`, separated and of finite type, over a finitely generated `ℤ`-subalgebra `R ⊆ k`
(`AlgebraicGeometry.exists_grpObj_model`). An affine open `Spec B ⊆ 𝒜` has infinitely many
`k`-points, so a spread-out Noether normalization of `B` gives infinitely many distinct points
`P_n ∈ 𝒜(k)`, each coming from a local domain `O_n` finite over `R` whose residue fields over the
maximal ideals of a dense open of `Spec R` have bounded degree `d`
(`exists_boundedDegree_points`). Choose two maximal ideals `𝔪₁, 𝔪₂` there of different residue
characteristics `ℓ₁ ≠ ℓ₂` (`exists_isMaximal_ringChar_ne`) and finite fields `Fᵢ` containing every
extension of degree `≤ d` of `R/𝔪ᵢ`. If all of `A(k)` were torsion, the part of the order of
`P_n` prime to `ℓᵢ` would be at most `#𝒜(Fᵢ)` (`AlgebraicGeometry.ordCompl_addOrderOf_le_natCard`),
so the orders of the `P_n` would be bounded, and the `P_n` would lie in the finite group
`A(k)[N]` for a fixed `N`: a contradiction.

## Main results

* `Stacks.Groupoids.exists_not_isOfFinAddOrder_of_charZero`.
* `Stacks.Groupoids.exists_not_isOfFinAddOrder_of_charZero_or_uncountable`: together with the
  uncountable case.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] (𝒜 : Over (Spec (.of R)))

/-- The ring map `R → Γ(𝒜, U)` of an affine open `U` of a scheme `𝒜` over `Spec R`: the unique one
whose spectrum is `U ≅ Spec Γ(𝒜, U) ⟶ 𝒜 ⟶ Spec R`. -/
noncomputable def affineSectionsRingHom {U : 𝒜.left.Opens} (hU : IsAffineOpen U) :
    CommRingCat.of R ⟶ Γ(𝒜.left, U) :=
  Spec.preimage (hU.fromSpec ≫ 𝒜.hom)

lemma specMap_affineSectionsRingHom {U : 𝒜.left.Opens} (hU : IsAffineOpen U) :
    Spec.map (affineSectionsRingHom 𝒜 hU) = hU.fromSpec ≫ 𝒜.hom :=
  Spec.map_preimage _

/-- The chart `Spec Γ(𝒜, U) ⟶ 𝒜` of an affine open, as a morphism over `Spec R`. -/
noncomputable def affineChart {U : 𝒜.left.Opens} (hU : IsAffineOpen U) :
    letI := (affineSectionsRingHom 𝒜 hU).hom.toAlgebra
    specOver R Γ(𝒜.left, U) ⟶ 𝒜 :=
  letI := (affineSectionsRingHom 𝒜 hU).hom.toAlgebra
  Over.homMk hU.fromSpec (specMap_affineSectionsRingHom 𝒜 hU).symm

lemma finiteType_affineSectionsRingHom [LocallyOfFiniteType 𝒜.hom] {U : 𝒜.left.Opens}
    (hU : IsAffineOpen U) : (affineSectionsRingHom 𝒜 hU).hom.FiniteType := by
  have : LocallyOfFiniteType (Spec.map (affineSectionsRingHom 𝒜 hU)) := by
    rw [specMap_affineSectionsRingHom]
    infer_instance
  exact HasRingHomProperty.Spec_iff.mp this

/-- **Points through an affine chart.** A `k`-point of `𝒜` over `Spec R` whose image lies in an
affine open `U` comes from an `R`-algebra map `Γ(𝒜, U) → k`. -/
lemma exists_algHom_of_mem {k : Type u} [Field k] [Algebra R k] {U : 𝒜.left.Opens}
    (hU : IsAffineOpen U) (p : specOver R k ⟶ 𝒜)
    (hp : p.left (IsLocalRing.closedPoint k) ∈ U) :
    letI := (affineSectionsRingHom 𝒜 hU).hom.toAlgebra
    ∃ σ : Γ(𝒜.left, U) →ₐ[R] k, specOverMap σ ≫ affineChart 𝒜 hU = p := by
  let := (affineSectionsRingHom 𝒜 hU).hom.toAlgebra
  have hrange : Set.range p.left ⊆ (U : Set 𝒜.left) := by
    rintro _ ⟨y, rfl⟩
    have : y = IsLocalRing.closedPoint k := by
      apply PrimeSpectrum.ext
      change y.asIdeal = IsLocalRing.maximalIdeal k
      rw [@Ideal.eq_bot_of_prime _ _ y.asIdeal y.isPrime, IsLocalRing.maximalIdeal_eq_bot]
    rw [this]
    exact hp
  let l : Spec (.of k) ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι p.left (by rw [Scheme.Opens.range_ι]; exact hrange)
  have hl : l ≫ U.ι = p.left := IsOpenImmersion.lift_fac _ _ _
  let σ₀ : Γ(𝒜.left, U) ⟶ CommRingCat.of k := Spec.preimage (l ≫ hU.isoSpec.hom)
  have hσ₀ : Spec.map σ₀ ≫ hU.fromSpec = p.left := by
    rw [Spec.map_preimage, IsAffineOpen.fromSpec, Category.assoc, Iso.hom_inv_id_assoc, hl]
  have hcomp : affineSectionsRingHom 𝒜 hU ≫ σ₀ = CommRingCat.ofHom (algebraMap R k) := by
    apply Spec.map_injective
    rw [Spec.map_comp, specMap_affineSectionsRingHom, ← Category.assoc, hσ₀]
    exact Over.w p
  refine ⟨{ σ₀.hom with commutes' := fun r => congrArg (fun φ => φ.hom r) hcomp }, ?_⟩
  apply Over.OverMorphism.ext
  exact hσ₀

/-- **Some affine chart carries infinitely many `k`-points.** If `𝒜` is quasi-compact over
`Spec R` and has infinitely many `k`-points, then for some affine open `U` there are infinitely
many `R`-algebra maps `Γ(𝒜, U) → k`. -/
lemma exists_isAffineOpen_infinite_algHom [QuasiCompact 𝒜.hom] {k : Type u} [Field k]
    [Algebra R k] [Infinite (specOver R k ⟶ 𝒜)] :
    ∃ (U : 𝒜.left.Opens) (hU : IsAffineOpen U),
      letI := (affineSectionsRingHom 𝒜 hU).hom.toAlgebra
      Infinite (Γ(𝒜.left, U) →ₐ[R] k) := by
  have : CompactSpace 𝒜.left := by
    have : QuasiCompact (𝒜.hom ≫ terminal.from _) := inferInstance
    exact (quasiCompact_iff_compactSpace _).mp ‹_›
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : 𝒜.left.affineOpens => (U : Set 𝒜.left)) (fun U => U.1.2) (fun x _ => by
      obtain ⟨W, hW, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
      exact Set.mem_iUnion.2 ⟨⟨W, hW⟩, hx⟩)
  by_contra hcon
  simp only [not_exists, not_infinite_iff_finite] at hcon
  have hfinV : ∀ V : 𝒜.left.affineOpens,
      {p : specOver R k ⟶ 𝒜 | p.left (IsLocalRing.closedPoint k) ∈ (V : Set 𝒜.left)}.Finite := by
    intro V
    let := (affineSectionsRingHom 𝒜 V.2).hom.toAlgebra
    have := hcon V.1 V.2
    have hσ : ∀ p : {p : specOver R k ⟶ 𝒜 |
        p.left (IsLocalRing.closedPoint k) ∈ (V : Set 𝒜.left)},
        ∃ σ : Γ(𝒜.left, V.1) →ₐ[R] k, specOverMap σ ≫ affineChart 𝒜 V.2 = p.1 :=
      fun p => exists_algHom_of_mem 𝒜 V.2 p.1 p.2
    choose σ hσ using hσ
    exact Set.finite_coe_iff.mp (Finite.of_injective σ fun p q h =>
      Subtype.ext ((hσ p).symm.trans (h ▸ hσ q)))
  have hall : (Set.univ : Set (specOver R k ⟶ 𝒜)) ⊆ ⋃ V ∈ t,
      {p : specOver R k ⟶ 𝒜 | p.left (IsLocalRing.closedPoint k) ∈ (V : Set 𝒜.left)} := by
    intro p _
    obtain ⟨V, hV, hx⟩ :=
      Set.mem_iUnion₂.1 (ht (Set.mem_univ (p.left (IsLocalRing.closedPoint k))))
    exact Set.mem_iUnion₂.2 ⟨V, hV, hx⟩
  have hfin := (t.finite_toSet.biUnion fun V _ => hfinV V).subset hall
  have := Set.finite_univ_iff.mp hfin
  exact not_finite (specOver R k ⟶ 𝒜)

/-- **A commutative group scheme over a finitely generated `ℤ`-domain of characteristic zero with
infinitely many `k`-points and finite `N`-torsion has a `k`-point of infinite order.** -/
theorem exists_not_isOfFinAddOrder_of_model [IsDomain R] [Algebra.FiniteType ℤ R] [CharZero R]
    [GrpObj 𝒜] [IsCommMonObj 𝒜] [LocallyOfFiniteType 𝒜.hom] [QuasiCompact 𝒜.hom]
    [IsSeparated 𝒜.hom] {k : Type u} [Field k] [IsAlgClosed k] [Algebra R k]
    (hk : Function.Injective (algebraMap R k)) [Infinite (specOver R k ⟶ 𝒜)]
    (htors : ∀ N : ℕ, N ≠ 0 →
      {x : Additive (specOver R k ⟶ 𝒜) | N • x = 0}.Finite) :
    ∃ x : Additive (specOver R k ⟶ 𝒜), ¬ IsOfFinAddOrder x := by
  have : Infinite R := Infinite.of_injective Nat.cast Nat.cast_injective
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  obtain ⟨U, hU, hinf⟩ := exists_isAffineOpen_infinite_algHom 𝒜 (k := k)
  let := (affineSectionsRingHom 𝒜 hU).hom.toAlgebra
  have : Algebra.FiniteType R Γ(𝒜.left, U) := finiteType_affineSectionsRingHom 𝒜 hU
  obtain ⟨f, hf, d, ρ, hρ, hdata⟩ :=
    exists_boundedDegree_points_of_infinite (B := Γ(𝒜.left, U)) hk hinf
  obtain ⟨m₁, m₂, hm₁, hm₂, hf₁, hf₂, hne⟩ := exists_isMaximal_ringChar_ne f hf
  -- the points
  let P : ℕ → (specOver R k ⟶ 𝒜) := fun n => specOverMap (ρ n) ≫ affineChart 𝒜 hU
  have hP : Function.Injective P := by
    intro n n' h
    apply hρ
    have h1 := congrArg CommaMorphism.left h
    simp only [P, Over.comp_left, specOverMap_left, affineChart, Over.homMk_left] at h1
    have h2 := Spec.map_injective ((cancel_mono hU.fromSpec).mp h1)
    exact AlgHom.ext fun b => congrArg (fun φ => φ.hom b) h2
  -- the bound at one maximal ideal
  have hbound : ∀ (m : Ideal R) [m.IsMaximal], f ∉ m → ∃ ℓ C : ℕ, ℓ.Prime ∧
      ringChar (R ⧸ m) = ℓ ∧ ∀ n, IsOfFinAddOrder (Additive.ofMul (P n)) →
        ordCompl[ℓ] (addOrderOf (Additive.ofMul (P n))) ≤ C := by
    intro m hm hfm
    have : Finite (R ⧸ m) := finite_quotient_of_isMaximal_of_finiteType_int m
    let : Field (R ⧸ m) := Ideal.Quotient.field m
    have hℓ : (ringChar (R ⧸ m)).Prime := CharP.char_is_prime (R ⧸ m) _
    obtain ⟨F, _, _, _, hF⟩ := FiniteField.exists_algHom_of_finrank_le (R ⧸ m) d
    let : Algebra R F := ((algebraMap (R ⧸ m) F).comp (Ideal.Quotient.mk m)).toAlgebra
    have : IsScalarTower R (R ⧸ m) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
    refine ⟨ringChar (R ⧸ m), Nat.card (specOver R F ⟶ 𝒜), hℓ, rfl, fun n hn => ?_⟩
    obtain ⟨O, _, _, _, _, β, gk, hgk, hgkβ, hcomap, _, _, _, hrank⟩ := hdata n m hfm
    obtain ⟨τ₀⟩ := hF (IsLocalRing.ResidueField O) hrank
    have hchar : CharP (IsLocalRing.ResidueField O) (ringChar (R ⧸ m)) :=
      charP_of_injective_algebraMap (algebraMap (R ⧸ m) _).injective _
    have hPn : P n = specOverMap gk ≫ (specOverMap β ≫ affineChart 𝒜 hU) := by
      simp only [P, ← hgkβ, ← specOverMap_comp, Category.assoc]
    rw [hPn] at hn ⊢
    exact ordCompl_addOrderOf_le_natCard 𝒜 gk hgk (τ₀.restrictScalars R) hℓ hchar _ hn
  obtain ⟨ℓ₁, C₁, hℓ₁, hc₁, hC₁⟩ := hbound m₁ hf₁
  obtain ⟨ℓ₂, C₂, hℓ₂, hc₂, hC₂⟩ := hbound m₂ hf₂
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hle : ∀ n, addOrderOf (Additive.ofMul (P n)) ≤ C₁ * C₂ := fun n =>
    addOrderOf_le_mul_of_ordCompl_le (hcon _) hℓ₁ hℓ₂ (hc₁ ▸ hc₂ ▸ hne) (hC₁ n (hcon _))
      (hC₂ n (hcon _))
  have hM : (C₁ * C₂).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hmem : ∀ n, Additive.ofMul (P n) ∈
      {x : Additive (specOver R k ⟶ 𝒜) | (C₁ * C₂).factorial • x = 0} := fun n =>
    addOrderOf_dvd_iff_nsmul_eq_zero.mp (Nat.dvd_factorial (hcon _).addOrderOf_pos (hle n))
  have := (htors _ hM).to_subtype
  have : Finite ℕ := Finite.of_injective
    (fun n => (⟨Additive.ofMul (P n), hmem n⟩ : {x : Additive (specOver R k ⟶ 𝒜) |
      (C₁ * C₂).factorial • x = 0})) fun n n' h => hP (congrArg Subtype.val h)
  exact not_finite ℕ

end AlgebraicGeometry

namespace Stacks.Groupoids

/-- **An abelian variety `A ≠ 0` over an algebraically closed field `k` of characteristic zero
has a rational point of infinite order.**

This is the case of characteristic zero of the fact the proof of Stacks Tag 0AFB, part (a), uses
without proof ("there is such a nontorsion point as `k` is algebraically closed and not the
algebraic closure of a finite field -- this is actually not trivial to prove"). -/
theorem exists_not_isOfFinAddOrder_of_charZero {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] (A : Over (Spec (.of k))) [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A]
    (hA : 0 < topologicalKrullDim A.left) :
    ∃ a : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A), ¬ IsOfFinAddOrder a := by
  obtain ⟨R, _, _, _, φ, hφ, 𝒜, _, e, hlfp, hqc, hsep, hmon⟩ := exists_grpObj_model A
  let : Algebra R k := φ.toAlgebra
  have : CharZero R := φ.charZero
  have : LocallyOfFiniteType 𝒜.X.hom := inferInstance
  let ψ := basePointsHom φ 𝒜 e
  have hψi : Function.Injective ψ := basePointsHom_injective φ 𝒜 e
  have hψs : Function.Surjective ψ := basePointsHom_surjective φ 𝒜 e
  have : Infinite (specOver R k ⟶ 𝒜.X) := by
    have hk : Infinite k := inferInstance
    have h1 := cardinalMk_le_points A hA
    have : Infinite (𝟙_ (Over (Spec (.of k))) ⟶ A) :=
      Cardinal.infinite_iff.mpr ((Cardinal.infinite_iff.mp hk).trans h1)
    exact Infinite.of_surjective ψ hψs
  have htors : ∀ N : ℕ, N ≠ 0 → {x : Additive (specOver R k ⟶ 𝒜.X) | N • x = 0}.Finite := by
    intro N hN
    have hfin := finite_torsionBy_of_ne_zero A N hN
    refine Set.finite_coe_iff.mp (Finite.of_injective
      (fun x : {x : Additive (specOver R k ⟶ 𝒜.X) | N • x = 0} =>
        (⟨Additive.ofMul (ψ x.1.toMul), ?_⟩ : Submodule.torsionBy ℤ
          (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (N : ℤ))) ?_)
    · rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
      have := congrArg (fun y => Additive.ofMul (ψ y.toMul)) x.2
      simpa [toMul_nsmul, map_pow] using this
    · intro x y h
      exact Subtype.ext (Additive.toMul.injective (hψi (Additive.ofMul.injective
        (congrArg Subtype.val h))))
  obtain ⟨x, hx⟩ := exists_not_isOfFinAddOrder_of_model 𝒜.X (k := k) hφ htors
  refine ⟨Additive.ofMul (ψ x.toMul), fun h => hx ?_⟩
  have hinj : Function.Injective (MonoidHom.toAdditive ψ) := hψi
  rw [← addOrderOf_pos_iff] at h ⊢
  rwa [← addOrderOf_injective _ hinj x]

/-- **An abelian variety `A ≠ 0` over an algebraically closed field `k` which has characteristic
zero or is uncountable has a rational point of infinite order.** The general case, `k` not
algebraic over a finite prime field, is `Stacks.Groupoids.exists_not_isOfFinAddOrder`, in
`StacksFrontier/AlgebraicGeometry/GroupScheme/OverField/AbelianVarietyNonTorsionPointGeneral.lean`. -/
theorem exists_not_isOfFinAddOrder_of_charZero_or_uncountable {k : Type u} [Field k]
    [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A]
    (hA : 0 < topologicalKrullDim A.left) (hk : CharZero k ∨ Uncountable k) :
    ∃ a : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A), ¬ IsOfFinAddOrder a := by
  rcases hk with hk | hk
  · exact exists_not_isOfFinAddOrder_of_charZero A hA
  · exact exists_not_isOfFinAddOrder_of_uncountable A hA

end Stacks.Groupoids

end
