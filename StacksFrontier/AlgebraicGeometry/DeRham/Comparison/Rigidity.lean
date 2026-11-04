module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.LocalDescription
public import StacksFrontier.LinearAlgebra.ExteriorPower.Wedge
public import StacksFrontier.RingTheory.CompleteIntersection.CotangentDeterminant

/-!
# Rigidity of the canonical maps on differential forms

Let `ι : K → H` be a linear map, `L` a module and `δ ∈ L`. A family of maps
`c p : ⋀ᵖ H → ⋀ᵖ K ⊗ L` taking `1` to `1 ⊗ δ` and commuting with wedging on the left by the image
of `⋀^q K` is determined on the image of `⋀ᵖ K`: there it is `ω ↦ ω ⊗ δ`. If the cokernel of `ι`
is killed by powers of some `J` and `J` is a nonzerodivisor on every `⋀ᵖ K ⊗ L`, then such a
family is unique. Applied to `K = B ⊗[A] Ω[A⁄ℤ]` and `H = Ω[B⁄ℤ]`, this is the uniqueness of the
maps of Section 0FL7 on the "nice" objects of the proof of Tag 0FLA: there `Ω[A⁄ℤ]` is free, the
determinant line `L` has no `J`-torsion, and `J` is the Jacobian determinant of a square
presentation, which kills `Ω[B⁄A]`.

## Main definitions

* `Stacks.DeRham.IsFunnyMapFamily`: the two conditions `c⁰(1) = δ` and
  `c^{q+p}(ω ∧ η) = ω ∧ c^p(η)` of Section 0FL7.

## Main results

* `exteriorPower.exists_pow_smul_mem_range_map`: if the cokernel of `f` is `J`-power torsion,
  so is the cokernel of `⋀ᵖ f`.
* `Stacks.DeRham.IsFunnyMapFamily.map_map_eq_tmul`: on forms pulled back along `ι` the maps are
  `ω ↦ ω ⊗ δ`.
* `Stacks.DeRham.IsFunnyMapFamily.eq`: the rigidity statement for abstract modules.
* `Stacks.DeRham.IsFunnyMapFamily.eq_of_kaehler`: the rigidity statement for the maps
  `⋀ᵖ Ω[B⁄ℤ] → ⋀ᵖ (B ⊗[A] Ω[A⁄ℤ]) ⊗ L` when `Ω[B⁄A]` is `J`-power torsion.
* `Stacks.DeRham.IsFunnyMapFamily.eq_of_presentation` and
  `Stacks.DeRham.IsFunnyMapFamily.eq_of_presentation_of_isLocalization`: the case where `J` is the
  Jacobian determinant of a square presentation (of `B`, or of a ring of which `B` is a
  localization) and `Ω[A⁄ℤ]` is free.
* `Stacks.DeRham.IsFunnyMapFamily.presentationFunnyMap`: the maps of Tag 0FL9 form such a family.
* `Algebra.Presentation.relationJacobiMatrix_det_smul_eq_zero`: the Jacobian determinant of a
  square presentation kills `Ω[B⁄A]`.

## Implementation notes

The rigidity argument is the one of the proof of Tag 0FLA: if `J^k η = ⋀ᵖ ι (ω)` then
`J^k c(η) = c(⋀ᵖ ι (ω)) = ω ⊗ δ = J^k c'(η)`, and `J` is a nonzerodivisor on the target. The
hypothesis on `Ω[B⁄A]` replaces "`A → B[1/J]` is étale": it holds when `A → B[1/J]` is formally
unramified (`exists_pow_smul_eq_zero_of_formallyUnramified`), and for the Jacobian determinant of
a square presentation it holds with `k = 1` by Cramer's rule applied to the relations
`∑ᵢ ∂fⱼ/∂xᵢ dxᵢ = 0` of `Ω[B⁄A]`.

## References

* [Stacks Project, Tag 0FLA](https://stacks.math.columbia.edu/tag/0FLA)
* [Stacks Project, Section 0FL7](https://stacks.math.columbia.edu/tag/0FL7)
-/

@[expose] public section

open scoped TensorProduct

namespace exteriorPower

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- If every element of `N` is carried into the range of `f : M → N` by a power of `J`, the same
holds for the exterior powers: every element of `⋀ᵖ N` is carried into the range of `⋀ᵖ f` by a
power of `J`. -/
theorem exists_pow_smul_mem_range_map (f : M →ₗ[R] N) (J : R)
    (hf : ∀ x : N, ∃ k : ℕ, J ^ k • x ∈ LinearMap.range f) (p : ℕ) (η : ⋀[R]^p N) :
    ∃ k : ℕ, J ^ k • η ∈ LinearMap.range (map p f) := by
  have hη : η ∈ Submodule.span R (Set.range (ιMulti R p)) := by
    rw [ιMulti_span]
    exact Submodule.mem_top
  induction hη using Submodule.span_induction with
  | mem η hη =>
    obtain ⟨v, rfl⟩ := hη
    choose k w hw using fun i ↦ hf (v i)
    refine ⟨∑ i, k i, LinearMap.mem_range.mpr ⟨ιMulti R p w, ?_⟩⟩
    have hfw : (f ∘ w) = fun i ↦ J ^ k i • v i := funext hw
    rw [map_apply_ιMulti, hfw, (ιMulti R p).map_smul_univ, Finset.prod_pow_eq_pow_sum]
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    have hxy : J ^ (a + b) • (x + y) = J ^ b • (J ^ a • x) + J ^ a • (J ^ b • y) := by
      rw [smul_add, ← mul_smul, ← mul_smul, ← pow_add, ← pow_add, add_comm b a]
    exact ⟨a + b, hxy ▸ add_mem (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ hb)⟩
  | smul r x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, by rw [smul_comm]; exact Submodule.smul_mem _ r ha⟩

/-- Wedging on the right with the empty wedge `1 ∈ ⋀⁰ M` is the identity. -/
theorem wedgeMul_ιMulti_zero (p : ℕ) (x : ⋀[R]^p M) :
    wedgeMul p 0 x (ιMulti R 0 (fun j ↦ Fin.elim0 j)) = x :=
  Subtype.ext (by
    rw [wedgeMul_apply_coe, ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply, mul_one])

end exteriorPower

namespace Stacks.DeRham

open exteriorPower

section Abstract

variable {R K H L : Type*} [CommRing R] [AddCommGroup K] [Module R K] [AddCommGroup H]
  [Module R H] [AddCommGroup L] [Module R L]

/-- The two conditions of Section 0FL7 on a family of maps `c p : ⋀ᵖ H → ⋀ᵖ K ⊗ L` relative to
`ι : K → H` and `δ ∈ L`: the empty wedge goes to `1 ⊗ δ`, and `c` commutes with wedging on the
left by the image under `ι` of an exterior power of `K`. These are the properties
`Stacks.DeRham.presentationFunnyMap_zero` and `Stacks.DeRham.presentationFunnyMap_wedge` of the
maps of Tag 0FL9, for `K = B ⊗[A] Ω[A⁄ℤ]`, `H = Ω[B⁄ℤ]` and `L = det(NL_{B/A})`. -/
structure IsFunnyMapFamily (ι : K →ₗ[R] H) (δ : L)
    (c : ∀ p : ℕ, (⋀[R]^p H) →ₗ[R] (⋀[R]^p K) ⊗[R] L) : Prop where
  /-- The empty wedge goes to `1 ⊗ δ`. -/
  map_zero : c 0 (ιMulti R 0 (fun j ↦ Fin.elim0 j)) = ιMulti R 0 (fun j ↦ Fin.elim0 j) ⊗ₜ[R] δ
  /-- The maps commute with wedging on the left by pulled back forms. -/
  map_wedge : ∀ (q p : ℕ) (ω : ⋀[R]^q K) (η : ⋀[R]^p H),
    c (q + p) (wedgeMul q p (map q ι ω) η) = (wedgeMul q p ω).rTensor L (c p η)

namespace IsFunnyMapFamily

variable {ι : K →ₗ[R] H} {δ : L} {c c' : ∀ p : ℕ, (⋀[R]^p H) →ₗ[R] (⋀[R]^p K) ⊗[R] L}

/-- On forms pulled back along `ι` the maps of a family as in Section 0FL7 are `ω ↦ ω ⊗ δ`. -/
theorem map_map_eq_tmul (hc : IsFunnyMapFamily ι δ c) (p : ℕ) (ω : ⋀[R]^p K) :
    c p (map p ι ω) = ω ⊗ₜ[R] δ := by
  calc c p (map p ι ω)
      = c (p + 0) (wedgeMul p 0 (map p ι ω) (ιMulti R 0 (fun j ↦ Fin.elim0 j))) := by
        rw [wedgeMul_ιMulti_zero]
        rfl
    _ = (wedgeMul p 0 ω).rTensor L (ιMulti R 0 (fun j ↦ Fin.elim0 j) ⊗ₜ[R] δ) := by
        rw [hc.map_wedge, hc.map_zero]
    _ = ω ⊗ₜ[R] δ := by
        rw [LinearMap.rTensor_tmul, wedgeMul_ιMulti_zero]

/-- **Rigidity of the maps of Section 0FL7.** If every element of `H` is carried into the range
of `ι` by a power of `J`, and `J` is a nonzerodivisor on every `⋀ᵖ K ⊗ L`, then two families as in
Section 0FL7 relative to `ι` and the same `δ` agree. -/
theorem eq (hc : IsFunnyMapFamily ι δ c) (hc' : IsFunnyMapFamily ι δ c') (J : R)
    (hJ : ∀ x : H, ∃ k : ℕ, J ^ k • x ∈ LinearMap.range ι)
    (hreg : ∀ p : ℕ, IsSMulRegular ((⋀[R]^p K) ⊗[R] L) J) (p : ℕ) : c p = c' p := by
  refine LinearMap.ext fun η ↦ ?_
  obtain ⟨k, ω, hω⟩ := exists_pow_smul_mem_range_map ι J hJ p η
  refine ((hreg p).pow k) ?_
  show J ^ k • c p η = J ^ k • c' p η
  rw [← map_smul, ← map_smul, ← hω, hc.map_map_eq_tmul, hc'.map_map_eq_tmul]

end IsFunnyMapFamily

end Abstract

section Kaehler

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- If `Ω[B⁄A]` is killed by powers of `J`, then every element of `Ω[B⁄R]` is carried by a power of
`J` into the image of `B ⊗[A] Ω[A⁄R]`: the cokernel of that map is `Ω[B⁄A]`. -/
theorem exists_pow_smul_mem_range_mapBaseChange (R : Type*) [CommRing R] [Algebra R A]
    [Algebra R B] [IsScalarTower R A B] (J : B) (hJ : ∀ x : Ω[B⁄A], ∃ k : ℕ, J ^ k • x = 0)
    (x : Ω[B⁄R]) :
    ∃ k : ℕ, J ^ k • x ∈ LinearMap.range (KaehlerDifferential.mapBaseChange R A B) := by
  obtain ⟨k, hk⟩ := hJ (KaehlerDifferential.map R A B B x)
  exact ⟨k, by rw [KaehlerDifferential.range_mapBaseChange, LinearMap.mem_ker, map_smul, hk]⟩

/-- If `A → B[1/J]` is formally unramified, then `Ω[B⁄A]` is killed by powers of `J`: it is
`J`-power torsion because its localization `Ω[B[1/J]⁄A]` vanishes. -/
theorem exists_pow_smul_eq_zero_of_formallyUnramified (J : B)
    [Algebra.FormallyUnramified A (Localization.Away J)] (x : Ω[B⁄A]) :
    ∃ k : ℕ, J ^ k • x = 0 := by
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers J)
    (KaehlerDifferential.map A A B (Localization.Away J))).mp (Subsingleton.elim _ _)
  exact ⟨k, hk⟩

/-- If `J` kills `Ω[B⁄A]`, then its image kills `Ω[B'⁄A]` for every localization `B'` of `B`:
the latter is generated by the differentials of elements of `B`. -/
theorem algebraMap_smul_eq_zero_of_isLocalization {B' : Type*} [CommRing B'] [Algebra B B']
    [Algebra A B'] [IsScalarTower A B B'] (M : Submonoid B) [IsLocalization M B'] (J : B)
    (hJ : ∀ x : Ω[B⁄A], J • x = 0) (x : Ω[B'⁄A]) : algebraMap B B' J • x = 0 := by
  have hx : x ∈ Submodule.span B'
      (Set.range (KaehlerDifferential.map A A B B' ∘ KaehlerDifferential.D A B)) := by
    rw [KaehlerDifferential.span_range_map_derivation_of_isLocalization A B B' M]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    rw [Function.comp_apply, algebraMap_smul, ← map_smul, hJ, map_zero]
  | zero => exact smul_zero _
  | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
  | smul r y _ hy => rw [smul_comm, hy, smul_zero]

namespace IsFunnyMapFamily

variable {L : Type*} [AddCommGroup L] [Module B L] {δ : L}
  {c c' : ∀ p : ℕ, (⋀[B]^p Ω[B⁄ℤ]) →ₗ[B] (⋀[B]^p (B ⊗[A] Ω[A⁄ℤ])) ⊗[B] L}

/-- **Rigidity of the maps of Section 0FL7, Tag 0FLA.** Two families of maps
`⋀ᵖ Ω[B⁄ℤ] → ⋀ᵖ (B ⊗[A] Ω[A⁄ℤ]) ⊗ L` satisfying the conditions of Section 0FL7 for the same `δ`
agree, provided `Ω[B⁄A]` is killed by powers of `J` and `J` is a nonzerodivisor on every
`⋀ᵖ (B ⊗[A] Ω[A⁄ℤ]) ⊗ L`. -/
theorem eq_of_kaehler (hc : IsFunnyMapFamily (KaehlerDifferential.mapBaseChange ℤ A B) δ c)
    (hc' : IsFunnyMapFamily (KaehlerDifferential.mapBaseChange ℤ A B) δ c') (J : B)
    (hJ : ∀ x : Ω[B⁄A], ∃ k : ℕ, J ^ k • x = 0)
    (hreg : ∀ p : ℕ, IsSMulRegular ((⋀[B]^p (B ⊗[A] Ω[A⁄ℤ])) ⊗[B] L) J) (p : ℕ) :
    c p = c' p :=
  hc.eq hc' J (exists_pow_smul_mem_range_mapBaseChange ℤ J hJ) hreg p

/-- **Rigidity of the maps of Section 0FL7 on nice algebras, Tag 0FLA.** If `Ω[A⁄ℤ]` is free,
`Ω[B⁄A]` is killed by powers of `J` and `J` is a nonzerodivisor on `L`, then two families as in
Section 0FL7 for the same `δ` agree. -/
theorem eq_of_free [Module.Free A Ω[A⁄ℤ]]
    (hc : IsFunnyMapFamily (KaehlerDifferential.mapBaseChange ℤ A B) δ c)
    (hc' : IsFunnyMapFamily (KaehlerDifferential.mapBaseChange ℤ A B) δ c') (J : B)
    (hJ : ∀ x : Ω[B⁄A], ∃ k : ℕ, J ^ k • x = 0) (hL : IsSMulRegular L J) (p : ℕ) :
    c p = c' p :=
  hc.eq_of_kaehler hc' J hJ (fun _ ↦ hL.lTensor _) p

end IsFunnyMapFamily

end Kaehler

end Stacks.DeRham

namespace Algebra.Presentation

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}

/-- In `Ω[B⁄A]` the differentials of the generators satisfy the relations
`∑ᵢ ∂fⱼ/∂xᵢ dxᵢ = 0`, one for each relation `fⱼ` of the presentation. -/
theorem sum_relationJacobiMatrix_smul_D (P : Algebra.Presentation A B (Fin n) (Fin n))
    (j : Fin n) :
    ∑ i, P.relationJacobiMatrix i j • KaehlerDifferential.D A B (P.val i) = 0 := by
  have hsum : ((1 : B) ⊗ₜ[P.toExtension.Ring]
      KaehlerDifferential.D A P.toExtension.Ring (P.relation j) :
      P.toExtension.CotangentSpace) =
        ∑ i, P.relationJacobiMatrix i j • P.cotangentSpaceBasis i := by
    conv_lhs => rw [← P.cotangentSpaceBasis.sum_repr (1 ⊗ₜ _)]
    exact Finset.sum_congr rfl fun i _ ↦
      congrArg (· • P.cotangentSpaceBasis i) (P.cotangentSpaceBasis_repr_one_tmul _ i)
  have h := P.toExtension.exact_cotangentComplex_toKaehler.apply_apply_eq_zero
    (Algebra.Extension.Cotangent.mk ⟨P.relation j, P.relation_mem_ker j⟩)
  rw [Algebra.Extension.cotangentComplex_mk] at h
  change P.toExtension.toKaehler
    ((1 : B) ⊗ₜ[P.toExtension.Ring]
      KaehlerDifferential.D A P.toExtension.Ring (P.relation j)) = 0 at h
  rw [hsum, map_sum] at h
  simpa only [map_smul, Algebra.Generators.toKaehler_cotangentSpaceBasis] using h

/-- **The Jacobian determinant of a square presentation kills `Ω[B⁄A]`.** -/
theorem relationJacobiMatrix_det_smul_eq_zero (P : Algebra.Presentation A B (Fin n) (Fin n))
    (x : Ω[B⁄A]) : P.relationJacobiMatrix.det • x = 0 := by
  set M := P.relationJacobiMatrix
  set e : Fin n → Ω[B⁄A] := fun i ↦ KaehlerDifferential.D A B (P.val i)
  have hcol (k : Fin n) : M.det • e k = 0 := by
    calc M.det • e k = ∑ i, (M * M.adjugate) i k • e i := by
          rw [Matrix.mul_adjugate]
          simp [Matrix.one_apply, ite_smul]
      _ = ∑ j, M.adjugate j k • ∑ i, M i j • e i := by
          simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          simp only [mul_comm]
      _ = 0 := by simp [e, M, sum_relationJacobiMatrix_smul_D]
  obtain ⟨y, rfl⟩ := P.toExtension.toKaehler_surjective x
  rw [← P.cotangentSpaceBasis.sum_repr y]
  simp only [map_sum, map_smul, Algebra.Generators.toKaehler_cotangentSpaceBasis,
    Finset.smul_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [smul_comm, hcol, smul_zero]

end Algebra.Presentation

namespace Stacks.DeRham.IsFunnyMapFamily

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}
  {L : Type*} [AddCommGroup L] [Module B L] {δ : L}
  {c c' : ∀ p : ℕ, (⋀[B]^p Ω[B⁄ℤ]) →ₗ[B] (⋀[B]^p (B ⊗[A] Ω[A⁄ℤ])) ⊗[B] L}

/-- **Rigidity of the maps of Section 0FL7 for a square presentation, Tag 0FLA.** If `Ω[A⁄ℤ]` is
free and the Jacobian determinant `J` of a square presentation of `B` over `A` is a
nonzerodivisor on `L` (e.g. `L` free of rank one and `J` a nonzerodivisor of `B`), then two
families as in Section 0FL7 for the same `δ` agree. -/
theorem eq_of_presentation [Module.Free A Ω[A⁄ℤ]]
    (hc : IsFunnyMapFamily (KaehlerDifferential.mapBaseChange ℤ A B) δ c)
    (hc' : IsFunnyMapFamily (KaehlerDifferential.mapBaseChange ℤ A B) δ c')
    (P : Algebra.Presentation A B (Fin n) (Fin n))
    (hL : IsSMulRegular L P.relationJacobiMatrix.det) (p : ℕ) : c p = c' p :=
  hc.eq_of_free hc' _ (fun x ↦ ⟨1, by rw [pow_one, P.relationJacobiMatrix_det_smul_eq_zero]⟩)
    hL p

/-- **Rigidity of the maps of Section 0FL7 on a localization of a square presentation,
Tag 0FLA.** Let `B` be a localization of an `A`-algebra `B₀` with a square presentation, whose
Jacobian determinant has image `J` in `B`. If `Ω[A⁄ℤ]` is free and `J` is a nonzerodivisor on
`L`, then two families as in Section 0FL7 for the same `δ` agree. -/
theorem eq_of_presentation_of_isLocalization [Module.Free A Ω[A⁄ℤ]] {B₀ : Type*} [CommRing B₀]
    [Algebra A B₀] [Algebra B₀ B] [IsScalarTower A B₀ B] (M : Submonoid B₀) [IsLocalization M B]
    (hc : IsFunnyMapFamily (KaehlerDifferential.mapBaseChange ℤ A B) δ c)
    (hc' : IsFunnyMapFamily (KaehlerDifferential.mapBaseChange ℤ A B) δ c')
    (P : Algebra.Presentation A B₀ (Fin n) (Fin n))
    (hL : IsSMulRegular L (algebraMap B₀ B P.relationJacobiMatrix.det)) (p : ℕ) :
    c p = c' p :=
  hc.eq_of_free hc' _ (fun x ↦ ⟨1, by
    rw [pow_one, algebraMap_smul_eq_zero_of_isLocalization M _
      P.relationJacobiMatrix_det_smul_eq_zero]⟩) hL p

/-- The canonical maps of Tag 0FL9 attached to a square relative global complete intersection
presentation form a family as in Section 0FL7, for `δ` the determinant element of the naive
cotangent complex. -/
theorem presentationFunnyMap (P : Algebra.Presentation A B (Fin n) (Fin n))
    [P.IsRelativeGlobalCompleteIntersection] :
    IsFunnyMapFamily (KaehlerDifferential.mapBaseChange ℤ A B) (cotangentDeterminantElement P)
      (Stacks.DeRham.presentationFunnyMap P) :=
  ⟨presentationFunnyMap_zero P, presentationFunnyMap_wedge P⟩

end Stacks.DeRham.IsFunnyMapFamily

end
