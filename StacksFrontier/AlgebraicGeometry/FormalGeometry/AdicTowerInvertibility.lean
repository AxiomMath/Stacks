module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicThickeningUnwinding
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemTheorem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.GradedSplitting

/-!
# A coherent module invertible along a complete adic tower is invertible

Let `A` be a Noetherian ring complete with respect to `I`, let `fX : X ⟶ Spec A` be proper and
let `kₙ : Xₙ ⟶ X` exhibit `Xₙ = X ×_{Spec A} Spec(A/Iⁿ⁺¹)`. A coherent `𝒪_X`-module `ℳ` whose
pullbacks `kₙ^* ℳ` are all invertible is invertible. This is the step of the proof of
[Stacks, Tag 089A] that makes the algebraized module invertible.

At a point `x` over `V(I)` the stalk `ℳ_x` is a finite module over the Noetherian local ring
`R = 𝒪_{X,x}` with `Rₙ ⊗_R ℳ_x ≅ Rₙ` for the quotients `Rₙ = 𝒪_{Xₙ,x}` of `R`, whose kernels lie
in `(I R)ⁿ⁺¹`; by Nakayama's lemma `ℳ_x` is cyclic and by Krull's intersection theorem it is free
of rank one, so `ℳ` is trivial near `x` ([Stacks, Tag 0B8J]). The locus where `ℳ` is not trivial
is closed, misses the fibre over `V(I)`, and so has closed image in `Spec A` missing `V(I)`;
since `I` lies in the Jacobson radical of `A`, that image is empty.

## Main results

* `Stacks.AdicTowerInvert.nonempty_linearEquiv_of_tensor`: the commutative algebra.
* `Stacks.AdicTowerInvert.ker_stalkMap_le_map`: the kernels of the stalk maps of a closed
  immersion with ideal sheaf `J𝒪_X`.
* `Stacks.AdicTowerInvert.adicTowerInvertibility`: the input
  `Stacks.AmpleFormalSystemTheorem.AdicTowerInvertibility` of [Stacks, Tag 089A] holds.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.AdicTowerInvert

/-! ### The commutative algebra -/

section Algebra

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- In `S ⊗_R M` with `R ⟶ S` surjective, `1 ⊗ y = 0` forces `y ∈ ker(R ⟶ S) · M`. -/
lemma mem_smul_top_of_one_tmul_eq_zero {S : Type u} [CommRing S] [Algebra R S]
    (hS : Function.Surjective (algebraMap R S)) (y : M) (hy : (1 : S) ⊗ₜ[R] y = 0) :
    y ∈ RingHom.ker (algebraMap R S) • (⊤ : Submodule R M) := by
  let K := RingHom.ker (algebraMap R S)
  let e : (R ⧸ K) ≃ₐ[R] S := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hS
  let φ : S ⊗[R] M ≃ₗ[R] M ⧸ (K • (⊤ : Submodule R M)) :=
    TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl R M) ≪≫ₗ
      TensorProduct.quotTensorEquivQuotSMul M K
  have h1 : φ ((1 : S) ⊗ₜ[R] y) = Submodule.Quotient.mk y := by
    show TensorProduct.quotTensorEquivQuotSMul M K (e.symm 1 ⊗ₜ[R] y) = _
    rw [map_one, ← map_one (Ideal.Quotient.mk K),
      TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  rw [hy, map_zero] at h1
  exact (Submodule.Quotient.mk_eq_zero _).mp h1.symm

/-- In `S ⊗_R M` with `R ⟶ S` surjective, every element is some `1 ⊗ y`. -/
lemma exists_one_tmul_eq {S : Type u} [CommRing S] [Algebra R S]
    (hS : Function.Surjective (algebraMap R S)) (t : S ⊗[R] M) :
    ∃ y : M, (1 : S) ⊗ₜ[R] y = t := by
  induction t with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul s m =>
    obtain ⟨r, rfl⟩ := hS s
    exact ⟨r • m, by rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
      mul_one]⟩
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨y₁, rfl⟩ := h₁
    obtain ⟨y₂, rfl⟩ := h₂
    exact ⟨y₁ + y₂, TensorProduct.tmul_add _ _ _⟩

/-- In `S ⊗_R M`, `1 ⊗ (r • y) = (image of r in S) • (1 ⊗ y)`. -/
lemma one_tmul_smul {S : Type u} [CommRing S] [Algebra R S] (r : R) (y : M) :
    (1 : S) ⊗ₜ[R] (r • y) = algebraMap R S r • ((1 : S) ⊗ₜ[R] y) := by
  rw [TensorProduct.tmul_smul, algebraMap_smul]

/-- **A finite module that becomes free of rank one modulo a separated family of ideals is free
of rank one.** Let `J ⊆ R` lie in the Jacobson radical with `⋂ₙ Jⁿ⁺¹ = 0`, and for every `n`
let `R ⟶ Sₙ` be surjective with kernel inside `Jⁿ⁺¹` and `Sₙ ⊗_R M ≅ Sₙ`. Then `M ≅ R`:
Nakayama's lemma makes `M` cyclic, and a scalar killing the generator dies in every `Sₙ`. -/
theorem nonempty_linearEquiv_of_tensor [Module.Finite R M] (J : Ideal R)
    (hJ : J ≤ Ideal.jacobson ⊥) (hKrull : ⨅ n : ℕ, J ^ (n + 1) = ⊥)
    (h : ∀ n : ℕ, ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Function.Surjective (algebraMap R S) ∧ RingHom.ker (algebraMap R S) ≤ J ^ (n + 1) ∧
        Nonempty (S ⊗[R] M ≃ₗ[S] S)) :
    Nonempty (M ≃ₗ[R] R) := by
  classical
  obtain ⟨S₀, _, _, hS₀, hK₀, ⟨e₀⟩⟩ := h 0
  obtain ⟨m, hm⟩ := exists_one_tmul_eq hS₀ (e₀.symm 1)
  -- `m` generates `M`.
  have hgen : (⊤ : Submodule R M) ≤ R ∙ m := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := RingHom.ker (algebraMap R S₀))
      (Module.Finite.fg_top) ((hK₀.trans (by rw [zero_add, pow_one])).trans hJ) ?_
    intro x _
    obtain ⟨r, hr⟩ := hS₀ (e₀ ((1 : S₀) ⊗ₜ[R] x))
    have hzero : (1 : S₀) ⊗ₜ[R] (x - r • m) = 0 := by
      apply e₀.injective
      rw [TensorProduct.tmul_sub, map_sub, map_zero, one_tmul_smul, LinearEquiv.map_smul, hm,
        LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one, hr, sub_self]
    rw [show x = r • m + (x - r • m) by abel]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ r (Submodule.mem_span_singleton_self m))
      (mem_smul_top_of_one_tmul_eq_zero hS₀ _ hzero)
  -- `r ↦ r • m` is injective.
  have hinj : ∀ a : R, a • m = 0 → a = 0 := by
    intro a ha
    have hall : ∀ n : ℕ, a ∈ J ^ (n + 1) := by
      intro n
      obtain ⟨S, _, _, hS, hK, ⟨e⟩⟩ := h n
      refine hK ?_
      set u := e ((1 : S) ⊗ₜ[R] m) with hu
      obtain ⟨y, hy⟩ := exists_one_tmul_eq hS (e.symm 1)
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hgen (Submodule.mem_top (x := y)))
      have hunit : algebraMap R S c * u = 1 := by
        rw [hu, ← smul_eq_mul, ← LinearEquiv.map_smul, ← one_tmul_smul, hc, hy,
          LinearEquiv.apply_symm_apply]
      have h0 : algebraMap R S a * u = 0 := by
        rw [hu, ← smul_eq_mul, ← LinearEquiv.map_smul, ← one_tmul_smul, ha,
          TensorProduct.tmul_zero, map_zero]
      rw [RingHom.mem_ker]
      linear_combination algebraMap R S c * h0 - algebraMap R S a * hunit
    rw [← Ideal.mem_bot, ← hKrull]
    exact Ideal.mem_iInf.mpr hall
  exact ⟨(LinearEquiv.ofBijective (LinearMap.toSpanSingleton R M m)
    ⟨fun a b hab => sub_eq_zero.mp (hinj (a - b) (by rwa [sub_smul, sub_eq_zero])),
      fun x => Submodule.mem_span_singleton.mp (hgen trivial)⟩).symm⟩

end Algebra

/-! ### The kernels of the stalk maps -/

section Kernel

variable (A : Type u) [CommRing A] (J : Ideal A) {X W : Scheme.{u}} (fX : X ⟶ Spec (.of A))
  (k : W ⟶ X) [IsClosedImmersion k]

/-- The image of `J` in the stalk of `X` at `x`, through `A ⟶ Γ(X, 𝒪_X) ⟶ 𝒪_{X,x}`. -/
abbrev stalkIdeal (x : X) : Ideal (X.presheaf.stalk x) :=
  Ideal.map ((X.presheaf.Γgerm x).hom.comp ((Scheme.ΓSpecIso (.of A)).inv ≫ fX.appTop).hom) J

omit [IsClosedImmersion k] in
/-- For an open `U ∋ x`, `stalkIdeal A J fX x` is the image in `𝒪_{X,x}` of the image of `J` in
`Γ(U, 𝒪_X)`. -/
lemma stalkIdeal_eq_map (x : X) (U : X.Opens) (hx : x ∈ U) :
    stalkIdeal A J fX x = Ideal.map (X.presheaf.germ U x hx).hom
      (Ideal.map (Stacks.Coherent.baseSectionHom A fX U) J) := by
  have h : (X.presheaf.germ U x hx).hom.comp (Stacks.Coherent.baseSectionHom A fX U) =
      (X.presheaf.Γgerm x).hom.comp ((Scheme.ΓSpecIso (.of A)).inv ≫ fX.appTop).hom := by
    rw [Stacks.Coherent.baseSectionHom, ← RingHom.comp_assoc, ← CommRingCat.hom_comp,
      TopCat.Presheaf.germ_res]
    rfl
  rw [Ideal.map_map, h]

/-- **The stalk maps of a closed immersion with ideal sheaf `J𝒪_X` have kernel inside
`J𝒪_{X,x}`.** A germ killed by the stalk map is, on an affine neighbourhood, killed by a power of
a function invertible at the point, by the affine-local description of the ideal sheaf. -/
theorem ker_stalkMap_le_map (hker : k.ker = Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J fX)
    (y : W) : RingHom.ker (k.stalkMap y).hom ≤ stalkIdeal A J fX (k y) := by
  intro s hs
  obtain ⟨V, hxV, t, rfl⟩ := X.presheaf.germ_exist s
  obtain ⟨U₀, hU₀, hxU, hUV⟩ :=
    (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hxV
  let U : X.affineOpens := ⟨U₀, hU₀⟩
  have hgerm : X.presheaf.germ V (k y) hxV t =
      X.presheaf.germ U.1 (k y) hxU (X.presheaf.map (homOfLE hUV).op t) :=
    (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hUV) (k y) hxU t).symm
  rw [hgerm] at hs ⊢
  set t' := X.presheaf.map (homOfLE hUV).op t
  rw [RingHom.mem_ker, Scheme.Hom.germ_stalkMap_apply] at hs
  have hyU : y ∈ k ⁻¹ᵁ U.1 := hxU
  obtain ⟨O, hyO, iO, iO', hO⟩ := W.presheaf.germ_eq y hyU hyU (k.app U.1 t') 0
    (by rw [hs, map_zero])
  rw [map_zero] at hO
  have hU' : IsAffineOpen (k ⁻¹ᵁ U.1) := U.2.preimage k
  obtain ⟨c, hcO, hyc⟩ := hU'.exists_basicOpen_le ⟨y, hyO⟩ hyU
  have hres : (k.app U.1 t') |_ (W.basicOpen c) = 0 := by
    show W.presheaf.map (homOfLE (W.basicOpen_le c)).op (k.app U.1 t') = 0
    rw [show (homOfLE (W.basicOpen_le c)).op = iO.op ≫ (homOfLE hcO).op from rfl,
      Functor.map_comp, CommRingCat.comp_apply, hO, map_zero]
  obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen W hU' _ c hres
  obtain ⟨h, rfl⟩ := Scheme.Hom.app_surjective k U.1 U.2 c
  have hmem : h ^ m * t' ∈ Ideal.map (Stacks.Coherent.baseSectionHom A fX U.1) J := by
    rwa [← Stacks.Coherent.baseIdealSheaf_ideal_eq_map A J fX U, ← hker, Scheme.Hom.ker_apply,
      RingHom.mem_ker, map_mul, map_pow]
  have hunit : IsUnit (X.presheaf.germ U.1 (k y) hxU h) := by
    rw [← Scheme.mem_basicOpen]
    rwa [← Scheme.preimage_basicOpen] at hyc
  rw [stalkIdeal_eq_map A J fX (k y) U.1 hxU]
  have h2 := Ideal.mem_map_of_mem (X.presheaf.germ U.1 (k y) hxU).hom hmem
  rw [map_mul, map_pow] at h2
  exact (Ideal.unit_mul_mem_iff_mem _ (hunit.pow m)).mp h2

/-- The image of `J` dies in the stalks of `W`. -/
theorem map_le_ker_stalkMap
    (hker : k.ker = Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J fX) (y : W) :
    stalkIdeal A J fX (k y) ≤ RingHom.ker (k.stalkMap y).hom := by
  obtain ⟨U₀, hU₀, hxU, -⟩ :=
    (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show k y ∈ (⊤ : X.Opens) from trivial)
  let U : X.affineOpens := ⟨U₀, hU₀⟩
  rw [stalkIdeal_eq_map A J fX (k y) U.1 hxU, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [← Stacks.Coherent.baseIdealSheaf_ideal_eq_map A J fX U, ← hker, Scheme.Hom.ker_apply,
    RingHom.mem_ker] at ha
  rw [Ideal.mem_comap, RingHom.mem_ker, Scheme.Hom.germ_stalkMap_apply, ha, map_zero]

end Kernel

/-! ### The stalks over `V(I)` -/

section Tower

open Stacks.SheafOfModules.TensorStalkRingedSpace

variable (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (fX : X ⟶ Spec (.of A))
  {Xn : ℕ → Scheme.{u}} (q : ∀ n, Xn n ⟶ adicThickening A I n) (k : ∀ n, Xn n ⟶ X)
  (hkcart : ∀ n, IsPullback (k n) (q n) fX (adicThickeningι A I n))

include hkcart in
/-- The ideal sheaf of `kₙ : Xₙ ⟶ X` is `Iⁿ⁺¹𝒪_X`. -/
lemma ker_k (n : ℕ) :
    (k n).ker = Stacks.Cohomology.FormalFunctions.baseIdealSheaf A (I ^ (n + 1)) fX := by
  rw [← (hkcart n).isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    AdicFiniteAlgebra.ker_adicBaseChange_fst A I fX n,
    Stacks.Cohomology.FormalFunctions.baseIdealSheaf_pow]

omit fX in
/-- The image of `Sₙ ⟶ Spec A` is `V(I)`. -/
lemma range_adicThickeningι (n : ℕ) :
    Set.range (adicThickeningι A I n) = PrimeSpectrum.zeroLocus (I : Set A) := by
  show Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (n + 1)))) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
    PrimeSpectrum.zeroLocus_pow I (Nat.succ_ne_zero n)]

include hkcart in
/-- Every point of `X` over `V(I)` is in the image of every `kₙ`. -/
lemma mem_range_k (n : ℕ) (x : X) (hx : fX x ∈ PrimeSpectrum.zeroLocus (I : Set A)) :
    ∃ y : Xn n, k n y = x := by
  obtain ⟨w, hw⟩ : x ∈ Set.range (pullback.fst fX (adicThickeningι A I n)) := by
    rwa [Scheme.Pullback.range_fst, Set.mem_preimage, range_adicThickeningι]
  refine ⟨(hkcart n).isoPullback.inv w, ?_⟩
  have e : (hkcart n).isoPullback.inv ≫ k n = pullback.fst fX (adicThickeningι A I n) := by
    rw [Iso.inv_comp_eq, (hkcart n).isoPullback_hom_fst]
  rw [← hw, ← e, Scheme.Hom.comp_apply]

variable [IsClosedImmersion (k 0)]

include hkcart in
/-- Over `V(I)` the image of `I` lies in the maximal ideal of the stalk. -/
lemma stalkIdeal_le_maximalIdeal (y : Xn 0) :
    stalkIdeal A I fX (k 0 y) ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk (k 0 y)) := by
  have h := map_le_ker_stalkMap A (I ^ (0 + 1)) fX (k 0) (ker_k A I fX q k hkcart 0) y
  rw [zero_add, pow_one] at h
  refine h.trans fun a ha => (IsLocalRing.mem_maximalIdeal a).mpr fun hu => ?_
  have := hu.map ((k 0).stalkMap y).hom
  rw [RingHom.mem_ker.mp ha] at this
  exact not_isUnit_zero this

omit [IsClosedImmersion (k 0)] in
include hkcart in
/-- **The stalk of `ℳ` modulo the kernel of `𝒪_{X,x} ⟶ 𝒪_{Xₙ,y}`**: when `kₙ^* ℳ` is
invertible, `𝒪_{Xₙ,y} ⊗ ℳ_x ≅ 𝒪_{Xₙ,y}` ([Stacks, Tag 0098] and [Stacks, Tag 0AFW]), and
`𝒪_{X,x} ⟶ 𝒪_{Xₙ,y}` is surjective with kernel inside `(I𝒪_{X,x})ⁿ⁺¹`. -/
lemma exists_tensor_stalk (M : X.Modules) (n : ℕ) [IsClosedImmersion (k n)]
    (hinv : Stacks.Ample.IsInvertibleModule (Xn n) ((Scheme.Modules.pullback (k n)).obj M))
    (y : Xn n) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra (ringStalk X.toRingedSpace (k n y)) S),
      Function.Surjective (algebraMap (ringStalk X.toRingedSpace (k n y)) S) ∧
      RingHom.ker (algebraMap (ringStalk X.toRingedSpace (k n y)) S) ≤
        stalkIdeal A I fX (k n y) ^ (n + 1) ∧
      letI := stalkModule X.toRingedSpace M.val (k n y)
      Nonempty (S ⊗[ringStalk X.toRingedSpace (k n y)] grpStalk X.toRingedSpace M.val (k n y)
        ≃ₗ[S] S) := by
  let : Algebra (ringStalk X.toRingedSpace (k n y)) (ringStalk (Xn n).toRingedSpace y) :=
    Stacks.PullbackTensorIso.commStalkAlgebra (k n).toLRSHom.toShHom y
  have halg : algebraMap (ringStalk X.toRingedSpace (k n y)) (ringStalk (Xn n).toRingedSpace y) =
      ((k n).stalkMap y).hom :=
    Stacks.NonvanishingPullback.commStalkRingMap_eq_stalkMap (k n) y
  have : AlgebraicGeometry.SheafOfModules.IsInvertible (Xn n).toRingedSpace.presheaf
      (structureSheafRing (Xn n).toRingedSpace).property
      (Stacks.PullbackTensorIso.pullbackSheaf (k n).toLRSHom.toShHom M) := hinv
  have : ∀ z : (Xn n).toRingedSpace.carrier, IsLocalRing (ringStalk (Xn n).toRingedSpace z) :=
    fun z => inferInstanceAs (IsLocalRing ((Xn n).presheaf.stalk z))
  obtain ⟨e⟩ := Stacks.SheafOfModules.nonempty_grpStalk_linearEquiv (Xn n).toRingedSpace
    (Stacks.PullbackTensorIso.pullbackSheaf (k n).toLRSHom.toShHom M) y
  refine ⟨ringStalk (Xn n).toRingedSpace y, inferInstance, inferInstance, ?_, ?_,
    ⟨(Stacks.PullbackTensorIso.pullbackStalkEquiv (k n).toLRSHom.toShHom y M).trans e⟩⟩
  · rw [halg]
    exact (k n).stalkMap_surjective y
  · rw [halg, ← Ideal.map_pow]
    exact ker_stalkMap_le_map A (I ^ (n + 1)) fX (k n) (ker_k A I fX q k hkcart n) y

omit [IsClosedImmersion (k 0)] in
include hkcart in
/-- **At a point over `V(I)`, the stalk of `ℳ` is free of rank one.** -/
theorem nonempty_stalk_linearEquiv [IsNoetherianRing A] [IsAdicComplete I A]
    [IsLocallyNoetherian X] [∀ n, IsClosedImmersion (k n)] (M : X.Modules) [M.IsFiniteType]
    (hinv : ∀ n, Stacks.Ample.IsInvertibleModule (Xn n) ((Scheme.Modules.pullback (k n)).obj M))
    (y : Xn 0) :
    letI := stalkModule X.toRingedSpace M.val (k 0 y)
    Nonempty (grpStalk X.toRingedSpace M.val (k 0 y) ≃ₗ[ringStalk X.toRingedSpace (k 0 y)]
      ringStalk X.toRingedSpace (k 0 y)) := by
  let := stalkModule X.toRingedSpace M.val (k 0 y)
  have : Module.Finite (ringStalk X.toRingedSpace (k 0 y))
      (grpStalk X.toRingedSpace M.val (k 0 y)) := by
    have h : @Module.Finite (ringStalk X.toRingedSpace (k 0 y))
        (grpStalk X.toRingedSpace M.val (k 0 y)) _ _
        (PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.toRingedSpace.presheaf) M.val (k 0 y)) :=
      _root_.SheafOfModules.finite_stalk X.sheaf M (k 0 y)
    rwa [← Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace M.val (k 0 y)] at h
  set J := stalkIdeal A I fX (k 0 y)
  have hJm : J ≤ IsLocalRing.maximalIdeal _ := stalkIdeal_le_maximalIdeal A I fX q k hkcart y
  have hJ : J ≤ Ideal.jacobson ⊥ := hJm.trans (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have hne : J ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hJm
  have hKrull : ⨅ n : ℕ, J ^ (n + 1) = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing J hne]
    exact le_iInf fun i => (iInf_le _ i).trans (Ideal.pow_le_pow_right (Nat.le_succ i))
  have hx : fX (k 0 y) ∈ PrimeSpectrum.zeroLocus (I : Set A) := by
    rw [← range_adicThickeningι A I 0, ← Scheme.Hom.comp_apply, (hkcart 0).w,
      Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  refine nonempty_linearEquiv_of_tensor J hJ hKrull fun n => ?_
  obtain ⟨yn, hyn⟩ := mem_range_k A I fX q k hkcart n (k 0 y) hx
  have h := exists_tensor_stalk A I fX q k hkcart M n (hinv n) yn
  rwa [hyn] at h

end Tower

/-! ### The theorem -/

/-- **The invertibility input of [Stacks, Tag 089A] holds**: over a Noetherian ring complete with
respect to `I`, a coherent module on an H-projective `fX : X ⟶ Spec A` whose pullbacks along a
cartesian adic tower are all invertible is invertible.

Near every point over `V(I)` the module is trivial (`nonempty_stalk_linearEquiv` and
[Stacks, Tag 0B8J]). The set of points near which it is not trivial is closed, so its image in
`Spec A` is closed (`fX` is proper); a nonempty closed subset of `Spec A` contains a closed point,
which lies in `V(I)` because `I` is in the Jacobson radical of `A`. So that set is empty. -/
theorem adicTowerInvertibility (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    [IsAdicComplete I A] {Xn : ℕ → Scheme.{u}} (q : ∀ n, Xn n ⟶ adicThickening A I n) :
    Stacks.AmpleFormalSystemTheorem.AdicTowerInvertibility A I q := by
  intro X fX hfX k hkcart M hMcoh hinv
  have := isProper_of_isProjectiveMorphism fX hfX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian fX
  have : ∀ n, IsClosedImmersion (k n) :=
    Stacks.AmpleFormalSystemLineBundle.isClosedImmersion_of_isPullback A I fX q k hkcart
  have : _root_.SheafOfModules.IsCoherent M := hMcoh
  have : M.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType
  have hnear : ∀ y : Xn 0, ∃ U : X.Opens, k 0 y ∈ U ∧
      Nonempty (M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) := by
    intro y
    obtain ⟨e⟩ := nonempty_stalk_linearEquiv A I fX q k hkcart M hinv y
    obtain ⟨U, hU, ⟨e'⟩⟩ := Stacks.SheafOfModules.exists_iso_free_over_of_stalk_iso_free M
      (Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_of_isCoherent' M) (k 0 y) 1
      (Stacks.SheafOfModules.nonempty_stalk_linearEquiv_finsupp X.toRingedSpace M.val (k 0 y) ⟨e⟩)
    exact ⟨U, hU, ⟨e' ≪≫ coproductUniqueIso _⟩⟩
  refine Stacks.InvertibleRankOneScheme.isInvertibleModule_of_forall_exists_mem_isoUnit_over X M
    fun x => ?_
  by_contra hx
  let Z : Set X := {x | ¬ ∃ U : X.Opens, x ∈ U ∧
    Nonempty (M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))}
  have hZ : IsClosed Z := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x' hx'
    obtain ⟨U, hxU, he⟩ := not_not.mp hx'
    exact ⟨U, fun x'' hx'' => not_not.mpr ⟨U, hx'', he⟩, U.isOpen, hxU⟩
  have hcl : IsClosed (fX '' Z) := fX.isClosedMap _ hZ
  obtain ⟨p, ⟨z, hz, rfl⟩, hpcl⟩ := hcl.exists_closed_singleton ⟨_, x, hx, rfl⟩
  have hmax : (fX z).asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hpcl
  have hI : fX z ∈ PrimeSpectrum.zeroLocus (I : Set A) := by
    intro a ha
    exact (sInf_le (show (fX z).asIdeal ∈ {J : Ideal A | ⊥ ≤ J ∧ J.IsMaximal} from
      ⟨bot_le, hmax⟩) : Ideal.jacobson ⊥ ≤ (fX z).asIdeal)
      (IsAdicComplete.le_jacobson_bot (I := I) ha)
  obtain ⟨y, hy⟩ := mem_range_k A I fX q k hkcart 0 z hI
  obtain ⟨U, hU, he⟩ := hnear y
  exact hz ⟨U, hy ▸ hU, he⟩

end Stacks.AdicTowerInvert

end
