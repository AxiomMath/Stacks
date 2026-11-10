module

public import StacksFrontier.RingTheory.AdicCompletion.BlowupChartCompletionDepth.ChartCompletions
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.ChartResidualSupport

/-!
# A local model of the completed affine blowup chart

For a prime `Q` of the affine blowup algebra `A[I/f]`, this file introduces the ring
`(A_𝔮)^∧ ⊗_A A[I/f]`, its local ring `T` at the prime cut out by the closed point of
`(A[I/f]_Q)^∧`, and the maps `A[I/f]_Q → T → (A[I/f]_Q)^∧`, and shows that
`A[I/f]_Q → T` is flat and induces an isomorphism modulo `I`.

## References

* [Stacks Project, Tag 0EJK](https://stacks.math.columbia.edu/tag/0EJK)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace Stacks.Algebraization

/-! ### An algebraic model of the chart completion -/

namespace BlowupChartModel

section Model

variable {A : Type u} [CommRing A] (I : Ideal A) (f : A) (Q : Ideal (affineBlowup I f))
  [Q.IsPrime]

/-- The ring `(A_𝔮)^∧ ⊗_A A[I/f]`, an algebra of finite type over `(A_𝔮)^∧` mapping to
`(A[I/f]_Q)^∧`. It is a `def` so that instance search does not look inside the tensor product. -/
def Tensor : Type u :=
  TensorProduct A (affineBlowupBaseCompletion I f Q) (affineBlowup I f)

/-- The ring structure of `(A_𝔮)^∧ ⊗_A A[I/f]`. -/
noncomputable instance : CommRing (Tensor I f Q) :=
  inferInstanceAs (CommRing (TensorProduct A (affineBlowupBaseCompletion I f Q) _))

/-- The `(A_𝔮)^∧`-algebra structure of `(A_𝔮)^∧ ⊗_A A[I/f]`. -/
noncomputable instance : Algebra (affineBlowupBaseCompletion I f Q) (Tensor I f Q) :=
  inferInstanceAs (Algebra _ (TensorProduct A (affineBlowupBaseCompletion I f Q) _))

/-- The map `(A_𝔮)^∧ ⊗_A A[I/f] → (A[I/f]_Q)^∧`. -/
noncomputable def toChart : Tensor I f Q →+* affineBlowupChartCompletion I f Q :=
  (affineBlowupTensorChartMap I f Q).toRingHom

/-- The map `A[I/f] → (A_𝔮)^∧ ⊗_A A[I/f]`. -/
noncomputable def inr : affineBlowup I f →+* Tensor I f Q :=
  (Algebra.TensorProduct.includeRight : affineBlowup I f →ₐ[A]
    TensorProduct A (affineBlowupBaseCompletion I f Q) (affineBlowup I f)).toRingHom

/-- On `A[I/f]`, the map `(A_𝔮)^∧ ⊗_A A[I/f] → (A[I/f]_Q)^∧` is `A[I/f] → (A[I/f]_Q)^∧`. -/
theorem toChart_inr (b : affineBlowup I f) :
    toChart I f Q (inr I f Q b) =
      algebraMap (Localization.AtPrime Q) (affineBlowupChartCompletion I f Q)
        (algebraMap (affineBlowup I f) (Localization.AtPrime Q) b) :=
  Algebra.TensorProduct.productMap_right_apply _ _ b

/-- On `(A_𝔮)^∧`, the map `(A_𝔮)^∧ ⊗_A A[I/f] → (A[I/f]_Q)^∧` is the completion map. -/
theorem toChart_algebraMap (r : affineBlowupBaseCompletion I f Q) :
    toChart I f Q (algebraMap _ (Tensor I f Q) r) = affineBlowupCompletionMap I f Q r :=
  Algebra.TensorProduct.productMap_left_apply _ _ r

/-- The two maps `A → (A_𝔮)^∧ ⊗_A A[I/f]`, through `A[I/f]` and through `(A_𝔮)^∧`, agree. -/
theorem inr_comp_algebraMap :
    (inr I f Q).comp (algebraMap A (affineBlowup I f)) =
      (algebraMap (affineBlowupBaseCompletion I f Q) (Tensor I f Q)).comp
        (algebraMap A (affineBlowupBaseCompletion I f Q)) := by
  ext a
  change (1 : affineBlowupBaseCompletion I f Q) ⊗ₜ[A] algebraMap A (affineBlowup I f) a =
    algebraMap A (affineBlowupBaseCompletion I f Q) a ⊗ₜ[A] (1 : affineBlowup I f)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one a, TensorProduct.smul_tmul]

/-- An induction principle for `(A_𝔮)^∧ ⊗_A A[I/f]` phrased with its ring operations: every
element is a sum of products `r · b` with `r ∈ (A_𝔮)^∧` and `b ∈ A[I/f]`. -/
theorem tensor_induction {P : Tensor I f Q → Prop}
    (hmul : ∀ r b, P (algebraMap (affineBlowupBaseCompletion I f Q) (Tensor I f Q) r * inr I f Q b))
    (hadd : ∀ x y, P x → P y → P (x + y)) (x : Tensor I f Q) : P x := by
  refine TensorProduct.inductionOn (motive := P) x (fun r b => ?_) hadd
  have h := hmul r b
  have htm : algebraMap (affineBlowupBaseCompletion I f Q) (Tensor I f Q) r * inr I f Q b =
      r ⊗ₜ[A] b := by
    change (r ⊗ₜ[A] (1 : affineBlowup I f)) * ((1 : affineBlowupBaseCompletion I f Q) ⊗ₜ[A] b) =
      r ⊗ₜ[A] b
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rwa [htm] at h

/-- For every `t ∈ (A_𝔮)^∧ ⊗_A A[I/f]`, some power `f ^ n · t` lies in the image of `(A_𝔮)^∧`. -/
theorem exists_pow_mul_eq_algebraMap (t : Tensor I f Q) :
    ∃ (n : ℕ) (r : affineBlowupBaseCompletion I f Q),
      algebraMap _ (Tensor I f Q) (algebraMap A (affineBlowupBaseCompletion I f Q) f ^ n) * t =
        algebraMap _ (Tensor I f Q) r :=
  exists_pow_mul_eq_algebraMap_tensorProduct_affineBlowup I f t

/-- An element of `(A_𝔮)^∧` vanishing in `(A_𝔮)^∧ ⊗_A A[I/f]` is killed by a power of `f`. -/
theorem exists_pow_mul_eq_zero (r : affineBlowupBaseCompletion I f Q)
    (hr : algebraMap _ (Tensor I f Q) r = 0) :
    ∃ n : ℕ, algebraMap A (affineBlowupBaseCompletion I f Q) f ^ n * r = 0 :=
  exists_pow_mul_eq_zero_of_algebraMap_tensorProduct_affineBlowup I f r hr

/-- The prime of `(A_𝔮)^∧ ⊗_A A[I/f]` cut out by the closed point of `(A[I/f]_Q)^∧`. -/
noncomputable def prime : Ideal (Tensor I f Q) :=
  ((maximalIdeal (Localization.AtPrime Q)).map
    (algebraMap (Localization.AtPrime Q) (affineBlowupChartCompletion I f Q))).comap
      (toChart I f Q)

variable [IsNoetherianRing A]

/-- Over a Noetherian ring `A`, the affine blowup algebra `A[I/f]` is of finite type. -/
instance : Algebra.FiniteType A (affineBlowup I f) :=
  ResolutionOfSurfaces.CartierDescent.finiteType_affineBlowup I f (IsNoetherian.noetherian I)

/-- Over a Noetherian ring `A`, the affine blowup algebra `A[I/f]` is Noetherian. -/
instance : IsNoetherianRing (affineBlowup I f) := Algebra.FiniteType.isNoetherianRing A _

/-- The local ring `A_𝔮` is Noetherian. -/
instance : IsNoetherianRing (Localization.AtPrime (Q.under A)) :=
  IsLocalization.isNoetherianRing (Q.under A).primeCompl _ inferInstance

/-- The local ring `A[I/f]_Q` is Noetherian. -/
instance : IsNoetherianRing (Localization.AtPrime Q) :=
  IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance

/-- The completion `(A_𝔮)^∧` is Noetherian. -/
instance : IsNoetherianRing (affineBlowupBaseCompletion I f Q) :=
  AdicCompletion.isNoetherianRing _

/-- The completion `(A[I/f]_Q)^∧` is Noetherian. -/
instance : IsNoetherianRing (affineBlowupChartCompletion I f Q) :=
  AdicCompletion.isNoetherianRing _

/-- The completion `(A_𝔮)^∧` is flat over `A`. -/
instance : Module.Flat A (affineBlowupBaseCompletion I f Q) := by
  have : Module.Flat (Localization.AtPrime (Q.under A)) (affineBlowupBaseCompletion I f Q) :=
    AdicCompletion.flat_of_isNoetherian _
  exact Module.Flat.trans A (Localization.AtPrime (Q.under A)) _

/-- The ring `(A_𝔮)^∧ ⊗_A A[I/f]` is of finite type over `(A_𝔮)^∧`. -/
instance : Algebra.FiniteType (affineBlowupBaseCompletion I f Q) (Tensor I f Q) :=
  inferInstanceAs (Algebra.FiniteType (affineBlowupBaseCompletion I f Q)
    (TensorProduct A (affineBlowupBaseCompletion I f Q) (affineBlowup I f)))

/-- The ring `(A_𝔮)^∧ ⊗_A A[I/f]` is Noetherian. -/
instance : IsNoetherianRing (Tensor I f Q) :=
  Algebra.FiniteType.isNoetherianRing (affineBlowupBaseCompletion I f Q) _

/-- The map `A[I/f] → (A_𝔮)^∧ ⊗_A A[I/f]` is flat. -/
theorem flat_inr : (inr I f Q).Flat :=
  flat_includeRight A (affineBlowupBaseCompletion I f Q) (affineBlowup I f)

variable [hJ : Fact (I.map (algebraMap A (Localization.AtPrime Q)) ≤
  maximalIdeal (Localization.AtPrime Q))]

omit [IsNoetherianRing A] in
include hJ in
/-- If `I A[I/f]_Q` is proper, then `I ⊆ 𝔮`. -/
theorem le_under : I ≤ Q.under A := by
  intro x hx
  have h1 : algebraMap A (Localization.AtPrime Q) x ∈ maximalIdeal _ :=
    hJ.out (Ideal.mem_map_of_mem _ hx)
  rw [IsScalarTower.algebraMap_apply A (affineBlowup I f) (Localization.AtPrime Q)] at h1
  exact (SetLike.ext_iff.mp (Localization.AtPrime.under_maximalIdeal (I := Q)) _).mp h1

omit [IsNoetherianRing A] in
include hJ in
/-- If `I A[I/f]_Q` is proper, then `I A_𝔮` lies in the maximal ideal of `A_𝔮`. -/
theorem map_le_maximalIdeal_under :
    I.map (algebraMap A (Localization.AtPrime (Q.under A))) ≤ maximalIdeal _ := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change algebraMap A _ x ∈ maximalIdeal (Localization.AtPrime (Q.under A))
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.mem_map_of_mem _ (le_under I f Q hx)

/-- The completion `(A_𝔮)^∧` is a local ring. -/
instance : IsLocalRing (affineBlowupBaseCompletion I f Q) :=
  AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal _
    (map_le_maximalIdeal_under I f Q)

/-- The completion `(A[I/f]_Q)^∧` is a local ring. -/
instance : IsLocalRing (affineBlowupChartCompletion I f Q) :=
  AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal _ hJ.out

/-- The maximal ideal of `(A[I/f]_Q)^∧` is generated by the maximal ideal of `A[I/f]_Q`. -/
theorem maximalIdeal_chartCompletion :
    maximalIdeal (affineBlowupChartCompletion I f Q) =
      (maximalIdeal (Localization.AtPrime Q)).map (algebraMap _ _) :=
  (IsLocalRing.eq_maximalIdeal (R := affineBlowupChartCompletion I f Q)
    (AdicCompletion.isMaximal_map_of_le _ _ hJ.out (Ideal.fg_of_isNoetherianRing _))).symm

/-- The maximal ideal of `(A_𝔮)^∧` is generated by the maximal ideal of `A_𝔮`. -/
theorem maximalIdeal_baseCompletion :
    maximalIdeal (affineBlowupBaseCompletion I f Q) =
      (maximalIdeal (Localization.AtPrime (Q.under A))).map (algebraMap _ _) :=
  (IsLocalRing.eq_maximalIdeal (R := affineBlowupBaseCompletion I f Q)
    (AdicCompletion.isMaximal_map_of_le _ _ (map_le_maximalIdeal_under I f Q)
      (Ideal.fg_of_isNoetherianRing _))).symm

/-- A ring map of local rings whose source maximal ideal maps into the target one is local. -/
private theorem comap_maximalIdeal_eq_of_le_comap {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (g : R →+* S) (h : maximalIdeal R ≤ (maximalIdeal S).comap g) :
    (maximalIdeal S).comap g = maximalIdeal R :=
  ((IsLocalRing.local_hom_TFAE g).out 4 5).mp h

/-- The maximal ideal of `(A[I/f]_Q)^∧` contracts to the maximal ideal of `A[I/f]_Q`. -/
theorem comap_maximalIdeal_chartCompletion :
    (maximalIdeal (affineBlowupChartCompletion I f Q)).comap (algebraMap _ _) =
      maximalIdeal (Localization.AtPrime Q) :=
  comap_maximalIdeal_eq_of_le_comap _
    (Ideal.map_le_iff_le_comap.mp (maximalIdeal_chartCompletion I f Q).ge)

omit [IsNoetherianRing A] hJ in
/-- The two maps `A_𝔮 → (A[I/f]_Q)^∧`, through `A[I/f]_Q` and through `(A_𝔮)^∧`, agree. -/
theorem algebraMap_comp_localRingHom :
    (algebraMap (Localization.AtPrime Q) (affineBlowupChartCompletion I f Q)).comp
        (Localization.localRingHom (Q.under A) Q (algebraMap A (affineBlowup I f)) rfl) =
      (affineBlowupCompletionMap I f Q).comp (algebraMap _ (affineBlowupBaseCompletion I f Q)) :=
  RingHom.ext fun x => (affineBlowupCompletionMap_algebraMap I f Q x).symm

/-- The completion map `(A_𝔮)^∧ → (A[I/f]_Q)^∧` is local. -/
theorem comap_maximalIdeal_completionMap :
    (maximalIdeal (affineBlowupChartCompletion I f Q)).comap (affineBlowupCompletionMap I f Q) =
      maximalIdeal (affineBlowupBaseCompletion I f Q) := by
  refine comap_maximalIdeal_eq_of_le_comap _ ?_
  rw [maximalIdeal_baseCompletion, Ideal.map_le_iff_le_comap, Ideal.comap_comap,
    ← algebraMap_comp_localRingHom, ← Ideal.comap_comap, comap_maximalIdeal_chartCompletion]
  intro x hx
  exact map_nonunit (Localization.localRingHom (Q.under A) Q (algebraMap A (affineBlowup I f)) rfl)
    x hx

/-- The prime `prime I f Q` is the contraction of the maximal ideal of `(A[I/f]_Q)^∧`. -/
theorem prime_eq :
    prime I f Q = (maximalIdeal (affineBlowupChartCompletion I f Q)).comap (toChart I f Q) := by
  rw [prime, maximalIdeal_chartCompletion]

/-- The ideal `prime I f Q` is prime. -/
instance : (prime I f Q).IsPrime := by
  rw [prime_eq]; exact Ideal.comap_isPrime _ _

/-- An element lies in `prime I f Q` if and only if its image lies in the maximal ideal of
`(A[I/f]_Q)^∧`. -/
theorem mem_prime_iff (x : Tensor I f Q) :
    x ∈ prime I f Q ↔ toChart I f Q x ∈ maximalIdeal (affineBlowupChartCompletion I f Q) := by
  rw [prime_eq]; rfl

/-- The prime `prime I f Q` contracts to `Q` in `A[I/f]`. -/
theorem comap_prime_inr : (prime I f Q).comap (inr I f Q) = Q := by
  ext b
  rw [Ideal.mem_comap, mem_prime_iff, toChart_inr]
  change algebraMap _ (Localization.AtPrime Q) b ∈
    (maximalIdeal (affineBlowupChartCompletion I f Q)).comap (algebraMap _ _) ↔ b ∈ Q
  rw [comap_maximalIdeal_chartCompletion]
  exact SetLike.ext_iff.mp (Localization.AtPrime.under_maximalIdeal (I := Q)) b

/-- The prime `prime I f Q` contracts to the maximal ideal of `(A_𝔮)^∧`. -/
theorem comap_prime_algebraMap :
    (prime I f Q).comap (algebraMap (affineBlowupBaseCompletion I f Q) (Tensor I f Q)) =
      maximalIdeal (affineBlowupBaseCompletion I f Q) := by
  ext r
  rw [Ideal.mem_comap, mem_prime_iff, toChart_algebraMap, ← comap_maximalIdeal_completionMap I f Q]
  rfl

/-- The local ring `T` of `(A_𝔮)^∧ ⊗_A A[I/f]` at the prime cut out by the closed point. It is a
`def` so that instance search does not look inside the localization. -/
def Loc : Type u := Localization.AtPrime (prime I f Q)

/-- The ring structure of `T`. -/
noncomputable instance : CommRing (Loc I f Q) :=
  inferInstanceAs (CommRing (Localization.AtPrime (prime I f Q)))

/-- The `(A_𝔮)^∧ ⊗_A A[I/f]`-algebra structure of `T`. -/
noncomputable instance : Algebra (Tensor I f Q) (Loc I f Q) :=
  inferInstanceAs (Algebra _ (Localization.AtPrime (prime I f Q)))

/-- The ring `T` is the localization of `(A_𝔮)^∧ ⊗_A A[I/f]` at `prime I f Q`. -/
instance : IsLocalization.AtPrime (Loc I f Q) (prime I f Q) :=
  inferInstanceAs (IsLocalization.AtPrime (Localization.AtPrime (prime I f Q)) _)

/-- The ring `T` is local. -/
instance : IsLocalRing (Loc I f Q) :=
  inferInstanceAs (IsLocalRing (Localization.AtPrime (prime I f Q)))

/-- The `(A_𝔮)^∧`-algebra structure of `T`. -/
noncomputable instance : Algebra (affineBlowupBaseCompletion I f Q) (Loc I f Q) :=
  inferInstanceAs (Algebra _ (Localization.AtPrime (prime I f Q)))

/-- The maps `(A_𝔮)^∧ → (A_𝔮)^∧ ⊗_A A[I/f] → T` form a scalar tower. -/
instance : IsScalarTower (affineBlowupBaseCompletion I f Q) (Tensor I f Q) (Loc I f Q) :=
  inferInstanceAs (IsScalarTower _ _ (Localization.AtPrime (prime I f Q)))

/-- The ring `T` is Noetherian. -/
instance : IsNoetherianRing (Loc I f Q) :=
  IsLocalization.isNoetherianRing (prime I f Q).primeCompl _ inferInstance

/-- The maximal ideal of `T` contracts to `prime I f Q`. -/
theorem comap_maximalIdeal_loc :
    (maximalIdeal (Loc I f Q)).comap (algebraMap (Tensor I f Q) (Loc I f Q)) = prime I f Q :=
  Localization.AtPrime.under_maximalIdeal (I := prime I f Q)

/-- The map `A[I/f]_Q → T`. -/
noncomputable def ιB : Localization.AtPrime Q →+* Loc I f Q :=
  Localization.localRingHom Q (prime I f Q) (inr I f Q) (comap_prime_inr I f Q).symm

/-- The map `A[I/f]_Q → T` is local. -/
instance : IsLocalHom (ιB I f Q) := Localization.isLocalHom_localRingHom _ _ _ _

/-- On `A[I/f]`, the map `A[I/f]_Q → T` is `A[I/f] → (A_𝔮)^∧ ⊗_A A[I/f] → T`. -/
theorem ιB_algebraMap (b : affineBlowup I f) :
    ιB I f Q (algebraMap _ (Localization.AtPrime Q) b) =
      algebraMap (Tensor I f Q) (Loc I f Q) (inr I f Q b) :=
  Localization.localRingHom_to_map _ _ _ _ b

/-- The map `A[I/f]_Q → T` is flat. -/
theorem flat_ιB : (ιB I f Q).Flat :=
  (flat_inr I f Q).localRingHom (prime I f Q) Q (comap_prime_inr I f Q).symm

/-- The two maps `A_𝔮 → T`, through `(A_𝔮)^∧` and through `A[I/f]_Q`, agree. -/
theorem algebraMap_comp_algebraMap_eq :
    (algebraMap (affineBlowupBaseCompletion I f Q) (Loc I f Q)).comp
        (algebraMap (Localization.AtPrime (Q.under A)) _) =
      (ιB I f Q).comp
        (Localization.localRingHom (Q.under A) Q (algebraMap A (affineBlowup I f)) rfl) := by
  refine IsLocalization.ringHom_ext (Q.under A).primeCompl (RingHom.ext fun a => ?_)
  simp only [RingHom.comp_apply]
  rw [localRingHom_under_algebraMap,
    IsScalarTower.algebraMap_apply A (affineBlowup I f) (Localization.AtPrime Q), ιB_algebraMap,
    ← IsScalarTower.algebraMap_apply A (Localization.AtPrime (Q.under A)),
    IsScalarTower.algebraMap_apply _ (Tensor I f Q) (Loc I f Q)]
  exact congrArg (algebraMap (Tensor I f Q) (Loc I f Q))
    (RingHom.congr_fun (inr_comp_algebraMap I f Q) a).symm

/-- The map `T → (A[I/f]_Q)^∧` induced by `(A_𝔮)^∧ ⊗_A A[I/f] → (A[I/f]_Q)^∧`. -/
noncomputable def ψ : Loc I f Q →+* affineBlowupChartCompletion I f Q :=
  IsLocalization.lift (M := (prime I f Q).primeCompl) (g := toChart I f Q) fun y =>
    IsLocalRing.notMem_maximalIdeal.mp fun h => y.2 ((mem_prime_iff I f Q y.1).mpr h)

/-- On `(A_𝔮)^∧ ⊗_A A[I/f]`, the map `T → (A[I/f]_Q)^∧` is `toChart`. -/
theorem ψ_algebraMap (x : Tensor I f Q) :
    ψ I f Q (algebraMap _ (Loc I f Q) x) = toChart I f Q x :=
  IsLocalization.lift_eq _ x

/-- The composite `A[I/f]_Q → T → (A[I/f]_Q)^∧` is the completion map of `A[I/f]_Q`. -/
theorem ψ_comp_ιB :
    (ψ I f Q).comp (ιB I f Q) = algebraMap _ (affineBlowupChartCompletion I f Q) := by
  refine IsLocalization.ringHom_ext Q.primeCompl (RingHom.ext fun b => ?_)
  simp only [RingHom.comp_apply]
  rw [ιB_algebraMap, ψ_algebraMap, toChart_inr]

/-- The ideal `I T` of `T`. -/
noncomputable abbrev ideal : Ideal (Loc I f Q) :=
  (I.map (algebraMap A (Localization.AtPrime Q))).map (ιB I f Q)

/-- The ideal `I T` lies in the maximal ideal of `T`. -/
theorem ideal_le_maximalIdeal : ideal I f Q ≤ maximalIdeal (Loc I f Q) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  exact map_nonunit (ιB I f Q) x (hJ.out hx)

/-- The ideal `I (A_𝔮)^∧` lands in `I T`. -/
theorem algebraMap_mem_ideal (j : affineBlowupBaseCompletion I f Q)
    (hj : j ∈ (I.map (algebraMap A (Localization.AtPrime (Q.under A)))).map (algebraMap _ _)) :
    algebraMap _ (Loc I f Q) j ∈ ideal I f Q := by
  have heq : ((I.map (algebraMap A (Localization.AtPrime (Q.under A)))).map
      (algebraMap _ (affineBlowupBaseCompletion I f Q))).map (algebraMap _ (Loc I f Q)) =
      ideal I f Q := by
    rw [Ideal.map_map, algebraMap_comp_algebraMap_eq, ← Ideal.map_map,
      map_localRingHom_under_map]
  rw [← heq]
  exact Ideal.mem_map_of_mem _ hj

omit hJ in
/-- Every element of `(A_𝔮)^∧` is congruent modulo `I (A_𝔮)^∧` to an element of the image of
`A_𝔮`. -/
theorem exists_sub_mem_map_baseCompletion (r : affineBlowupBaseCompletion I f Q) :
    ∃ y : Localization.AtPrime (Q.under A), r - algebraMap _ (affineBlowupBaseCompletion I f Q) y ∈
      (I.map (algebraMap A (Localization.AtPrime (Q.under A)))).map (algebraMap _ _) := by
  let JA := I.map (algebraMap A (Localization.AtPrime (Q.under A)))
  let r' : AdicCompletion JA (Localization.AtPrime (Q.under A)) := r
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ JA r')
  have hmem : r' - algebraMap _ (AdicCompletion JA _) y ∈
      JA.map (algebraMap _ (AdicCompletion JA (Localization.AtPrime (Q.under A)))) := by
    rw [← AdicCompletion.ker_evalOneₐ_eq_map _ (Ideal.fg_of_isNoetherianRing _), RingHom.mem_ker]
    change AdicCompletion.evalOneₐ JA (r' - _) = 0
    rw [map_sub, ← hy, show AdicCompletion.evalOneₐ JA
      (algebraMap _ (AdicCompletion JA (Localization.AtPrime (Q.under A))) y) =
        Ideal.Quotient.mk _ y from
      RingHom.congr_fun (AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk _) y, sub_self]
  exact ⟨y, hmem⟩

/-- A product `r · b` in `(A_𝔮)^∧ ⊗_A A[I/f]` is congruent modulo `I T` to an element of the
image of `A[I/f]_Q`. -/
theorem exists_sub_mem_ideal_mul (r : affineBlowupBaseCompletion I f Q) (b : affineBlowup I f) :
    ∃ c : Localization.AtPrime Q, algebraMap _ (Loc I f Q)
      (algebraMap (affineBlowupBaseCompletion I f Q) (Tensor I f Q) r * inr I f Q b) -
        ιB I f Q c ∈ ideal I f Q := by
  obtain ⟨y, hry⟩ := exists_sub_mem_map_baseCompletion I f Q r
  refine ⟨Localization.localRingHom (Q.under A) Q (algebraMap A (affineBlowup I f)) rfl y *
    algebraMap _ (Localization.AtPrime Q) b, ?_⟩
  have hy' := RingHom.congr_fun (algebraMap_comp_algebraMap_eq I f Q) y
  simp only [RingHom.comp_apply] at hy'
  rw [map_mul, map_mul (ιB I f Q), ← IsScalarTower.algebraMap_apply, ιB_algebraMap, ← hy',
    ← sub_mul, ← map_sub]
  exact Ideal.mul_mem_right _ _ (algebraMap_mem_ideal I f Q _ hry)

/-- Every element of `(A_𝔮)^∧ ⊗_A A[I/f]` is congruent modulo `I T` to an element of the image of
`A[I/f]_Q`. -/
theorem exists_sub_mem_ideal (x : Tensor I f Q) :
    ∃ b : Localization.AtPrime Q, algebraMap _ (Loc I f Q) x - ιB I f Q b ∈ ideal I f Q := by
  refine tensor_induction I f Q (P := fun x => ∃ b : Localization.AtPrime Q,
    algebraMap _ (Loc I f Q) x - ιB I f Q b ∈ ideal I f Q)
    (exists_sub_mem_ideal_mul I f Q) ?_ x
  rintro x y ⟨b₁, h₁⟩ ⟨b₂, h₂⟩
  refine ⟨b₁ + b₂, ?_⟩
  have heq : algebraMap (Tensor I f Q) (Loc I f Q) (x + y) - ιB I f Q (b₁ + b₂) =
      (algebraMap (Tensor I f Q) (Loc I f Q) x - ιB I f Q b₁) +
        (algebraMap (Tensor I f Q) (Loc I f Q) y - ιB I f Q b₂) := by
    rw [map_add (algebraMap (Tensor I f Q) (Loc I f Q)), (ιB I f Q).map_add b₁ b₂]
    abel
  rw [heq]
  exact add_mem h₁ h₂

/-- The map `T → A[I/f]_Q ⧸ I` through `(A[I/f]_Q)^∧`. -/
noncomputable def evalOne : Loc I f Q →+* Localization.AtPrime Q ⧸
    I.map (algebraMap A (Localization.AtPrime Q)) :=
  (AdicCompletion.evalOneₐ (I.map (algebraMap A (Localization.AtPrime Q)))).toRingHom.comp
    (ψ I f Q)

/-- The composite `A[I/f]_Q → T → A[I/f]_Q ⧸ I` is the quotient map. -/
theorem evalOne_ιB (x : Localization.AtPrime Q) :
    evalOne I f Q (ιB I f Q x) = Ideal.Quotient.mk _ x := by
  change AdicCompletion.evalOneₐ _ ((ψ I f Q).comp (ιB I f Q) x) = _
  rw [ψ_comp_ιB]
  exact RingHom.congr_fun (AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk _) x

/-- The ideal `I T` lies in the kernel of `T → A[I/f]_Q ⧸ I`. -/
theorem ideal_le_ker_evalOne : ideal I f Q ≤ RingHom.ker (evalOne I f Q) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker, evalOne_ιB, Ideal.Quotient.eq_zero_iff_mem]
  exact hx

/-- The map `A[I/f]_Q ⧸ I → T ⧸ I T` is injective. -/
theorem injective_quotientMap :
    Function.Injective (Ideal.quotientMap (ideal I f Q) (ιB I f Q) Ideal.le_comap_map) := by
  refine Function.LeftInverse.injective (g := Ideal.Quotient.lift (ideal I f Q) (evalOne I f Q)
    fun a ha => ideal_le_ker_evalOne I f Q ha) fun z => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [Ideal.quotientMap_mk]
  exact (Ideal.Quotient.lift_mk _ _ _).trans (evalOne_ιB I f Q x)

/-- If `b ∈ A[I/f]_Q` is congruent modulo `I T` to an element `s ∉ prime I f Q`, then `b` is a
unit. -/
theorem isUnit_of_sub_mem_ideal (s : (prime I f Q).primeCompl) (b : Localization.AtPrime Q)
    (hb : algebraMap _ (Loc I f Q) (s : Tensor I f Q) - ιB I f Q b ∈ ideal I f Q) : IsUnit b := by
  by_contra hb'
  have h1 : ιB I f Q b ∈ maximalIdeal (Loc I f Q) :=
    map_nonunit (ιB I f Q) b ((IsLocalRing.mem_maximalIdeal _).mpr hb')
  have h2 := (maximalIdeal (Loc I f Q)).add_mem (ideal_le_maximalIdeal I f Q hb) h1
  rw [sub_add_cancel] at h2
  exact (IsLocalRing.mem_maximalIdeal _).mp h2 (IsLocalization.map_units _ s)

/-- The map `A[I/f]_Q ⧸ I → T ⧸ I T` is surjective. -/
theorem surjective_quotientMap :
    Function.Surjective (Ideal.quotientMap (ideal I f Q) (ιB I f Q) Ideal.le_comap_map) := by
  intro z
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨x, s, hxs⟩ := IsLocalization.exists_mk'_eq (prime I f Q).primeCompl t
  obtain ⟨bx, hbx⟩ := exists_sub_mem_ideal I f Q x
  obtain ⟨bs, hbs⟩ := exists_sub_mem_ideal I f Q s
  obtain ⟨u, rfl⟩ := isUnit_of_sub_mem_ideal I f Q s bs hbs
  refine ⟨Ideal.Quotient.mk _ (bx * ↑u⁻¹), ?_⟩
  rw [Ideal.quotientMap_mk, ← hxs]
  have hspec := congrArg (Ideal.Quotient.mk (ideal I f Q))
    (IsLocalization.mk'_spec (Loc I f Q) x s)
  rw [map_mul, Ideal.Quotient.eq.mpr hbx, Ideal.Quotient.eq.mpr hbs] at hspec
  rw [map_mul (ιB I f Q), map_mul (Ideal.Quotient.mk (ideal I f Q)), ← hspec, mul_assoc,
    ← map_mul (Ideal.Quotient.mk (ideal I f Q)), ← map_mul (ιB I f Q), Units.mul_inv,
    map_one (ιB I f Q), map_one (Ideal.Quotient.mk (ideal I f Q)), mul_one]

end Model

end BlowupChartModel

end Stacks.Algebraization
