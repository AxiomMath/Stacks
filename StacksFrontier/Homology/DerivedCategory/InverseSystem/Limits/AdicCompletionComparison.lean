module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.CompletionUnitDenseAnyDegree
public import StacksFrontier.Algebra.Homology.DerivedHomologyLinear
public import StacksFrontier.CategoryTheory.Abelian.InverseSystemModuleCat
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.AdicSystem
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorProjections
public import StacksFrontier.Homology.DerivedComplete.AdicKoszulTower
public import StacksFrontier.Homology.DerivedComplete.FlatAdicCompletionExtension
public import StacksFrontier.RingTheory.AdicCompletion.EndomorphismBijective

/-!
# The canonical comparison of completed cohomology with the limit of derived reductions

Let `I` be an ideal of a Noetherian ring `A`, let `K ∈ D(A)` and set `Kₙ = K ⊗ᴸ[A] A/Iⁿ⁺¹`. The
reduction maps `K ⟶ Kₙ` induce maps `Hⁱ(K) ⟶ Hⁱ(Kₙ)`, which factor through `Hⁱ(K)/Iⁿ⁺¹Hⁱ(K)`
because `Iⁿ⁺¹` kills `Hⁱ(Kₙ)`, and so induce the canonical map
`lim Hⁱ(K)/Iⁿ⁺¹Hⁱ(K) ⟶ lim Hⁱ(Kₙ)`. If every `Hⁱ(K)` is finite and every system `Hⁱ(Kₙ)` is
Mittag--Leffler, this canonical map is an isomorphism (Stacks 0EGS).

The canonical form of Stacks 0EGS is `isIso_adicCompletionToLimitHomology`. The theorem
`adicCompletion_homology_iso_limit_derivedReduction` (also tagged 0EGS) gives only an abstract
isomorphism between the two sides; it follows from this one, and is used in its proof.

## Main definitions

* `adicCompletionToLimitHomology`: the canonical map from the `I`-adic completion of `Hⁱ(K)`
  to the inverse limit of the `Hⁱ(Kₙ)`.

## Main results

* `exists_isDerivedLimitWithProjections_derivedReductionMap`:
  over a Noetherian ring the derived completion of `K` is a derived limit of the `Kₙ` whose
  projections, composed with the completion unit (precomposed with an automorphism of `K`), are
  the reduction maps.
* `isIso_adicCompletionToLimitHomology` ([Stacks, Tag 0EGS]): the canonical map is an isomorphism.

## Implementation notes

The proof follows Stacks. The derived completion `K^∧` is a derived limit of the `Kₙ`
(Stacks 0922), with projections compatible with the reduction maps; by the Mittag--Leffler
condition the Milnor sequence (Stacks 0CQE, 091D) makes `Hⁱ(K^∧) ⟶ lim Hⁱ(Kₙ)` an isomorphism, and
the completion unit `Hⁱ(K) ⟶ Hⁱ(K^∧)` is surjective modulo `I` (Stacks 0A06). Hence the canonical
map is surjective modulo `I`; since its source and target are isomorphic (the existing
`adicCompletion_homology_iso_limit_derivedReduction`), it is an isomorphism by
`AdicCompletion.bijective_of_linearEquiv_of_range_sup_smul_eq_top`.

Stacks 0922 is available with projections pinned to the reduction maps only over `ULift A`; it is
brought down along the universe-lift equivalence `D(A) ≌ D(ULift A)`. The comparison of the two
derived tensor products across that equivalence is only known to be natural, not to respect the
unit isomorphisms, so the reduction maps are matched up to an automorphism of `K`, which is
harmless for a statement about the image of `Hⁱ(K)`.

## References

* [Stacks Project, Tag 0EGS](https://stacks.math.columbia.edu/tag/0EGS)
* [Stacks Project, Tag 0922](https://stacks.math.columbia.edu/tag/0922)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace Stacks.InverseSystem.AdicCompletionCohomology

open NoetherianAdicCompletion

/-- Countable products exist in `D(R)`. -/
local instance derivedCategoryHasProductsNat (R : Type u) [Ring R]
    [HasDerivedCategory (ModuleCat.{u} R)] :
    HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} R)) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]

/-! ### The reduction maps -/

/-- The quotient maps `A ⟶ A/Iⁿ⁺¹` placed in degree zero form a cone on the tower
`n ↦ (A/Iⁿ⁺¹)[0]`. -/
theorem idealPowerQuotientMap_comp_map_succ (I : Ideal A) (n : ℕ) :
    idealPowerQuotientMap I (n + 1) ≫
        (idealPowerQuotientSystem I).map (homOfLE (Nat.le_succ n)).op =
      idealPowerQuotientMap I n := by
  rw [← cancel_mono ((idealPowerQuotientSystemIso I).hom.app ⟨n⟩), Category.assoc,
    (idealPowerQuotientSystemIso I).hom.naturality, ← Category.assoc,
    idealPowerQuotientMap_comp_idealPowerQuotientSystemIso_hom,
    idealPowerQuotientMap_comp_idealPowerQuotientSystemIso_hom, Functor.comp_map]
  refine ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map_comp _ _).symm.trans
    (congrArg _ ?_)
  rw [show (AdicCompletionTor.idealPowerQuotientModuleSystem I).map (homOfLE (Nat.le_succ n)).op =
    idealPowerQuotientTransition I (n + 1) n (Nat.le_succ n) from
    Functor.ofOpSequence_map_homOfLE_succ _ n]
  ext
  rfl

/-- The reduction maps `K ⟶ K ⊗ᴸ[A] A/Iⁿ⁺¹` form a cone on the tower of derived reductions. -/
theorem derivedReductionMap_comp_map_succ (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℕ) :
    (derivedReductionMap I T (n + 1)).app K ≫
        (idealPowerQuotientSystem I ⋙ T.tensor.obj K).map (homOfLE (Nat.le_succ n)).op =
      (derivedReductionMap I T n).app K := by
  simp only [derivedReductionMap, NatTrans.comp_app, Functor.flip_map_app, Category.assoc,
    Functor.comp_map]
  rw [← Functor.map_comp, idealPowerQuotientMap_comp_map_succ]

/-- The ideal `Iⁿ⁺¹` kills the cohomology of `K ⊗ᴸ[A] A/Iⁿ⁺¹`. -/
theorem smul_eq_zero_of_mem_pow (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (n : ℕ) {r : A} (hr : r ∈ I ^ (n + 1))
    (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      ((idealPowerQuotientSystem I ⋙ T.tensor.obj K).obj ⟨n⟩)) :
    r • y = 0 := by
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let e := (idealPowerQuotientSystemIso I).app ⟨n⟩
  have hM : r • 𝟙 (ModuleCat.of A (A ⧸ I ^ (n + 1))) = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change r • Ideal.Quotient.mk (I ^ (n + 1)) a = 0
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ hr
  have hS : r • 𝟙 ((AdicCompletionTor.idealPowerQuotientModuleSystem I ⋙ S).obj ⟨n⟩) = 0 := by
    change r • 𝟙 (S.obj (ModuleCat.of A (A ⧸ I ^ (n + 1)))) = 0
    rw [← S.map_id, ← Functor.map_smul, hM, Functor.map_zero]
  have hQ : r • 𝟙 ((idealPowerQuotientSystem I).obj ⟨n⟩) = 0 := by
    calc r • 𝟙 _ = r • (e.hom ≫ e.inv) := by rw [e.hom_inv_id]
      _ = e.hom ≫ (r • 𝟙 _) ≫ e.inv := by
        rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul]
      _ = 0 := by rw [hS, zero_comp, comp_zero]
  have hF : r • 𝟙 ((idealPowerQuotientSystem I ⋙ T.tensor.obj K).obj ⟨n⟩) = 0 := by
    have h := AdicKoszul.tensor_map_smul_id T.toGeneral K ((idealPowerQuotientSystem I).obj ⟨n⟩) r
    change (T.tensor.obj K).map _ = _ at h
    rw [hQ, Functor.map_zero] at h
    exact h.symm
  have hH := congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map hF
  rw [Stacks.HomologyLinear.derivedHomologyMap_smul, CategoryTheory.Functor.map_id,
    Functor.map_zero] at hH
  exact congrArg (fun f => f.hom y) hH

/-! ### The canonical map -/

/-- The map `Hⁱ(K) ⟶ Hⁱ(K ⊗ᴸ[A] A/Iⁿ⁺¹)` induced by the reduction map. -/
abbrev homologyReductionMap (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K ⟶
      ((idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ⟨n⟩ :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map ((derivedReductionMap I T n).app K)

/-- The map `Hⁱ(K)/Iⁿ⁺¹Hⁱ(K) ⟶ Hⁱ(K ⊗ᴸ[A] A/Iⁿ⁺¹)` induced by the reduction map. -/
def quotientHomologyReductionMap (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (n : ℕ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K ⧸
        (I ^ (n + 1) • ⊤ :
          Submodule A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)))
      →ₗ[A] ((idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ⟨n⟩ :=
  (I ^ (n + 1) • ⊤ : Submodule A _).liftQ (homologyReductionMap I T K i n).hom
    (Submodule.smul_le.2 fun r hr m _ => by
      rw [LinearMap.mem_ker, map_smul]
      exact smul_eq_zero_of_mem_pow I T K i n hr _)

@[simp]
theorem quotientHomologyReductionMap_mk (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (n : ℕ)
    (m : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) :
    quotientHomologyReductionMap I T K i n (Submodule.Quotient.mk m) =
      (homologyReductionMap I T K i n).hom m := rfl

/-- The cone on the cohomology tower `n ↦ Hⁱ(K ⊗ᴸ[A] A/Iⁿ⁺¹)` with vertex the `I`-adic
completion of `Hⁱ(K)`, given by the maps `Hⁱ(K)/Iⁿ⁺¹Hⁱ(K) ⟶ Hⁱ(K ⊗ᴸ[A] A/Iⁿ⁺¹)`. -/
def adicCompletionCone (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    Cone ((idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) where
  pt := ModuleCat.of A
    (AdicCompletion I ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K))
  π := NatTrans.ofOpSequence
    (fun n => ModuleCat.ofHom (quotientHomologyReductionMap I T K i n ∘ₗ
      AdicCompletion.eval I _ (n + 1)))
    (fun n => by
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (x.val (n + 1 + 1))
      have h1 : x.val (n + 1) = Submodule.Quotient.mk m := by
        rw [← AdicCompletion.transitionMap_comp_eval_apply I _ (Nat.le_succ (n + 1)) x, ← hm]
        rfl
      change quotientHomologyReductionMap I T K i n (x.val (n + 1)) =
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
          ((idealPowerQuotientSystem I ⋙ T.tensor.obj K).map (homOfLE (Nat.le_succ n)).op)).hom
          (quotientHomologyReductionMap I T K i (n + 1) (x.val (n + 1 + 1)))
      rw [h1, ← hm, quotientHomologyReductionMap_mk, quotientHomologyReductionMap_mk,
        homologyReductionMap, homologyReductionMap, ← ModuleCat.comp_apply, ← Functor.map_comp,
        derivedReductionMap_comp_map_succ])

/-- **The canonical map** `lim Hⁱ(K)/Iⁿ⁺¹Hⁱ(K) ⟶ lim Hⁱ(K ⊗ᴸ[A] A/Iⁿ⁺¹)`, from the `I`-adic
completion of `Hⁱ(K)` to the inverse limit of the cohomology of the derived reductions, induced
by the reduction maps `K ⟶ K ⊗ᴸ[A] A/Iⁿ⁺¹`. -/
def adicCompletionToLimitHomology (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    ModuleCat.of A
        (AdicCompletion I ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) ⟶
      limit ((idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) :=
  limit.lift _ (adicCompletionCone I T K i)

/-- The `n`-th component of the canonical map sends a compatible family to the image of its
`(n + 1)`-st term under `Hⁱ(K)/Iⁿ⁺¹Hⁱ(K) ⟶ Hⁱ(K ⊗ᴸ[A] A/Iⁿ⁺¹)`. -/
@[simp]
theorem adicCompletionToLimitHomology_π (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (n : ℕ) :
    adicCompletionToLimitHomology I T K i ≫ limit.π _ ⟨n⟩ =
      ModuleCat.ofHom (quotientHomologyReductionMap I T K i n ∘ₗ
        AdicCompletion.eval I _ (n + 1)) :=
  limit.lift_π _ _

/-- On the image of `Hⁱ(K)` the canonical map is given by the maps
`Hⁱ(K) ⟶ Hⁱ(K ⊗ᴸ[A] A/Iⁿ⁺¹)` induced by the reduction maps. -/
theorem of_comp_adicCompletionToLimitHomology_π (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (n : ℕ) :
    ModuleCat.ofHom (AdicCompletion.of I _) ≫ adicCompletionToLimitHomology I T K i ≫
        limit.π _ ⟨n⟩ = homologyReductionMap I T K i n := by
  rw [adicCompletionToLimitHomology_π]
  rfl

/-! ### Stacks 0922 with the reduction maps, over `A` -/

/-- The ring isomorphism `A/Iⁿ⁺¹ ≅ ULift A/Jⁿ⁺¹`, for `J` the ideal of `ULift A` corresponding
to `I`. -/
def quotientPowUliftRingEquiv (I : Ideal A) (n : ℕ) :
    A ⧸ I ^ (n + 1) ≃+* ULift.{u} A ⧸ uliftIdeal I ^ (n + 1) :=
  Ideal.quotientEquiv _ _ (ULift.ringEquiv : ULift.{u} A ≃+* A).symm (by
    ext r
    change r ∈ uliftIdeal I ^ (n + 1) ↔
      r ∈ Ideal.map (ULift.ringEquiv : ULift.{u} A ≃+* A).symm (I ^ (n + 1))
    rw [mem_uliftIdeal_pow_iff, ← Ideal.symm_apply_mem_of_equiv_iff]
    rfl)

/-- The lift of `A/Iⁿ⁺¹` to `ULift A` is `ULift A/Jⁿ⁺¹`. -/
def quotientPowUliftLinearEquiv (I : Ideal A) (n : ℕ) :
    (AdicKoszul.moduleUniverseLift.{u, u} A).obj (ModuleCat.of A (A ⧸ I ^ (n + 1))) ≃ₗ[ULift.{u} A]
      ULift.{u} A ⧸ uliftIdeal I ^ (n + 1) where
  toFun x := quotientPowUliftRingEquiv I n x.down
  invFun y := ULift.up ((quotientPowUliftRingEquiv I n).symm y)
  map_add' x y := map_add (quotientPowUliftRingEquiv I n) x.down y.down
  map_smul' r x := by
    obtain ⟨y⟩ := x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨b⟩ := r
    change quotientPowUliftRingEquiv I n (b • Ideal.Quotient.mk (I ^ (n + 1)) a) =
      (ULift.up b : ULift.{u} A) • quotientPowUliftRingEquiv I n (Ideal.Quotient.mk _ a)
    have h1 : b • Ideal.Quotient.mk (I ^ (n + 1)) a = Ideal.Quotient.mk (I ^ (n + 1)) (b * a) :=
      (Submodule.Quotient.mk_smul _ b a).symm
    have h2 : (ULift.up b : ULift.{u} A) •
        Ideal.Quotient.mk (uliftIdeal I ^ (n + 1)) (ULift.up a : ULift.{u} A) =
        Ideal.Quotient.mk (uliftIdeal I ^ (n + 1)) (ULift.up b * ULift.up a : ULift.{u} A) :=
      (Submodule.Quotient.mk_smul _ _ _).symm
    rw [h1, show quotientPowUliftRingEquiv I n (Ideal.Quotient.mk _ (b * a)) =
        Ideal.Quotient.mk (uliftIdeal I ^ (n + 1)) (ULift.up (b * a) : ULift.{u} A) from
        Ideal.quotientEquiv_mk _ _ _ _ _,
      show quotientPowUliftRingEquiv I n (Ideal.Quotient.mk _ a) =
        Ideal.Quotient.mk (uliftIdeal I ^ (n + 1)) (ULift.up a : ULift.{u} A) from
        Ideal.quotientEquiv_mk _ _ _ _ _, h2]
    rfl
  left_inv x := by
    change ULift.up ((quotientPowUliftRingEquiv I n).symm
      (quotientPowUliftRingEquiv I n x.down)) = x
    rw [RingEquiv.symm_apply_apply]
    exact ULift.up_down x
  right_inv y := by
    change quotientPowUliftRingEquiv I n ((quotientPowUliftRingEquiv I n).symm y) = y
    rw [RingEquiv.apply_symm_apply]

/-- The tower of quotients `n ↦ A/Iⁿ⁺¹`, lifted to `ULift A`, is the tower `n ↦ ULift A/Jⁿ⁺¹`. -/
def quotientModuleSystemUliftIso (I : Ideal A) :
    AdicCompletionTor.idealPowerQuotientModuleSystem I ⋙ AdicKoszul.moduleUniverseLift.{u, u} A ≅
      AdicCompletionTor.idealPowerQuotientModuleSystem (uliftIdeal I) :=
  let α : AdicCompletionTor.idealPowerQuotientModuleSystem I ⋙
      AdicKoszul.moduleUniverseLift.{u, u} A ⟶
      AdicCompletionTor.idealPowerQuotientModuleSystem (uliftIdeal I) :=
    NatTrans.ofOpSequence
      (F := AdicCompletionTor.idealPowerQuotientModuleSystem I ⋙
        AdicKoszul.moduleUniverseLift.{u, u} A)
      (G := AdicCompletionTor.idealPowerQuotientModuleSystem (uliftIdeal I))
      (fun n => ModuleCat.ofHom (quotientPowUliftLinearEquiv I n).toLinearMap) (fun n => by
        rw [Functor.comp_map,
          show (AdicCompletionTor.idealPowerQuotientModuleSystem I).map
              (homOfLE (n.le_add_right 1)).op =
            idealPowerQuotientTransition I (n + 1) n (Nat.le_succ n) from
            Functor.ofOpSequence_map_homOfLE_succ _ n,
          show (AdicCompletionTor.idealPowerQuotientModuleSystem (uliftIdeal I)).map
              (homOfLE (n.le_add_right 1)).op =
            idealPowerQuotientTransition (uliftIdeal I) (n + 1) n (Nat.le_succ n) from
            Functor.ofOpSequence_map_homOfLE_succ _ n]
        refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        obtain ⟨y⟩ := x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
        rfl)
  have (n : ℕᵒᵖ) : IsIso (α.app n) :=
    inferInstanceAs (IsIso ((quotientPowUliftLinearEquiv I n.unop).toModuleIso).hom)
  have : IsIso α := NatIso.isIso_of_isIso_app α
  asIso α

/-- The lift of the `A`-module `A` to `ULift A` is the `ULift A`-module `ULift A`. -/
def ringUliftLinearEquiv (A : Type u) [CommRing A] :
    (AdicKoszul.moduleUniverseLift.{u, u} A).obj (ModuleCat.of A A) ≃ₗ[ULift.{u} A]
      ULift.{u} A where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The lift of `A` to `ULift A`, placed in degree zero. -/
def ringUliftSingleIso (A : Type u) [CommRing A] :
    (AdicKoszul.derivedUniverseLift.{u, u} A).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (ULift.{u} A)) 0).obj
        (ModuleCat.of (ULift.{u} A) (ULift.{u} A)) :=
  ((AdicKoszul.moduleUniverseLift.{u, u} A).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of A A) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} (ULift.{u} A)) 0).mapIso
      (ringUliftLinearEquiv A).toModuleIso

/-- The tower `n ↦ (A/Iⁿ⁺¹)[0]` of `D(A)`, lifted to `D(ULift A)`, is the tower
`n ↦ (ULift A/Jⁿ⁺¹)[0]`. -/
def idealPowerQuotientSystemUliftIso (I : Ideal A) :
    idealPowerQuotientSystem I ⋙ AdicKoszul.derivedUniverseLift.{u, u} A ≅
      idealPowerQuotientSystem (uliftIdeal I) :=
  Functor.isoWhiskerRight (idealPowerQuotientSystemIso I) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((AdicKoszul.moduleUniverseLift.{u, u} A).mapDerivedCategorySingleFunctor 0) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (quotientModuleSystemUliftIso I) _ ≪≫
    (idealPowerQuotientSystemIso (uliftIdeal I)).symm

/-- Under `idealPowerQuotientSystemUliftIso`, the lift of the quotient map `A ⟶ A/Iⁿ⁺¹` is the
quotient map `ULift A ⟶ ULift A/Jⁿ⁺¹`. -/
theorem map_idealPowerQuotientMap_comp_uliftIso_hom (I : Ideal A) (n : ℕ) :
    (AdicKoszul.derivedUniverseLift.{u, u} A).map (idealPowerQuotientMap I n) ≫
        (idealPowerQuotientSystemUliftIso I).hom.app ⟨n⟩ =
      (ringUliftSingleIso A).hom ≫ idealPowerQuotientMap (uliftIdeal I) n := by
  let V := AdicKoszul.moduleUniverseLift.{u, u} A
  let S' := DerivedCategory.singleFunctor (ModuleCat.{u} (ULift.{u} A)) 0
  have h1 := idealPowerQuotientMap_comp_idealPowerQuotientSystemIso_hom I n
  have h2 := idealPowerQuotientMap_comp_idealPowerQuotientSystemIso_hom (uliftIdeal I) n
  have hnat := (V.mapDerivedCategorySingleFunctor 0).hom.naturality
    (ModuleCat.ofHom (I ^ (n + 1)).mkQ)
  rw [← cancel_mono ((idealPowerQuotientSystemIso (uliftIdeal I)).hom.app ⟨n⟩), Category.assoc,
    Category.assoc, h2]
  simp only [idealPowerQuotientSystemUliftIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.id_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← Functor.map_comp_assoc, h1]
  refine (reassoc_of% hnat) _ |>.trans ?_
  have hmod : (AdicKoszul.moduleUniverseLift.{u, u} A).map (ModuleCat.ofHom (I ^ (n + 1)).mkQ) ≫
      (quotientModuleSystemUliftIso I).hom.app ⟨n⟩ =
      (ringUliftLinearEquiv A).toModuleIso.hom ≫
        ModuleCat.ofHom (uliftIdeal I ^ (n + 1)).mkQ :=
    ModuleCat.hom_ext (LinearMap.ext fun x => rfl)
  have key : S'.map ((AdicKoszul.moduleUniverseLift.{u, u} A).map
        (ModuleCat.ofHom (I ^ (n + 1)).mkQ)) ≫
        S'.map ((quotientModuleSystemUliftIso I).hom.app ⟨n⟩) =
      S'.map (ringUliftLinearEquiv A).toModuleIso.hom ≫
        S'.map (ModuleCat.ofHom (uliftIdeal I ^ (n + 1)).mkQ) :=
    ((Functor.map_comp _ _ _).symm.trans (congrArg _ hmod)).trans (Functor.map_comp _ _ _)
  exact (congrArg (fun g => (V.mapDerivedCategorySingleFunctor 0).hom.app (ModuleCat.of A A) ≫ g)
    key).trans (Category.assoc _ _ _).symm

/-- **Stacks 0922 over `A`, with the reduction maps.** Let `I` be an ideal of a Noetherian ring
`A`, let `T` be a derived tensor product on `D(A)` and `K ∈ D(A)`. There are a reflection
`L ⊣ ι` of `D(A)` onto the derived `I`-complete objects, an automorphism `θ` of `K` and
projections `pₙ : K^∧ ⟶ K ⊗ᴸ[A] A/Iⁿ⁺¹` exhibiting `K^∧` as a derived limit of the derived
reductions of `K`, such that the unit `K ⟶ K^∧`, precomposed with `θ` and followed by `pₙ`, is
the reduction map. -/
theorem exists_isDerivedLimitWithProjections_derivedReductionMap
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    ∃ (L : DerivedCategory (ModuleCat.{u} A) ⥤
        (Dualizing.derivedCompleteProperty.{u, u} A I).FullSubcategory)
      (adj : L ⊣ (Dualizing.derivedCompleteProperty.{u, u} A I).ι) (θ : K ≅ K)
      (p : ∀ n : ℕ, (L ⋙ (Dualizing.derivedCompleteProperty.{u, u} A I).ι).obj K ⟶
        (idealPowerQuotientSystem I ⋙ T.tensor.obj K).obj ⟨n⟩),
      IsDerivedLimitWithProjections (idealPowerQuotientSystem I ⋙ T.tensor.obj K)
          ((L ⋙ (Dualizing.derivedCompleteProperty.{u, u} A I).ι).obj K) p ∧
        ∀ n : ℕ, θ.hom ≫ adj.unit.app K ≫ p n = (derivedReductionMap I T n).app K := by
  let TB := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{u} A)
  let U := AdicKoszul.derivedUniverseLift.{u, u} A
  obtain ⟨L, adj, π, hlim, hunit⟩ := idealPowerDerivedLimit_isLeftAdjoint.{u, u} A I TB
  obtain ⟨t⟩ := AdicCompletionTor.nonempty_tensorUliftFunctorIso A T K
  let j := idealPowerQuotientSystemUliftIso I
  let F := idealPowerQuotientSystem I ⋙ T.tensor.obj K
  let E : F ⋙ U ≅ idealPowerQuotientSystem (uliftIdeal I) ⋙ TB.tensor.obj (U.obj K) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ t ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight j _
  have hE (n : ℕ) : E.hom.app ⟨n⟩ = t.hom.app ((idealPowerQuotientSystem I).obj ⟨n⟩) ≫
      (TB.tensor.obj (U.obj K)).map (j.hom.app ⟨n⟩) := by
    simp only [E, Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    exact (Category.id_comp _).trans (congrArg _ (Category.id_comp _))
  let θU : U.obj K ≅ U.obj K :=
    U.mapIso (T.rightUnitor.app K).symm ≪≫ t.app _ ≪≫
      (TB.tensor.obj (U.obj K)).mapIso (ringUliftSingleIso A) ≪≫ TB.rightUnitor.app (U.obj K)
  have hcan (n : ℕ) : U.map ((derivedReductionMap I T n).app K) ≫ E.hom.app ⟨n⟩ =
      θU.hom ≫ (derivedReductionMap (uliftIdeal I) TB n).app (U.obj K) := by
    have ht := t.hom.naturality (idealPowerQuotientMap I n)
    simp only [Functor.comp_map] at ht
    rw [hE]
    simp only [derivedReductionMap, NatTrans.comp_app, Functor.flip_map_app, Functor.map_comp,
      Category.assoc]
    rw [reassoc_of% ht, ← Functor.map_comp, map_idealPowerQuotientMap_comp_uliftIso_hom,
      Functor.map_comp]
    simp [θU]
    rfl
  let hU := Functor.FullyFaithful.ofFullyFaithful U
  let θ : K ≅ K := hU.preimageIso θU
  have hθ : U.map θ.hom = θU.hom := hU.map_preimage _
  let X := (L ⋙ (Dualizing.derivedCompleteProperty.{u, u} A I).ι).obj K
  let p : ∀ n : ℕ, X ⟶ F.obj ⟨n⟩ := fun n => hU.preimage ((π n).app K ≫ E.inv.app ⟨n⟩)
  have hp (n : ℕ) : U.map (p n) = (π n).app K ≫ E.inv.app ⟨n⟩ := hU.map_preimage _
  refine ⟨L, adj, θ, p, ?_, fun n => ?_⟩
  · refine isDerivedLimitWithProjections_of_map_of_equivalence U F X p ?_
    have h := (hlim K).ofNatIso E.symm
    simp only [Iso.symm_hom] at h
    have hfun : (fun n => U.map (p n)) = fun n => (π n).app K ≫ E.inv.app ⟨n⟩ := funext hp
    rw [hfun]
    exact h
  · apply hU.map_injective
    rw [Functor.map_comp, Functor.map_comp, hθ, hp, ← Category.assoc (U.map _), hunit K n,
      ← Category.assoc, ← hcan, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _

/-- **The completion unit is surjective modulo `I` on cohomology, for any reflection.** Let `I`
be an ideal of a Noetherian ring `A` and `K ∈ D(A)` with finite cohomology modules. For any
reflection `L ⊣ ι` of `D(A)` onto the derived `I`-complete objects and any automorphism `θ` of
`K`, the image of `Hᵠ(K) ⟶ Hᵠ(K^∧)` under `θ` followed by the unit, together with
`I • Hᵠ(K^∧)`, is all of `Hᵠ(K^∧)`. -/
theorem range_homologyMap_comp_unit_sup_smul_eq_top
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ n : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj K))
    (L : DerivedCategory (ModuleCat.{u} A) ⥤
      (Dualizing.derivedCompleteProperty.{u, u} A I).FullSubcategory)
    (adj : L ⊣ (Dualizing.derivedCompleteProperty.{u, u} A I).ι) (θ : K ≅ K) (q : ℤ) :
    LinearMap.range ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).map
          (θ.hom ≫ adj.unit.app K)).hom ⊔
        I • (⊤ : Submodule A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
          ((L ⋙ (Dualizing.derivedCompleteProperty.{u, u} A I).ι).obj K))) = ⊤ := by
  have hI : I.FG := IsNoetherian.noetherian I
  have h0 := Stacks.Algebraization.range_homologyMap_adicCompletionUnit_sup_smul_eq_top_degree
    A I hI K hK q
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) q
  let w := Adjunction.leftAdjointUniq (Stacks.Algebraization.adicCompletionAdjunction A I hI) adj
  have hw := Adjunction.unit_leftAdjointUniq_hom_app
    (Stacks.Algebraization.adicCompletionAdjunction A I hI) adj K
  refine Stacks.Algebraization.range_sup_smul_eq_top_of_linearEquiv I _ _
    (H.mapIso θ.symm).toLinearEquiv
    (H.mapIso ((Dualizing.derivedCompleteProperty.{u, u} A I).ι.mapIso (w.app K))).toLinearEquiv
    (fun m => ?_) h0
  have hsq : H.map ((Stacks.Algebraization.adicCompletionUnit A I hI).app K) ≫
      H.map ((Dualizing.derivedCompleteProperty.{u, u} A I).ι.map (w.hom.app K)) =
      H.map θ.inv ≫ H.map (θ.hom ≫ adj.unit.app K) := by
    rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_assoc]
    exact congrArg H.map hw
  exact congrArg (fun g => g.hom m) hsq

/-- **Stacks 0EGS (Kollár--Kovács).** Let `I` be an ideal of a Noetherian ring `A` and
`K ∈ D(A)`, and set `Kₙ = K ⊗ᴸ[A] A/Iⁿ⁺¹`. Suppose that every cohomology module `Hⁱ(K)` is
finite and that, in every degree, the system `Hⁱ(Kₙ)` is Mittag--Leffler. Then for every `i` the
canonical map `lim Hⁱ(K)/Iⁿ⁺¹Hⁱ(K) ⟶ lim Hⁱ(Kₙ)`, induced by the reduction maps `K ⟶ Kₙ`, is an
isomorphism. -/
@[stacks 0EGS "The equality `lim Hⁱ(K)/IⁿHⁱ(K) = lim Hⁱ(Kₙ)` is the statement that the canonical
map induced by the reduction maps `K → Kₙ` is an isomorphism; positive powers of `I` are indexed
by `n + 1`."]
public theorem isIso_adicCompletionToLimitHomology
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (hK : ∀ i : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (hML : ∀ i : ℤ,
      (((idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) ⋙
        forget (ModuleCat.{u} A)).IsMittagLeffler) :
    ∀ i : ℤ, IsIso (adicCompletionToLimitHomology I T K i) := by
  intro i
  have hI : I.FG := IsNoetherian.noetherian I
  have := hK i
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
  let F := idealPowerQuotientSystem I ⋙ T.tensor.obj K
  obtain ⟨ψ⟩ := adicCompletion_homology_iso_limit_derivedReduction A I K T hK hML i
  obtain ⟨L, adj, θ, p, hlim, hcan⟩ :=
    exists_isDerivedLimitWithProjections_derivedReductionMap A I T K
  have hepi := Stacks.Algebraization.epi_milnorDifference_of_isMittagLefflerCategorical _
    (isMittagLefflerCategorical_of_isMittagLeffler_forget _ (hML (i - 1)))
  let X := (L ⋙ (Dualizing.derivedCompleteProperty.{u, u} A I).ι).obj K
  let β : H.obj X ⟶ limit (F ⋙ H) := limit.lift (F ⋙ H) (H.mapCone hlim.cone)
  have hβ : IsIso β := hlim.isIso_lift_mapCone_homology_of_epi i hepi
  have hβπ (n : ℕ) : β ≫ limit.π (F ⋙ H) ⟨n⟩ = H.map (p n) := limit.lift_π _ _
  let c := adicCompletionToLimitHomology I T K i
  have hφ : H.map (θ.hom ≫ adj.unit.app K) ≫ β = ModuleCat.ofHom (AdicCompletion.of I _) ≫ c := by
    refine limit.hom_ext fun n => ?_
    induction n using Opposite.rec with
    | op n =>
      rw [Category.assoc, hβπ, Category.assoc, of_comp_adicCompletionToLimitHomology_π,
        ← Functor.map_comp, Category.assoc, hcan n]
  have hdense := range_homologyMap_comp_unit_sup_smul_eq_top A I K hK L adj θ i
  have h1 : LinearMap.range (H.map (θ.hom ≫ adj.unit.app K) ≫ β).hom ⊔
      I • (⊤ : Submodule A ((limit (F ⋙ H) : ModuleCat.{u} A))) = ⊤ :=
    Stacks.Algebraization.range_sup_smul_eq_top_of_linearEquiv I _ _ (LinearEquiv.refl A _)
      (asIso β).toLinearEquiv (fun m => rfl) hdense
  have hc : LinearMap.range c.hom ⊔
      I • (⊤ : Submodule A ((limit (F ⋙ H) : ModuleCat.{u} A))) = ⊤ := by
    refine eq_top_iff.2 (h1.symm.le.trans (sup_le_sup_right ?_ _))
    rw [hφ]
    rintro _ ⟨m, rfl⟩
    exact ⟨AdicCompletion.of I _ m, rfl⟩
  exact (ConcreteCategory.isIso_iff_bijective c).2
    (AdicCompletion.bijective_of_linearEquiv_of_range_sup_smul_eq_top hI ψ.toLinearEquiv c.hom hc)

end Stacks.InverseSystem.AdicCompletionCohomology

end
