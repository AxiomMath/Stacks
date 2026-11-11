module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicCompleteComparisonBijective
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.CompletionUnitDenseAnyDegree
public import StacksFrontier.CategoryTheory.Abelian.InverseSystemModuleCat
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.DerivedLimitWithProjections
public import StacksFrontier.Homology.DerivedComplete.FlatAdicCompletionExtension
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.Tor.CanonicalTensorDerivedBifunctor
public import StacksFrontier.RingTheory.Module.AdicSystem.PseudoCoherentHomology

/-!
# The canonical comparison between completed cohomology and the cohomology of adic reductions

Let `I` be an ideal of a commutative ring `A`, let `K` be an object of `D(A)` and write
`Kₙ = K ⊗ᴸ[A] A/Iⁿ⁺¹`. The canonical maps `K ⟶ Kₙ` induce maps `Hⁱ(K) ⟶ Hⁱ(Kₙ)`, compatible
with the transition maps, and `Hⁱ(Kₙ)` is annihilated by `Iⁿ⁺¹`. They therefore induce a
canonical map

`Hⁱ(K)^∧ = lim Hⁱ(K)/Iⁿ⁺¹Hⁱ(K) ⟶ lim Hⁱ(Kₙ)`.

This file constructs that map and proves that it is an isomorphism in the situation of the
Kollár--Kovács lemma: over a Noetherian ring, if every `Hⁱ(K)` is finite and every system
`Hⁱ(Kₙ)` is Mittag--Leffler (Stacks 0EGS); in particular whenever `K` is pseudo-coherent
(Stacks 0EGV).

## Main definitions

* `Stacks.PseudoCoherent.AdicCompletion.adicCompletionToLimitDerivedReduction`: the canonical map
  `Hⁱ(K)^∧ ⟶ lim Hⁱ(K ⊗ᴸ[A] A/Iⁿ⁺¹)`.

## Main results

* `Stacks.PseudoCoherent.AdicCompletion.smul_eq_zero_homology_derivedReduction`: `Iⁿ⁺¹` kills
  `Hⁱ(K ⊗ᴸ[A] A/Iⁿ⁺¹)`.
* `Stacks.PseudoCoherent.AdicCompletion.of_comp_adicCompletionToLimitDerivedReduction_π`: the
  canonical map restricted along `Hⁱ(K) ⟶ Hⁱ(K)^∧` and projected to level `n` is `Hⁱ` of the
  reduction map `K ⟶ K ⊗ᴸ[A] A/Iⁿ⁺¹`.
* `Stacks.PseudoCoherent.AdicCompletion.isIso_adicCompletionToLimitDerivedReduction`: Stacks 0EGS.
* `pseudoCoherent_mittagLeffler_and_isIso_adicCompletionToLimitDerivedReduction` (in the same
  namespace): Stacks 0EGV.

## Implementation notes

The proof follows Stacks. The derived completion `K^∧` is a derived limit of the tower `Kₙ`
(Stacks 0922). That theorem is available with its projections pinned to the reduction maps only
for a derived tensor product over `ULift A`; it is moved to `A` and to an arbitrary derived tensor
product along the universe-lift equivalence `AdicKoszul.derivedUniverseLift`. The comparison of
the two towers is natural in the second variable, so it matches the two families of reduction maps
up to one automorphism of `K`, which is absorbed into the projections. The Milnor sequence of the
pinned presentation identifies `Hⁱ(K^∧)` with `lim Hⁱ(Kₙ)` compatibly with the reduction maps
when the system one degree below is Mittag--Leffler (Stacks 091D, 0CQE). Finally the completion
unit is surjective modulo `I` on cohomology, and `lim Hⁱ(Kₙ)` is abstractly isomorphic to
`Hⁱ(K)^∧` (the non-canonical form of Stacks 0EGS); a map out of `Hⁱ(K)^∧` with these two
properties is bijective (`Stacks.Algebraization.bijective_of_isAdicComplete_of_range_sup_eq_top`).

## References

* [Stacks Project, Tag 0EGS](https://stacks.math.columbia.edu/tag/0EGS)
* [Stacks Project, Tag 0EGV](https://stacks.math.columbia.edu/tag/0EGV)
* [Stacks Project, Tag 0922](https://stacks.math.columbia.edu/tag/0922)
* Email from Sándor Kovács, 23 February 2018.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.PseudoCoherent.AdicCompletion

variable {A : Type u} [CommRing A]

/-- Countable products in `D(A)`, used by the derived-limit presentations below. -/
local instance hasProductsOfShapeNatDerivedModuleCat (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] :
    HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} R)) :=
  Stacks.DerivedProducts.hasProductsOfShape_nat

/-! ### Torsion in the cohomology of the reductions -/

/-- If a scalar kills the `i`-th term of a complex of modules, it kills its `i`-th homology. -/
private theorem smul_eq_zero_homology_of_smul_eq_zero (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ) (r : A) (h : ∀ x : C.X i, r • x = 0) (y : C.homology i) : r • y = 0 := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ i)).1 inferInstance y
  have hz : r • z = 0 := by
    apply (ModuleCat.mono_iff_injective (C.iCycles i)).1 inferInstance
    rw [map_smul, map_zero]
    exact h _
  rw [← map_smul, hz, map_zero]

/-- **`Iⁿ⁺¹` kills `Hⁱ(K ⊗ᴸ[A] A/Iⁿ⁺¹)`.** Computing the derived tensor product on a K-flat
representative `P` of `K`, the module `Hⁱ(K ⊗ᴸ[A] A/Iⁿ⁺¹)` is the `i`-th homology of the complex
`P/Iⁿ⁺¹P`, whose terms are killed by `Iⁿ⁺¹`. -/
theorem smul_eq_zero_homology_derivedReduction (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (n : ℕ) {r : A} (hr : r ∈ I ^ (n + 1))
    (x : (((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ⟨n⟩)) : r • x = 0 := by
  obtain ⟨P, hP, ⟨e⟩⟩ := CochainComplex.DerivedTensor.exists_kFlat_iso A K
  let C := (LiftAcyclic.reduceComplex (I ^ (n + 1))).obj P
  let E := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
      ((T.tensor.mapIso e.symm).app
        ((NoetherianAdicCompletion.idealPowerQuotientSystem I).obj ⟨n⟩)) ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
      ((derivedReductionSystemIsoDegreewise I T P hP).app ⟨n⟩) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app C
  have hC : ∀ y : C.X i, r • y = 0 := by
    intro y
    refine Submodule.Quotient.induction_on _ y fun z ↦ ?_
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul hr Submodule.mem_top)
  apply (ConcreteCategory.bijective_of_isIso E.hom).1
  rw [map_smul, map_zero]
  exact smul_eq_zero_homology_of_smul_eq_zero C i r hC _

/-! ### The canonical comparison map -/

/-- The reduction maps `K ⟶ K ⊗ᴸ[A] A/Iⁿ⁺¹` are compatible with the transition maps. -/
theorem derivedReductionMap_app_comp_map_succ (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℕ) :
    (NoetherianAdicCompletion.derivedReductionMap I T (n + 1)).app K ≫
        (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K).map
          (homOfLE (Nat.le_succ n)).op =
      (NoetherianAdicCompletion.derivedReductionMap I T n).app K := by
  have hle : (I ^ (n + 1 + 1) : Ideal A) ≤ I ^ (n + 1) :=
    Ideal.pow_le_pow_right (Nat.add_le_add_right (Nat.le_succ n) 1)
  have hq : NoetherianAdicCompletion.idealPowerQuotientMap I (n + 1) ≫
      (NoetherianAdicCompletion.idealPowerQuotientSystem I).map (homOfLE (Nat.le_succ n)).op =
        NoetherianAdicCompletion.idealPowerQuotientMap I n := by
    rw [NoetherianAdicCompletion.idealPowerQuotientSystem_map]
    have hnat := AdicCompletionTor.singleExtendIso.inv.naturality
      (NoetherianAdicCompletion.quotientFactor hle)
    have hmkQ := NoetherianAdicCompletion.mkQ_comp_quotientFactor hle
    change (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
          (ModuleCat.ofHom (I ^ (n + 1 + 1)).mkQ) ≫
        DerivedCategory.Q.map (AdicCompletionTor.singleExtendIso.inv.app _) ≫
          DerivedCategory.Q.map
            ((ChainComplex.single₀ (ModuleCat.{u} A) ⋙
              ComplexShape.embeddingDownNat.extendFunctor _).map
                (NoetherianAdicCompletion.quotientFactor hle)) = _
    rw [← DerivedCategory.Q.map_comp, ← hnat, DerivedCategory.Q.map_comp]
    change _ ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
        (NoetherianAdicCompletion.quotientFactor hle) ≫ _ = _
    rw [← Category.assoc, ← Functor.map_comp, hmkQ]
    rfl
  simp only [NoetherianAdicCompletion.derivedReductionMap, NatTrans.comp_app,
    Functor.flip_map_app, Functor.comp_map, Category.assoc]
  rw [← Functor.map_comp, hq]

/-- The map `Hⁱ(K) ⟶ Hⁱ(K ⊗ᴸ[A] A/Iⁿ⁺¹)` induced by the reduction map. -/
abbrev homologyDerivedReductionMap (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K ⟶
      (((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ⟨n⟩) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
    ((NoetherianAdicCompletion.derivedReductionMap I T n).app K)

/-- The `n`-th component of the canonical comparison: evaluate at level `n + 1` and apply the map
`Hⁱ(K)/Iⁿ⁺¹Hⁱ(K) ⟶ Hⁱ(K ⊗ᴸ[A] A/Iⁿ⁺¹)` induced by the reduction map. -/
def adicCompletionToDerivedReduction (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (n : ℕ) :
    ModuleCat.of A (AdicCompletion I ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K))
      ⟶ (((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ⟨n⟩) :=
  ModuleCat.ofHom <|
    (Submodule.liftQ _ (homologyDerivedReductionMap I T K i n).hom (by
      rw [Submodule.smul_le]
      intro r hr m _
      rw [LinearMap.mem_ker, map_smul]
      exact smul_eq_zero_homology_derivedReduction I T K i n hr _)) ∘ₗ
    AdicCompletion.eval I _ (n + 1)

/-- On the image of `Hⁱ(K)`, the `n`-th component is `Hⁱ` of the reduction map. -/
theorem adicCompletionToDerivedReduction_of (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (n : ℕ)
    (m : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) :
    adicCompletionToDerivedReduction I T K i n (AdicCompletion.of I _ m) =
      homologyDerivedReductionMap I T K i n m := by
  rfl

/-- The components `adicCompletionToDerivedReduction` are compatible with the transition maps. -/
theorem adicCompletionToDerivedReduction_comp_map_succ (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (n : ℕ) :
    adicCompletionToDerivedReduction I T K i (n + 1) ≫
        ((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map (homOfLE (Nat.le_succ n)).op =
      adicCompletionToDerivedReduction I T K i n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨m, hm⟩ := Submodule.mkQ_surjective _ (AdicCompletion.eval I _ (n + 1 + 1) x)
  have hm' : AdicCompletion.eval I _ (n + 1) x = Submodule.mkQ _ m := by
    rw [AdicCompletion.eval_apply,
      ← AdicCompletion.transitionMap_comp_eval_apply I _ (Nat.le_succ (n + 1)) x,
      ← AdicCompletion.eval_apply, ← hm]
    rfl
  have h := congrArg (fun f ↦ f m) (congrArg ModuleCat.Hom.hom
    (congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (derivedReductionMap_app_comp_map_succ I T K n)))
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  simp only [adicCompletionToDerivedReduction, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.comp_apply, ← hm, hm', Submodule.mkQ_apply, Submodule.liftQ_apply]
  exact h

/-- The cone on the tower `n ↦ Hⁱ(K ⊗ᴸ[A] A/Iⁿ⁺¹)` with vertex `Hⁱ(K)^∧` given by the
components `adicCompletionToDerivedReduction`. -/
def adicCompletionDerivedReductionCone (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    Cone ((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) where
  pt := ModuleCat.of A
    (AdicCompletion I ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K))
  π := NatTrans.ofOpSequence (fun n ↦ adicCompletionToDerivedReduction I T K i n) (fun n ↦ by
    rw [Functor.const_obj_map]
    exact (Category.id_comp _).trans
      (adicCompletionToDerivedReduction_comp_map_succ I T K i n).symm)

/-- **The canonical comparison `Hⁱ(K)^∧ ⟶ lim Hⁱ(K ⊗ᴸ[A] A/Iⁿ⁺¹)`**, induced by the reduction maps
`K ⟶ K ⊗ᴸ[A] A/Iⁿ⁺¹` (see `of_comp_adicCompletionToLimitDerivedReduction_π`). -/
def adicCompletionToLimitDerivedReduction (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    ModuleCat.of A
        (AdicCompletion I ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) ⟶
      limit ((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) :=
  limit.lift _ (adicCompletionDerivedReductionCone I T K i)

/-- **The canonical comparison is induced by the reduction maps.** Restricted along the completion
map `Hⁱ(K) ⟶ Hⁱ(K)^∧` and followed by the projection to level `n`, the comparison is `Hⁱ` of the
reduction map `K ⟶ K ⊗ᴸ[A] A/Iⁿ⁺¹`. -/
theorem of_comp_adicCompletionToLimitDerivedReduction_π (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (n : ℕ) :
    ModuleCat.ofHom (AdicCompletion.of I _) ≫ adicCompletionToLimitDerivedReduction I T K i ≫
        limit.π ((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) ⟨n⟩ =
      homologyDerivedReductionMap I T K i n := by
  refine (congrArg (ModuleCat.ofHom (AdicCompletion.of I _) ≫ ·)
    (limit.lift_π (adicCompletionDerivedReductionCone I T K i) ⟨n⟩)).trans ?_
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  exact adicCompletionToDerivedReduction_of I T K i n m

/-! ### Stacks 0922 with pinned projections, over `A` and for an arbitrary tensor product -/

/-- The tower `n ↦ (A/Iⁿ⁺¹)[0]`, lifted along the universe enlargement, is the tower
`n ↦ (B/Jⁿ⁺¹)[0]` over `B = ULift A`, compatibly with the quotient maps out of the unit up to a
fixed identification of the units. -/
private theorem exists_idealPowerQuotientSystem_uliftIso (I : Ideal A) :
    ∃ (eQ : NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
          AdicKoszul.derivedUniverseLift.{u, u} A ≅
        NoetherianAdicCompletion.idealPowerQuotientSystem
          (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom))
      (s : (AdicKoszul.derivedUniverseLift.{u, u} A).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} (ULift.{u} A)) 0).obj
          (ModuleCat.of (ULift.{u} A) (ULift.{u} A))),
      ∀ n : ℕ, (AdicKoszul.derivedUniverseLift.{u, u} A).map
          (NoetherianAdicCompletion.idealPowerQuotientMap I n) ≫ eQ.hom.app ⟨n⟩ =
        s.hom ≫ NoetherianAdicCompletion.idealPowerQuotientMap
          (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom) n := by
  let B := ULift.{u} A
  let J : Ideal B := I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom
  let V := AdicKoszul.moduleUniverseLift.{u, u} A
  let U := AdicKoszul.derivedUniverseLift.{u, u} A
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let S' := DerivedCategory.singleFunctor (ModuleCat.{u} B) 0
  let X := AdicCompletionTor.idealPowerQuotientModuleSystem I
  let Y := AdicCompletionTor.idealPowerQuotientModuleSystem J
  -- the quotient rings agree
  let q : ∀ n : ℕ, A ⧸ I ^ (n + 1) ≃+* B ⧸ J ^ (n + 1) := fun n ↦
    Ideal.quotientEquiv (I ^ (n + 1)) (J ^ (n + 1)) (ULift.ringEquiv.symm : A ≃+* B) (by
      rw [Ideal.map_pow, Ideal.map_comap_of_equiv]
      rfl)
  let f : ∀ n : ℕ, V.obj (ModuleCat.of A (A ⧸ I ^ (n + 1))) ⟶ ModuleCat.of B (B ⧸ J ^ (n + 1)) :=
    fun n ↦ ModuleCat.ofHom
      { toFun := fun x ↦ q n x.down
        map_add' := fun x y ↦ (q n).map_add x.down y.down
        map_smul' := fun r x ↦ by
          change q n ((Ideal.Quotient.mk (I ^ (n + 1)) r.down) * x.down) =
            (Ideal.Quotient.mk (J ^ (n + 1)) r) * q n x.down
          rw [(q n).map_mul]
          rfl }
  have hf : ∀ n, IsIso (f n) := fun n ↦
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨fun _ _ h ↦ congrArg ULift.up ((q n).injective h),
        fun y ↦ ⟨ULift.up ((q n).symm y), (q n).apply_symm_apply y⟩⟩
  let α : X ⋙ V ⟶ Y := NatTrans.ofOpSequence f (fun n ↦ by
    simp only [Functor.comp_map, X, Y, AdicCompletionTor.idealPowerQuotientModuleSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x⟩
    induction x using Quotient.inductionOn with
    | _ a => rfl)
  have : IsIso α := by
    have : ∀ n : ℕᵒᵖ, IsIso (α.app n) := fun n ↦ hf n.unop
    exact NatIso.isIso_of_isIso_app α
  let modIso : X ⋙ V ≅ Y := asIso α
  let s₀ : V.obj (ModuleCat.of A A) ≅ ModuleCat.of B B :=
    { hom := ModuleCat.ofHom
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      inv := ModuleCat.ofHom
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl } }
  have hmod : ∀ n : ℕ, V.map (ModuleCat.ofHom (I ^ (n + 1)).mkQ) ≫ modIso.hom.app ⟨n⟩ =
      s₀.hom ≫ ModuleCat.ofHom (J ^ (n + 1)).mkQ := fun n ↦ by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨a⟩
    rfl
  let ε : S ⋙ U ≅ V ⋙ S' := V.mapDerivedCategorySingleFunctor 0
  let eQ : NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ U ≅
      NoetherianAdicCompletion.idealPowerQuotientSystem J :=
    Functor.isoWhiskerRight (NoetherianAdicCompletion.idealPowerQuotientSystemIso I) U ≪≫
      Functor.associator X S U ≪≫ Functor.isoWhiskerLeft X ε ≪≫
      (Functor.associator X V S').symm ≪≫ Functor.isoWhiskerRight modIso S' ≪≫
      (NoetherianAdicCompletion.idealPowerQuotientSystemIso J).symm
  refine ⟨eQ, ε.app (ModuleCat.of A A) ≪≫ S'.mapIso s₀, fun n ↦ ?_⟩
  have h₁ := NoetherianAdicCompletion.idealPowerQuotientMap_comp_idealPowerQuotientSystemIso_hom
    I n
  have h₂ := NoetherianAdicCompletion.idealPowerQuotientMap_comp_idealPowerQuotientSystemIso_hom
    J n
  have h₃ := ε.hom.naturality (ModuleCat.ofHom (I ^ (n + 1)).mkQ)
  simp only [eQ, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Iso.symm_hom, Category.id_comp,
    Iso.app_hom, Functor.mapIso_hom]
  rw [← Functor.map_comp_assoc, h₁]
  have h₃' : U.map (S.map (ModuleCat.ofHom (I ^ (n + 1)).mkQ)) ≫ ε.hom.app (X.obj ⟨n⟩) =
      ε.hom.app (ModuleCat.of A A) ≫ S'.map (V.map (ModuleCat.ofHom (I ^ (n + 1)).mkQ)) := h₃
  refine (congrArg (U.map (S.map (ModuleCat.ofHom (I ^ (n + 1)).mkQ)) ≫ ·)
    (Category.id_comp _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ S'.map (modIso.hom.app ⟨n⟩) ≫
    (NoetherianAdicCompletion.idealPowerQuotientSystemIso J).inv.app ⟨n⟩) h₃').trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (ε.hom.app (ModuleCat.of A A) ≫ ·) ?_
  refine (S'.map_comp_assoc _ _ _).symm.trans ?_
  refine (congrArg (fun g ↦ S'.map g ≫
    (NoetherianAdicCompletion.idealPowerQuotientSystemIso J).inv.app ⟨n⟩) (hmod n)).trans ?_
  refine (S'.map_comp_assoc _ _ _).trans ?_
  refine congrArg (S'.map s₀.hom ≫ ·) ?_
  exact (Iso.comp_inv_eq ((NoetherianAdicCompletion.idealPowerQuotientSystemIso J).app ⟨n⟩)).2
    h₂.symm

/-- **Stacks 0922 with pinned projections, for an arbitrary derived tensor product over `A`.**
There is a reflection `L` of `D(A)` onto the derived `I`-complete objects and maps
`p n : K^∧ ⟶ K ⊗ᴸ[A] A/Iⁿ⁺¹` presenting `K^∧` as a derived limit of the reduction tower, whose
composites with the unit are the reduction maps. -/
theorem exists_isDerivedLimitWithProjections_unit_comp_eq_derivedReductionMap
    [IsNoetherianRing A] (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) := fun K ↦ IsDerivedComplete I K
    ∃ (L : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory) (adj : L ⊣ P.ι)
      (p : ∀ n : ℕ, (L ⋙ P.ι).obj K ⟶
        (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K).obj ⟨n⟩),
      NoetherianAdicCompletion.IsDerivedLimitWithProjections
          (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K)
          ((L ⋙ P.ι).obj K) p ∧
        ∀ n : ℕ, adj.unit.app K ≫ p n =
          (NoetherianAdicCompletion.derivedReductionMap I T n).app K := by
  classical
  intro P
  let B := ULift.{u} A
  let J : Ideal B := I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom
  let U := AdicKoszul.derivedUniverseLift.{u, u} A
  let TB := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct B
  let ι := P.ι
  let : (ModuleCat.uliftFunctor.{u, u} A).IsEquivalence :=
    Functor.isEquivalence_of_iso (NatIso.ofComponents (fun M =>
      { hom := ModuleCat.ofHom (ULift.moduleEquiv (R := A) (M := M)).toLinearMap
        inv := ModuleCat.ofHom (ULift.moduleEquiv (R := A) (M := M)).symm.toLinearMap })
      (fun _ => rfl) : ModuleCat.uliftFunctor.{u, u} A ≅ 𝟭 (ModuleCat.{u} A)).symm
  let : (ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom).IsEquivalence := by
    change (StacksDraft.DerivedHom.uliftModuleEquivalence.{u, u, u} A).inverse.IsEquivalence
    infer_instance
  let : (AdicKoszul.moduleUniverseLift.{u, u} A).IsEquivalence := by
    change (ModuleCat.uliftFunctor.{u, u} A ⋙ ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom).IsEquivalence
    infer_instance
  let : U.IsEquivalence :=
    Stacks.Injectives.mapDerivedCategory_isEquivalence (AdicKoszul.moduleUniverseLift.{u, u} A)
  obtain ⟨τ⟩ := AdicCompletionTor.nonempty_tensorUliftFunctorIso A T K
  obtain ⟨L, adj, π, hlim, hunit⟩ :=
    NoetherianAdicCompletion.idealPowerDerivedLimit_isLeftAdjoint.{u, u} A I TB
  obtain ⟨eQ, s, hs⟩ := exists_idealPowerQuotientSystem_uliftIso I
  let QA := NoetherianAdicCompletion.idealPowerQuotientSystem I
  let QB := NoetherianAdicCompletion.idealPowerQuotientSystem J
  let A₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let e : (QA ⋙ T.tensor.obj K) ⋙ U ≅ QB ⋙ TB.tensor.obj (U.obj K) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft QA τ ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eQ (TB.tensor.obj (U.obj K))
  have he : ∀ n : ℕ, e.hom.app ⟨n⟩ =
      τ.hom.app (QA.obj ⟨n⟩) ≫ (TB.tensor.obj (U.obj K)).map (eQ.hom.app ⟨n⟩) := fun n ↦ by
    simp only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    exact (Category.id_comp _).trans (congrArg (τ.hom.app (QA.obj ⟨n⟩) ≫ ·) (Category.id_comp _))
  let ζ : U.obj K ≅ U.obj K :=
    U.mapIso (T.rightUnitor.app K).symm ≪≫ τ.app A₀ ≪≫ (TB.tensor.obj (U.obj K)).mapIso s ≪≫
      TB.rightUnitor.app (U.obj K)
  have hζ : ∀ n : ℕ, U.map ((NoetherianAdicCompletion.derivedReductionMap I T n).app K) ≫
      e.hom.app ⟨n⟩ =
        ζ.hom ≫ (NoetherianAdicCompletion.derivedReductionMap J TB n).app (U.obj K) := fun n ↦ by
    have hτ := τ.hom.naturality (NoetherianAdicCompletion.idealPowerQuotientMap I n)
    simp only [Functor.comp_map] at hτ
    simp only [NoetherianAdicCompletion.derivedReductionMap, NatTrans.comp_app,
      Functor.flip_map_app, he, ζ, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
      Iso.app_hom, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hτ, ← Functor.map_comp, hs n, Functor.map_comp,
      Iso.hom_inv_id_app_assoc]
  let ζ₀ : K ≅ K := U.preimageIso ζ
  let p : ∀ n : ℕ, (L ⋙ ι).obj K ⟶ (QA ⋙ T.tensor.obj K).obj ⟨n⟩ := fun n ↦
    U.preimage ((π n).app K ≫ e.inv.app ⟨n⟩)
  have hp : NoetherianAdicCompletion.IsDerivedLimitWithProjections (QA ⋙ T.tensor.obj K)
      ((L ⋙ ι).obj K) p := by
    refine NoetherianAdicCompletion.isDerivedLimitWithProjections_of_map_of_equivalence U
      (QA ⋙ T.tensor.obj K) _ p ?_
    have heq : (fun n : ℕ ↦ U.map (p n)) = fun n : ℕ ↦ (π n).app K ≫ e.inv.app ⟨n⟩ := by
      funext n
      exact U.map_preimage _
    rw [heq]
    exact (hlim K).ofNatIso e.symm
  refine ⟨L, adj, fun n ↦ (L ⋙ ι).map ζ₀.hom ≫ p n, hp.ofIso ((L ⋙ ι).mapIso ζ₀).symm,
    fun n ↦ ?_⟩
  have hnat : ζ₀.hom ≫ adj.unit.app K = adj.unit.app K ≫ (L ⋙ ι).map ζ₀.hom :=
    adj.unit.naturality ζ₀.hom
  change adj.unit.app K ≫ (L ⋙ ι).map ζ₀.hom ≫ p n = _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ p n) hnat.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  apply U.map_injective
  have h₁ : U.map (ζ₀.hom ≫ adj.unit.app K ≫ p n) =
      ζ.hom ≫ U.map (adj.unit.app K) ≫ (π n).app K ≫ e.inv.app ⟨n⟩ := by
    simp only [Functor.map_comp, ζ₀, p, Functor.preimageIso_hom, Functor.map_preimage]
  have h₂ : U.map ((NoetherianAdicCompletion.derivedReductionMap I T n).app K) =
      ζ.hom ≫ U.map (adj.unit.app K) ≫ (π n).app K ≫ e.inv.app ⟨n⟩ := by
    rw [← Category.assoc (U.map (adj.unit.app K)), hunit K n, ← Category.assoc, ← hζ n,
      Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  exact h₁.trans h₂.symm

/-! ### Stacks 0EGS and 0EGV -/

/-- **Stacks 0EGS (Kollár--Kovács), canonical form.** Let `I` be an ideal of a Noetherian ring
`A` and `K ∈ D(A)`, and set `Kₙ = K ⊗ᴸ[A] A/Iⁿ⁺¹`. Suppose that every cohomology module `Hⁱ(K)` is
finite and that, in every degree, the inverse system `Hⁱ(Kₙ)` is Mittag--Leffler. Then for every
`i` the canonical map `lim Hⁱ(K)/IⁿHⁱ(K) ⟶ lim Hⁱ(Kₙ)`, induced by the reduction maps
`K ⟶ Kₙ` (`adicCompletionToLimitDerivedReduction`), is an isomorphism. -/
@[stacks 0EGS]
theorem isIso_adicCompletionToLimitDerivedReduction
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (hK : ∀ i : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (hML : ∀ i : ℤ,
      (((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) ⋙
        forget (ModuleCat.{u} A)).IsMittagLeffler) :
    ∀ i : ℤ, IsIso (adicCompletionToLimitDerivedReduction I T K i) := by
  intro i
  have hI : I.FG := I.fg_of_isNoetherianRing
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
  let F := (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙ H
  let M := H.obj K
  have : Module.Finite A M := hK i
  let c := adicCompletionToLimitDerivedReduction I T K i
  -- the abstract identification of the non-canonical form of Stacks 0EGS
  obtain ⟨θ₀⟩ :=
    Stacks.InverseSystem.AdicCompletionCohomology.adicCompletion_homology_iso_limit_derivedReduction
      A I K T hK hML i
  let θ : (limit F : ModuleCat.{u} A) ≃ₗ[A] AdicCompletion I M := θ₀.symm.toLinearEquiv
  -- the pinned derived-limit presentation of the derived completion
  obtain ⟨L, adj, p, hp, hunit⟩ :=
    exists_isDerivedLimitWithProjections_unit_comp_eq_derivedReductionMap I T K
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) := fun K ↦ IsDerivedComplete I K
  let ι := P.ι
  have hML' : IsMittagLefflerCategorical
      ((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i - 1)) :=
    isMittagLefflerCategorical_of_isMittagLeffler_forget _ (hML (i - 1))
  obtain ⟨q, hq, hqπ⟩ :=
    NoetherianAdicCompletion.IsDerivedLimitWithProjections.exists_isIso_comp_limit_π
      A _ _ p hp i hML'
  -- the completion map followed by `c` is the unit followed by the Milnor comparison
  let a : M ⟶ limit F := ModuleCat.ofHom (AdicCompletion.of I M) ≫ c
  have ha : a = H.map (adj.unit.app K) ≫ q := by
    refine limit.hom_ext fun n ↦ ?_
    induction n using Opposite.rec with
    | op n =>
      simp only [Category.assoc]
      rw [hqπ n, ← H.map_comp, hunit n]
      exact of_comp_adicCompletionToLimitDerivedReduction_π I T K i n
  -- density of the unit modulo `I`, transported from the named derived completion
  have hdense₀ := Stacks.Algebraization.range_homologyMap_adicCompletionUnit_sup_smul_eq_top_degree
    A I hI K hK i
  let adj' := Stacks.Algebraization.adicCompletionAdjunction A I hI
  let ψ := (Adjunction.leftAdjointUniq adj adj').app K
  have hψ : adj.unit.app K ≫ ι.map ψ.hom = adj'.unit.app K :=
    Adjunction.unit_leftAdjointUniq_hom_app adj adj' K
  have h₁ : adj'.unit.app K ≫ ι.map ψ.inv = adj.unit.app K := by
    rw [← hψ, Category.assoc, ← ι.map_comp, ψ.hom_inv_id, ι.map_id]
    exact Category.comp_id _
  have hkey : H.map (adj'.unit.app K) ≫ H.map (ι.map ψ.inv) = H.map (adj.unit.app K) :=
    (H.map_comp _ _).symm.trans (congrArg H.map h₁)
  have hdense₁ : LinearMap.range (H.map (adj.unit.app K)).hom ⊔
      I • (⊤ : Submodule A (H.obj ((L ⋙ ι).obj K))) = ⊤ :=
    Stacks.Algebraization.range_sup_smul_eq_top_of_linearEquiv I _ _
      (LinearEquiv.refl A M) (H.mapIso (ι.mapIso ψ)).symm.toLinearEquiv
      (fun m ↦ ConcreteCategory.congr_hom hkey m) hdense₀
  have hdense : LinearMap.range a.hom ⊔ I • (⊤ : Submodule A (limit F : ModuleCat.{u} A)) = ⊤ := by
    refine Stacks.Algebraization.range_sup_smul_eq_top_of_linearEquiv I _ _
      (LinearEquiv.refl A M) (asIso q).toLinearEquiv (fun m ↦ ?_) hdense₁
    rw [ha]
    rfl
  have hbij : Function.Bijective c.hom :=
    Stacks.Algebraization.bijective_of_isAdicComplete_of_range_sup_eq_top I θ a.hom c.hom
      (fun _ ↦ rfl) hdense
  exact (ConcreteCategory.isIso_iff_bijective c).2 hbij

/-- **Stacks 0EGV (Kollár--Kovács), canonical form.** Let `I` be an ideal of a Noetherian ring
`A` and `K` a pseudo-coherent object of `D(A)`, and set `Kₙ = K ⊗ᴸ[A] A/Iⁿ⁺¹`. Then for every `i`
the inverse system `Hⁱ(Kₙ)` is Mittag--Leffler, and the canonical map
`lim Hⁱ(K)/IⁿHⁱ(K) ⟶ lim Hⁱ(Kₙ)`, induced by the reduction maps `K ⟶ Kₙ`
(`adicCompletionToLimitDerivedReduction`), is an isomorphism. -/
@[stacks 0EGV]
theorem pseudoCoherent_mittagLeffler_and_isIso_adicCompletionToLimitDerivedReduction
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    ∀ i : ℤ,
      (((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) ⋙
        forget (ModuleCat.{u} A)).IsMittagLeffler ∧
      IsIso (adicCompletionToLimitDerivedReduction I T K i) := by
  have hML := fun i ↦
    (pseudoCoherent_mittagLeffler_and_adicCompletion_iso_limit_derivedReduction A I K T hK i).1
  have hfin : ∀ i : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) :=
    fun i ↦ (((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      K i A).2.1).mp hK).2 i
  exact fun i ↦ ⟨hML i, isIso_adicCompletionToLimitDerivedReduction A I K T hfin hML i⟩

end Stacks.PseudoCoherent.AdicCompletion

end
