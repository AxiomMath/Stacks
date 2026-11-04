module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.CosimplicialCartesian
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.CechCosimplicialModule
public import StacksFrontier.AlgebraicGeometry.Descent.Module.TransitionSplitEqualizer

/-!
# Descent data are cartesian modules over the Čech algebra

Let `R → A` be a ring map.  A descent datum `(N, φ)` for `A / R` gives a cosimplicial module
over the Čech algebra `(A / R)_•` (Stacks 023H), which is cartesian
(`ModuleCat.cartesian_descentCosimplicialModuleFunctor_obj`).  This file proves that the resulting
functor `ModuleCat.descentCartesianModuleFunctor` from descent data to cartesian
`(A / R)_•`-modules is an equivalence of categories: **descent data for `A / R` correspond to
cartesian `(A / R)_•`-modules**, which is step (2) of Stacks 039Y.

## Main definitions

* `ModuleCat.cechDegOneRingEquiv`: `(A / R)_1 ≅ A ⊗_R A`, and `ModuleCat.cechDegTwoToTensor`, the
  ring map `(A / R)_2 → (A ⊗_R A) ⊗_R A`, both sending the coprojections to the tensor
  inclusions.
* `ModuleCat.tensorToModule`: the map `C ⊗_R M₀ → X`, `c ⊗ x ↦ ℓ'(c) • ι(x)`, attached to a
  semilinear map `ι : M₀ → X` whose transpose is bijective.
* `ModuleCat.descentDataOfCartesian`: the descent datum of a cartesian `(A / R)_•`-module `M`,
  with module `M_0` and transition the composite of the two cartesian isomorphisms
  `M_0 ⊗_R A ≅ M_1 ≅ A ⊗_R M_0`; `ModuleCat.cartesianDescentDataFunctor` is the functor.
* `ModuleCat.descentUnit`: a descent datum maps isomorphically to the descent datum of its
  cosimplicial module.
* `ModuleCat.descentDataEquivCartesianCechModule`: the equivalence between descent data for
  `A / R` and cartesian `(A / R)_•`-modules.

## Main results

* `ModuleCat.injective_tensorToModule` and `ModuleCat.bijective_tensorToModule`: the criterion by
  which the cartesian isomorphisms of `M` are compared with the tensor products of a descent
  datum.
* `ModuleCat.DescentData.isIso_of_bijective`: a morphism of descent data with bijective
  underlying map is an isomorphism.

## Implementation notes

The Čech algebra `(A / R)_n` is an abstract wide pushout.  Only two facts about it are used in
degrees `1` and `2`: ring maps out of it into the tensor powers of `A` over `R`, determined by
their values on the coprojections, and the generation of `(A / R)_1` by products of coprojections
(`Stacks.Descent.cechDegOneIso`).  Through them, the two maps
`A ⊗_R M_0 → M_1`, `a ⊗ y ↦ a • M(δ⁰) y`, and `M_0 ⊗_R A → M_1`, `y ⊗ b ↦ b • M(δ¹) y`, are
bijective for a cartesian `M`, and the transition of the descent datum of `M` is read off from
them.  Morphisms are compared in degree zero, by
`Stacks.PresheafOfModules.hom_ext_of_cartesian_app_zero` and
`Stacks.PresheafOfModules.homOfDegreeZero`.

## References

* [Stacks Project, Tag 039Y](https://stacks.math.columbia.edu/tag/039Y)
* [Stacks Project, Tag 023H](https://stacks.math.columbia.edu/tag/023H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct Simplicial
open scoped ChangeOfRings

universe u w

namespace ModuleCat

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

section Rings

/-- **`(A / R)_1 ≅ A ⊗_R A`**, as rings, the coprojections going to the two tensor inclusions. -/
noncomputable def cechDegOneRingEquiv : (cechCosimplicialAlgebra R A).obj ⦋1⦌ ≃+* A ⊗[R] A :=
  let := ULift.algebra' R (ULift.{u} A)
  (CommAlgCat.algEquivOfIso (cechAlgebraDegOneIso R A)).toRingEquiv.trans
    ((Algebra.TensorProduct.uliftEquiv.{u} R R A A).symm.toRingEquiv.trans ULift.ringEquiv)

/-- `cechDegOneRingEquiv` sends the coprojection `ℓ₀(a)` to `a ⊗ 1`. -/
theorem cechDegOneRingEquiv_leg_zero (a : ULift.{u} A) :
    cechDegOneRingEquiv R A (cechLeg R A ⦋1⦌ 0 a) = a.down ⊗ₜ[R] (1 : A) := by
  let := ULift.algebra' R (ULift.{u} A)
  have h := congrArg (fun φ => (CommAlgCat.Hom.hom φ) a)
    (Stacks.Descent.cechι_zero_comp_cechDegOneFwd (ULift.{u} R) (ULift.{u} A))
  exact congrArg (fun t => ((Algebra.TensorProduct.uliftEquiv.{u} R R A A).symm t).down) h

/-- `cechDegOneRingEquiv` sends the coprojection `ℓ₁(a)` to `1 ⊗ a`. -/
theorem cechDegOneRingEquiv_leg_one (a : ULift.{u} A) :
    cechDegOneRingEquiv R A (cechLeg R A ⦋1⦌ 1 a) = (1 : A) ⊗ₜ[R] a.down := by
  let := ULift.algebra' R (ULift.{u} A)
  have h := congrArg (fun φ => (CommAlgCat.Hom.hom φ) a)
    (Stacks.Descent.cechι_one_comp_cechDegOneFwd (ULift.{u} R) (ULift.{u} A))
  exact congrArg (fun t => ((Algebra.TensorProduct.uliftEquiv.{u} R R A A).symm t).down) h

/-- An `R`-algebra map out of `A`, read as a `ULift R`-algebra map out of `ULift A`. -/
noncomputable def uliftAlgHom {X : Type u} [CommRing X] [Algebra R X] (f : A →ₐ[R] X) :
    @AlgHom (ULift.{u} R) (ULift.{u} A) X _ _ _ (ULift.algebra' R (ULift.{u} A))
      (ULift.algebra' R X) :=
  let := ULift.algebra' R (ULift.{u} A)
  let := ULift.algebra' R X
  { toRingHom := f.toRingHom.comp ULift.ringEquiv.toRingHom
    commutes' := fun r => by
      change f (algebraMap R A r.down) = algebraMap R X r.down
      exact f.commutes r.down }

/-- The commutative `ULift R`-algebra underlying an `R`-algebra. -/
noncomputable abbrev uliftAlgObj (X : Type u) [CommRing X] [Algebra R X] :
    CommAlgCat.{u} (ULift.{u} R) :=
  let := ULift.algebra' R X
  CommAlgCat.of (ULift.{u} R) X

/-- The morphism out of the degree-`n` Čech algebra determined by `n + 1` algebra maps out of
`A`. -/
noncomputable def cechDescHom (n : SimplexCategory) {X : Type u} [CommRing X] [Algebra R X]
    (f : Fin (n.len + 1) → (A →ₐ[R] X)) :
    (cechCosimplicialAlgebra R A).obj n ⟶ uliftAlgObj R X :=
  let := ULift.algebra' R (ULift.{u} A)
  let := ULift.algebra' R X
  WidePushout.desc (arrows := Arrow.cechLegs (AlgebraicTopology.algebraMapArrow R A) n)
      (X := uliftAlgObj R X) (CommAlgCat.ofHom (Algebra.ofId _ _))
      (fun i => CommAlgCat.ofHom (uliftAlgHom R A (f i)))
      (fun _ => Stacks.Descent.algebraArrow_left_hom_ext (ULift.{u} R) (ULift.{u} A) _ _)

/-- The ring map out of the degree-`n` Čech algebra determined by `n + 1` algebra maps out of
`A`. -/
noncomputable def cechDesc (n : SimplexCategory) {X : Type u} [CommRing X] [Algebra R X]
    (f : Fin (n.len + 1) → (A →ₐ[R] X)) :
    (cechCosimplicialAlgebra R A).obj n →+* X :=
  letI := ULift.algebra' R (ULift.{u} A)
  let := ULift.algebra' R X
  (cechDescHom R A n f).hom.toRingHom

/-- `cechDesc R A n f` sends the `i`-th coprojection of `a` to `f i a`. -/
theorem cechDesc_cechLeg (n : SimplexCategory) {X : Type u} [CommRing X] [Algebra R X]
    (f : Fin (n.len + 1) → (A →ₐ[R] X)) (i : Fin (n.len + 1)) (a : ULift.{u} A) :
    cechDesc R A n f (cechLeg R A n i a) = f i a.down := by
  let := ULift.algebra' R (ULift.{u} A)
  let := ULift.algebra' R X
  have h := congrArg (fun φ : _ ⟶ uliftAlgObj R X => φ.hom a)
    (WidePushout.ι_desc (arrows := Arrow.cechLegs (AlgebraicTopology.algebraMapArrow R A) n)
      (X := uliftAlgObj R X) (CommAlgCat.ofHom (Algebra.ofId _ _))
      (fun i => CommAlgCat.ofHom (uliftAlgHom R A (f i)))
      (fun _ => Stacks.Descent.algebraArrow_left_hom_ext (ULift.{u} R) (ULift.{u} A) _ _) i)
  simp only [CommAlgCat.hom_comp, AlgHom.coe_comp] at h
  exact h

/-- The ring map `(A / R)_2 → (A ⊗_R A) ⊗_R A` sending the three coprojections to the three
tensor inclusions. -/
noncomputable abbrev cechDegTwoToTensor :
    (cechCosimplicialAlgebra R A).obj ⦋2⦌ →+* (A ⊗[R] A) ⊗[R] A :=
  cechDesc R A ⦋2⦌ ![Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeLeft,
    Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeRight,
    Algebra.TensorProduct.includeRight]

end Rings


section Bijectivity

/-! ### A bijectivity criterion

Let `S` be generated, as a pushout of rings, by `ℓ' : C → S` and `ℓ = d ∘ e : A → S`, in the sense
that `S ≅ C ⊗_R A` compatibly.  If `X` is an `S`-module with a `d`-semilinear map `ι : M₀ → X`
whose transpose `S ⊗_{S₀} M₀ → X` is bijective, then `C ⊗_R M₀ → X`, `c ⊗ x ↦ ℓ'(c) • ι(x)`, is
bijective. -/

variable {R A}
variable {C S₀ S : Type u} [CommRing C] [Algebra R C] [CommRing S₀] [CommRing S]

/-- The transpose of a semilinear map, on a pure tensor. -/
theorem homEquiv_symm_tmul (d : S₀ →+* S) {M₀ : ModuleCat.{max u w} S₀}
    {X : ModuleCat.{max u w} S} (ι : M₀ ⟶ (ModuleCat.restrictScalars d).obj X) (s : S)
    (x : M₀) :
    ((ModuleCat.extendRestrictScalarsAdj d).homEquiv _ _).symm ι (s ⊗ₜ[S₀, d] x) = s • ι x := by
  have hone : ((ModuleCat.extendRestrictScalarsAdj d).homEquiv _ _).symm ι
      ((1 : S) ⊗ₜ[S₀, d] x) = ι x :=
    congrArg (fun a => a x)
      (((ModuleCat.extendRestrictScalarsAdj d).homEquiv M₀ X).apply_symm_apply ι)
  have hsm := (((ModuleCat.extendRestrictScalarsAdj d).homEquiv _ _).symm ι).hom.map_smul s
    ((1 : S) ⊗ₜ[S₀, d] x)
  exact (congrArg (fun c => ((ModuleCat.extendRestrictScalarsAdj d).homEquiv _ _).symm ι
      (c ⊗ₜ[S₀, d] x)) (mul_one s).symm).trans (hsm.trans (congrArg (fun z => s • z) hone))

variable (e : A ≃+* S₀) (d : S₀ →+* S) (ℓ' : C →+* S)
  (hR : ∀ r : R, ℓ' (algebraMap R C r) = d (e (algebraMap R A r)))
  {M₀ : ModuleCat.{max u w} S₀} {X : ModuleCat.{max u w} S}
  (ι : M₀ ⟶ (ModuleCat.restrictScalars d).obj X)

/-- The `A`-module underlying `M₀`. -/
noncomputable abbrev restrictAlong (M₀ : ModuleCat.{max u w} S₀) : ModuleCat.{max u w} A :=
  (ModuleCat.restrictScalars e.toRingHom).obj M₀

/-- `ι` as an additive map `M₀ → X`. -/
noncomputable def semilinearX : M₀ →+ X where
  toFun x := ι.hom x
  map_zero' := ι.hom.map_zero
  map_add' := ι.hom.map_add

/-- `semilinearX d ι` is `d`-semilinear: `ι(t • x) = d(t) • ι(x)`. -/
theorem semilinearX_smul (t : S₀) (x : M₀) : semilinearX d ι (t • x) = d t • semilinearX d ι x :=
  ι.hom.map_smul t x

/-- `x ↦ ℓ'(c) • ι(x)`, as an additive map out of the `R`-module underlying `M₀`. -/
noncomputable def smulSemilinear (c : C) : restrictModule R A (restrictAlong e M₀) →+ X :=
  (DistribSMul.toAddMonoidHom X (ℓ' c)).comp (semilinearX d ι)

include hR in
/-- The map `C ⊗_R M₀ → X`, `c ⊗ x ↦ ℓ'(c) • ι(x)`. -/
noncomputable def tensorToModule :
    C ⊗[R] restrictModule R A (restrictAlong e M₀) →+ X :=
  TensorProduct.liftAddHom
    { toFun := fun c => smulSemilinear e d ℓ' ι c
      map_zero' := AddMonoidHom.ext fun x => by
        change ℓ' 0 • semilinearX d ι x = 0
        rw [map_zero, zero_smul]
      map_add' := fun c c' => AddMonoidHom.ext fun x => by
        change ℓ' (c + c') • semilinearX d ι x =
          ℓ' c • semilinearX d ι x + ℓ' c' • semilinearX d ι x
        rw [map_add, add_smul] }
    (fun r c x => by
      change ℓ' (r • c) • semilinearX d ι x =
        ℓ' c • semilinearX d ι (e (algebraMap R A r) • (show M₀ from x))
      rw [semilinearX_smul, Algebra.smul_def, map_mul,
        hR, mul_comm, mul_smul])

/-- `tensorToModule` on a pure tensor: `c ⊗ x ↦ ℓ'(c) • ι(x)`. -/
theorem tensorToModule_tmul (c : C) (x : restrictModule R A (restrictAlong e M₀)) :
    tensorToModule e d ℓ' hR ι (c ⊗ₜ[R] x) = ℓ' c • semilinearX d ι x :=
  rfl

/-- The additive map `(C ⊗_R A) × M₀ → C ⊗_R M₀`, `(c ⊗ a, x) ↦ c ⊗ a • x`. -/
noncomputable def tensorActAdd :
    C ⊗[R] A →+ M₀ →+ C ⊗[R] restrictModule R A (restrictAlong e M₀) :=
  TensorProduct.liftAddHom
    { toFun := fun c =>
        { toFun := fun a =>
            ((TensorProduct.mk R C (restrictModule R A (restrictAlong e M₀)) c).toAddMonoidHom.comp
              (DistribSMul.toAddMonoidHom M₀ (e a)) :
                M₀ →+ C ⊗[R] restrictModule R A (restrictAlong e M₀))
          map_zero' := AddMonoidHom.ext fun x => by
            change c ⊗ₜ[R] (show restrictModule R A (restrictAlong e M₀) from e 0 • x) = 0
            rw [map_zero, zero_smul]
            exact TensorProduct.tmul_zero _ _
          map_add' := fun a a' => AddMonoidHom.ext fun x => by
            change c ⊗ₜ[R] (show restrictModule R A (restrictAlong e M₀) from e (a + a') • x) =
              c ⊗ₜ[R] (show restrictModule R A (restrictAlong e M₀) from e a • x) +
                c ⊗ₜ[R] (show restrictModule R A (restrictAlong e M₀) from e a' • x)
            rw [map_add, add_smul]
            exact TensorProduct.tmul_add _ _ _ }
      map_zero' := by
        ext a x
        exact TensorProduct.zero_tmul _ _
      map_add' := fun c c' => by
        ext a x
        exact TensorProduct.add_tmul _ _ _ }
    (fun r c a => AddMonoidHom.ext fun x => by
      change (r • c) ⊗ₜ[R] (show restrictModule R A (restrictAlong e M₀) from e a • x) =
        c ⊗ₜ[R] (show restrictModule R A (restrictAlong e M₀) from e (r • a) • x)
      rw [TensorProduct.smul_tmul]
      congr 1
      change e (algebraMap R A r) • e a • x = e (r • a) • x
      rw [Algebra.smul_def, map_mul, mul_smul])

/-- `tensorActAdd` on a pure tensor: `(c ⊗ a, x) ↦ c ⊗ a • x`. -/
theorem tensorActAdd_tmul (c : C) (a : A) (x : M₀) :
    tensorActAdd e (c ⊗ₜ[R] a) x =
      c ⊗ₜ[R] (show restrictModule R A (restrictAlong e M₀) from e a • x) :=
  rfl

/-- Multiplying the first argument of `tensorActAdd` by `1 ⊗ a` is acting on the second by `a`. -/
theorem tensorActAdd_mul (a : A) (t : C ⊗[R] A) (x : M₀) :
    tensorActAdd e (((1 : C) ⊗ₜ[R] a) * t) x = tensorActAdd e t (e a • x) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [mul_zero, map_zero, AddMonoidHom.zero_apply]
  | tmul c b =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, tensorActAdd_tmul, tensorActAdd_tmul,
      map_mul, mul_comm, mul_smul]
  | add t t' ht ht' =>
    rw [mul_add, map_add, AddMonoidHom.add_apply, ht, ht', map_add, AddMonoidHom.add_apply]

variable (ν : S →+* C ⊗[R] A) (hν' : ∀ c, ν (ℓ' c) = c ⊗ₜ[R] (1 : A))
  (hν : ∀ a, ν (d (e a)) = (1 : C) ⊗ₜ[R] a)

include hν in
/-- The left inverse `S ⊗_{S₀} M₀ → C ⊗_R M₀` of `ModuleCat.tensorToModule`, before the
identification `S ⊗_{S₀} M₀ ≅ X`. -/
noncomputable def tensorRetractionAux :
    (ModuleCat.extendScalars d).obj M₀ →+ C ⊗[R] restrictModule R A (restrictAlong e M₀) :=
  TensorProduct.liftAddHom ((tensorActAdd e).comp ν.toAddMonoidHom)
    (fun t s x => by
      change tensorActAdd e (ν (d t * (show S from s))) x =
        tensorActAdd e (ν (show S from s)) (t • x)
      obtain ⟨a, rfl⟩ := e.surjective t
      rw [map_mul, hν, tensorActAdd_mul])

variable [IsIso (((ModuleCat.extendRestrictScalarsAdj d).homEquiv M₀ X).symm ι)]

include hν' hν in
/-- **The injectivity criterion.** -/
theorem injective_tensorToModule : Function.Injective (tensorToModule e d ℓ' hR ι) := by
  set τ := ((ModuleCat.extendRestrictScalarsAdj d).homEquiv M₀ X).symm ι
  have hτ : ∀ (s : S) (x : M₀), τ (s ⊗ₜ[S₀, d] x) = s • semilinearX d ι x :=
    homEquiv_symm_tmul d ι
  let κ : X →+ C ⊗[R] restrictModule R A (restrictAlong e M₀) :=
    (tensorRetractionAux e d ν hν).comp (inv τ).hom.toAddMonoidHom
  have hκ : ∀ z, κ (tensorToModule e d ℓ' hR ι z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul c x =>
      have h1 : (inv τ) (ℓ' c • semilinearX d ι (show M₀ from x)) =
          ℓ' c ⊗ₜ[S₀, d] (show M₀ from x) :=
        (congrArg (inv τ) (hτ (ℓ' c) x).symm).trans (CategoryTheory.IsIso.hom_inv_id_apply τ _)
      refine (congrArg (tensorRetractionAux e d ν hν) h1).trans ?_
      show tensorActAdd e (ν (ℓ' c)) (show M₀ from x) = _
      rw [hν']
      exact (tensorActAdd_tmul e c 1 x).trans (congrArg (fun y => c ⊗ₜ[R] y)
        ((congrArg (fun t : S₀ => t • (show M₀ from x)) (map_one e)).trans (one_smul _ _)))
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  exact Function.LeftInverse.injective hκ

/-- **The bijectivity criterion.** -/
theorem bijective_tensorToModule (ν : S ≃+* C ⊗[R] A) (hν' : ∀ c, ν (ℓ' c) = c ⊗ₜ[R] (1 : A))
    (hν : ∀ a, ν (d (e a)) = (1 : C) ⊗ₜ[R] a) :
    Function.Bijective (tensorToModule e d ℓ' hR ι) := by
  set τ := ((ModuleCat.extendRestrictScalarsAdj d).homEquiv M₀ X).symm ι
  have hτ : ∀ (s : S) (x : M₀), τ (s ⊗ₜ[S₀, d] x) = s • semilinearX d ι x :=
    homEquiv_symm_tmul d ι
  refine ⟨injective_tensorToModule e d ℓ' hR ι ν.toRingHom hν' hν, ?_⟩
  intro y
  obtain ⟨z, rfl⟩ : ∃ z, τ z = y := ⟨(inv τ) y, CategoryTheory.IsIso.inv_hom_id_apply τ y⟩
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, (map_zero _).trans (map_zero τ.hom).symm⟩
  | tmul s x =>
    have key : ∀ t : C ⊗[R] A, ∃ w, tensorToModule e d ℓ' hR ι w =
        ν.symm t • semilinearX d ι x := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => exact ⟨0, by rw [map_zero, map_zero, zero_smul]⟩
      | tmul c a =>
        refine ⟨c ⊗ₜ[R] (show restrictModule R A (restrictAlong e M₀) from e a • x), ?_⟩
        have hs : ν.symm (c ⊗ₜ[R] a) = ℓ' c * d (e a) := by
          rw [RingEquiv.symm_apply_eq, map_mul, hν', hν, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul]
        rw [hs, tensorToModule_tmul, mul_smul]
        exact congrArg (fun y => ℓ' c • y) (semilinearX_smul d ι (e a) x)
      | add t t' ht ht' =>
        obtain ⟨w, hw⟩ := ht
        obtain ⟨w', hw'⟩ := ht'
        exact ⟨w + w', by rw [map_add, hw, hw', map_add, add_smul]⟩
    obtain ⟨w, hw⟩ := key (ν s)
    exact ⟨w, hw.trans ((congrArg (fun t => t • semilinearX d ι x) (ν.symm_apply_apply s)).trans
      (hτ s x).symm)⟩
  | add z z' hz hz' =>
    obtain ⟨w, hw⟩ := hz
    obtain ⟨w', hw'⟩ := hz'
    exact ⟨w + w', (map_add _ w w').trans ((congrArg₂ (· + ·) hw hw').trans
      (map_add τ.hom _ _).symm)⟩

end Bijectivity


section CartesianModule

/-! ### The descent datum of a cartesian module -/

/-- The cosimplicial ring `(A / R)_•`, as a presheaf of rings. -/
noncomputable abbrev cechRing := cosimplicialRingPresheaf (cechCosimplicialAlgebra R A)

/-- The `i`-th coprojection `A → (A / R)_n`. -/
noncomputable abbrev coproj (n : ℕ) (i : Fin (n + 1)) : A →+* (cechRing R A).obj (op (op ⦋n⦌)) :=
  (cechLeg R A ⦋n⦌ i).comp ULift.ringEquiv.symm.toRingHom

/-- `A ≅ (A / R)_0`. -/
noncomputable def coprojEquiv : A ≃+* (cechRing R A).obj (op (op ⦋0⦌)) :=
  RingEquiv.ofBijective (coproj R A 0 0) <| by
    have := isIso_cechLegHom_degZero R A
    have hb : Function.Bijective (cechLegHom R A ⦋0⦌ 0).hom :=
      (ConcreteCategory.bijective_of_isIso (cechLegHom R A ⦋0⦌ 0))
    exact hb.comp ULift.ringEquiv.symm.bijective

/-- `coprojEquiv` is the coprojection `A → (A / R)_0`. -/
theorem coprojEquiv_apply (a : A) : coprojEquiv R A a = coproj R A 0 0 a := rfl

/-- The structure maps of `(A / R)_•` carry coprojections to coprojections. -/
theorem cechRing_map_coproj {n m : ℕ} (β : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) (a : A) :
    ((cechRing R A).map β.op.op).hom (coproj R A n i a) = coproj R A m (β.toOrderHom i) a :=
  congrArg (fun φ => φ (ULift.up a)) (cechRingMap_comp_cechLeg R A β i)

/-- `(A / R)_1 ≅ A ⊗_R A`, with `a ⊗ b` corresponding to `ℓ₀(a) ℓ₁(b)`. -/
noncomputable abbrev degOneEquiv : (cechRing R A).obj (op (op ⦋1⦌)) ≃+* A ⊗[R] A :=
  cechDegOneRingEquiv R A

/-- `degOneEquiv` sends the coprojection `ℓ₀(a)` to `a ⊗ 1`. -/
theorem degOneEquiv_coproj_zero (a : A) : degOneEquiv R A (coproj R A 1 0 a) = a ⊗ₜ[R] 1 :=
  cechDegOneRingEquiv_leg_zero R A (ULift.up a)

/-- `degOneEquiv` sends the coprojection `ℓ₁(a)` to `1 ⊗ a`. -/
theorem degOneEquiv_coproj_one (a : A) : degOneEquiv R A (coproj R A 1 1 a) = 1 ⊗ₜ[R] a :=
  cechDegOneRingEquiv_leg_one R A (ULift.up a)

/-- The ring map `A ⊗_R A → (A / R)_1`, `a ⊗ b ↦ ℓ₀(a) ℓ₁(b)`. -/
noncomputable abbrev degOneMul : A ⊗[R] A →+* (cechRing R A).obj (op (op ⦋1⦌)) :=
  (degOneEquiv R A).symm.toRingHom

/-- `degOneMul (a ⊗ b) = ℓ₀(a) ℓ₁(b)`. -/
theorem degOneMul_tmul (a b : A) :
    degOneMul R A (a ⊗ₜ[R] b) = coproj R A 1 0 a * coproj R A 1 1 b := by
  show (degOneEquiv R A).symm _ = _
  rw [RingEquiv.symm_apply_eq, map_mul, degOneEquiv_coproj_zero, degOneEquiv_coproj_one,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The ring map `(A / R)_2 → (A ⊗_R A) ⊗_R A`. -/
noncomputable abbrev degTwoToTensor : (cechRing R A).obj (op (op ⦋2⦌)) →+* (A ⊗[R] A) ⊗[R] A :=
  cechDegTwoToTensor R A

/-- `degTwoToTensor` sends the coprojections `ℓ₀(a)`, `ℓ₁(a)`, `ℓ₂(a)` to `(a ⊗ 1) ⊗ 1`,
`(1 ⊗ a) ⊗ 1` and `(1 ⊗ 1) ⊗ a`. -/
theorem degTwoToTensor_coproj (i : Fin 3) (a : A) :
    degTwoToTensor R A (coproj R A 2 i a) =
      ![(a ⊗ₜ[R] 1) ⊗ₜ[R] 1, ((1 : A) ⊗ₜ[R] a) ⊗ₜ[R] 1, (1 : A ⊗[R] A) ⊗ₜ[R] a] i := by
  refine (cechDesc_cechLeg R A ⦋2⦌ _ i (ULift.up a)).trans ?_
  fin_cases i <;> rfl

/-- The ring map `A ⊗_R A → (A / R)_2`, `a ⊗ b ↦ ℓ₀(a) ℓ₁(b)`: the image of `A ⊗_R A ≅ (A / R)_1`
under the coface `δ²` (the edge `01`). -/
noncomputable abbrev degTwoFirstTwo : A ⊗[R] A →+* (cechRing R A).obj (op (op ⦋2⦌)) :=
  ((cechRing R A).map (SimplexCategory.δ (n := 1) 2).op.op).hom.comp (degOneMul R A)

/-- `degTwoFirstTwo (a ⊗ b) = ℓ₀(a) ℓ₁(b)` in `(A / R)_2`. -/
theorem degTwoFirstTwo_tmul (a b : A) :
    degTwoFirstTwo R A (a ⊗ₜ[R] b) = coproj R A 2 0 a * coproj R A 2 1 b := by
  rw [RingHom.comp_apply, degOneMul_tmul, map_mul, cechRing_map_coproj, cechRing_map_coproj]
  rfl

/-- `degTwoToTensor (degTwoFirstTwo c) = c ⊗ 1`. -/
theorem degTwoToTensor_degTwoFirstTwo (c : A ⊗[R] A) :
    degTwoToTensor R A (degTwoFirstTwo R A c) = c ⊗ₜ[R] 1 := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [degTwoFirstTwo_tmul, map_mul, degTwoToTensor_coproj, degTwoToTensor_coproj]
    simp
  | add c c' hc hc' => rw [map_add, map_add, hc, hc', TensorProduct.add_tmul]


/-- All coprojections `A → (A / R)_n` agree on the image of `R`. -/
theorem coproj_algebraMap (n : ℕ) (i j : Fin (n + 1)) (r : R) :
    coproj R A n i (algebraMap R A r) = coproj R A n j (algebraMap R A r) :=
  (cechLeg_algebraMap R A ⦋n⦌ i r).trans (cechLeg_algebraMap R A ⦋n⦌ j r).symm

/-- The structure maps of `(A / R)_•` out of degree zero carry `coprojEquiv` to the
coprojections. -/
theorem cechRing_map_coprojEquiv {m : ℕ} (β : ⦋0⦌ ⟶ ⦋m⦌) (a : A) :
    ((cechRing R A).map β.op.op).hom (coprojEquiv R A a) = coproj R A m (β.toOrderHom 0) a :=
  cechRing_map_coproj R A β 0 a

open Stacks.PresheafOfModules

variable (M : CechModule.{u, u, w} R A)

/-- The `A`-module `M_0` of a cosimplicial `(A / R)_•`-module. -/
noncomputable abbrev degZeroModule : ModuleCat.{max u w} A :=
  restrictAlong (coprojEquiv R A) (M.obj (op (op ⦋0⦌)))

/-- An element of the `R`-module underlying `M_0`, read in `M_0`. -/
def toDegZero (y : restrictModule R A (degZeroModule R A M)) : M.obj (op (op ⦋0⦌)) := y

/-- The map `A ⊗_R M_0 → M_1`, `a ⊗ y ↦ ℓ₀(a) • M(δ⁰) y`. -/
noncomputable abbrev psiZero :
    A ⊗[R] restrictModule R A (degZeroModule R A M) →+ M.obj (op (op ⦋1⦌)) :=
  tensorToModule (C := A) (coprojEquiv R A) ((cechRing R A).map (cof₀ 0)).hom (coproj R A 1 0)
    (fun r => by rw [cechRing_map_coprojEquiv]; exact coproj_algebraMap R A 1 _ _ r)
    (M.map (cof₀ 0))

/-- The map `A ⊗_R M_0 → M_1`, `b ⊗ y ↦ ℓ₁(b) • M(δ¹) y`. -/
noncomputable abbrev psiOne' :
    A ⊗[R] restrictModule R A (degZeroModule R A M) →+ M.obj (op (op ⦋1⦌)) :=
  tensorToModule (C := A) (coprojEquiv R A) ((cechRing R A).map (cof₀ 1)).hom (coproj R A 1 1)
    (fun r => by rw [cechRing_map_coprojEquiv]; exact coproj_algebraMap R A 1 _ _ r)
    (M.map (cof₀ 1))

/-- The map `M_0 ⊗_R A → M_1`, `y ⊗ b ↦ ℓ₁(b) • M(δ¹) y`. -/
noncomputable abbrev psiOne :
    restrictModule R A (degZeroModule R A M) ⊗[R] A →+ M.obj (op (op ⦋1⦌)) :=
  (psiOne' R A M).comp (TensorProduct.comm R _ A).toLinearMap.toAddMonoidHom

/-- `psiZero (a ⊗ y) = ℓ₀(a) • M(δ⁰) y`. -/
theorem psiZero_tmul (a : A) (y : restrictModule R A (degZeroModule R A M)) :
    psiZero R A M (a ⊗ₜ[R] y) = coproj R A 1 0 a • M.map (cof₀ 0) (toDegZero R A M y) :=
  rfl

/-- `psiOne (y ⊗ b) = ℓ₁(b) • M(δ¹) y`. -/
theorem psiOne_tmul (y : restrictModule R A (degZeroModule R A M)) (b : A) :
    psiOne R A M (y ⊗ₜ[R] b) = coproj R A 1 1 b • M.map (cof₀ 1) (toDegZero R A M y) :=
  rfl

variable (hM : cartesianModules (cechRing R A) M)

include hM in
/-- For a cartesian `M`, `psiZero : A ⊗_R M_0 → M_1` is bijective. -/
theorem bijective_psiZero : Function.Bijective (psiZero R A M) :=
  have := hM (cof₀ 0)
  bijective_tensorToModule _ _ _ _ _ (degOneEquiv R A) (degOneEquiv_coproj_zero R A)
    (fun a => by rw [cechRing_map_coprojEquiv]; exact degOneEquiv_coproj_one R A a)

include hM in
/-- For a cartesian `M`, `psiZero : A ⊗_R M_0 → M_1` is injective. -/
theorem injective_psiZero' : Function.Injective (psiZero R A M) := (bijective_psiZero R A M hM).1

include hM in
/-- For a cartesian `M`, `psiOne : M_0 ⊗_R A → M_1` is bijective. -/
theorem bijective_psiOne : Function.Bijective (psiOne R A M) := by
  have := hM (cof₀ 1)
  refine (bijective_tensorToModule (C := A) (coprojEquiv R A) ((cechRing R A).map (cof₀ 1)).hom
    (coproj R A 1 1)
    (fun r => by rw [cechRing_map_coprojEquiv]; exact coproj_algebraMap R A 1 _ _ r)
    (M.map (cof₀ 1))
    ((degOneEquiv R A).trans (Algebra.TensorProduct.comm R A A).toRingEquiv)
    (fun c => ?_) (fun a => ?_)).comp (TensorProduct.comm R _ A).bijective
  · show Algebra.TensorProduct.comm R A A (degOneEquiv R A (coproj R A 1 1 c)) = _
    rw [degOneEquiv_coproj_one, Algebra.TensorProduct.comm_tmul]
  · show Algebra.TensorProduct.comm R A A (degOneEquiv R A _) = _
    rw [cechRing_map_coprojEquiv]
    exact (congrArg _ (degOneEquiv_coproj_zero R A a)).trans
      (Algebra.TensorProduct.comm_tmul (R := R) (A := A) (B := A) a 1)


/-- A coface `M(δᵏ) : M_0 → M_1` carries `a • y` to `ℓ_{δᵏ(0)}(a) • M(δᵏ) y`. -/
theorem map_cof₀_smul (k : Fin 2) (a : A) (y : M.obj (op (op ⦋0⦌))) :
    M.map (cof₀ k) (coprojEquiv R A a • y) =
      coproj R A 1 (SimplexCategory.δ k |>.toOrderHom 0) a • M.map (cof₀ k) y :=
  (M.map_smul (cof₀ k) (coprojEquiv R A a) y).trans
    (congrArg (fun t => t • M.map (cof₀ k) y) (cechRing_map_coprojEquiv R A _ a))

/-- An additive map out of `P ⊗_R Q` into an `S`-module is semilinear over `A ⊗_R A → S` as soon
as it is on pure tensors acting on pure tensors. -/
private theorem map_smul_of_tmul_smul_tmul {P Q S Y : Type*} [AddCommMonoid P] [AddCommMonoid Q]
    [Module R P] [Module R Q] [Module (A ⊗[R] A) (P ⊗[R] Q)] [Semiring S] [AddCommMonoid Y]
    [Module S Y] (σ : A ⊗[R] A →+* S) (f : P ⊗[R] Q →+ Y)
    (h : ∀ (a b : A) (p : P) (q : Q),
      f ((a ⊗ₜ[R] b) • p ⊗ₜ[R] q) = σ (a ⊗ₜ[R] b) • f (p ⊗ₜ[R] q))
    (t : A ⊗[R] A) (z : P ⊗[R] Q) : f (t • z) = σ t • f z := by
  induction t using TensorProduct.induction_on with
  | zero => rw [zero_smul, map_zero, map_zero, zero_smul]
  | add t t' ht ht' => rw [add_smul, map_add, ht, ht', map_add, add_smul]
  | tmul a b =>
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | add z z' hz hz' => rw [smul_add, map_add, hz, hz', map_add, smul_add]
    | tmul p q => exact h a b p q

/-- `psiZero` is `A ⊗_R A`-linear, `A ⊗_R A` acting on `M_1` through `degOneMul`. -/
theorem psiZero_smul (t : A ⊗[R] A) (z : A ⊗[R] restrictModule R A (degZeroModule R A M)) :
    psiZero R A M (t • z) = degOneMul R A t • psiZero R A M z := by
  refine map_smul_of_tmul_smul_tmul R A (degOneMul R A) (psiZero R A M) (fun a b c y => ?_) t z
  rw [targetTensor_smul_tmul, psiZero_tmul, psiZero_tmul, degOneMul_tmul]
  show coproj R A 1 0 (a * c) • M.map (cof₀ 0) (coprojEquiv R A b • (toDegZero R A M y)) =
    (coproj R A 1 0 a * coproj R A 1 1 b) • coproj R A 1 0 c • M.map (cof₀ 0) (toDegZero R A M y)
  have h1 : (SimplexCategory.δ (n := 0) 0).toOrderHom 0 = 1 := rfl
  rw [map_cof₀_smul, h1, map_mul, smul_smul, smul_smul]
  congr 1
  ring

/-- `psiOne` is `A ⊗_R A`-linear, `A ⊗_R A` acting on `M_1` through `degOneMul`. -/
theorem psiOne_smul (t : A ⊗[R] A) (z : restrictModule R A (degZeroModule R A M) ⊗[R] A) :
    psiOne R A M (t • z) = degOneMul R A t • psiOne R A M z := by
  refine map_smul_of_tmul_smul_tmul R A (degOneMul R A) (psiOne R A M) (fun a b y c => ?_) t z
  rw [sourceTensor_smul_tmul, psiOne_tmul, psiOne_tmul, degOneMul_tmul]
  show coproj R A 1 1 (b * c) • M.map (cof₀ 1) (coprojEquiv R A a • (toDegZero R A M y)) =
    (coproj R A 1 0 a * coproj R A 1 1 b) • coproj R A 1 1 c • M.map (cof₀ 1) (toDegZero R A M y)
  have h1 : (SimplexCategory.δ (n := 0) 1).toOrderHom 0 = 0 := rfl
  rw [map_cof₀_smul, h1, map_mul, smul_smul, smul_smul]
  congr 1
  ring

/-- `ModuleCat.psiZero` as an `A ⊗_R A`-linear map into `M_1`. -/
noncomputable def psiZeroLinear :
    A ⊗[R] restrictModule R A (degZeroModule R A M) →ₗ[A ⊗[R] A]
      (ModuleCat.restrictScalars (degOneMul R A)).obj (M.obj (op (op ⦋1⦌))) where
  toFun := psiZero R A M
  map_add' := map_add _
  map_smul' := psiZero_smul R A M

/-- `ModuleCat.psiOne` as an `A ⊗_R A`-linear map into `M_1`. -/
noncomputable def psiOneLinear :
    restrictModule R A (degZeroModule R A M) ⊗[R] A →ₗ[A ⊗[R] A]
      (ModuleCat.restrictScalars (degOneMul R A)).obj (M.obj (op (op ⦋1⦌))) where
  toFun := psiOne R A M
  map_add' := map_add _
  map_smul' := psiOne_smul R A M

variable {M} in
/-- **The transition isomorphism of a cartesian module**: `N ⊗_R A ≅ M_1 ≅ A ⊗_R N`. -/
noncomputable def cartesianTransition (hM : cartesianModules (cechRing R A) M) :
    (restrictModule R A (degZeroModule R A M) ⊗[R] A) ≃ₗ[A ⊗[R] A]
      (A ⊗[R] restrictModule R A (degZeroModule R A M)) :=
  (LinearEquiv.ofBijective (psiOneLinear R A M) (bijective_psiOne R A M hM)).trans
    (LinearEquiv.ofBijective (psiZeroLinear R A M) (bijective_psiZero R A M hM)).symm

/-- `psiZero ∘ cartesianTransition = psiOne`. -/
theorem psiZero_cartesianTransition (hM : cartesianModules (cechRing R A) M)
    (z : restrictModule R A (degZeroModule R A M) ⊗[R] A) :
    psiZero R A M (cartesianTransition R A hM z) = psiOne R A M z :=
  (LinearEquiv.ofBijective (psiZeroLinear R A M) (bijective_psiZero R A M hM)).apply_symm_apply _


/-- The map `(A ⊗_R A) ⊗_R M_0 → M_2`, `(a ⊗ b) ⊗ y ↦ ℓ₀(a) ℓ₁(b) • M(2) y`, along the vertex `2`
of `⦋2⦌`. -/
noncomputable abbrev psiTwo :
    (A ⊗[R] A) ⊗[R] restrictModule R A (degZeroModule R A M) →+ M.obj (op (op ⦋2⦌)) :=
  tensorToModule (C := A ⊗[R] A) (coprojEquiv R A) ((cechRing R A).map (vert₂ 2)).hom
    (degTwoFirstTwo R A)
    (fun r => by
      rw [cechRing_map_coprojEquiv, Algebra.TensorProduct.algebraMap_apply, degTwoFirstTwo_tmul,
        map_one, mul_one]
      exact coproj_algebraMap R A 2 _ _ r)
    (M.map (vert₂ 2))

/-- `psiTwo ((a ⊗ b) ⊗ y) = ℓ₀(a) ℓ₁(b) • M(2) y`. -/
theorem psiTwo_tmul (a b : A) (y : restrictModule R A (degZeroModule R A M)) :
    psiTwo R A M ((a ⊗ₜ[R] b) ⊗ₜ[R] y) =
      (coproj R A 2 0 a * coproj R A 2 1 b) • M.map (vert₂ 2) (toDegZero R A M y) := by
  rw [tensorToModule_tmul, degTwoFirstTwo_tmul]
  rfl

include hM in
/-- For a cartesian `M`, `psiTwo : (A ⊗_R A) ⊗_R M_0 → M_2` is injective. -/
theorem injective_psiTwo : Function.Injective (psiTwo R A M) :=
  have := hM (vert₂ 2)
  injective_tensorToModule _ _ _ _ _ (degTwoToTensor R A) (degTwoToTensor_degTwoFirstTwo R A)
    (fun a => by
      rw [cechRing_map_coprojEquiv, degTwoToTensor_coproj]
      rfl)

/-- A coface `M(δʲ) : M_1 → M_2` carries `ℓᵢ(a) • y` to `ℓ_{δʲ(i)}(a) • M(δʲ) y`. -/
theorem map_cof₁_smul (j : Fin 3) (i : Fin 2) (a : A) (y : M.obj (op (op ⦋1⦌))) :
    M.map (cof₁ j) (coproj R A 1 i a • y) =
      coproj R A 2 (SimplexCategory.δ j |>.toOrderHom i) a • M.map (cof₁ j) y :=
  (M.map_smul (cof₁ j) (coproj R A 1 i a) y).trans
    (congrArg (fun t => t • M.map (cof₁ j) y) (cechRing_map_coproj R A _ i a))

/-- `M(δʲ) ∘ M(δⁱ) : M_0 → M_2` is `M` of the vertex `k = δʲ(δⁱ(0))`. -/
theorem map_cof₁_map_cof₀ (i : Fin 2) (j k : Fin 3)
    (h : (SimplexCategory.δ j).toOrderHom ((SimplexCategory.δ i).toOrderHom 0) = k)
    (y : M.obj (op (op ⦋0⦌))) :
    M.map (cof₁ j) (M.map (cof₀ i) y) = M.map (vert₂ k) y :=
  map_map_eq M _ _ _ (cof₀_comp_cof₁ i j k h) y

/-- Scalars of `(A / R)_•` commute in their action on a cosimplicial module. -/
theorem smul_comm_cech {X : SimplexCategoryᵒᵖᵒᵖ} (r t : (cechRing R A).obj X) (m : M.obj X) :
    r • t • m = t • r • m := by
  rw [smul_smul, mul_comm, ← smul_smul]

/-- `M(δʲ) (ℓᵢ(a) • M(δⁱ') y) = ℓ_{δʲ(i)}(a) • M(k) y`, where `k = δʲ(δⁱ'(0))`. -/
theorem map_cof₁_smul_map_cof₀ (j : Fin 3) (i i' : Fin 2) (k : Fin 3)
    (h : (SimplexCategory.δ j).toOrderHom ((SimplexCategory.δ i').toOrderHom 0) = k) (a : A)
    (y : M.obj (op (op ⦋0⦌))) :
    M.map (cof₁ j) (coproj R A 1 i a • M.map (cof₀ i') y) =
      coproj R A 2 (SimplexCategory.δ j |>.toOrderHom i) a • M.map (vert₂ k) y :=
  (map_cof₁_smul R A M j i a _).trans
    (congrArg (fun z => coproj R A 2 (SimplexCategory.δ j |>.toOrderHom i) a • z)
      (map_cof₁_map_cof₀ R A M i' j k h y))

/-- `psiTwo` of `a ⊗ w`, reassociated, is `ℓ₀(a) • M(δ⁰) (psiZero w)`. -/
theorem psiTwo_assoc_symm (a : A) (w : A ⊗[R] restrictModule R A (degZeroModule R A M)) :
    psiTwo R A M ((TensorProduct.assoc R A A _).symm (a ⊗ₜ[R] w)) =
      coproj R A 2 0 a • M.map (cof₁ 0) (psiZero R A M w) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero, map_zero, map_zero, smul_zero]; rfl
  | add w w' hw hw' =>
    rw [TensorProduct.tmul_add, map_add, map_add, hw, hw', map_add, map_add, smul_add]
    rfl
  | tmul a' y =>
    exact (psiTwo_tmul R A M a a' y).trans ((mul_smul _ _ _).trans
      (congrArg (fun z => coproj R A 2 0 a • z)
        (map_cof₁_smul_map_cof₀ R A M 0 0 0 2 rfl a' (toDegZero R A M y)).symm))

/-- `psiTwo` of `w ⊗ a`, with the last two factors exchanged, is `ℓ₁(a) • M(δ¹) (psiZero w)`. -/
theorem psiTwo_rightComm (a : A) (w : A ⊗[R] restrictModule R A (degZeroModule R A M)) :
    psiTwo R A M ((TensorProduct.rightComm R A _ A) (w ⊗ₜ[R] a)) =
      coproj R A 2 1 a • M.map (cof₁ 1) (psiZero R A M w) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero, map_zero, map_zero, smul_zero]; rfl
  | add w w' hw hw' =>
    rw [TensorProduct.add_tmul, map_add, map_add, hw, hw', map_add, map_add, smul_add]
    rfl
  | tmul a' y =>
    exact (psiTwo_tmul R A M a' a y).trans ((mul_smul _ _ _).trans ((smul_comm _ _ _).trans
      (congrArg (fun z => coproj R A 2 1 a • z)
        (map_cof₁_smul_map_cof₀ R A M 1 0 0 2 rfl a' (toDegZero R A M y)).symm)))

/-- `psiTwo (transition12 (w ⊗ b)) = ℓ₂(b) • M(δ²) (psiZero w)`. -/
theorem psiTwo_transition12 (hM : cartesianModules (cechRing R A) M)
    (w : A ⊗[R] restrictModule R A (degZeroModule R A M)) (b : A) :
    psiTwo R A M (transition12 R A (degZeroModule R A M) (cartesianTransition R A hM) (w ⊗ₜ[R] b)) =
      coproj R A 2 2 b • M.map (cof₁ 2) (psiZero R A M w) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero, map_zero, map_zero, smul_zero]; rfl
  | add w w' hw hw' =>
    rw [TensorProduct.add_tmul, map_add, map_add, hw, hw', map_add, map_add, smul_add]
    rfl
  | tmul a y =>
    have ht : transition12 R A (degZeroModule R A M) (cartesianTransition R A hM)
        ((a ⊗ₜ[R] y) ⊗ₜ[R] b) = (TensorProduct.assoc R A A _).symm
          (a ⊗ₜ[R] cartesianTransition R A hM (y ⊗ₜ[R] b)) := by
      rw [transition12]; simp
    rw [ht, psiTwo_assoc_symm, psiZero_cartesianTransition]
    exact (congrArg (fun z => coproj R A 2 0 a • z)
        (map_cof₁_smul_map_cof₀ R A M 0 1 1 1 rfl b (toDegZero R A M y))).trans
      ((smul_comm_cech R A M _ _ _).trans (congrArg (fun z => coproj R A 2 2 b • z)
        (map_cof₁_smul_map_cof₀ R A M 2 0 0 1 rfl a (toDegZero R A M y)).symm))

/-- `psiTwo (transition02 (y ⊗ b)) = ℓ₂(b) • M(δ²) (psiOne y)`. -/
theorem psiTwo_transition02 (hM : cartesianModules (cechRing R A) M)
    (y : restrictModule R A (degZeroModule R A M) ⊗[R] A) (b : A) :
    psiTwo R A M (transition02 R A (degZeroModule R A M) (cartesianTransition R A hM) (y ⊗ₜ[R] b)) =
      coproj R A 2 2 b • M.map (cof₁ 2) (psiOne R A M y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero, map_zero, map_zero, smul_zero]; rfl
  | add y y' hy hy' =>
    rw [TensorProduct.add_tmul, map_add, map_add, hy, hy', map_add, map_add, smul_add]
    rfl
  | tmul x a =>
    have ht : transition02 R A (degZeroModule R A M) (cartesianTransition R A hM)
        ((x ⊗ₜ[R] a) ⊗ₜ[R] b) = (TensorProduct.rightComm R A _ A)
          (cartesianTransition R A hM (x ⊗ₜ[R] b) ⊗ₜ[R] a) := by
      rw [transition02]; simp
    rw [ht, psiTwo_rightComm, psiZero_cartesianTransition]
    exact (congrArg (fun z => coproj R A 2 1 a • z)
        (map_cof₁_smul_map_cof₀ R A M 1 1 1 0 rfl b (toDegZero R A M x))).trans
      ((smul_comm_cech R A M _ _ _).trans (congrArg (fun z => coproj R A 2 2 b • z)
        (map_cof₁_smul_map_cof₀ R A M 2 1 1 0 rfl a (toDegZero R A M x)).symm))

/-- **The descent datum of a cartesian `(A / R)_•`-module** `M`: the `A`-module `M_0`, with the
transition `N ⊗_R A ≅ M_1 ≅ A ⊗_R N`.  The cocycle condition is checked in `M_2`. -/
noncomputable def descentDataOfCartesian (hM : cartesianModules (cechRing R A) M) :
    DescentData.{u, u, max u w} R A where
  module := degZeroModule R A M
  transition := cartesianTransition R A hM
  cocycle := TensorProduct.ext' fun y b => injective_psiTwo R A M hM <| by
    rw [LinearMap.comp_apply, transition01, LinearMap.rTensor_tmul, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, psiTwo_transition12, psiTwo_transition02, psiZero_cartesianTransition]


variable {M} {M' : CechModule.{u, u, w} R A} (φ : M ⟶ M')

/-- A morphism of cosimplicial modules, in degree zero, as an `A`-linear map. -/
noncomputable abbrev degZeroHom : degZeroModule R A M ⟶ degZeroModule R A M' :=
  (ModuleCat.restrictScalars (coprojEquiv R A).toRingHom).map (φ.app (op (op ⦋0⦌)))

/-- `psiZero` is natural with respect to morphisms of cosimplicial modules. -/
theorem psiZero_naturality (w : A ⊗[R] restrictModule R A (degZeroModule R A M)) :
    psiZero R A M' ((restrictHom R A (degZeroHom R A φ)).lTensor A w) =
      φ.app (op (op ⦋1⦌)) (psiZero R A M w) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add w w' hw hw' => rw [map_add, map_add, hw, hw', map_add, map_add]
  | tmul a y =>
    rw [LinearMap.lTensor_tmul, psiZero_tmul, psiZero_tmul]
    exact (congrArg (fun z => coproj R A 1 0 a • z)
      (PresheafOfModules.naturality_apply φ (cof₀ 0) (toDegZero R A M y)).symm).trans
      ((φ.app (op (op ⦋1⦌))).hom.map_smul _ _).symm

/-- `psiOne` is natural with respect to morphisms of cosimplicial modules. -/
theorem psiOne_naturality (z : restrictModule R A (degZeroModule R A M) ⊗[R] A) :
    psiOne R A M' ((restrictHom R A (degZeroHom R A φ)).rTensor A z) =
      φ.app (op (op ⦋1⦌)) (psiOne R A M z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]
  | tmul y b =>
    rw [LinearMap.rTensor_tmul, psiOne_tmul, psiOne_tmul]
    exact (congrArg (fun z => coproj R A 1 1 b • z)
      (PresheafOfModules.naturality_apply φ (cof₀ 1) (toDegZero R A M y)).symm).trans
      ((φ.app (op (op ⦋1⦌))).hom.map_smul _ _).symm

variable {R A} in
/-- The morphism of descent data of a morphism of cartesian modules. -/
noncomputable def descentDataHomOfCartesian (hM₁ : cartesianModules (cechRing R A) M)
    (hM₂ : cartesianModules (cechRing R A) M') :
    descentDataOfCartesian R A M hM₁ ⟶ descentDataOfCartesian R A M' hM₂ where
  hom := degZeroHom R A φ
  comm := LinearMap.ext fun z => injective_psiZero' R A M' hM₂ <|
    (psiZero_cartesianTransition R A M' hM₂ _).trans ((psiOne_naturality R A φ z).trans
      ((congrArg (φ.app (op (op ⦋1⦌))) (psiZero_cartesianTransition R A M hM₁ z)).symm.trans
        (psiZero_naturality R A φ _).symm))


/-- `A ⊗_R -` of an `A`-linear map, as an `A ⊗_R A`-linear map. -/
noncomputable def lTensorTarget {N N' : ModuleCat.{max u w} A} (g : N ⟶ N') :
    A ⊗[R] restrictModule R A N →ₗ[A ⊗[R] A] A ⊗[R] restrictModule R A N' where
  toFun := (restrictHom R A g).lTensor A
  map_add' := map_add _
  map_smul' t z := by
    change (restrictHom R A g).lTensor A (t • z) = t • (restrictHom R A g).lTensor A z
    induction t using TensorProduct.induction_on with
    | zero => rw [zero_smul, map_zero, zero_smul]
    | add t t' ht ht' => rw [add_smul, map_add, ht, ht', add_smul]
    | tmul a b =>
      induction z using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | add z z' hz hz' => rw [smul_add, map_add, hz, hz', map_add, smul_add]
      | tmul c y =>
        rw [targetTensor_smul_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
          targetTensor_smul_tmul]
        congr 1
        exact g.hom.map_smul b y

/-- The `A ⊗_R A`-linear isomorphism `A ⊗_R M_0 ≅ M_1`. -/
noncomputable abbrev psiZeroEquiv (hM : cartesianModules (cechRing R A) M) :
    A ⊗[R] restrictModule R A (degZeroModule R A M) ≃ₗ[A ⊗[R] A]
      (ModuleCat.restrictScalars (degOneMul R A)).obj (M.obj (op (op ⦋1⦌))) :=
  LinearEquiv.ofBijective (psiZeroLinear R A M) (bijective_psiZero R A M hM)

/-- `degOneMul : A ⊗_R A → (A / R)_1` is surjective. -/
theorem degOneMul_surjective : Function.Surjective (degOneMul R A) :=
  (degOneEquiv R A).symm.surjective

variable {R A} in
/-- The degree-one component of the morphism of cartesian modules determined by a morphism of
their descent data. -/
noncomputable def degOneHomOfDescent (hM : cartesianModules (cechRing R A) M)
    (g : degZeroModule R A M ⟶ degZeroModule R A M') :
    M.obj (op (op ⦋1⦌)) ⟶ M'.obj (op (op ⦋1⦌)) :=
  let f : (ModuleCat.restrictScalars (degOneMul R A)).obj (M.obj (op (op ⦋1⦌))) →ₗ[A ⊗[R] A]
      (ModuleCat.restrictScalars (degOneMul R A)).obj (M'.obj (op (op ⦋1⦌))) :=
    (psiZeroLinear R A M').comp ((lTensorTarget R A g).comp (psiZeroEquiv R A hM).symm.toLinearMap)
  ModuleCat.ofHom
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun t y => by
        obtain ⟨z, rfl⟩ := degOneMul_surjective R A t
        exact f.map_smul z y }

/-- `degOneHomOfDescent hM g` sends `psiZero w` to `psiZero ((A ⊗ g) w)`. -/
theorem degOneHomOfDescent_psiZero (hM : cartesianModules (cechRing R A) M)
    (g : degZeroModule R A M ⟶ degZeroModule R A M')
    (w : A ⊗[R] restrictModule R A (degZeroModule R A M)) :
    degOneHomOfDescent hM g (psiZero R A M w) =
      psiZero R A M' ((restrictHom R A g).lTensor A w) := by
  show psiZero R A M' ((restrictHom R A g).lTensor A ((psiZeroEquiv R A hM).symm
    ((psiZeroEquiv R A hM) w))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- `M(δ¹) x = psiOne (x ⊗ 1)`. -/
theorem map_cof₀_one_eq_psiOne (x : restrictModule R A (degZeroModule R A M)) :
    M.map (cof₀ 1) (toDegZero R A M x) = psiOne R A M (x ⊗ₜ[R] 1) := by
  rw [psiOne_tmul, map_one, one_smul]

/-- `M(δ⁰) x = psiZero (1 ⊗ x)`. -/
theorem map_cof₀_zero_eq_psiZero (x : restrictModule R A (degZeroModule R A M)) :
    M.map (cof₀ 0) (toDegZero R A M x) = psiZero R A M (1 ⊗ₜ[R] x) := by
  rw [psiZero_tmul, map_one, one_smul]


variable {R A} in
/-- An `A`-linear map `M_0 → M'_0`, as an `(A / R)_0`-linear map. -/
noncomputable def degZeroHomOfLinear (g : degZeroModule R A M ⟶ degZeroModule R A M') :
    M.obj (op (op ⦋0⦌)) ⟶ M'.obj (op (op ⦋0⦌)) :=
  ModuleCat.ofHom
    { toFun := g.hom
      map_add' := g.hom.map_add
      map_smul' := fun t y => by
        obtain ⟨a, rfl⟩ := (coprojEquiv R A).surjective t
        exact g.hom.map_smul a y }

variable {R A} in
/-- **The morphism of cartesian modules of a morphism of their descent data.** -/
noncomputable def cartesianHomOfDescent (hM₁ : cartesianModules (cechRing R A) M)
    (hM₂ : cartesianModules (cechRing R A) M')
    (g : descentDataOfCartesian R A M hM₁ ⟶ descentDataOfCartesian R A M' hM₂) : M ⟶ M' :=
  homOfDegreeZero hM₁ (degZeroHomOfLinear g.hom) (degOneHomOfDescent hM₁ g.hom)
    (fun y => (congrArg (degOneHomOfDescent hM₁ g.hom) (map_cof₀_one_eq_psiOne R A y)).trans <|
      (congrArg (degOneHomOfDescent hM₁ g.hom)
        (psiZero_cartesianTransition R A M hM₁ (y ⊗ₜ[R] 1)).symm).trans <|
      (degOneHomOfDescent_psiZero R A hM₁ g.hom _).trans <|
      (congrArg (psiZero R A M') (LinearMap.congr_fun g.comm (y ⊗ₜ[R] 1)).symm).trans <|
      (psiZero_cartesianTransition R A M' hM₂ _).trans
        (map_cof₀_one_eq_psiOne R A (g.hom y)).symm)
    (fun y => (congrArg (degOneHomOfDescent hM₁ g.hom) (map_cof₀_zero_eq_psiZero R A y)).trans <|
      (degOneHomOfDescent_psiZero R A hM₁ g.hom _).trans
        (map_cof₀_zero_eq_psiZero R A (g.hom y)).symm)

/-- In degree zero, `cartesianHomOfDescent hM₁ hM₂ g` is the underlying map of `g`. -/
theorem cartesianHomOfDescent_app_zero (hM₁ : cartesianModules (cechRing R A) M)
    (hM₂ : cartesianModules (cechRing R A) M')
    (g : descentDataOfCartesian R A M hM₁ ⟶ descentDataOfCartesian R A M' hM₂) :
    (cartesianHomOfDescent hM₁ hM₂ g).app (op (op ⦋0⦌)) = degZeroHomOfLinear g.hom := by
  unfold cartesianHomOfDescent
  exact homOfDegreeZero_app_zero _ _ _ _ _


end CartesianModule

section Functor

open Stacks.PresheafOfModules

variable {R A}

/-- The underlying cosimplicial module of a cartesian `(A / R)_•`-module is cartesian. -/
theorem cartesianModules_of (M : CartesianCechModule.{u, u, w} R A) :
    cartesianModules (cechRing R A) M.obj :=
  fun _ _ g => M.property g.unop.unop

variable (R A)

/-- **The descent datum of a cartesian `(A / R)_•`-module**, as a functor. -/
noncomputable def cartesianDescentDataFunctor :
    CartesianCechModule.{u, u, w} R A ⥤ DescentData.{u, u, max u w} R A where
  obj M := descentDataOfCartesian R A M.obj (cartesianModules_of M)
  map φ := descentDataHomOfCartesian φ.hom (cartesianModules_of _) (cartesianModules_of _)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor `cartesianDescentDataFunctor` is faithful. -/
instance : (cartesianDescentDataFunctor R A).Faithful where
  map_injective {M M'} φ ψ h := by
    refine ObjectProperty.hom_ext _ (hom_ext_of_cartesian_app_zero (cartesianModules_of M) ?_)
    have h' := congrArg DescentData.Hom.hom h
    exact ModuleCat.hom_ext (LinearMap.ext fun x =>
      congrArg (fun f : degZeroModule R A M.obj ⟶ degZeroModule R A M'.obj => f x) h')

/-- The functor `cartesianDescentDataFunctor` is full. -/
instance : (cartesianDescentDataFunctor R A).Full where
  map_surjective {M M'} g :=
    ⟨ObjectProperty.homMk (cartesianHomOfDescent (cartesianModules_of M)
        (cartesianModules_of M') g), by
      refine DescentData.Hom.ext ?_
      exact congrArg (ModuleCat.restrictScalars (coprojEquiv R A).toRingHom).map
        (cartesianHomOfDescent_app_zero R A (cartesianModules_of M) (cartesianModules_of M') g)⟩

end Functor

section EssSurj

open Stacks.PresheafOfModules

variable {R A}

/-- The coprojection `ULift A → (A / R)_0` is bijective. -/
theorem bijective_cechLeg_zero : Function.Bijective (cechLeg R A ⦋0⦌ 0) :=
  (coprojEquiv R A).bijective.comp ULift.ringEquiv.bijective

/-- `(A / R)_0 ≅ ULift A`, through the unique coprojection. -/
noncomputable abbrev cechLegZeroEquiv : ULift.{u} A ≃+* (cechCosimplicialAlgebra R A).obj ⦋0⦌ :=
  RingEquiv.ofBijective (cechLeg R A ⦋0⦌ 0) bijective_cechLeg_zero

/-- An element of the lifted module, read in the module. -/
def liftedDown {N : ModuleCat.{max u w} A} (y : liftedModule.{u, u, max u w} A N) : N := y.down

/-- An element of the scalar factor of an extension of scalars, read in the ring. -/
def scalarElt (s : (ModuleCat.restrictScalars (cechLeg R A ⦋0⦌ 0)).obj
    (ModuleCat.of _ ((cechCosimplicialAlgebra R A).obj ⦋0⦌))) :
    (cechCosimplicialAlgebra R A).obj ⦋0⦌ := s

/-- `ℓ⁻¹ : (A / R)_0 → A`. -/
noncomputable def legZeroInv (s : (cechCosimplicialAlgebra R A).obj ⦋0⦌) : A :=
  (cechLegZeroEquiv.symm s).down

/-- `ℓ⁻¹(ℓ(t) s) = t ℓ⁻¹(s)`. -/
theorem legZeroInv_mul (t : ULift.{u} A) (s : (cechCosimplicialAlgebra R A).obj ⦋0⦌) :
    legZeroInv (cechLeg R A ⦋0⦌ 0 t * s) = t.down * legZeroInv s := by
  unfold legZeroInv
  rw [map_mul, show cechLegZeroEquiv.symm (cechLeg R A ⦋0⦌ 0 t) = t from
    cechLegZeroEquiv.symm_apply_apply t]
  rfl

/-- The additive map `y ↦ ℓ⁻¹(s) • y`. -/
noncomputable def retractionSlice (N : ModuleCat.{max u w} A)
    (s : (cechCosimplicialAlgebra R A).obj ⦋0⦌) :
    liftedModule.{u, u, max u w} A N →+ N where
  toFun y := legZeroInv s • liftedDown y
  map_zero' := smul_zero _
  map_add' y y' := smul_add _ (liftedDown y) (liftedDown y')

/-- The retraction `(A / R)_0 ⊗ N → N`, `s ⊗ y ↦ ℓ⁻¹(s) • y`. -/
noncomputable def cechDegreeZeroRetraction (N : ModuleCat.{max u w} A) :
    cechDegreeObj R A N ⦋0⦌ 0 →+ restrictModule R A N :=
  TensorProduct.liftAddHom
    { toFun := fun s => retractionSlice N (scalarElt s)
      map_zero' := AddMonoidHom.ext fun y => by
        change legZeroInv (0 : (cechCosimplicialAlgebra R A).obj ⦋0⦌) • liftedDown y = 0
        rw [legZeroInv, map_zero]
        exact zero_smul _ _
      map_add' := fun s s' => AddMonoidHom.ext fun y => by
        change legZeroInv (scalarElt s + scalarElt s') • liftedDown y =
          legZeroInv (scalarElt s) • liftedDown y + legZeroInv (scalarElt s') • liftedDown y
        rw [legZeroInv, legZeroInv, legZeroInv, map_add]
        exact add_smul _ _ _ }
    (fun t s y => by
      change legZeroInv (cechLeg R A ⦋0⦌ 0 t * scalarElt s) • liftedDown y =
        legZeroInv (scalarElt s) • (t.down • liftedDown y)
      rw [legZeroInv_mul, mul_comm, mul_smul])

/-- In degree zero, `cechGenerator`, `x ↦ 1 ⊗ x`, is bijective. -/
theorem bijective_cechGenerator_zero (N : ModuleCat.{max u w} A) :
    Function.Bijective (cechGenerator R A N ⦋0⦌ 0) := by
  constructor
  · refine Function.LeftInverse.injective (g := cechDegreeZeroRetraction N) fun x => ?_
    rw [cechGenerator_eq_tmul]
    show legZeroInv (1 : (cechCosimplicialAlgebra R A).obj ⦋0⦌) • (x : N) = x
    rw [legZeroInv, map_one]
    exact one_smul _ _
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul s y =>
      refine ⟨(legZeroInv (scalarElt s) • liftedDown y : N), ?_⟩
      have hs : cechLeg R A ⦋0⦌ 0 (cechLegZeroEquiv.symm (scalarElt s)) = scalarElt s :=
        cechLegZeroEquiv.apply_symm_apply _
      refine (cechGenerator_smul R A N ⦋0⦌ 0 _ _).trans ?_
      refine (congrArg (fun t => t • cechGenerator R A N ⦋0⦌ 0 (liftedDown y)) hs).trans ?_
      refine (congrArg (fun z => scalarElt s • z) (cechGenerator_eq_tmul R A N ⦋0⦌ 0 _)).trans ?_
      refine (ModuleCat.ExtendScalars.smul_tmul _ _ _ _).trans ?_
      rw [mul_one]
      rfl
    | add z z' hz hz' =>
      obtain ⟨x, rfl⟩ := hz
      obtain ⟨x', rfl⟩ := hz'
      exact ⟨x + x', map_add _ _ _⟩

/-- A morphism of descent data whose underlying map is bijective is an isomorphism. -/
theorem DescentData.isIso_of_bijective {D E : DescentData.{u, u, max u w} R A} (g : D ⟶ E)
    (hg : Function.Bijective g.hom) : IsIso g := by
  let e := (LinearEquiv.ofBijective g.hom.hom hg)
  let gi : E.module ⟶ D.module := ModuleCat.ofHom e.symm.toLinearMap
  have h1 : g.hom ≫ gi = 𝟙 _ := ModuleCat.hom_ext (LinearMap.ext fun x => e.symm_apply_apply x)
  have h2 : gi ≫ g.hom = 𝟙 _ := ModuleCat.hom_ext (LinearMap.ext fun x => e.apply_symm_apply x)
  let ginv : E ⟶ D :=
    { hom := gi
      comm := by
        have hc := g.comm
        have hr : ((restrictHom R A g.hom).rTensor A).comp ((restrictHom R A gi).rTensor A) =
            LinearMap.id := by
          rw [← LinearMap.rTensor_comp, ← restrictHom_comp, h2, restrictHom_id,
            LinearMap.rTensor_id]
        have hl : ((restrictHom R A gi).lTensor A).comp ((restrictHom R A g.hom).lTensor A) =
            LinearMap.id := by
          rw [← LinearMap.lTensor_comp, ← restrictHom_comp, h1, restrictHom_id,
            LinearMap.lTensor_id]
        calc (D.transition.toLinearMap.restrictScalars R).comp ((restrictHom R A gi).rTensor A)
            = (((restrictHom R A gi).lTensor A).comp ((restrictHom R A g.hom).lTensor A)).comp
                ((D.transition.toLinearMap.restrictScalars R).comp
                  ((restrictHom R A gi).rTensor A)) := by rw [hl, LinearMap.id_comp]
          _ = ((restrictHom R A gi).lTensor A).comp
                ((((restrictHom R A g.hom).lTensor A).comp
                  (D.transition.toLinearMap.restrictScalars R)).comp
                    ((restrictHom R A gi).rTensor A)) := by
              simp only [LinearMap.comp_assoc]
          _ = ((restrictHom R A gi).lTensor A).comp
                ((E.transition.toLinearMap.restrictScalars R).comp
                  (((restrictHom R A g.hom).rTensor A).comp
                    ((restrictHom R A gi).rTensor A))) := by
              rw [← hc]; simp only [LinearMap.comp_assoc]
          _ = ((restrictHom R A gi).lTensor A).comp
                (E.transition.toLinearMap.restrictScalars R) := by
              rw [hr, LinearMap.comp_id] }
  exact ⟨ginv, DescentData.Hom.ext h1, DescentData.Hom.ext h2⟩

variable (D : DescentData.{u, u, max u w} R A)

/-- The cosimplicial module of a descent datum. -/
noncomputable abbrev descentModule : CechModule.{u, u, w} R A :=
  (descentCosimplicialModuleFunctor.{u, u, max u w} R A).obj D

/-- The identification of the degree-`n` module of the cosimplicial module of a descent datum
with `N_{n, n}`. -/
noncomputable abbrev castDeg (n : SimplexCategory) :
    cechDegreeObj R A D.module n (Fin.last n.len) ⟶ (descentModule D).obj (op (op n)) :=
  eqToHom (descentCosimplicialModuleFunctor_obj R A D n).symm

/-- `castDeg` carries the structure maps of `descentModule D` to `cechStructureMap D`. -/
theorem castDeg_map {n m : SimplexCategory} (β : n ⟶ m) :
    castDeg D n ≫ (descentModule D).map β.op.op =
      cechStructureMap D β ≫ (ModuleCat.restrictScalars (cechRingMap R A β)).map (castDeg D m) := by
  have h := descentCosimplicialModuleFunctor_map R A D β
  simp only [descentModule] at h ⊢
  rw [h, eqToHom_map]
  exact (eqToHom_trans_assoc _ _ _).trans
    ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _))

/-- `transitionGen D n i i` is `cechGenerator` after the action `A ⊗_R N → N`. -/
theorem transitionGen_diag (n : SimplexCategory) (i : Fin (n.len + 1))
    (z : A ⊗[R] restrictModule R A D.module) :
    transitionGen D n i i z = cechGenerator R A D.module n i
      (TensorProduct.lift (restrictedScalarAction R A D.module).toLinearMap z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add z z' hz hz' => rw [map_add, hz, hz', map_add, map_add]
  | tmul a y =>
    rw [transitionGen_tmul, TensorProduct.lift.tmul]
    exact (cechGenerator_smul R A D.module n i a y).symm

/-- `transitionBase D n i i` is `cechGenerator R A D.module n i`. -/
theorem transitionBase_diag (n : SimplexCategory) (i : Fin (n.len + 1))
    (x : restrictModule R A D.module) :
    transitionBase D n i i x = cechGenerator R A D.module n i x :=
  (transitionGen_diag D n i _).trans (congrArg (cechGenerator R A D.module n i)
    (DescentData.lift_restrictedScalarAction_transition_tmul_one D x))

/-- `transitionGen D n i j` carries multiplication by `1 ⊗ b` to multiplication by `ℓⱼ(b)`. -/
theorem transitionGen_smul_right (n : SimplexCategory) (i j : Fin (n.len + 1)) (b : A)
    (w : A ⊗[R] restrictModule R A D.module) :
    transitionGen D n i j (((1 : A) ⊗ₜ[R] b) • w) =
      cechLeg R A n j (ULift.up b) • transitionGen D n i j w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add w w' hw hw' => rw [smul_add, map_add, hw, hw', map_add, smul_add]
  | tmul c y =>
    rw [targetTensor_smul_tmul, one_mul, transitionGen_tmul, transitionGen_tmul]
    show _ • cechGenerator R A D.module n j (b • y) = _
    rw [cechGenerator_smul, smul_comm]


/-- `M(β) (castDeg z) = castDeg (cechStructureMap D β z)`, for the structure maps `M(β)` of
`descentModule D`. -/
theorem castDeg_map_apply {n m : SimplexCategory} (β : n ⟶ m)
    (z : cechDegreeObj R A D.module n (Fin.last n.len)) :
    (descentModule D).map β.op.op (castDeg D n z) = castDeg D m (cechStructureMap D β z) :=
  ConcreteCategory.congr_hom (castDeg_map D β) z

/-- The cosimplicial module of a descent datum is cartesian. -/
theorem cartesianModules_descentModule : cartesianModules (cechRing R A) (descentModule D) :=
  cartesianModules_of ((descentCartesianModuleFunctor.{u, u, max u w} R A).obj D)

/-- The comparison `N → M_0` from the module of a descent datum to degree zero of its cosimplicial
module, `x ↦ 1 ⊗ x`. -/
noncomputable def descentUnitHom : D.module ⟶ degZeroModule R A (descentModule D) :=
  ModuleCat.ofHom (X := D.module) (Y := degZeroModule R A (descentModule D))
    { toFun := fun x => castDeg D ⦋0⦌ (cechGenerator R A D.module ⦋0⦌ 0 x)
      map_add' := fun x y => (congrArg (castDeg D ⦋0⦌)
        ((cechGenerator R A D.module ⦋0⦌ 0).map_add x y)).trans ((castDeg D ⦋0⦌).hom.map_add _ _)
      map_smul' := fun a x => (congrArg (castDeg D ⦋0⦌)
        (cechGenerator_smul R A D.module ⦋0⦌ 0 a x)).trans
          ((castDeg D ⦋0⦌).hom.map_smul _ _) }

/-- `descentUnitHom D x` is `1 ⊗ x` in degree zero. -/
theorem descentUnitHom_apply (x : D.module) :
    descentUnitHom D x = castDeg D ⦋0⦌ (cechGenerator R A D.module ⦋0⦌ 0 x) := rfl

/-- `w ↦ 1 ⊗ φ(w)` in degree one. -/
noncomputable def descentPsi (w : A ⊗[R] restrictModule R A D.module) :
    (descentModule D).obj (op (op ⦋1⦌)) :=
  castDeg D ⦋1⦌ (transitionGen D ⦋1⦌ 0 1 w)

/-- `psiZero` after `A ⊗ descentUnitHom D` is `descentPsi D`. -/
theorem psiZero_descentUnit (w : A ⊗[R] restrictModule R A D.module) :
    psiZero R A (descentModule D) ((restrictHom R A (descentUnitHom D)).lTensor A w) =
      descentPsi D w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, descentPsi, map_zero, map_zero]
  | add w w' hw hw' => rw [map_add, map_add, hw, hw', descentPsi, descentPsi, descentPsi,
      map_add, map_add]
  | tmul a y =>
    rw [LinearMap.lTensor_tmul, psiZero_tmul, descentPsi, transitionGen_tmul]
    refine (congrArg (fun z => coproj R A 1 0 a • z)
      ((castDeg_map_apply D (SimplexCategory.δ 0) _).trans (congrArg (castDeg D ⦋1⦌)
        ((cechStructureMap_generator R A D (SimplexCategory.δ 0) y).trans
          (transitionBase_diag D ⦋1⦌ 1 y))))).trans ?_
    exact ((castDeg D ⦋1⦌).hom.map_smul _ _).symm

/-- `psiOne` after `descentUnitHom D ⊗ A` is `descentPsi D` after the transition of `D`. -/
theorem psiOne_descentUnit (z : restrictModule R A D.module ⊗[R] A) :
    psiOne R A (descentModule D) ((restrictHom R A (descentUnitHom D)).rTensor A z) =
      descentPsi D (D.transition z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, descentPsi, map_zero, map_zero]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, descentPsi, descentPsi, descentPsi,
      map_add, map_add]
  | tmul y b =>
    have hyb : (y ⊗ₜ[R] b : restrictModule R A D.module ⊗[R] A) =
        ((1 : A) ⊗ₜ[R] b) • (y ⊗ₜ[R] (1 : A)) := by
      rw [sourceTensor_smul_tmul, mul_one]
      congr 1
      exact (LinearMap.congr_fun ((restrictedScalarAction R A D.module).map_one) y).symm
    rw [LinearMap.rTensor_tmul, psiOne_tmul, hyb, map_smul, descentPsi,
      transitionGen_smul_right]
    refine (congrArg (fun z => coproj R A 1 1 b • z)
      ((castDeg_map_apply D (SimplexCategory.δ 1) _).trans (congrArg (castDeg D ⦋1⦌)
        (cechStructureMap_generator R A D (SimplexCategory.δ 1) y)))).trans ?_
    exact ((castDeg D ⦋1⦌).hom.map_smul _ _).symm

/-- **The unit of the equivalence**: a descent datum maps to the descent datum of its
cosimplicial module. -/
noncomputable def descentUnit :
    D ⟶ descentDataOfCartesian R A (descentModule D) (cartesianModules_descentModule D) where
  hom := descentUnitHom D
  comm := LinearMap.ext fun z => injective_psiZero' R A (descentModule D)
    (cartesianModules_descentModule D) <|
    (psiZero_cartesianTransition R A (descentModule D) (cartesianModules_descentModule D) _).trans
      ((psiOne_descentUnit D z).trans (psiZero_descentUnit D _).symm)

/-- `descentUnitHom D : N → M_0` is bijective. -/
theorem bijective_descentUnitHom : Function.Bijective (descentUnitHom D) :=
  (ConcreteCategory.bijective_of_isIso (castDeg D ⦋0⦌)).comp
    (bijective_cechGenerator_zero D.module)

/-- `descentUnit D` is an isomorphism of descent data. -/
instance isIso_descentUnit : IsIso (descentUnit D) :=
  DescentData.isIso_of_bijective _ (bijective_descentUnitHom D)


/-- `castDeg` is natural in the descent datum. -/
theorem castDeg_naturality {D E : DescentData.{u, u, max u w} R A} (g : D ⟶ E)
    (n : SimplexCategory) :
    castDeg D n ≫ ((descentCosimplicialModuleFunctor.{u, u, max u w} R A).map g).app (op (op n)) =
      cechDegreeMap R A g n (Fin.last n.len) ≫ castDeg E n := by
  rw [descentCosimplicialModuleFunctor_map_hom]
  exact (eqToHom_trans_assoc _ _ _).trans
    ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _))

/-- `descentUnit` is natural in the descent datum. -/
theorem descentUnit_naturality {D E : DescentData.{u, u, max u w} R A} (g : D ⟶ E) :
    g ≫ descentUnit E = descentUnit D ≫ (cartesianDescentDataFunctor.{u, w} R A).map
      ((descentCartesianModuleFunctor.{u, u, max u w} R A).map g) := by
  refine DescentData.Hom.ext (ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  show castDeg E ⦋0⦌ (cechGenerator R A E.module ⦋0⦌ 0 (g.hom x)) =
    ((descentCosimplicialModuleFunctor.{u, u, max u w} R A).map g).app (op (op ⦋0⦌))
      (castDeg D ⦋0⦌ (cechGenerator R A D.module ⦋0⦌ 0 x))
  refine Eq.trans ?_ (ConcreteCategory.congr_hom (castDeg_naturality g ⦋0⦌) _).symm
  refine congrArg (castDeg E ⦋0⦌) ?_
  exact (cechGenerator_eq_tmul R A E.module ⦋0⦌ 0 _).trans
    ((ModuleCat.ExtendScalars.map_tmul (cechLeg R A ⦋0⦌ 0)
        ((ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom).map
          ((ModuleCat.uliftFunctor.{u, max u w, u} A).map g.hom)) 1 (ULift.up x)).symm.trans
      (congrArg (cechDegreeMap R A g ⦋0⦌ 0) (cechGenerator_eq_tmul R A D.module ⦋0⦌ 0 x).symm))

variable (R A) in
/-- The descent datum of the cosimplicial module of a descent datum is the descent datum itself,
naturally. -/
noncomputable def descentUnitIso :
    𝟭 (DescentData.{u, u, max u w} R A) ≅
      descentCartesianModuleFunctor.{u, u, max u w} R A ⋙ cartesianDescentDataFunctor.{u, w} R A :=
  NatIso.ofComponents (fun D => @asIso _ _ _ _ (descentUnit D) (isIso_descentUnit D))
    (fun g => descentUnit_naturality g)

variable (R A)

/-- The functor `cartesianDescentDataFunctor` is essentially surjective. -/
instance : (cartesianDescentDataFunctor.{u, w} R A).EssSurj where
  mem_essImage D :=
    ⟨(descentCartesianModuleFunctor.{u, u, max u w} R A).obj D,
      ⟨(@asIso _ _ _ _ (descentUnit D) (isIso_descentUnit D)).symm⟩⟩

/-- The functor `cartesianDescentDataFunctor` is an equivalence. -/
instance : (cartesianDescentDataFunctor.{u, w} R A).IsEquivalence where

/-- The functor from cartesian `(A / R)_•`-modules to descent data is an equivalence. -/
noncomputable def cartesianCechModuleEquivDescentData :
    CartesianCechModule.{u, u, w} R A ≌ DescentData.{u, u, max u w} R A :=
  (cartesianDescentDataFunctor.{u, w} R A).asEquivalence

/-- The cosimplicial module of a descent datum is an equivalence onto the cartesian modules. -/
instance isEquivalence_descentCartesianModuleFunctor :
    (descentCartesianModuleFunctor.{u, u, max u w} R A).IsEquivalence :=
  have e : descentCartesianModuleFunctor.{u, u, max u w} R A ≅
      (cartesianCechModuleEquivDescentData.{u, w} R A).inverse :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ (cartesianCechModuleEquivDescentData.{u, w} R A).unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (descentUnitIso R A).symm _ ≪≫ Functor.leftUnitor _
  @Functor.isEquivalence_of_iso _ _ _ _ _ _ e.symm
    (cartesianCechModuleEquivDescentData.{u, w} R A).isEquivalence_inverse

/-- Let `A` be an `R`-algebra.  Descent data for `A / R` correspond to cartesian
`(A / R)_•`-modules: the functor `(N, φ) ↦ N_•`, sending a descent datum to its cosimplicial
module over the Čech algebra `(A / R)_•` (`N_n = N_{n, n}`, `N_•(β) = φᵐ_{β(n), m} ∘ N_{β, n}`),
is an equivalence of categories between descent data and cartesian `(A / R)_•`-modules.  Its
inverse sends a cartesian module `M` to `M_0` with the transition `M_0 ⊗_R A ≅ M_1 ≅ A ⊗_R M_0`
read off from the cartesian isomorphisms along the two cofaces `⦋0⦌ ⟶ ⦋1⦌`
(`ModuleCat.cartesianDescentDataFunctor`).  No flatness is assumed. -/
@[stacks 039Y "(2): descent data for `A / R` correspond to cartesian `(A / R)_•`-modules, \
  through the cosimplicial module of a descent datum of Stacks 023H"]
noncomputable def descentDataEquivCartesianCechModule :
    DescentData.{u, u, max u w} R A ≌ CartesianCechModule.{u, u, max u w} R A :=
  (descentCartesianModuleFunctor.{u, u, max u w} R A).asEquivalence

end EssSurj

end ModuleCat

end
