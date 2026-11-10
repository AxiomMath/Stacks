module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.LinearAlgebra.Span.TensorProduct
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.Pairing

/-!
# Changing the finite algebra in a relative dualizing module

Let `A → B` be a quasi-finite map of Noetherian rings and let `A → B' → B` be a finite-open
factorization, so that the relative dualizing module is `ω = Hom_A(B', A) ⊗_{B'} B`. This file
shows that enlarging `B'` inside `B` does not change `ω`: if `B' → D` is a map to a finite
`A`-algebra `D` that embeds in `B` and is compatible with the maps to `B`, then
`Hom_A(D, A) ⊗_D B` and `ω` are canonically isomorphic as `B`-modules.

The mechanism is a pushout. Flatness of `B` over `B'` and the fact that `B' → B` is a ring
epimorphism force `B ⊗_{B'} D ≅ B`, and the dual of `D` over `A` is computed from the dual of
`B'` by the adjunction between restriction of scalars and the `B'`-linear dual.

## Main definitions

* `Stacks.Discriminant.dualRestrictLinear` restricts an `A`-linear functional along an algebra
  map, as a linear map over the smaller algebra.
* `Stacks.Discriminant.dualHomModule` is the module structure of an algebra on the linear maps
  out of it.
* `Stacks.Discriminant.dualAdjunction` identifies the `A`-linear dual of `C` with the `F`-linear
  maps from `C` to the `A`-linear dual of `F`.
* `Stacks.Discriminant.dualizingModule_commonChange` compares the two scalar extensions across
  a pushout square.
* `Stacks.Discriminant.finiteAlgebraChangeToF` and
  `Stacks.Discriminant.finiteSubalgebraChangeToF` are the resulting comparisons with the
  relative dualizing module.

## Main results

* `Stacks.Discriminant.finiteOpenFactorization_flat`: the target of a finite-open factorization
  is flat over the intermediate algebra.
* `Stacks.Discriminant.isPushout_of_flat_epi_of_injective`: a flat epimorphism makes every
  intermediate algebra embedded in the target into a pushout square.
* `Stacks.Discriminant.dualRestrictLinear_apply`: restriction of a functional is evaluation
  after the algebra map.
* `Stacks.Discriminant.finiteSubalgebraChangeToF_tmul`: the comparison is determined on pure
  tensors by restricting the functional.

## Implementation notes

The `B'`-module structure on `Hom_A(B', A)` is `Stacks.Discriminant.algebraDualModule`, which is
not a global instance; every statement that needs it supplies it with `letI`, as the
construction of `Stacks.Discriminant.dualizingModule` does.

## References

* [Stacks Project, Tag 0BT1](https://stacks.math.columbia.edu/tag/0BT1)
-/

@[expose] public section

universe u v w x y

namespace Stacks.Discriminant

open scoped TensorProduct

/-- Restriction of `A`-linear functionals along an `A`-algebra map `r : F →ₐ[A] H`, as an
`F`-linear map for the natural actions of `F` and `H` on their duals. -/
def dualRestrictLinear
    {A F H : Type*} [CommRing A] [CommRing F] [CommRing H]
    [Algebra A F] [Algebra A H] (r : F →ₐ[A] H) :
    letI : Module H (Module.Dual A H) := algebraDualModule A H
    letI : Module F (Module.Dual A H) := Module.compHom (Module.Dual A H) r.toRingHom
    letI : Module F (Module.Dual A F) := algebraDualModule A F
    Module.Dual A H →ₗ[F] Module.Dual A F := by
  let : Module H (Module.Dual A H) := algebraDualModule A H
  let : Module F (Module.Dual A H) := Module.compHom (Module.Dual A H) r.toRingHom
  let : Module F (Module.Dual A F) := algebraDualModule A F
  refine { toFun := fun φ => φ.comp r.toLinearMap, map_add' := ?_, map_smul' := ?_ }
  · intro φ ψ
    ext z
    rfl
  · intro c φ
    ext z
    rw [algebraDualModule_smul_apply]
    change φ (r c * r z) = φ (r (c * z))
    exact congrArg φ (map_mul r c z).symm

/-- Restriction of functionals is evaluation after the algebra map. -/
theorem dualRestrictLinear_apply
    {A F H : Type*} [CommRing A] [CommRing F] [CommRing H]
    [Algebra A F] [Algebra A H] (r : F →ₐ[A] H)
    (φ : Module.Dual A H) (z : F) :
    dualRestrictLinear r φ z = φ (r z) := rfl

/-- Restriction of functionals along a composite of algebra maps is the composite of the
restrictions, in the reverse order. -/
theorem dualRestrictLinear_comp
    {A F H K : Type*} [CommRing A] [CommRing F] [CommRing H] [CommRing K]
    [Algebra A F] [Algebra A H] [Algebra A K]
    (r : F →ₐ[A] H) (s : H →ₐ[A] K) (φ : Module.Dual A K) :
    dualRestrictLinear r (dualRestrictLinear s φ) =
      dualRestrictLinear (s.comp r) φ := by
  ext z
  rfl

/-- The module structure of a commutative algebra `C` on the `F`-linear maps out of `C`,
given by precomposition with multiplication. -/
@[instance_reducible]
def dualHomModule
    {F C M : Type*} [CommRing F] [CommRing C] [AddCommGroup M]
    [Algebra F C] [Module F M] : Module C (C →ₗ[F] M) where
  smul c f := f.comp (Algebra.lmul F C c)
  one_smul f := by ext c; change f (1 * c) = f c; rw [one_mul]
  mul_smul a b f := by
    ext c
    change f ((a * b) * c) = f (b * (a * c))
    congr 1; ac_rfl
  smul_zero c := by ext x; change (0 : M) = 0; rfl
  smul_add c f g := by ext x; rfl
  add_smul a b f := by
    ext x
    change f ((a + b) * x) = f (a * x) + f (b * x)
    rw [add_mul, map_add]
  zero_smul f := by ext x; change f (0 * x) = 0; rw [zero_mul, map_zero]

/-- Evaluation characterizes the action of `C` on the `F`-linear maps out of `C`. -/
theorem dualHomModule_smul_apply
    {F C M : Type*} [CommRing F] [CommRing C] [AddCommGroup M]
    [Algebra F C] [Module F M] (c : C) (f : C →ₗ[F] M) (x : C) :
    letI : Module C (C →ₗ[F] M) := dualHomModule
    (c • f) x = f (c * x) := rfl

/-- For a tower `A → F → C`, the `A`-linear dual of `C` is the module of `F`-linear maps from
`C` to the `A`-linear dual of `F`. This is the adjunction between restriction of scalars along
`F → C` and the `F`-linear dual. -/
noncomputable def dualAdjunction
    {A F C : Type*} [CommRing A] [CommRing F] [CommRing C]
    [Algebra A F] [Algebra A C] [Algebra F C] [IsScalarTower A F C] :
    letI : Module C (Module.Dual A C) := algebraDualModule A C
    letI : Module F (Module.Dual A F) := algebraDualModule A F
    letI : Module C (C →ₗ[F] Module.Dual A F) := dualHomModule
    Module.Dual A C ≃ₗ[C] (C →ₗ[F] Module.Dual A F) := by
  let : Module C (Module.Dual A C) := algebraDualModule A C
  let : Module F (Module.Dual A F) := algebraDualModule A F
  let : Module C (C →ₗ[F] Module.Dual A F) := dualHomModule
  let adj : Module.Dual A C → C →ₗ[F] Module.Dual A F := fun φ =>
    { toFun := fun c =>
        { toFun := fun a => φ (c * algebraMap F C a)
          map_add' := by intro a b; simp [map_add, mul_add]
          map_smul' := by
            intro a x
            simp only [Algebra.smul_def]
            change φ (c * algebraMap F C (algebraMap A F a * x)) =
              algebraMap A A a * φ (c * algebraMap F C x)
            rw [map_mul (algebraMap F C)]
            have hmap : algebraMap F C (algebraMap A F a) = algebraMap A C a :=
              congrArg (fun f : A →+* C => f a) (IsScalarTower.algebraMap_eq A F C).symm
            rw [hmap]
            calc
              φ (c * (algebraMap A C a * algebraMap F C x)) =
                  φ (algebraMap A C a * (c * algebraMap F C x)) := by congr 1; ring
              _ = algebraMap A A a * φ (c * algebraMap F C x) := by
                  have hs := φ.map_smul a (c * algebraMap F C x)
                  simpa [Algebra.smul_def] using hs }
      map_add' := by
        intro c d
        ext x
        simp [map_add, add_mul]
      map_smul' := by
        intro b c
        ext x
        simp only [Algebra.smul_def]
        change φ ((algebraMap F C b * c) * algebraMap F C x) =
          φ (c * algebraMap F C (b * x))
        simp only [map_mul]
        congr 1; ring }
  let unadj : (C →ₗ[F] Module.Dual A F) → Module.Dual A C := fun ψ =>
    { toFun := fun c => ψ c 1
      map_add' := by intro c d; exact congrArg (fun f : Module.Dual A F => f 1) (ψ.map_add c d)
      map_smul' := by
        intro a c
        simp only [Algebra.smul_def]
        have hs := congrArg (fun f : Module.Dual A F => f 1) (ψ.map_smul (algebraMap A F a) c)
        have hA := (ψ c).map_smul a (1 : F)
        have hcomp : algebraMap F C (algebraMap A F a) = algebraMap A C a :=
          congrArg (fun f : A →+* C => f a) (IsScalarTower.algebraMap_eq A F C).symm
        rw [Algebra.smul_def, hcomp, algebraDualModule_smul_apply] at hs
        change ψ (algebraMap A C a * c) 1 = algebraMap A A a * ψ c 1
        have hA' : ψ c (algebraMap A F a * 1) = algebraMap A A a * ψ c 1 := by
          simpa [Algebra.smul_def] using hA
        rw [← hA']
        exact hs }
  let L : Module.Dual A C →ₗ[C] (C →ₗ[F] Module.Dual A F) :=
    { toFun := adj
      map_add' := by
        intro φ ψ
        change adj (φ + ψ) = adj φ + adj ψ
        apply LinearMap.ext
        intro c
        apply LinearMap.ext
        intro a
        rfl
      map_smul' := by
        intro d φ
        change adj (d • φ) = d • adj φ
        apply LinearMap.ext
        intro c
        apply LinearMap.ext
        intro a
        change φ (d * (c * algebraMap F C a)) = φ ((d * c) * algebraMap F C a)
        congr 1; ring }
  apply LinearEquiv.ofBijective L
  constructor
  · intro φ ψ h
    apply LinearMap.ext
    intro c
    have h' := congrArg (fun f : C →ₗ[F] Module.Dual A F => f c) h
    have hz := congrArg (fun f : Module.Dual A F => f 1) h'
    simpa [L, adj] using hz
  · intro ψ
    refine ⟨unadj ψ, ?_⟩
    dsimp [L, adj, unadj]
    apply LinearMap.ext
    intro c
    apply LinearMap.ext
    intro a
    have hs := congrArg (fun f : Module.Dual A F => f 1) (ψ.map_smul a c)
    calc
      ψ (c * algebraMap F C a) 1 = ψ (algebraMap F C a * c) 1 := by rw [mul_comm c]
      _ = ψ c a := by simpa [Algebra.smul_def, algebraDualModule_smul_apply] using hs


/-- The adjunction evaluated at `1` is restriction of functionals along `F → C`. -/
theorem dualAdjunction_apply_one
    {A F C : Type*} [CommRing A] [CommRing F] [CommRing C]
    [Algebra A F] [Algebra A C] [Algebra F C] [IsScalarTower A F C]
    (φ : Module.Dual A C) :
    letI : Module F (Module.Dual A F) := algebraDualModule A F
    letI : Module C (Module.Dual A C) := algebraDualModule A C
    letI : Module C (C →ₗ[F] Module.Dual A F) := dualHomModule
    (dualAdjunction (A := A) (F := F) (C := C) φ) 1 =
      dualRestrictLinear (IsScalarTower.toAlgHom A F C) φ := by
  let : Module F (Module.Dual A F) := algebraDualModule A F
  let : Module C (Module.Dual A C) := algebraDualModule A C
  let : Module C (C →ₗ[F] Module.Dual A F) := dualHomModule
  ext a
  change φ ((1 : C) * algebraMap F C a) = φ (algebraMap F C a)
  simp

/-- The target of a finite-open factorization is flat over the intermediate algebra: the
induced morphism of spectra is an open immersion, hence flat. -/
theorem finiteOpenFactorization_flat
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) : Module.Flat F.middle B := by
  let f : F.middle →+* B := algebraMap F.middle B
  let fU : ULift.{max v w} F.middle →+* ULift.{max v w} B :=
    f.ulift.{max v w, max v w}
  have hOpen := specMap_ulift_isOpenImmersion f
    F.isOpenEmbedding_comap F.awayMap_bijective
  let schemeMap := AlgebraicGeometry.Spec.map (CommRingCat.ofHom fU)
  have hFlatScheme : AlgebraicGeometry.Flat schemeMap := inferInstance
  have hFlatRing : RingHom.Flat fU :=
    (AlgebraicGeometry.Flat.SpecMap_iff (f := CommRingCat.ofHom fU)).mp hFlatScheme
  have hf : RingHom.Flat f := (RingHom.Flat.ulift_iff (f := f)).mp hFlatRing
  exact (RingHom.flat_algebraMap_iff (R := F.middle) (S := B)).mp hf

/-- If `B` is flat over `F` and `F → B` is a ring epimorphism, then any intermediate algebra
`C` with `C → B` injective makes `B ⊗_F C ≅ B`, that is, the square `F → B`, `F → C`, `C → B`
is a pushout. -/
theorem isPushout_of_flat_epi_of_injective
    {F B C : Type*} [CommRing F] [CommRing B] [CommRing C]
    [Algebra F B] [Algebra F C] [Algebra C B] [IsScalarTower F C B]
    [Module.Flat F B] [Algebra.IsEpi F B]
    (hinj : Function.Injective (algebraMap C B)) :
    Algebra.IsPushout F B C B := by
  let i : C →ₐ[F] B := IsScalarTower.toAlgHom F C B
  let P : Submodule F B := i.toLinearMap.range
  let eP : C ≃ₗ[F] P :=
    LinearEquiv.ofBijective i.toLinearMap.rangeRestrict
      ⟨fun x y h => hinj (Subtype.ext_iff.mp h), fun x => by
        obtain ⟨c, hc⟩ := x.property
        exact ⟨c, Subtype.ext hc⟩⟩
  let eAdd := TensorProduct.congr (LinearEquiv.refl F B) eP
  let eTensor : B ⊗[F] C ≃ₗ[B] B ⊗[F] P :=
    eAdd.toAddEquiv.toLinearEquiv (by
      intro b z
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy, smul_add]
      | tmul x y => simp [eAdd, TensorProduct.smul_tmul'])
  let eSpan : B ⊗[F] P ≃ₗ[B] Submodule.span B (P : Set B) := P.tensorEquivSpan B
  have hspan : Submodule.span B (P : Set B) = ⊤ := by
    apply Submodule.eq_top_iff'.2
    intro b
    rw [← mul_one b]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨1, by simp [i]⟩
  let e : B ⊗[F] C ≃ₗ[B] B :=
    eTensor.trans (eSpan.trans ((LinearEquiv.ofEq _ _ hspan).trans Submodule.topEquiv))
  have he (c : C) : e (1 ⊗ₜ[F] c) = algebraMap C B c := by
    simp [e, eTensor, eSpan, eAdd, P, i,
      Submodule.tensorEquivSpan_apply_tmul]
    rfl
  exact Algebra.IsPushout.mk (IsBaseChange.of_equiv e (fun c => he c))

/-- Base change of the dual along a pushout square: for a tower `A → F → C` with `C` finitely
presented over `F`, `B` flat over `F`, and `B ⊗_F C ≅ B`, the dual of `C` and the dual of `F`
induce the same `B`-module after scalar extension. -/
noncomputable def dualizingModule_commonChange
    {A F C B : Type*} [CommRing A] [CommRing F] [CommRing C] [CommRing B]
    [Algebra A F] [Algebra A C] [Algebra A B] [Algebra F C] [Algebra F B] [Algebra C B]
    [IsScalarTower A F C] [IsScalarTower A F B] [IsScalarTower F C B]
    [Module.Flat F B] [Module.FinitePresentation F C]
    (hpush : Algebra.IsPushout F B C B) :
    letI : Module F (Module.Dual A F) := algebraDualModule A F
    letI : Module C (Module.Dual A C) := algebraDualModule A C
    letI : Module C (C →ₗ[F] Module.Dual A F) := dualHomModule
    letI : Module B (Module.Dual A C ⊗[C] B) :=
      (TensorProduct.comm C (Module.Dual A C) B).toAddEquiv.module B
    letI : Module B (Module.Dual A F ⊗[F] B) :=
      (TensorProduct.comm F (Module.Dual A F) B).toAddEquiv.module B
    (Module.Dual A C ⊗[C] B) ≃ₗ[B] (Module.Dual A F ⊗[F] B) := by
  let : Module F (Module.Dual A F) := algebraDualModule A F
  let : Module C (Module.Dual A C) := algebraDualModule A C
  let : Module C (C →ₗ[F] Module.Dual A F) := dualHomModule
  let : IsScalarTower F C (C →ₗ[F] Module.Dual A F) := ⟨by
    intro f c ψ
    ext z x
    simp only [LinearMap.smul_apply, dualHomModule_smul_apply]
    calc
      ψ ((f • c) * z) x = ψ (f • (c * z)) x := by
        congr 2
        simp only [Algebra.smul_def]
        ring
      _ = (f • ψ (c * z)) x :=
        congrArg (fun φ : Module.Dual A F => φ x) (ψ.map_smul f (c * z))
      _ = ψ (c * z) (f * x) := by simp [algebraDualModule_smul_apply]⟩
  let : Module B (Module.Dual A C ⊗[C] B) :=
    (TensorProduct.comm C (Module.Dual A C) B).toAddEquiv.module B
  let : Module B (Module.Dual A F ⊗[F] B) :=
    (TensorProduct.comm F (Module.Dual A F) B).toAddEquiv.module B
  let adj := dualAdjunction (A := A) (F := F) (C := C)
  let eSwap₁ : Module.Dual A C ⊗[C] B ≃ₗ[B] B ⊗[C] Module.Dual A C :=
    (TensorProduct.comm C (Module.Dual A C) B).toAddEquiv.toLinearEquiv (by
      intro b z
      change (TensorProduct.comm C (Module.Dual A C) B).toAddEquiv
        ((TensorProduct.comm C (Module.Dual A C) B).toAddEquiv.symm
          (b • (TensorProduct.comm C (Module.Dual A C) B).toAddEquiv z)) = _
      simp)
  let eAdj : B ⊗[C] Module.Dual A C ≃ₗ[B] B ⊗[C] (C →ₗ[F] Module.Dual A F) :=
    (TensorProduct.congr (LinearEquiv.refl C B) adj).toAddEquiv.toLinearEquiv (by
      intro b z
      induction z using TensorProduct.inductionOn with
      | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂, smul_add]
      | tmul c φ => simp [TensorProduct.smul_tmul'])
  let : Algebra.IsPushout F B C B := hpush
  let eCancel : B ⊗[C] (C →ₗ[F] Module.Dual A F) ≃ₗ[B]
      B ⊗[F] (C →ₗ[F] Module.Dual A F) :=
    Algebra.IsPushout.cancelBaseChange F B C B (C →ₗ[F] Module.Dual A F)
  let hBC : IsBaseChange B (LinearMap.baseChangeHom F B C (Module.Dual A F)) :=
    Module.FinitePresentation.isBaseChange_map F C (Module.Dual A F) B
  let eBase : B ⊗[F] (C →ₗ[F] Module.Dual A F) ≃ₗ[B]
      ((B ⊗[F] C) →ₗ[B] (B ⊗[F] Module.Dual A F)) :=
    hBC.equiv
  let ePush : B ⊗[F] C ≃ₐ[B] B := Algebra.IsPushout.equiv F B C B
  let eArrow : ((B ⊗[F] C) →ₗ[B] (B ⊗[F] Module.Dual A F)) ≃ₗ[B]
      (B →ₗ[B] (B ⊗[F] Module.Dual A F)) :=
    LinearEquiv.arrowCongr ePush.toLinearEquiv (LinearEquiv.refl B (B ⊗[F] Module.Dual A F))
  let eEval : (B →ₗ[B] (B ⊗[F] Module.Dual A F)) ≃ₗ[B]
      (B ⊗[F] Module.Dual A F) :=
    { toFun := fun f => f 1
      invFun := fun m =>
        { toFun := fun b => b • m
          map_add' := fun _ _ => add_smul _ _ _
          map_smul' := fun _ _ => mul_smul _ _ _ }
      left_inv := by
        intro f
        refine LinearMap.ext fun b => ?_
        simpa using (f.map_smul b (1 : B)).symm
      right_inv := by intro m; simp
      map_add' := by intro f g; rfl
      map_smul' := by intro b f; rfl }
  let eSwap₂ : B ⊗[F] Module.Dual A F ≃ₗ[B] Module.Dual A F ⊗[F] B :=
    (TensorProduct.comm F (Module.Dual A F) B).symm.toAddEquiv.toLinearEquiv (by
      intro b z
      change (TensorProduct.comm F (Module.Dual A F) B).symm.toAddEquiv (b • z) =
        (TensorProduct.comm F (Module.Dual A F) B).symm.toAddEquiv
          (b • (TensorProduct.comm F (Module.Dual A F) B).toAddEquiv
            ((TensorProduct.comm F (Module.Dual A F) B).symm.toAddEquiv z))
      simp)
  exact eSwap₁.trans (eAdj.trans (eCancel.trans (eBase.trans (eArrow.trans (eEval.trans eSwap₂)))))

/-- The comparison of scalar extensions carries a pure tensor to the pure tensor of the
restricted functional. -/
theorem dualizingModule_commonChange_tmul
    {A F C B : Type*} [CommRing A] [CommRing F] [CommRing C] [CommRing B]
    [Algebra A F] [Algebra A C] [Algebra A B] [Algebra F C] [Algebra F B] [Algebra C B]
    [IsScalarTower A F C] [IsScalarTower A F B] [IsScalarTower F C B]
    [Module.Flat F B] [Module.FinitePresentation F C]
    (hpush : Algebra.IsPushout F B C B) (φ : Module.Dual A C) (b : B) :
    letI : Module F (Module.Dual A F) := algebraDualModule A F
    letI : Module C (Module.Dual A C) := algebraDualModule A C
    letI : Module C (C →ₗ[F] Module.Dual A F) := dualHomModule
    letI : Module B (Module.Dual A C ⊗[C] B) :=
      (TensorProduct.comm C (Module.Dual A C) B).toAddEquiv.module B
    letI : Module B (Module.Dual A F ⊗[F] B) :=
      (TensorProduct.comm F (Module.Dual A F) B).toAddEquiv.module B
    dualizingModule_commonChange hpush (φ ⊗ₜ[C] b) =
      dualRestrictLinear (IsScalarTower.toAlgHom A F C) φ ⊗ₜ[F] b := by
  let : Module F (Module.Dual A F) := algebraDualModule A F
  let : Module C (Module.Dual A C) := algebraDualModule A C
  let : Module C (C →ₗ[F] Module.Dual A F) := dualHomModule
  let : Module B (Module.Dual A C ⊗[C] B) :=
    (TensorProduct.comm C (Module.Dual A C) B).toAddEquiv.module B
  let : Module B (Module.Dual A F ⊗[F] B) :=
    (TensorProduct.comm F (Module.Dual A F) B).toAddEquiv.module B
  classical
  let e : Module.Dual A C ⊗[C] B ≃ₗ[B] Module.Dual A F ⊗[F] B :=
    dualizingModule_commonChange hpush
  have hsmul : φ ⊗ₜ[C] b = b • (φ ⊗ₜ[C] (1 : B)) := by
    apply (TensorProduct.comm C (Module.Dual A C) B).toAddEquiv.injective
    simpa [Equiv.smul_def] using (TensorProduct.smul_tmul' (R := C) (R' := B) (M := B)
      (N := Module.Dual A C) b (1 : B) φ).symm
  have hone : e (φ ⊗ₜ[C] (1 : B)) =
      dualRestrictLinear (IsScalarTower.toAlgHom A F C) φ ⊗ₜ[F] (1 : B) := by
    simp [e, dualizingModule_commonChange, dualRestrictLinear,
      LinearEquiv.trans_apply, Algebra.IsPushout.cancelBaseChange_tmul,
      IsBaseChange.equiv_tmul, LinearMap.baseChange_tmul,
      Algebra.TensorProduct.one_def, dualAdjunction_apply_one]
  calc
    e (φ ⊗ₜ[C] b) = e (b • (φ ⊗ₜ[C] (1 : B))) := congrArg e hsmul
    _ = b • e (φ ⊗ₜ[C] (1 : B)) := map_smul e b _
    _ = dualRestrictLinear (IsScalarTower.toAlgHom A F C) φ ⊗ₜ[F] b := by
      rw [hone]
      apply (TensorProduct.comm F (Module.Dual A F) B).toAddEquiv.injective
      change b • (TensorProduct.comm F (Module.Dual A F) B).toAddEquiv
        (dualRestrictLinear (IsScalarTower.toAlgHom A F C) φ ⊗ₜ[F] (1 : B)) = _
      simpa [Equiv.smul_def] using
        TensorProduct.smul_tmul' (R := F) (R' := B) (M := B)
          (N := Module.Dual A F) b (1 : B)
          (dualRestrictLinear (IsScalarTower.toAlgHom A F C) φ)

/-- The target of a finite-open factorization is a pushout over the middle algebra with any
algebra `D` over the middle algebra that embeds in the target. -/
private theorem isPushout_middle_of_injective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    {D : Type*} [CommRing D] [Algebra D B] [Algebra F.middle D] [IsScalarTower F.middle D B]
    (hinj : Function.Injective (algebraMap D B)) :
    Algebra.IsPushout F.middle B D B := by
  have := finiteOpenFactorization_flat F
  have := isEpi_of_finiteOpenFactorization F
  exact isPushout_of_flat_epi_of_injective hinj

/-- A finite `A`-algebra over the middle algebra of a finite-open factorization is finitely
presented over it. -/
private theorem finitePresentation_middle
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    {D : Type*} [CommRing D] [Algebra A D] [Algebra F.middle D] [IsScalarTower A F.middle D]
    (hfin : Module.Finite A D) : Module.FinitePresentation F.middle D := by
  have := Module.Finite.of_restrictScalars_finite A F.middle D
  have := IsNoetherianRing.of_finite A F.middle
  exact Module.finitePresentation_of_finite F.middle D

/-- Computing the relative dualizing module of `F` through a larger finite algebra `D` that
embeds in the target gives the same `B`-module. -/
noncomputable def finiteAlgebraChangeToF
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    {D : Type*} [CommRing D] [Algebra A D] [Algebra D B]
    [IsScalarTower A D B]
    (hfin : Module.Finite A D) (r : F.middle →ₐ[A] D)
    (hcomp : (IsScalarTower.toAlgHom A D B).comp r =
      IsScalarTower.toAlgHom A F.middle B)
    (hinj : Function.Injective (algebraMap D B)) :
    letI : Algebra F.middle D := r.toAlgebra
    letI : IsScalarTower A F.middle D := IsScalarTower.of_algebraMap_eq' (by
      ext a
      change algebraMap A D a = r (algebraMap A F.middle a)
      exact (r.commutes a).symm)
    letI : IsScalarTower F.middle D B := IsScalarTower.of_algebraMap_eq (by
      intro a
      have hh := congrArg (fun f : F.middle →ₐ[A] B => f a) hcomp
      change algebraMap F.middle B a = algebraMap D B (r a)
      exact hh.symm)
    letI : Module D (Module.Dual A D) := algebraDualModule A D
    letI : Module B (Module.Dual A D ⊗[D] B) :=
      (TensorProduct.comm D (Module.Dual A D) B).toAddEquiv.module B
    Module.Dual A D ⊗[D] B ≃ₗ[B] dualizingModule F := by
  let : Algebra F.middle D := r.toAlgebra
  let : IsScalarTower A F.middle D := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change algebraMap A D a = r (algebraMap A F.middle a)
    exact (r.commutes a).symm)
  let : IsScalarTower F.middle D B := IsScalarTower.of_algebraMap_eq (by
    intro a
    have hh := congrArg (fun f : F.middle →ₐ[A] B => f a) hcomp
    change algebraMap F.middle B a = algebraMap D B (r a)
    exact hh.symm)
  let : Module.Flat F.middle B := finiteOpenFactorization_flat F
  let : Algebra.IsEpi F.middle B := isEpi_of_finiteOpenFactorization F
  let : Module.Finite A D := hfin
  let : Module.Finite F.middle D :=
    Module.Finite.of_restrictScalars_finite A F.middle D
  let : IsNoetherianRing F.middle := IsNoetherianRing.of_finite A F.middle
  let : Module.FinitePresentation F.middle D :=
    Module.finitePresentation_of_finite F.middle D
  have hTower : IsScalarTower F.middle D B := inferInstance
  let : IsScalarTower F.middle D B := hTower
  have hpush : Algebra.IsPushout F.middle B D B := by
    let : IsScalarTower F.middle D B := hTower
    exact @isPushout_of_flat_epi_of_injective F.middle B D
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      hTower inferInstance inferInstance hinj
  exact @dualizingModule_commonChange A F.middle D B
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    inferInstance inferInstance hTower
    inferInstance inferInstance hpush

/-- The comparison through a larger finite algebra carries a pure tensor to the pure tensor of
the restricted functional. -/
theorem finiteAlgebraChangeToF_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    {D : Type*} [CommRing D] [Algebra A D] [Algebra D B]
    [IsScalarTower A D B]
    (hfin : Module.Finite A D) (r : F.middle →ₐ[A] D)
    (hcomp : (IsScalarTower.toAlgHom A D B).comp r =
      IsScalarTower.toAlgHom A F.middle B)
    (hinj : Function.Injective (algebraMap D B))
    (φ : Module.Dual A D) (b : B) :
    letI : Algebra F.middle D := r.toAlgebra
    letI : IsScalarTower A F.middle D := IsScalarTower.of_algebraMap_eq' (by
      ext a
      change algebraMap A D a = r (algebraMap A F.middle a)
      exact (r.commutes a).symm)
    letI : IsScalarTower F.middle D B := IsScalarTower.of_algebraMap_eq (by
      intro a
      have hh := congrArg (fun f : F.middle →ₐ[A] B => f a) hcomp
      change algebraMap F.middle B a = algebraMap D B (r a)
      exact hh.symm)
    letI : Module F.middle (Module.Dual A F.middle) := algebraDualModule A F.middle
    letI : Module D (Module.Dual A D) := algebraDualModule A D
    letI : Module D (D →ₗ[F.middle] Module.Dual A F.middle) := dualHomModule
    letI : Module B (Module.Dual A D ⊗[D] B) :=
      (TensorProduct.comm D (Module.Dual A D) B).toAddEquiv.module B
    letI : Module B (Module.Dual A F.middle ⊗[F.middle] B) :=
      (TensorProduct.comm F.middle (Module.Dual A F.middle) B).toAddEquiv.module B
    finiteAlgebraChangeToF F hfin r hcomp hinj (φ ⊗ₜ[D] b) =
      dualRestrictLinear (IsScalarTower.toAlgHom A F.middle D) φ ⊗ₜ[F.middle] b := by
  let : Algebra F.middle D := r.toAlgebra
  let : IsScalarTower A F.middle D := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change algebraMap A D a = r (algebraMap A F.middle a)
    exact (r.commutes a).symm)
  let : IsScalarTower F.middle D B := IsScalarTower.of_algebraMap_eq (by
    intro a
    have hh := congrArg (fun f : F.middle →ₐ[A] B => f a) hcomp
    change algebraMap F.middle B a = algebraMap D B (r a)
    exact hh.symm)
  let : Module F.middle (Module.Dual A F.middle) := algebraDualModule A F.middle
  let : Module D (Module.Dual A D) := algebraDualModule A D
  let : Module D (D →ₗ[F.middle] Module.Dual A F.middle) := dualHomModule
  let : Module B (Module.Dual A D ⊗[D] B) :=
    (TensorProduct.comm D (Module.Dual A D) B).toAddEquiv.module B
  let : Module B (Module.Dual A F.middle ⊗[F.middle] B) :=
    (TensorProduct.comm F.middle (Module.Dual A F.middle) B).toAddEquiv.module B
  have := finiteOpenFactorization_flat F
  have := finitePresentation_middle F hfin
  exact dualizingModule_commonChange_tmul (isPushout_middle_of_injective F hinj) φ b

/-- The comparison of `finiteAlgebraChangeToF` for a finite subalgebra of the target. -/
noncomputable def finiteSubalgebraChangeToF
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (C : Subalgebra A B) (r : F.middle →ₐ[A] C)
    (hcomp : C.val.comp r = IsScalarTower.toAlgHom A F.middle B)
    (hfin : Module.Finite A C) :
    letI : Algebra F.middle C := r.toAlgebra
    letI : Algebra C B := C.val.toAlgebra
    letI : Module C (Module.Dual A C) := algebraDualModule A C
    letI : Module B (Module.Dual A C ⊗[C] B) :=
      (TensorProduct.comm C (Module.Dual A C) B).toAddEquiv.module B
    letI : IsScalarTower A F.middle C := IsScalarTower.of_algebraMap_eq' (by
      ext a
      rw [RingHom.algebraMap_toAlgebra]
      exact congrArg Subtype.val (r.commutes a).symm)
    letI : IsScalarTower F.middle C B := IsScalarTower.of_algebraMap_eq (by
      intro a
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
      have hh := congrArg (fun f : F.middle →ₐ[A] B => f a) hcomp
      simpa using hh.symm)
    Module.Dual A C ⊗[C] B ≃ₗ[B] dualizingModule F :=
  finiteAlgebraChangeToF F hfin r hcomp Subtype.val_injective

/-- The comparison through a finite subalgebra of the target carries a pure tensor to the pure
tensor of the restricted functional in the relative dualizing module. -/
theorem finiteSubalgebraChangeToF_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (C : Subalgebra A B) (r : F.middle →ₐ[A] C)
    (hcomp : C.val.comp r = IsScalarTower.toAlgHom A F.middle B)
    (hfin : Module.Finite A C) (φ : Module.Dual A C) (b : B) :
    letI : Algebra F.middle C := r.toAlgebra
    letI : Algebra C B := C.val.toAlgebra
    letI : IsScalarTower A F.middle C := IsScalarTower.of_algebraMap_eq' (by
      ext a
      rw [RingHom.algebraMap_toAlgebra]
      exact congrArg Subtype.val (r.commutes a).symm)
    letI : IsScalarTower F.middle C B := IsScalarTower.of_algebraMap_eq (by
      intro a
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
      have hh := congrArg (fun f : F.middle →ₐ[A] B => f a) hcomp
      simpa using hh.symm)
    letI : Module C (Module.Dual A C) := algebraDualModule A C
    finiteSubalgebraChangeToF F C r hcomp hfin (φ ⊗ₜ[C] b) =
      dualizingModule.tmul F (φ.comp r.toLinearMap) b := by
  let : Algebra F.middle C := r.toAlgebra
  let : Algebra C B := C.val.toAlgebra
  let : IsScalarTower A F.middle C := IsScalarTower.of_algebraMap_eq' (by
    ext a
    rw [RingHom.algebraMap_toAlgebra]
    exact congrArg Subtype.val (r.commutes a).symm)
  let : IsScalarTower F.middle C B := IsScalarTower.of_algebraMap_eq (by
    intro a
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
    have hh := congrArg (fun f : F.middle →ₐ[A] B => f a) hcomp
    simpa using hh.symm)
  let : Module F.middle (Module.Dual A F.middle) := algebraDualModule A F.middle
  let : Module C (Module.Dual A C) := algebraDualModule A C
  exact finiteAlgebraChangeToF_tmul F hfin r hcomp Subtype.val_injective φ b



end Stacks.Discriminant
