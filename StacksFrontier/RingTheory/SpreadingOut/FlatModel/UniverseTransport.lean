module

public import StacksFrontier.RingTheory.SpreadingOut.FlatModel.FiniteTypeModel
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.RingTheory.Finiteness.Small

/-!
# Flat models in prescribed universes

A flat model of Stacks 02JO may be replaced by an isomorphic model in prescribed universes.

## Main results

* `Module.Flat.exists_small_finiteType_model`, `Module.Flat.exists_small_finitePresentation_model`
-/

@[expose] public section

open scoped TensorProduct

/-! ### Universe transport

Stacks 02JO is a universe-independent statement, whereas the three parts above are proved with
`R` and `S` in one universe (this is inherited from 00R1) and, in part (1), with the model in that
same universe. The lemmas of this section close the gap. The mathematical content is smallness:
a ring of finite type over `ℤ`, an algebra of finite type over it and a finite module over that are
each `Small` in every universe, so each may be replaced by a `Shrink` copy; everything else is
transport of `Algebra.IsPushout`, `IsBaseChange` and the finiteness hypotheses along ring and
module isomorphisms.
-/

universe uR uS uM uI uA uB uN uR₀ uS₀ uM₀

/-- **A small copy of an algebra.** If the `R`-algebra `S` is `Small` relative to a universe `u`,
then there is an `R`-algebra `T` in `Type u` isomorphic to `S`.

The copy is produced as an existential rather than as `Shrink S` on purpose: the instances
transferred to `Shrink S` from `S` (any action of a ring `X` on `S` transfers to an action of `X`
on `Shrink S`) clash with the instances that a transport argument builds on the copy by hand, so
the copy has to be opaque. -/
theorem Algebra.exists_small_copy.{t, r, s} {R : Type r} {S : Type s} [CommRing R]
    [CommRing S] [Algebra R S] [Small.{t} S] :
    ∃ (T : Type t) (_ : CommRing T) (_ : Algebra R T), Nonempty (T ≃ₐ[R] S) :=
  ⟨Shrink.{t} S, inferInstance, inferInstance, ⟨Shrink.algEquiv.{t} R S⟩⟩

/-- **Transport of a base change along an isomorphism of the coefficient ring.** If `N` is the
base change of `M` to `S'` and `e : S ≃ₐ[R] S'` is an isomorphism of `R`-algebras acting on `N` in
the same way, then `N` is the base change of `M` to `S` as well. -/
theorem IsBaseChange.of_algEquiv {R S S' M N : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring S'] [Algebra R S] [Algebra R S']
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Module S N] [Module S' N]
    [IsScalarTower R S N] [IsScalarTower R S' N]
    {f : M →ₗ[R] N} (e : S ≃ₐ[R] S')
    (he : ∀ (s : S) (n : N), e s • n = s • n) (hf : IsBaseChange S' f) :
    IsBaseChange S f := by
  have key : ∀ x : S ⊗[R] M, f.liftBaseChange S x
      = hf.equiv (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M) x) := by
    intro x
    induction x with
    | tmul s m => simp [hf.equiv_tmul, he]
    | add x y hx hy => simp [hx, hy]
  have hbij : Function.Bijective (f.liftBaseChange S) := by
    have h2 : (f.liftBaseChange S : S ⊗[R] M → N) =
        hf.equiv ∘ (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M)) := funext key
    rw [h2]
    exact hf.equiv.bijective.comp (TensorProduct.congr e.toLinearEquiv
      (LinearEquiv.refl R M)).bijective
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hbij) (by simp)

/-- **Restricting the scalars of a base change along a surjection.** If `N` is the base change of
the `B`-module `P` to `S` and `A → B` is surjective, then `N` is also the base change of `P`
regarded as an `A`-module. -/
theorem IsBaseChange.restrictScalars_of_surjective
    {A B S P M : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring S]
    [Algebra A B] [Algebra A S] [Algebra B S] [IsScalarTower A B S]
    [AddCommMonoid P] [Module A P] [Module B P] [IsScalarTower A B P]
    [AddCommMonoid M] [Module A M] [Module B M] [Module S M]
    [IsScalarTower A B M] [IsScalarTower A S M] [IsScalarTower B S M]
    (h : Function.Surjective (algebraMap A B)) (f : P →ₗ[B] M)
    (hf : IsBaseChange S f) : IsBaseChange S (f.restrictScalars A) := by
  have : TensorProduct.CompatibleSMul A B S P :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective S P h
  apply IsBaseChange.of_equiv
    ((TensorProduct.equivOfCompatibleSMul B A S S P).trans hf.equiv)
  intro x
  show hf.equiv (1 ⊗ₜ[B] x) = f x
  simpa only [one_smul] using hf.equiv_tmul 1 x

/-- **Restricting the initial corner of a pushout square along a surjection.** If the square
`B → R`, `B → S`, `R → T`, `S → T` is a pushout and `A → B` is surjective, then the square with
`B` replaced by `A` is a pushout. -/
theorem Algebra.IsPushout.restrictScalars_of_surjective
    {A B R S T : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring R]
    [CommSemiring S] [CommSemiring T]
    [Algebra A B] [Algebra A R] [Algebra A S] [Algebra A T]
    [Algebra B R] [Algebra B S] [Algebra B T] [Algebra R T] [Algebra S T]
    [IsScalarTower A B R] [IsScalarTower A B S] [IsScalarTower A B T]
    [IsScalarTower A R T] [IsScalarTower A S T]
    [IsScalarTower B R T] [IsScalarTower B S T]
    [Algebra.IsPushout B R S T]
    (h : Function.Surjective (algebraMap A B)) : Algebra.IsPushout A R S T :=
  ⟨IsBaseChange.restrictScalars_of_surjective h
    (IsScalarTower.toAlgHom B S T).toLinearMap Algebra.IsPushout.out⟩

/-- **Transport of a pushout square along isomorphisms of its two right-hand corners.** If
`R → R'`, `R → S`, `R' → S'`, `S → S'` is a pushout square, `e : S ≃ₐ[R] T` and `e' : S' ≃ₐ[R'] T'`
are isomorphisms and the resulting square commutes, then `R → R'`, `R → T`, `R' → T'`, `T → T'` is
a pushout square. -/
theorem Algebra.IsPushout.of_algEquiv₂ {R R' S S' T T' : Type*}
    [CommRing R] [CommRing R'] [CommRing S] [CommRing S'] [CommRing T] [CommRing T']
    [Algebra R R'] [Algebra R S] [Algebra R S'] [Algebra R' S'] [Algebra S S']
    [Algebra R T] [Algebra R T'] [Algebra R' T'] [Algebra T T']
    [IsScalarTower R R' S'] [IsScalarTower R S S'] [IsScalarTower R R' T']
    [IsScalarTower R T T'] [Algebra.IsPushout R R' S S']
    (e : S ≃ₐ[R] T) (e' : S' ≃ₐ[R'] T')
    (he : ∀ x : S, e' (algebraMap S S' x) = algebraMap T T' (e x)) :
    Algebra.IsPushout R R' T T' := by
  have h := (Algebra.isPushout_iff R R' S S').mp inferInstance
  refine (Algebra.isPushout_iff R R' T T').mpr ?_
  refine (IsBaseChange.iff_of_equiv_comm e.toLinearEquiv e'.toLinearEquiv ?_).mp h
  ext x
  simpa using (he x).symm

/-- **A finitely presented module stays finitely presented over a ring mapping onto the base by a
bijection.** -/
theorem Module.FinitePresentation.of_bijective_algebraMap {R R' M : Type*} [CommRing R]
    [CommRing R'] [Algebra R R'] [AddCommGroup M] [Module R M] [Module R' M]
    [IsScalarTower R R' M] [Module.FinitePresentation R' M]
    (h : Function.Bijective (algebraMap R R')) : Module.FinitePresentation R M := by
  have : Module.FinitePresentation R R' :=
    Module.FinitePresentation.of_equiv (LinearEquiv.ofBijective (Algebra.linearMap R R') h)
  exact Module.FinitePresentation.trans R M R'

/-- **A flat finite type model exists in arbitrary universes.** A flat model `(C, D, P)` of
`(R → S, M)` with `C` of finite type over `ℤ`, `D` of finite type over `C` and `P` finite over `D`
can be replaced by an isomorphic model in any three prescribed universes: the three finiteness
hypotheses make `C`, `D` and `P` `Small` in every universe, so each may be replaced by a `Shrink`
copy, and the pushout square and the base change transport along the resulting isomorphisms.

This is the universe-generality statement of Stacks 02JO (1) relative to
`Module.Flat.exists_finiteType_model`, which produces the model in the universe of `R`. -/
theorem Module.Flat.exists_small_finiteType_model
    {C D R S P M : Type*} [CommRing C] [CommRing D] [CommRing R] [CommRing S]
    [Algebra C D] [Algebra C R] [Algebra C S] [Algebra R S] [Algebra D S]
    [IsScalarTower C R S] [IsScalarTower C D S]
    [AddCommGroup P] [Module C P] [Module D P] [IsScalarTower C D P]
    [AddCommGroup M] [Module D M] [Module S M] [IsScalarTower D S M]
    [Algebra.FiniteType ℤ C] [Algebra.FiniteType C D] [Module.Finite D P]
    [Module.Flat C P] [Algebra.IsPushout C R D S]
    (f : P →ₗ[D] M) (hf : IsBaseChange S f) :
    ∃ (C' : Type uR₀) (D' : Type uS₀) (P' : Type uM₀)
      (_ : CommRing C') (_ : CommRing D') (_ : Algebra C' D')
      (_ : Algebra C' R) (_ : Algebra D' S) (_ : Algebra C' S)
      (_ : IsScalarTower C' R S) (_ : IsScalarTower C' D' S)
      (_ : AddCommGroup P') (_ : Module D' P') (_ : Module C' P')
      (_ : IsScalarTower C' D' P') (_ : Module D' M)
      (_ : IsScalarTower D' S M) (f' : P' →ₗ[D'] M),
      Algebra.FiniteType ℤ C' ∧ Algebra.FiniteType C' D' ∧ Module.Finite D' P' ∧
      Module.Flat C' P' ∧ Algebra.IsPushout C' R D' S ∧ IsBaseChange S f' := by
  have : Small.{uR₀} C := Algebra.FiniteType.small.{uR₀} (R := ℤ)
  have : Small.{uS₀} C := Algebra.FiniteType.small.{uS₀} (R := ℤ)
  have : Small.{uS₀} D := Algebra.FiniteType.small.{uS₀} (R := C)
  have : Small.{uM₀} C := Algebra.FiniteType.small.{uM₀} (R := ℤ)
  have : Small.{uM₀} D := Algebra.FiniteType.small.{uM₀} (R := C)
  have : Small.{uM₀} P := Module.Finite.small.{uM₀} D P
  let C' := Shrink.{uR₀} C
  let D' := Shrink.{uS₀} D
  let P' := Shrink.{uM₀} P
  let eC : C' ≃ₐ[ℤ] C := Shrink.algEquiv.{uR₀} ℤ C
  let : Algebra C' C := eC.toRingHom.toAlgebra
  let : Algebra C' D := ((algebraMap C D).comp eC.toRingHom).toAlgebra
  let : Algebra C' R := ((algebraMap C R).comp eC.toRingHom).toAlgebra
  let : Algebra C' S := ((algebraMap C S).comp eC.toRingHom).toAlgebra
  have : IsScalarTower C' C D := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower C' C R := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower C' C S := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower C' R S := .of_algebraMap_eq fun x =>
    IsScalarTower.algebraMap_apply C R S (eC x)
  have : IsScalarTower C' D S := .of_algebraMap_eq fun x =>
    IsScalarTower.algebraMap_apply C D S (eC x)
  let eD : D' ≃ₐ[C'] D := Shrink.algEquiv.{uS₀} C' D
  let : Algebra D' D := eD.toRingHom.toAlgebra
  let : Algebra D' S := ((algebraMap D S).comp eD.toRingHom).toAlgebra
  have : IsScalarTower C' D' D := .of_algebraMap_eq fun x => (eD.commutes x).symm
  have : IsScalarTower D' D S := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower C' D' S := .of_algebraMap_eq fun x => by
    show algebraMap C' S x = algebraMap D S (eD (algebraMap C' D' x))
    rw [eD.commutes, ← IsScalarTower.algebraMap_apply C' D S]
  let : Module C' P := Module.compHom P eC.toRingHom
  let : Module D' P := Module.compHom P eD.toRingHom
  let : Module D' M := Module.compHom M eD.toRingHom
  have : IsScalarTower C' C P := .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower D' D P := .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower D' D M := .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower D' S M := .of_algebraMap_smul fun x m => by
    show algebraMap D S (eD x) • m = eD x • m
    exact IsScalarTower.algebraMap_smul S (eD x) m
  have : IsScalarTower C' D P := .of_algebraMap_smul fun x m => by
    show algebraMap C D (eC x) • m = eC x • m
    exact IsScalarTower.algebraMap_smul D (eC x) m
  have : IsScalarTower C' D' P := .of_algebraMap_smul fun x m => by
    show eD (algebraMap C' D' x) • m = eC x • m
    rw [eD.commutes]
    exact IsScalarTower.algebraMap_smul D (eC x) m
  have heP (c : C') (p : P') :
      (Shrink.linearEquiv.{uM₀} D' P) (c • p) =
        c • (Shrink.linearEquiv.{uM₀} D' P) p :=
    (Shrink.linearEquiv.{uM₀} C' P).map_smul c p
  have hP'tower : IsScalarTower C' D' P' := ⟨fun c d p => by
    apply (Shrink.linearEquiv.{uM₀} D' P).injective
    rw [map_smul, heP, map_smul, smul_assoc]⟩
  have hC : Function.Bijective (algebraMap C' C) := eC.bijective
  have hD : Function.Bijective (algebraMap D' D) := eD.bijective
  have : Module.Flat C' C := Module.Flat.of_linearEquiv
    (AlgEquiv.ofBijective (Algebra.ofId C' C) hC).symm.toLinearEquiv
  have : Module.Flat C' P := Module.Flat.trans C' C P
  have : Module.Flat C' P' := Module.Flat.of_linearEquiv (Shrink.linearEquiv.{uM₀} C' P)
  have : Algebra.FiniteType ℤ C' := Algebra.FiniteType.equiv inferInstance eC.symm
  have : Algebra.FiniteType C' C := Algebra.FiniteType.of_surjective
    (Algebra.ofId C' C) hC.surjective
  have : Algebra.FiniteType C' D := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType C' C) (inferInstance : Algebra.FiniteType C D)
  have : Algebra.FiniteType C' D' := Algebra.FiniteType.equiv inferInstance eD.symm
  have : Module.Finite D' D := Module.Finite.of_surjective (Algebra.linearMap D' D) hD.surjective
  have : Module.Finite D' P := Module.Finite.trans D P
  have : Module.Finite D' P' := inferInstance
  have : Algebra.IsPushout C' R D S :=
    Algebra.IsPushout.restrictScalars_of_surjective hC.surjective
  have hpush : Algebra.IsPushout C' R D' S := by
    constructor
    apply IsBaseChange.of_equiv
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R R) eD.toLinearEquiv).trans
        (Algebra.IsPushout.equiv C' R D S).toLinearEquiv)
    intro d
    show (Algebra.IsPushout.equiv C' R D S) (1 ⊗ₜ[C'] eD d) = algebraMap D' S d
    simp only [Algebra.IsPushout.equiv_tmul, map_one, one_mul]
    rfl
  have hf' := IsBaseChange.restrictScalars_of_surjective hD.surjective f hf
  let eP : P' ≃ₗ[D'] P := Shrink.linearEquiv.{uM₀} D' P
  let f' : P' →ₗ[D'] M := f.restrictScalars D' ∘ₗ eP.toLinearMap
  have hbase : IsBaseChange S f' := by
    apply IsBaseChange.of_equiv
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) eP).trans hf'.equiv)
    intro p
    show hf'.equiv (1 ⊗ₜ[D'] eP p) = f (eP p)
    simpa only [one_smul, LinearMap.restrictScalars_apply] using hf'.equiv_tmul 1 (eP p)
  exact ⟨C', D', P', inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (inferInstance : Module D' P'), (inferInstance : Module C' P'), hP'tower,
    inferInstance, inferInstance, f',
    inferInstance, inferInstance, inferInstance, inferInstance, hpush, hbase⟩

/-- **A flat finitely presented model exists in arbitrary large enough universes.** A flat model
`(D, P)` of `(R → S, M)` over a fixed base `C`, with `D` of finite presentation over `C` and `P`
of finite presentation over `D`, can be replaced by an isomorphic model in any two universes in
which `D` and `P` are `Small`.

This is the universe-generality statement of Stacks 02JO (2) relative to
`Module.Flat.exists_finitePresentation_model_of_directed`, which produces the model in the
universe generated by the base and the colimit. -/
theorem Module.Flat.exists_small_finitePresentation_model
    {C D R S P M : Type*} [CommRing C] [CommRing D] [CommRing R] [CommRing S]
    [Algebra C D] [Algebra C R] [Algebra C S] [Algebra R S] [Algebra D S]
    [IsScalarTower C R S] [IsScalarTower C D S]
    [AddCommGroup P] [Module C P] [Module D P] [IsScalarTower C D P]
    [AddCommGroup M] [Module D M] [Module S M] [IsScalarTower D S M]
    [Algebra.FinitePresentation C D] [Module.FinitePresentation D P]
    [Module.Flat C P] [Algebra.IsPushout C R D S]
    [Small.{uS₀} D] [Small.{uM₀} D] [Small.{uM₀} P]
    (f : P →ₗ[D] M) (hf : IsBaseChange S f) :
    ∃ (D' : Type uS₀) (P' : Type uM₀)
      (_ : CommRing D') (_ : Algebra C D') (_ : Algebra D' S) (_ : Algebra C S)
      (_ : IsScalarTower C R S) (_ : IsScalarTower C D' S)
      (_ : AddCommGroup P') (_ : Module D' P') (_ : Module C P')
      (_ : IsScalarTower C D' P') (_ : Module D' M) (_ : IsScalarTower D' S M)
      (f' : P' →ₗ[D'] M),
      Algebra.FinitePresentation C D' ∧ Module.FinitePresentation D' P' ∧
      Module.Flat C P' ∧ Algebra.IsPushout C R D' S ∧ IsBaseChange S f' := by
  let D' := Shrink.{uS₀} D
  let P' := Shrink.{uM₀} P
  let eD : D' ≃ₐ[C] D := Shrink.algEquiv.{uS₀} C D
  let : Algebra D' D := eD.toRingHom.toAlgebra
  let : Algebra D' S := ((algebraMap D S).comp eD.toRingHom).toAlgebra
  have : IsScalarTower C D' D := .of_algebraMap_eq fun x => (eD.commutes x).symm
  have : IsScalarTower D' D S := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower C D' S := .of_algebraMap_eq fun x => by
    show algebraMap C S x = algebraMap D S (eD (algebraMap C D' x))
    rw [eD.commutes, ← IsScalarTower.algebraMap_apply C D S]
  let : Module D' P := Module.compHom P eD.toRingHom
  let : Module D' M := Module.compHom M eD.toRingHom
  have : IsScalarTower D' D P := .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower D' D M := .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower D' S M := .of_algebraMap_smul fun x m => by
    show algebraMap D S (eD x) • m = eD x • m
    exact IsScalarTower.algebraMap_smul S (eD x) m
  have : IsScalarTower C D' P := .of_algebraMap_smul fun x m => by
    show eD (algebraMap C D' x) • m = x • m
    rw [eD.commutes]
    exact IsScalarTower.algebraMap_smul D x m
  have heP (c : C) (p : P') :
      (Shrink.linearEquiv.{uM₀} D' P) (c • p) =
        c • (Shrink.linearEquiv.{uM₀} D' P) p :=
    (Shrink.linearEquiv.{uM₀} C P).map_smul c p
  have hP'tower : IsScalarTower C D' P' := ⟨fun c d p => by
    apply (Shrink.linearEquiv.{uM₀} D' P).injective
    rw [map_smul, heP, map_smul, smul_assoc]⟩
  have hD : Function.Bijective (algebraMap D' D) := eD.bijective
  have : Module.Flat C P' := Module.Flat.of_linearEquiv (Shrink.linearEquiv.{uM₀} C P)
  have : Algebra.FinitePresentation C D' := Algebra.FinitePresentation.equiv eD.symm
  let eP : P' ≃ₗ[D'] P := Shrink.linearEquiv.{uM₀} D' P
  have : Module.FinitePresentation D' P :=
    Module.FinitePresentation.of_bijective_algebraMap hD
  have : Module.FinitePresentation D' P' := Module.FinitePresentation.of_equiv eP.symm
  have hpush : Algebra.IsPushout C R D' S := by
    constructor
    apply IsBaseChange.of_equiv
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R R) eD.toLinearEquiv).trans
        (Algebra.IsPushout.equiv C R D S).toLinearEquiv)
    intro d
    show (Algebra.IsPushout.equiv C R D S) (1 ⊗ₜ[C] eD d) = algebraMap D' S d
    simp only [Algebra.IsPushout.equiv_tmul, map_one, one_mul]
    rfl
  have hf' := IsBaseChange.restrictScalars_of_surjective hD.surjective f hf
  let f' : P' →ₗ[D'] M := f.restrictScalars D' ∘ₗ eP.toLinearMap
  have hbase : IsBaseChange S f' := by
    apply IsBaseChange.of_equiv
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) eP).trans hf'.equiv)
    intro p
    show hf'.equiv (1 ⊗ₜ[D'] eP p) = f (eP p)
    simpa only [one_smul, LinearMap.restrictScalars_apply] using hf'.equiv_tmul 1 (eP p)
  exact ⟨D', P', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, (inferInstance : Module D' P'), (inferInstance : Module C P'),
    hP'tower, inferInstance, inferInstance, f',
    inferInstance, inferInstance, inferInstance, hpush, hbase⟩
