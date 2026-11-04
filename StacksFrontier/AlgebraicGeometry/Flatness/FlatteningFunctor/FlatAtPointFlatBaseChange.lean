module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Spectrum.Prime.TensorProduct
public import StacksFrontier.RingTheory.Flat.BaseChangeAlongFlatAlgebra
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.LocalizedFlatness
public import StacksFrontier.RingTheory.Flat.HenselianFlattening

/-!
# A flat change of the local algebra does not change the flat-at-a-point functor

In the situation of Stacks Tag 05MK, let `B → C` be a flat local homomorphism of local
`A`-algebras and put `N = C ⊗[B] M`. Then the functor `F_lf` attached to the pair `(C, N)` is
the functor attached to `(B, M)`.

Over a base change `A'`, the closed fibre of `Spec (C ⊗[A] A')` surjects onto the closed fibre
of `Spec (B ⊗[A] A')`, because the corresponding map of residue-field tensor products is
faithfully flat; and above a prime `q` of `B ⊗[A] A'` in the closed fibre, flatness of `M'_q`
over `A'` is flatness of `N'_r` over `A'` for a prime `r` above it, because the local map
`(B ⊗[A] A')_q → (C ⊗[A] A')_r` is faithfully flat.

## Main definitions

* `Module.FlatAtPointSituation.baseChange` replaces the local algebra `B` by a local
  `B`-algebra `C` and extends the scalars of `M` to `C`.

## Main results

* `Module.FlatAtPointSituation.flatAtPointFunctor_baseChange`: **Stacks Tag 05P5**.

## Implementation notes

The module of the new situation is written `C ⊗[B] M`, on which the scalar extension module
structure is definitionally available, rather than the source's `M ⊗[B] C`. The base ring is
still `A`, so the two functors have the same source category and the conclusion is an equality
of functors.

## References

* [Stacks Project, Tag 05P5](https://stacks.math.columbia.edu/tag/05P5)
-/

@[expose] public section

open CategoryTheory IsLocalRing
open scoped TensorProduct

universe u v w x z

namespace Module.FlatAtPointSituation

/-- The algebra structure on the localizations of `S → T` at `r` and its contraction `p` makes
`S → Sp → Tr` a scalar tower. -/
private theorem isScalarTower_localization_atPrime {S T : Type*} [CommRing S] [CommRing T]
    [Algebra S T] (p : Ideal S) (r : Ideal T) [p.IsPrime] [r.IsPrime] [r.LiesOver p] :
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime r) :=
      Localization.AtPrime.algebraOfLiesOver p r
    IsScalarTower S (Localization.AtPrime p) (Localization.AtPrime r) := by
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime r) :=
    Localization.AtPrime.algebraOfLiesOver p r
  refine IsScalarTower.of_algebraMap_smul fun s x ↦ ?_
  show (algebraMap (Localization.AtPrime p) (Localization.AtPrime r))
    ((algebraMap S (Localization.AtPrime p)) s) • x = s • x
  rw [← IsScalarTower.algebraMap_apply S (Localization.AtPrime p) (Localization.AtPrime r) s,
    IsScalarTower.algebraMap_smul]

/-- Localizing a base change at a prime is the base change of the localization at the
contracted prime, along the induced map of localizations. -/
private noncomputable def localizedTensorBaseChangeEquiv {S T M : Type*} [CommRing S]
    [CommRing T] [Algebra S T] [AddCommGroup M] [Module S M] (r : Ideal T) [r.IsPrime] :
    let p := r.comap (algebraMap S T)
    let Sq := Localization.AtPrime p
    let Tr := Localization.AtPrime r
    letI : Algebra Sq Tr := Localization.AtPrime.algebraOfLiesOver p r
    TensorProduct Sq Tr (LocalizedModule.AtPrime p M) ≃ₗ[Tr]
      LocalizedModule.AtPrime r (T ⊗[S] M) := by
  let p := r.comap (algebraMap S T)
  have _ : p.IsPrime := Ideal.comap_isPrime _ _
  have _ : r.LiesOver p := ⟨rfl⟩
  let Sq := Localization.AtPrime p
  let Tr := Localization.AtPrime r
  letI : Algebra Sq Tr := Localization.AtPrime.algebraOfLiesOver p r
  have _ : IsScalarTower S Sq Tr := isScalarTower_localization_atPrime p r
  letI : Module S (LocalizedModule.AtPrime p M) := Module.compHom _ (algebraMap S Sq)
  exact ((LocalizedModule.equivTensorProduct p.primeCompl M).baseChange Sq Tr).trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange S Sq Tr Tr M).trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange S T Tr Tr M).symm.trans
        (LocalizedModule.equivTensorProduct r.primeCompl (T ⊗[S] M)).symm))

/-- For a flat algebra `S → T` and a prime `r` of `T`, the induced local map of localizations
at `r` and at its contraction is faithfully flat. -/
private theorem faithfullyFlat_localizationAtPrime {S T : Type*} [CommRing S] [CommRing T]
    [Algebra S T] [Module.Flat S T] (r : Ideal T) [r.IsPrime] :
    let p := r.comap (algebraMap S T)
    let Sq := Localization.AtPrime p
    let Tr := Localization.AtPrime r
    letI : Algebra Sq Tr := Localization.AtPrime.algebraOfLiesOver p r
    Module.FaithfullyFlat Sq Tr := by
  let p := r.comap (algebraMap S T)
  have _ : p.IsPrime := Ideal.comap_isPrime _ _
  have _ : r.LiesOver p := ⟨rfl⟩
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime r) :=
    Localization.AtPrime.algebraOfLiesOver p r
  have _ : IsScalarTower S (Localization.AtPrime p) (Localization.AtPrime r) :=
    isScalarTower_localization_atPrime p r
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The base change `B ⊗[A] R → C ⊗[A] R` of an `A`-algebra map `B → C` is compatible with the
`B`-algebra structures. -/
private theorem isScalarTower_tensorBaseChange {A B C R : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing R] [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Algebra A R] :
    letI : Algebra (B ⊗[A] R) (C ⊗[A] R) :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C) (AlgHom.id A R)).toRingHom.toAlgebra
    IsScalarTower B (B ⊗[A] R) (C ⊗[A] R) := by
  let fAlg : B ⊗[A] R →ₐ[A] C ⊗[A] R :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C) (AlgHom.id A R)
  let : Algebra (B ⊗[A] R) (C ⊗[A] R) := fAlg.toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun b ↦ by
    show fAlg (b ⊗ₜ[A] (1 : R)) = (algebraMap B C b) ⊗ₜ[A] (1 : R)
    rw [Algebra.TensorProduct.map_tmul]
    simp

/-- The base change `B ⊗[A] R → C ⊗[A] R` of an `A`-algebra map `B → C` is compatible with the
inclusions of `R`. -/
private theorem tensorBaseChange_comp_includeRight {A B C R : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing R] [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Algebra A R] :
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C) (AlgHom.id A R)).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom = Algebra.TensorProduct.includeRight.toRingHom :=
  by ext; simp

/-- The square `B → C`, `B ⊗[A] R → C ⊗[A] R` is a pushout. -/
private theorem isPushout_tensorBaseChange {A B C R : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing R] [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Algebra A R] :
    letI : Algebra (B ⊗[A] R) (C ⊗[A] R) :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C) (AlgHom.id A R)).toRingHom.toAlgebra
    ∀ [IsScalarTower B (B ⊗[A] R) (C ⊗[A] R)], Algebra.IsPushout B (B ⊗[A] R) C (C ⊗[A] R) :=
  by
  intros
  let : Algebra (B ⊗[A] R) (C ⊗[A] R) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C) (AlgHom.id A R)).toRingHom.toAlgebra
  exact (Algebra.IsPushout.tensorProduct_tensorProduct A R B C
    tensorBaseChange_comp_includeRight).symm

/-- The base change of a flat algebra map along a ring map out of the base is flat. -/
@[sga "3 V 7.4" "(i), special case"]
private theorem flat_tensorBaseChange {A B C R : Type*} [CommRing A] [CommRing B] [CommRing C]
    [CommRing R] [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] [Algebra A R]
    [Module.Flat B C] :
    let SR := B ⊗[A] R
    let TR := C ⊗[A] R
    let f : SR →+* TR :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C) (AlgHom.id A R)).toRingHom
    letI : Algebra SR TR := f.toAlgebra
    Module.Flat SR TR := by
  let SR := B ⊗[A] R
  let TR := C ⊗[A] R
  let fAlg : SR →ₐ[A] TR :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C) (AlgHom.id A R)
  let : Algebra SR TR := fAlg.toRingHom.toAlgebra
  have _ : IsScalarTower B SR TR :=
    isScalarTower_tensorBaseChange (A := A) (B := B) (C := C) (R := R)
  have _ : Algebra.IsPushout B SR C TR := isPushout_tensorBaseChange (A := A)
  have _ : Module.Flat SR (SR ⊗[B] C) := Module.Flat.baseChange B SR C
  exact Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv B SR C TR).toLinearEquiv.symm

/-- A module over `T` with a compatible `R`-action is a scalar tower over `R` and the localization
of `T` at a prime, after localizing the module. -/
private theorem isScalarTower_localizedModule {R T N : Type*} [CommRing R] [CommRing T]
    [AddCommGroup N] [Algebra R T] [Module T N] [Module R N] [IsScalarTower R T N]
    (q : Ideal T) [q.IsPrime] [Algebra R (Localization.AtPrime q)]
    (h : ∀ r : R, algebraMap R (Localization.AtPrime q) r =
      algebraMap T (Localization.AtPrime q) (algebraMap R T r)) :
    letI : SMul R (Localization.AtPrime q) := Algebra.toSMul
    IsScalarTower R (Localization.AtPrime q) (LocalizedModule q.primeCompl N) :=
  IsScalarTower.of_algebraMap_smul (R := R) (A := Localization.AtPrime q)
      (M := LocalizedModule q.primeCompl N) fun r x ↦ by
    induction x using LocalizedModule.induction_on with
    | h y s =>
      show (algebraMap R (Localization.AtPrime q) r) • LocalizedModule.mk y s =
        r • LocalizedModule.mk y s
      rw [h r,
        IsScalarTower.algebraMap_smul (R := T)
        (A := Localization.AtPrime q) (algebraMap R T r) (LocalizedModule.mk y s),
        LocalizedModule.smul'_mk, LocalizedModule.smul'_mk]
      exact congrArg (fun t ↦ LocalizedModule.mk t s)
        (IsScalarTower.algebraMap_smul (R := R) (A := T) r y)

/-- Above a prime `q` of the base change of `C`, flatness over the test algebra of the
localization of the base change of `C ⊗[B] M` is the flatness of the localization of the base
change of `M` at the contracted prime: the map of localizations is faithfully flat. -/
private theorem flat_localizedModule_baseChange_iff {A B C R M : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing R] [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Algebra A R] [AddCommGroup M] [Module B M] [Module.Flat B C] (q : Ideal (C ⊗[A] R))
    [q.IsPrime] :
    let S := B ⊗[A] R
    let T := C ⊗[A] R
    let f : S →+* T :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C) (AlgHom.id A R)).toRingHom
    letI : Algebra S T := f.toAlgebra
    letI : Algebra R S := Algebra.TensorProduct.rightAlgebra
    letI : Algebra R T := Algebra.TensorProduct.rightAlgebra
    Module.Flat R (LocalizedModule q.primeCompl (T ⊗[C] (C ⊗[B] M))) ↔
      Module.Flat R (LocalizedModule (q.comap f).primeCompl (S ⊗[B] M)) := by
  let S := B ⊗[A] R
  let T := C ⊗[A] R
  let fAlg : S →ₐ[A] T :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C) (AlgHom.id A R)
  let f : S →+* T := fAlg.toRingHom
  let : Algebra S T := f.toAlgebra
  let : Algebra R S := Algebra.TensorProduct.rightAlgebra
  let : Algebra R T := Algebra.TensorProduct.rightAlgebra
  have _ : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun r ↦
    (DFunLike.congr_fun (tensorBaseChange_comp_includeRight (A := A) (B := B) (C := C)) r).symm
  have _ : IsScalarTower B S T :=
    isScalarTower_tensorBaseChange (A := A) (B := B) (C := C) (R := R)
  have hflat : Module.Flat S T := flat_tensorBaseChange (A := A) (B := B) (C := C) (R := R)
  let p := q.comap f
  have _ : p.IsPrime := Ideal.comap_isPrime _ _
  have _ : q.LiesOver p := ⟨rfl⟩
  have _ : IsScalarTower S S T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let Sq := Localization.AtPrime p
  let Tr := Localization.AtPrime q
  let : Algebra Sq Tr := Localization.AtPrime.algebraOfLiesOver (A := S) (B := T) p q
  have _ : Localization.AtPrime.IsLiesOverAlgebra p q := ⟨rfl⟩
  let moduleSqTr : Module Sq Tr := Algebra.toModule
  let : Module Sq Tr := moduleSqTr
  let : SMul Sq Tr := moduleSqTr.toDistribMulAction.toDistribSMul.toSMul
  let : Algebra R Sq := ((algebraMap S Sq).comp (algebraMap R S)).toAlgebra
  let : Algebra R Tr := ((algebraMap T Tr).comp (algebraMap R T)).toAlgebra
  let : Algebra S Tr := ((algebraMap T Tr).comp (algebraMap S T)).toAlgebra
  let moduleTTr : Module T Tr := Algebra.toModule
  let : Module T Tr := moduleTTr
  let : SMul T Tr := moduleTTr.toDistribMulAction.toDistribSMul.toSMul
  let moduleRSq : Module R Sq := Algebra.toModule
  let : Module R Sq := moduleRSq
  let : SMul R Sq := moduleRSq.toDistribMulAction.toDistribSMul.toSMul
  let moduleSSq : Module S Sq := Algebra.toModule
  let : Module S Sq := moduleSSq
  let : SMul S Sq := moduleSSq.toDistribMulAction.toDistribSMul.toSMul
  let moduleRTr : Module R Tr := Algebra.toModule
  let : Module R Tr := moduleRTr
  let : SMul R Tr := moduleRTr.toDistribMulAction.toDistribSMul.toSMul
  let moduleSTr : Module S Tr := Algebra.toModule
  let : Module S Tr := moduleSTr
  let : SMul S Tr := moduleSTr.toDistribMulAction.toDistribSMul.toSMul
  have _ : IsScalarTower S T Tr := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have _ : IsScalarTower R S Sq := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have _ : IsScalarTower R T Tr := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have _ : IsScalarTower R Sq Tr := IsScalarTower.of_algebraMap_eq fun r ↦ by
    have hloc (s : S) :
        algebraMap Sq Tr (algebraMap S Sq s) = algebraMap T Tr (algebraMap S T s) := by
      rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq, Localization.localRingHom_to_map]
    calc
      algebraMap R Tr r = algebraMap T Tr (algebraMap R T r) := rfl
      _ = algebraMap T Tr (algebraMap S T (algebraMap R S r)) := by
        rw [IsScalarTower.algebraMap_apply R S T]
      _ = algebraMap Sq Tr (algebraMap S Sq (algebraMap R S r)) := (hloc (algebraMap R S r)).symm
      _ = algebraMap Sq Tr (algebraMap R Sq r) := by rw [← IsScalarTower.algebraMap_apply R S Sq]
  have _ : Module.Flat S T := hflat
  have _ : Module.FaithfullyFlat Sq Tr := faithfullyFlat_localizationAtPrime (S := S) (T := T) q
  let X := S ⊗[B] M
  let Z := T ⊗[S] X
  let Y := T ⊗[C] (C ⊗[B] M)
  have _ : IsScalarTower R Sq (LocalizedModule p.primeCompl X) :=
    IsScalarTower.of_algebraMap_smul (R := R) (A := Sq)
      (M := LocalizedModule p.primeCompl X) fun r x ↦ by
        induction x using LocalizedModule.induction_on with
        | h m s =>
          show (algebraMap R Sq r) • LocalizedModule.mk m s = r • LocalizedModule.mk m s
          rw [show (algebraMap R Sq) r = algebraMap S Sq ((algebraMap R S) r) from rfl,
            IsScalarTower.algebraMap_smul (R := S) (A := Sq) (algebraMap R S r)
              (LocalizedModule.mk m s), LocalizedModule.smul'_mk, LocalizedModule.smul'_mk]
          exact congrArg (fun t ↦ LocalizedModule.mk t s)
            (IsScalarTower.algebraMap_smul (R := R) (A := S) r m)
  let e : Z ≃ₗ[T] Y := (TensorProduct.AlgebraTensorModule.cancelBaseChange B S T T M).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B C T T M).symm
  let eLoc := IsLocalizedModule.mapEquiv q.primeCompl
    (LocalizedModule.mkLinearMap q.primeCompl Z)
    (LocalizedModule.mkLinearMap q.primeCompl Y) (Localization.AtPrime q) e
  let eLoc' := localizedTensorBaseChangeEquiv (S := S) (T := T) (M := X) q
  have hRmap (r : R) : algebraMap R Tr r = algebraMap T Tr (algebraMap R T r) :=
    IsScalarTower.algebraMap_apply R T Tr r
  have _ : IsScalarTower R Tr (LocalizedModule q.primeCompl Y) :=
    isScalarTower_localizedModule (R := R) (N := Y) q hRmap
  have _ : IsScalarTower R Tr (LocalizedModule q.primeCompl Z) :=
    isScalarTower_localizedModule (R := R) (N := Z) q hRmap
  have _ : LinearMap.CompatibleSMul (LocalizedModule q.primeCompl Z)
      (LocalizedModule q.primeCompl Y) R Tr := LinearMap.IsScalarTower.compatibleSMul
  have _ : LinearMap.CompatibleSMul (LocalizedModule q.primeCompl Y)
      (LocalizedModule q.primeCompl Z) R Tr := LinearMap.IsScalarTower.compatibleSMul
  let moduleRext : Module R (Tr ⊗[Sq] LocalizedModule p.primeCompl X) :=
    Module.compHom _ (algebraMap R Tr)
  let : Module R (Tr ⊗[Sq] LocalizedModule p.primeCompl X) := moduleRext
  let : SMul R (Tr ⊗[Sq] LocalizedModule p.primeCompl X) :=
    moduleRext.toDistribMulAction.toDistribSMul.toSMul
  have _ : IsScalarTower R Tr (Tr ⊗[Sq] LocalizedModule p.primeCompl X) :=
    IsScalarTower.of_compHom R Tr (Tr ⊗[Sq] LocalizedModule p.primeCompl X)
  have _ : LinearMap.CompatibleSMul (LocalizedModule q.primeCompl Z)
      (Tr ⊗[Sq] LocalizedModule p.primeCompl X) R Tr := LinearMap.IsScalarTower.compatibleSMul
  exact (Module.Flat.equiv_iff (eLoc.symm.restrictScalars R)).trans
    ((Module.Flat.equiv_iff (eLoc'.symm.restrictScalars R)).trans
      (Module.Flat.tensorProduct_iff_of_faithfullyFlat (R := R) (S := Sq) (S' := Tr)
        (M := LocalizedModule p.primeCompl X)))

/-- A prime of `B ⊗[A] R` in the closed fibre lifts to a prime of `C ⊗[A] R` in the closed
fibre, for a local homomorphism `B → C` of local rings. -/
private theorem exists_prime_closedFiber_lift {A B C R : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing R] [IsLocalRing B] [IsLocalRing C] [IsLocalRing R] [Algebra A B]
    [Algebra A C] [Algebra B C] [IsScalarTower A B C] [IsLocalHom (algebraMap B C)] [Algebra A R]
    (p : Ideal (B ⊗[A] R)) [p.IsPrime]
    (hp : Ideal.map Algebra.TensorProduct.includeRight.toRingHom (maximalIdeal R) ⊔
        Ideal.map Algebra.TensorProduct.includeLeftRingHom (maximalIdeal B) ≤ p) :
    ∃ q : Ideal (C ⊗[A] R), q.IsPrime ∧
      Ideal.map Algebra.TensorProduct.includeRight.toRingHom (maximalIdeal R) ⊔
          Ideal.map Algebra.TensorProduct.includeLeftRingHom (maximalIdeal C) ≤ q ∧
        q.comap ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C)
          (AlgHom.id A R)).toRingHom) = p := by
  let B' := B ⊗[A] R
  let C' := C ⊗[A] R
  let fAlg : B' →ₐ[A] C' :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C) (AlgHom.id A R)
  let : Algebra B' C' := fAlg.toRingHom.toAlgebra
  have _ : IsScalarTower B B' C' :=
    isScalarTower_tensorBaseChange (A := A) (B := B) (C := C) (R := R)
  have _ : Algebra.IsPushout B B' C C' := isPushout_tensorBaseChange (A := A)
  have hpB : p.comap (algebraMap B B') = maximalIdeal B :=
    le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.comap_isPrime (algebraMap B B') p).ne_top)
      (Ideal.map_le_iff_le_comap.mp (sup_le_iff.mp hp).2)
  obtain ⟨q, hq, hqp, hqC⟩ :=
    Stacks.Flatness.Stratification.exists_prime_pushout_of_closed_surjective (A := B) (B := B')
      (C := C) (D := C') p (maximalIdeal C)
      ⟨maximalIdeal C, inferInstance, le_rfl, by rw [IsLocalRing.maximalIdeal_comap, hpB]⟩
  have hR : (algebraMap B' C').comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom :=
    tensorBaseChange_comp_includeRight (A := A) (B := B) (C := C)
  refine ⟨q, hq, sup_le ?_ ((Ideal.map_le_iff_le_comap).mpr hqC), hqp⟩
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  show Algebra.TensorProduct.includeRight.toRingHom r ∈ q
  rw [← hR, RingHom.comp_apply]
  show Algebra.TensorProduct.includeRight.toRingHom r ∈ q.comap (algebraMap B' C')
  rw [hqp]
  exact (sup_le_iff.mp hp).1 (Ideal.mem_map_of_mem _ hr)

/-- The contraction of a prime of `C ⊗[A] R` in the closed fibre is in the closed fibre of
`B ⊗[A] R`, for a local homomorphism `B → C` of local rings. -/
private theorem closedFiber_le_comap {A B C R : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing R] [IsLocalRing B] [IsLocalRing C] [IsLocalRing R] [Algebra A B]
    [Algebra A C] [Algebra B C] [IsScalarTower A B C] [IsLocalHom (algebraMap B C)] [Algebra A R]
    (q : Ideal (C ⊗[A] R))
    (hq : Ideal.map Algebra.TensorProduct.includeRight.toRingHom (maximalIdeal R) ⊔
        Ideal.map Algebra.TensorProduct.includeLeftRingHom (maximalIdeal C) ≤ q) :
    Ideal.map Algebra.TensorProduct.includeRight.toRingHom (maximalIdeal R) ⊔
        Ideal.map Algebra.TensorProduct.includeLeftRingHom (maximalIdeal B) ≤
      q.comap ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C)
        (AlgHom.id A R)).toRingHom) := by
  let fAlg : B ⊗[A] R →ₐ[A] C ⊗[A] R :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C) (AlgHom.id A R)
  let f : B ⊗[A] R →+* C ⊗[A] R := fAlg.toRingHom
  refine sup_le ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    show (f.comp Algebra.TensorProduct.includeRight.toRingHom) r ∈ q
    have hR : f.comp Algebra.TensorProduct.includeRight.toRingHom =
        Algebra.TensorProduct.includeRight.toRingHom :=
      tensorBaseChange_comp_includeRight (A := A) (B := B) (C := C)
    exact (sup_le_iff.mp hq).1 (by
      simpa only [hR] using
        (Ideal.mem_map_of_mem (f.comp Algebra.TensorProduct.includeRight.toRingHom) hr))
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    show (f.comp (algebraMap B (B ⊗[A] R))) b ∈ q
    have hB : f.comp (algebraMap B (B ⊗[A] R)) =
        (algebraMap C (C ⊗[A] R)).comp (algebraMap B C) := by
      ext b
      show fAlg (b ⊗ₜ[A] (1 : R)) = (algebraMap B C b) ⊗ₜ[A] (1 : R)
      rw [Algebra.TensorProduct.map_tmul]
      simp
    rw [hB, RingHom.comp_apply]
    refine (sup_le_iff.mp hq).2 (Ideal.mem_map_of_mem _ ?_)
    rwa [← Ideal.mem_comap, IsLocalRing.maximalIdeal_comap (algebraMap B C)]

/-- The flat-at-a-point situation obtained by replacing the local algebra `B` by a local
`B`-algebra `C` and extending the scalars of `M` to `C`. -/
public abbrev baseChange (S : FlatAtPointSituation.{u, v, w}) (C : Type z) [CommRing C]
    [IsLocalRing C] [Algebra S.B C] [IsLocalHom (algebraMap S.B C)] :
    FlatAtPointSituation.{u, z, max w z} := by
  letI : Algebra S.A C := ((algebraMap S.B C).comp (algebraMap S.A S.B)).toAlgebra
  exact
    { A := S.A
      B := C
      M := TensorProduct S.B C S.M
      isLocalHomAB := RingHom.isLocalHom_comp (algebraMap S.B C) (algebraMap S.A S.B) }

/-- The flatness condition of Stacks Tag 05ML is unchanged by a flat local base change of the
local algebra. -/
private theorem condition_iff_baseChange (S : FlatAtPointSituation.{u, v, w}) (C : Type z)
    [CommRing C] [IsLocalRing C] [Algebra S.B C] [IsLocalHom (algebraMap S.B C)]
    [Module.Flat S.B C] (R : LocalAlgCat.{u, x} S.A) :
    S.Condition R ↔ (baseChange S C).Condition R := by
  let A := S.A
  let B := S.B
  let M := S.M
  let R₀ := (R : Type x)
  let : Algebra A C := ((algebraMap B C).comp (algebraMap A B)).toAlgebra
  have _ : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let B' := B ⊗[A] R₀
  let C' := C ⊗[A] R₀
  let : Algebra R₀ B' := Algebra.TensorProduct.rightAlgebra
  let : Algebra R₀ C' := Algebra.TensorProduct.rightAlgebra
  let fAlg : B' →ₐ[A] C' :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C) (AlgHom.id A R₀)
  let f : B' →+* C' := fAlg.toRingHom
  let : Algebra B' C' := f.toAlgebra
  constructor
  · intro h q hq hqcontain
    let p := q.comap f
    have _ : p.IsPrime := Ideal.comap_isPrime _ _
    exact (flat_localizedModule_baseChange_iff (A := A) (B := B) (C := C) (R := R₀)
      (M := M) q).mpr (h p inferInstance (by
        rw [Submodule.add_eq_sup]
        exact closedFiber_le_comap (A := A) (B := B) (C := C) (R := R₀) q
          (by rwa [← Submodule.add_eq_sup])))
  · intro h p hp hpcontain
    have _ : p.IsPrime := hp
    obtain ⟨q, hq, hqcontain', rfl⟩ :=
      exists_prime_closedFiber_lift (A := A) (B := B) (C := C) (R := R₀) p
        (by rwa [← Submodule.add_eq_sup])
    exact (flat_localizedModule_baseChange_iff (A := A) (B := B) (C := C) (R := R₀)
      (M := M) q).mp (h q hq (by rwa [Submodule.add_eq_sup]))

/-- **Stacks Project, Tag 05P5.** A flat local extension of the local algebra, with the module
extended along it, does not change the flat-at-a-point functor. -/
@[stacks 05P5]
public theorem flatAtPointFunctor_baseChange (S : FlatAtPointSituation.{u, v, w}) (C : Type z)
    [CommRing C] [IsLocalRing C] [Algebra S.B C] [IsLocalHom (algebraMap S.B C)]
    [Module.Flat S.B C] :
    (S.flatAtPointFunctor : LocalAlgCat.{u, x} S.A ⥤ Type) =
      (baseChange S C).flatAtPointFunctor :=
  CategoryTheory.Functor.ext fun R ↦ congrArg PLift (propext (condition_iff_baseChange S C R))

end Module.FlatAtPointSituation
