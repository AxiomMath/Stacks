module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Noetherian.OfPrime
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.AdicCompletion.CompletionMap
public import StacksFrontier.Deformation.Examples.Geometric.Rings
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Noetherian.NilpotentKernel
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples
public import StacksFrontier.RingTheory.AdicCompletion.SmulTopPow
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
public import StacksFrontier.RingTheory.AdicCompletion.Algebraization
public import StacksFrontier.RingTheory.AdicCompletion.QuotEquivMapPow

/-!
# Completion of deformations of an algebra

Let `P` be a Noetherian `k`-algebra and `J ⊆ P` an ideal. Completing a deformation of `P` at
the inverse image of `J` gives a deformation of the `J`-adic completion of `P` over the same
Artinian base, and this is a functor over `𝒞_Λ`.

The flat algebra of a deformation is Noetherian, because it is a finitely generated algebra
over the Artinian base modulo a nilpotent ideal and its special fibre is `P`; so its `J`-adic
completion is flat over the base, and finite over the completion of the base. The square
identifying the completed flat algebra as the base change of the completion of `P` is the
pushout square for a finite algebra over a Noetherian ring, transported along the canonical
identification of the completion of a base change with the base change of the completion.

## Main definitions

* `Deformation.Examples.AdicCompletionFunctorData`: a functor of deformation categories over
  `𝒞_Λ`, together with the identification of each completed flat algebra with the completion of
  the original one and the compatibility of that identification with the canonical completion
  maps.
* `Deformation.Examples.adicCompletionFunctor`: the completion functor itself.
* `Deformation.Examples.baseCompatibleAdicCompletionFunctor`: a completion functor datum chosen
  from the subtype cut out by
  `Deformation.Examples.AdicCompletionFunctorData.IsBaseCompatible`, so that the clause holds of
  it by construction.

## Main results

* `Deformation.Examples.nonempty_adicCompletionFunctorData`: completion at the inverse image of
  `J` is such a functor.
* `Deformation.Examples.surjective_deformationHomBase`: the map of Artinian bases underlying the
  structural morphism of a deformation is surjective onto the residue field.

## Implementation notes

As for localization, the functor is packaged with its comparison data rather than stated bare:
the content of the source's assertion is that the functor computes the completion on each
deformation, compatibly with the canonical maps into the completions, and that is what the
recorded data says. `adicCompletionFunctor` chooses one such functor.

## References

* [Stacks Project, Tag 0DYV](https://stacks.math.columbia.edu/tag/0DYV)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u w

namespace Deformation.Examples

open AdicCompletion
open TensorProduct
open scoped TensorProduct

private theorem completionMap_congr {A B : Type*} [CommRing A] [CommRing B]
    {f g : A →+* B} (hfg : f = g) (J : Ideal A) (I : Ideal B)
    (hf : J.map f ≤ I) (hg : J.map g ≤ I) :
    adicCompletionMap f J I hf = adicCompletionMap g J I hg := by
  cases hfg
  rfl

private theorem completionMap_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (J : Ideal A) (I : Ideal B) (K : Ideal C)
    (hJ : J.map f ≤ I) (hI : I.map g ≤ K) :
    (adicCompletionMap g I K hI).comp (adicCompletionMap f J I hJ) =
      adicCompletionMap (g.comp f) J K
        (by rw [← Ideal.map_map]; exact le_trans (Ideal.map_mono hJ) hI) := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [RingHom.comp_apply, adicCompletionMap_evalₐ, adicCompletionMap_evalₐ,
    adicCompletionMap_evalₐ]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ J n x)
  rw [← ha]
  simp [Ideal.quotientMap_mk]

private theorem completionMap_id {A : Type*} [CommRing A] (J : Ideal A) :
    adicCompletionMap (RingHom.id A) J J (by simp) = RingHom.id (AdicCompletion J A) := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  show evalₐ J n (adicCompletionMap (RingHom.id A) J J (by simp) x) = evalₐ J n x
  rw [adicCompletionMap_evalₐ]
  show (Ideal.quotientMap (J ^ n) (RingHom.id A) le_rfl) (evalₐ J n x) = _
  have hid : Ideal.quotientMap (J ^ n) (RingHom.id A) le_rfl =
      RingHom.id (A ⧸ J ^ n) := by
    ext a
    show (Ideal.Quotient.mk (J ^ n)) a = (Ideal.Quotient.mk (J ^ n)) a
    rfl
  rw [hid]
  rfl

private noncomputable def completionMapRingEquiv
    {A B : Type*} [CommRing A] [CommRing B] (f : A ≃+* B)
    (I : Ideal A) (J : Ideal B) (hIJ : I.map f.toRingHom = J) :
    AdicCompletion I A ≃+* AdicCompletion J B := by
  have hJI : J.map f.symm.toRingHom = I := by
    rw [← hIJ, Ideal.map_map]
    simp
  refine RingEquiv.ofRingHom
    (adicCompletionMap f.toRingHom I J hIJ.le)
    (adicCompletionMap f.symm.toRingHom J I hJI.le) ?_ ?_
  · have hh := completionMap_comp f.symm.toRingHom f.toRingHom J I J hJI.le hIJ.le
    simpa [completionMap_id] using hh
  · have hh := completionMap_comp f.toRingHom f.symm.toRingHom I J I hIJ.le hJI.le
    simpa [completionMap_id] using hh

private noncomputable def completionCongrOfCofinalPowers
    {R : Type*} [CommRing R] (I J : Ideal R) (hIJ : I ≤ J) (c : ℕ)
    (hcofinal : ∀ n : ℕ, J ^ (n + c) ≤ I ^ n) :
    AdicCompletion I R ≃+* AdicCompletion J R := by
  let forward : AdicCompletion I R →+* AdicCompletion J R :=
    adicCompletionMap (RingHom.id R) I J (by simpa using hIJ)
  let level (n : ℕ) : AdicCompletion J R →+* R ⧸ I ^ n :=
    (Ideal.quotientMap (I ^ n) (RingHom.id R) (hcofinal n)).comp
      (evalₐ J (n + c)).toRingHom
  have compatible {m n : ℕ} (hmn : m ≤ n) :
      (Ideal.Quotient.factorPow I hmn).comp (level n) = level m := by
    have hmn' : m + c ≤ n + c := Nat.add_le_add_right hmn c
    have hquot :
        (Ideal.Quotient.factorPow I hmn).comp
          (Ideal.quotientMap (I ^ n) (RingHom.id R) (hcofinal n)) =
        (Ideal.quotientMap (I ^ m) (RingHom.id R) (hcofinal m)).comp
          (Ideal.Quotient.factorPow J hmn') := by
      ext x
      rfl
    change (Ideal.Quotient.factorPow I hmn).comp
      ((Ideal.quotientMap (I ^ n) (RingHom.id R) (hcofinal n)).comp
        (evalₐ J (n + c)).toRingHom) = _
    rw [← RingHom.comp_assoc, hquot, RingHom.comp_assoc]
    congr 1
    ext x
    exact factorPow_evalₐ J hmn' x
  let backward : AdicCompletion J R →+* AdicCompletion I R :=
    AdicCompletion.liftRingHom I level compatible
  refine RingEquiv.ofRingHom forward backward ?_ ?_
  · apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    change evalₐ J n (forward (backward x)) = evalₐ J n x
    rw [adicCompletionMap_evalₐ]
    change (Ideal.quotientMap (J ^ n) (RingHom.id R) (by
        simpa using Ideal.pow_right_mono hIJ n)) (evalₐ I n (backward x)) = _
    rw [AdicCompletion.evalₐ_liftRingHom I level compatible]
    change (Ideal.quotientMap (J ^ n) (RingHom.id R) _)
      ((Ideal.quotientMap (I ^ n) (RingHom.id R) (hcofinal n))
        (evalₐ J (n + c) x)) = _
    have hfactor :
        (Ideal.quotientMap (J ^ n) (RingHom.id R) (by
          simpa using Ideal.pow_right_mono hIJ n)).comp
          (Ideal.quotientMap (I ^ n) (RingHom.id R) (hcofinal n)) =
        Ideal.Quotient.factorPow J (Nat.le_add_right n c) := by
      ext a
      rfl
    rw [← RingHom.comp_apply, hfactor]
    exact factorPow_evalₐ J (Nat.le_add_right n c) x
  · apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    change evalₐ I n (backward (forward x)) = evalₐ I n x
    rw [AdicCompletion.evalₐ_liftRingHom I level compatible]
    change (Ideal.quotientMap (I ^ n) (RingHom.id R) (hcofinal n))
      (evalₐ J (n + c) (forward x)) = _
    rw [adicCompletionMap_evalₐ]
    change (Ideal.quotientMap (I ^ n) (RingHom.id R) (hcofinal n))
      ((Ideal.quotientMap (J ^ (n + c)) (RingHom.id R) (by
        simpa using Ideal.pow_right_mono hIJ (n + c)))
        (evalₐ I (n + c) x)) = _
    have hfactor :
        (Ideal.quotientMap (I ^ n) (RingHom.id R) (hcofinal n)).comp
          (Ideal.quotientMap (J ^ (n + c)) (RingHom.id R) (by
            simpa using Ideal.pow_right_mono hIJ (n + c))) =
        Ideal.Quotient.factorPow I (Nat.le_add_right n c) := by
      ext a
      rfl
    rw [← RingHom.comp_apply, hfactor]
    exact factorPow_evalₐ I (Nat.le_add_right n c) x

private theorem map_comap_ideal_le {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] (f : A →+* B) (g : B →+* C) (h : A →+* C)
    (hcomp : g.comp f = h) (J : Ideal C) :
    (J.comap h).map f ≤ J.comap g := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  show g (f a) ∈ J
  rw [← RingHom.comp_apply, hcomp]
  exact ha

private theorem comap_le_map_comap_sup_ker
    {Q T P : Type*} [CommRing Q] [CommRing T] [CommRing P]
    (f : Q →+* T) (q : Q →+* P) (r : T →+* P)
    (hcomp : r.comp f = q) (hq : Function.Surjective q) (J : Ideal P) :
    J.comap r ≤ (J.comap q).map f ⊔ RingHom.ker r := by
  intro y hy
  obtain ⟨x, hx⟩ := hq (r y)
  have hxJ : x ∈ J.comap q := by
    show q x ∈ J
    rw [hx]
    exact hy
  refine Submodule.mem_sup.mpr ⟨f x, Ideal.mem_map_of_mem f hxJ,
    y - f x, ?_, by ring⟩
  show r (y - f x) = 0
  rw [map_sub, ← RingHom.comp_apply, hcomp, hx, sub_self]

private theorem adicCompletion_flat_over_of_flat
    {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [Module.Flat A R] [IsNoetherianRing R] (I : Ideal R) :
    Module.Flat A (AdicCompletion I R) := by
  let : Module.Flat R (AdicCompletion I R) := AdicCompletion.flat_of_isNoetherian I
  exact Module.Flat.trans A R (AdicCompletion I R)

private theorem baseMap_surjective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type w) [CommRing P] [Algebra k P]
    (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    Function.Surjective X.hom.base.hom := by
  intro z
  change k at z
  let e := X.left.base.residueEquiv.toRingEquiv
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (e.symm z : ResidueField X.left.base)
  refine ⟨a, ?_⟩
  have h := X.hom.base.residue_comm a
  have ht (x : k) :
      (residueFieldAlgebra (Λ := Λ) (k := k) P).base.residueEquiv
        (residue ((residueFieldAlgebra (Λ := Λ) (k := k) P).base) x) = x := by
    show ((Ideal.quotientEquivAlgOfEq Λ
      (IsLocalRing.maximalIdeal_eq_bot (R := k))).trans
      (AlgEquiv.quotientBot Λ k)) (residue k x) = x
    rw [residue_def]
    simp
  change (residueFieldAlgebra (Λ := Λ) (k := k) P).base.residueEquiv
      (residue _ (X.hom.base.hom a)) = X.left.base.residueEquiv (residue _ a) at h
  have htarget := ht (X.hom.base.hom a)
  rw [htarget, ha] at h
  have hz : X.left.base.residueEquiv (e.symm z) = z := by simp [e]
  rw [hz] at h
  exact h

/-- The kernel of the base map of a deformation is the maximal ideal of its Artinian base. -/
private theorem ker_base_eq_maximalIdeal
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type w) [CommRing P] [Algebra k P]
    (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    RingHom.ker X.hom.base.hom.toRingHom = IsLocalRing.maximalIdeal X.left.base :=
  IsLocalRing.ker_eq_maximalIdeal (R := X.left.base) (K := k) _
    (show Function.Surjective X.hom.base.hom from baseMap_surjective P X)

/-- **The map of Artinian bases underlying the structural morphism of a deformation is
surjective onto the residue field.** The residue map of an Artinian local ring is surjective and
the two chosen identifications with `k` are compatible with it, so the composite is. -/
public alias surjective_deformationHomBase := baseMap_surjective

private theorem specialFiberMap_surjective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type w) [CommRing P] [Algebra k P]
    (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    Function.Surjective X.hom.map.hom ∧
      RingHom.ker X.hom.map.hom =
        (RingHom.ker X.hom.base.hom.toRingHom).map
          (algebraMap X.left.base X.left.fiber) := by
  let A := X.left.base
  let Q := X.left.fiber
  let : CommRing A := X.left.base.commRing
  let : CommRing Q := X.left.commRing
  let : Algebra A Q := X.left.algebra
  let : Algebra A k := X.hom.base.hom.toRingHom.toAlgebra
  let : Algebra Q P := X.hom.map.hom.toAlgebra
  let : Algebra A P := ((algebraMap k P).comp (algebraMap A k)).toAlgebra
  have hcomp : (algebraMap Q P).comp (algebraMap A Q) =
      (algebraMap k P).comp (algebraMap A k) := by
    have hw := congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of P => f.hom)
      X.hom.cartesian.w
    dsimp [FlatAlgebraCategory.structureMap, FlatAlgebraCategory.baseMap] at hw
    change (X.hom.map.hom).comp (algebraMap A Q) =
      (algebraMap k P).comp X.hom.base.hom.toRingHom at hw
    rw [← RingHom.algebraMap_toAlgebra X.hom.map.hom,
      ← RingHom.algebraMap_toAlgebra X.hom.base.hom.toRingHom] at hw
    exact hw
  let : IsScalarTower A Q P := IsScalarTower.of_algebraMap_eq' hcomp.symm
  let : IsScalarTower A k P := IsScalarTower.of_algebraMap_eq' rfl
  have hcat := X.hom.cartesian
  have hcat' : IsPushout (CommRingCat.ofHom (algebraMap A k))
      (CommRingCat.ofHom (algebraMap A Q)) (CommRingCat.ofHom (algebraMap k P))
      (CommRingCat.ofHom (algebraMap Q P)) := hcat.flip
  have hpush : Algebra.IsPushout A k Q P := by
    apply (CommRingCat.isPushout_iff_isPushout (R := A) (S := Q) (R' := k) (S' := P)).mp
    exact hcat'
  let : Algebra.IsPushout A k Q P := hpush
  have hsurjBase : Function.Surjective X.hom.base.hom := by
    simpa [residueFieldAlgebra] using baseMap_surjective P X
  have hsurj : Function.Surjective (algebraMap A k) := by
    show Function.Surjective X.hom.base.hom
    exact hsurjBase
  have hresult := (Algebra.IsPushout.surjective_and_ker_eq_map_of_surjective
    (R := A) (S := k) (R' := Q) (S' := P) hsurj).1
  constructor
  · show Function.Surjective (algebraMap Q P)
    exact hresult
  · show RingHom.ker (algebraMap Q P) =
      (RingHom.ker (algebraMap A k)).map (algebraMap A Q)
    exact (Algebra.IsPushout.surjective_and_ker_eq_map_of_surjective
      (R := A) (S := k) (R' := Q) (S' := P) hsurj).2

/-- The kernel of the map of special fibres of a deformation is nilpotent. -/
private theorem isNilpotent_ker_map
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type w) [CommRing P] [Algebra k P]
    (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    IsNilpotent (RingHom.ker X.hom.map.hom) := by
  rw [(specialFiberMap_surjective P X).2]
  have hbaseNil : IsNilpotent (RingHom.ker X.hom.base.hom.toRingHom) := by
    rw [ker_base_eq_maximalIdeal P X, ← IsLocalRing.ringJacobson_eq_maximalIdeal,
      ← Ideal.jacobson_bot]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  obtain ⟨n, hn⟩ := hbaseNil
  exact ⟨n, by rw [← Ideal.map_pow, hn]; simp⟩

-- The prime ideal argument lifts finite generators across the nilpotent kernel.
private theorem deformationFiber_isNoetherian
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type w) [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    IsNoetherianRing X.left.fiber := by
  let A := X.left.base
  let Q := X.left.fiber
  let : CommRing A := X.left.base.commRing
  let : CommRing Q := X.left.commRing
  let : IsNoetherianRing P := inferInstance
  let : IsNoetherianRing A := inferInstance
  have hbaseFg : (RingHom.ker X.hom.base.hom.toRingHom).FG := by
    rw [ker_base_eq_maximalIdeal P X]
    exact Ideal.fg_of_isNoetherianRing _
  obtain ⟨hQsurj, hQker⟩ := specialFiberMap_surjective P X
  have hQfg : (RingHom.ker X.hom.map.hom).FG := by
    rw [hQker]
    exact Ideal.FG.map hbaseFg _
  have hQnil := isNilpotent_ker_map P X
  let : IsNoetherianRing (residueFieldAlgebra (Λ := Λ) (k := k) P).fiber := by
    show IsNoetherianRing P
    infer_instance
  exact isNoetherianRing_of_surjective_fg_nilpotent_ker
    X.hom.map.hom hQsurj hQfg hQnil

private theorem completionFinite_isPushout
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (I : Ideal R) :
    let L := I.map (algebraMap R S)
    IsPushout
      (CommRingCat.ofHom (algebraMap R (AdicCompletion I R)))
      (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (adicCompletionMap (algebraMap R S) I L le_rfl))
      (CommRingCat.ofHom (algebraMap S (AdicCompletion L S))) := by
  let L := I.map (algebraMap R S)
  let fhat : AdicCompletion I R →+* AdicCompletion L S :=
    adicCompletionMap (algebraMap R S) I L le_rfl
  let : Algebra (AdicCompletion I R) (AdicCompletion L S) := fhat.toAlgebra
  have hR : fhat.comp (algebraMap R (AdicCompletion I R)) =
      algebraMap R (AdicCompletion L S) := by
    rw [adicCompletionMap_comp_algebraMap]
    exact IsScalarTower.algebraMap_eq R S (AdicCompletion L S)
  let : IsScalarTower R (AdicCompletion I R) (AdicCompletion L S) :=
    IsScalarTower.of_algebraMap_eq' hR.symm
  let e := ofTensorProductAlgEquiv I S
  have hleft (a : AdicCompletion I R) :
      e (algebraMap (AdicCompletion I R) (AdicCompletion I R ⊗[R] S) a) = fhat a := by
    apply AdicCompletion.ext_evalₐ
    intro n
    show evalₐ L n (e (a ⊗ₜ[R] 1)) = evalₐ L n (fhat a)
    show evalₐ L n (ofTensorProductLinearEquiv I S (a ⊗ₜ[R] 1)) = _
    rw [ofTensorProductLinearEquiv_tmul_eval, adicCompletionMap_evalₐ]
    simp [L]
  let e' : (AdicCompletion I R ⊗[R] S) ≃ₐ[AdicCompletion I R]
      AdicCompletion L S :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) hleft
  have hright : e'.toRingHom.comp
      (Algebra.TensorProduct.includeRight : S →ₐ[R]
        AdicCompletion I R ⊗[R] S).toRingHom =
      algebraMap S (AdicCompletion L S) := by
    apply RingHom.ext
    intro s
    apply AdicCompletion.ext_evalₐ
    intro n
    show evalₐ L n (e (1 ⊗ₜ[R] s)) = _
    show evalₐ L n (ofTensorProductLinearEquiv I S (1 ⊗ₜ[R] s)) = _
    rw [ofTensorProductLinearEquiv_tmul_eval]
    simp [L]
  let : Algebra S (AdicCompletion I R ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let : Algebra.IsPushout R (AdicCompletion I R) S
      (AdicCompletion I R ⊗[R] S) := inferInstance
  have hp : Algebra.IsPushout R (AdicCompletion I R) S
      (AdicCompletion L S) :=
    Algebra.IsPushout.of_equiv e' hright
  have hcat := (CommRingCat.isPushout_iff_isPushout (R := R)
    (S := AdicCompletion I R) (R' := S) (S' := AdicCompletion L S)).mpr
    ((Algebra.IsPushout.comm R (AdicCompletion I R) S (AdicCompletion L S)).mp hp)
  change IsPushout (CommRingCat.ofHom (algebraMap R S))
    (CommRingCat.ofHom (algebraMap R (AdicCompletion I R)))
    (CommRingCat.ofHom (algebraMap S (AdicCompletion L S)))
    (CommRingCat.ofHom fhat) at hcat
  exact hcat.flip

private theorem completion_quotientAlgEquiv_apply
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I J : Ideal R) (x : AdicCompletion I R) :
    adicCompletionQuotientAlgEquiv I J
      (algebraMap (AdicCompletion I R)
        (AdicCompletion I R ⧸ J.map (algebraMap R (AdicCompletion I R))) x) =
      adicCompletionMap (Ideal.Quotient.mk J) I (I.map (Ideal.Quotient.mk J)) le_rfl x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  induction x using AdicCompletion.induction_on with
  | h a =>
      show evalₐ (I.map (algebraMap R (R ⧸ J))) n
          (ofTensorProductLinearEquiv I (R ⧸ J)
            ((AdicCompletion.mk I R a) ⊗ₜ[R] 1)) = _
      rw [ofTensorProductLinearEquiv_tmul_eval]
      simp [adicCompletionMap_evalₐ]

private noncomputable def completion_quotientRingEquiv
    {R S : Type*} [CommRing R] [IsNoetherianRing R] [CommRing S]
    (I L : Ideal R) (I' : Ideal S) (e : R ⧸ L ≃+* S)
    (he : (I.map (Ideal.Quotient.mk L)).map e.toRingHom = I') :
    (AdicCompletion I R ⧸ (L.map (algebraMap R (AdicCompletion I R)))) ≃+*
      AdicCompletion I' S := by
  exact (adicCompletionQuotientAlgEquiv I L).toRingEquiv.trans
    (completionMapRingEquiv e (I.map (Ideal.Quotient.mk L)) I' he)

private theorem completion_quotientRingEquiv_apply
    {R S : Type*} [CommRing R] [IsNoetherianRing R] [CommRing S]
    (I L : Ideal R) (I' : Ideal S) (e : R ⧸ L ≃+* S)
    (he : (I.map (Ideal.Quotient.mk L)).map e.toRingHom = I')
    (x : AdicCompletion I R) :
    completion_quotientRingEquiv I L I' e he
      (algebraMap (AdicCompletion I R)
        (AdicCompletion I R ⧸ (L.map (algebraMap R (AdicCompletion I R)))) x) =
    adicCompletionMap (e.toRingHom.comp (Ideal.Quotient.mk L)) I I'
        (by rw [← Ideal.map_map, he]) x := by
  show adicCompletionMap e.toRingHom (I.map (Ideal.Quotient.mk L)) I' he.le
      (adicCompletionQuotientAlgEquiv I L
        (algebraMap (AdicCompletion I R)
          (AdicCompletion I R ⧸ (L.map (algebraMap R (AdicCompletion I R)))) x)) = _
  rw [completion_quotientAlgEquiv_apply]
  have hc := completionMap_comp (Ideal.Quotient.mk L) e.toRingHom I
    (I.map (Ideal.Quotient.mk L)) I' le_rfl he.le
  exact DFunLike.congr_fun hc x

private theorem completion_pushout
    {A k Q P : Type*} [CommRing A] [Field k] [CommRing Q] [CommRing P]
    [Algebra A Q] [Algebra A k] [Algebra k P] [Algebra A P] [IsScalarTower A k P]
    [Algebra Q P] [IsScalarTower A Q P] [IsNoetherianRing Q]
    (q : Q →ₐ[A] P) (J : Ideal P)
    [Algebra (AdicCompletion (J.comap q.toRingHom) Q) (AdicCompletion J P)]
    [IsScalarTower A (AdicCompletion (J.comap q.toRingHom) Q) (AdicCompletion J P)]
    (hq : Function.Surjective q.toRingHom)
    (hf : Function.Surjective (algebraMap A k))
    (hker : RingHom.ker q.toRingHom =
      (RingHom.ker (algebraMap A k)).map (algebraMap A Q))
    (hmap : algebraMap (AdicCompletion (J.comap q.toRingHom) Q) (AdicCompletion J P) =
      adicCompletionMap q.toRingHom (J.comap q.toRingHom) J
        (Ideal.map_le_iff_le_comap.mpr le_rfl)) :
    Algebra.IsPushout A k (AdicCompletion (J.comap q.toRingHom) Q)
      (AdicCompletion J P) := by
  let L : Ideal A := RingHom.ker (algebraMap A k)
  let LQ : Ideal Q := L.map (algebraMap A Q)
  let K : Ideal Q := J.comap q.toRingHom
  have hK : K.map q.toRingHom = J := Ideal.map_comap_of_surjective _ hq J
  have hker' : RingHom.ker q.toRingHom = LQ := hker
  let eqKer : (Q ⧸ LQ) ≃ₐ[A] (Q ⧸ RingHom.ker q.toRingHom) :=
    Ideal.quotientEquivAlgOfEq A hker'.symm
  let eqSurj : (Q ⧸ RingHom.ker q.toRingHom) ≃ₐ[A] P :=
    Ideal.quotientKerAlgEquivOfSurjective hq
  let eqQ : (Q ⧸ LQ) ≃ₐ[A] P := eqKer.trans eqSurj
  have hqbar : eqQ.toRingHom.comp (Ideal.Quotient.mk LQ) = q.toRingHom := by
    ext x
    show (Ideal.quotientKerAlgEquivOfSurjective hq)
      (Ideal.Quotient.mk (RingHom.ker q.toRingHom) x) = q x
    exact Ideal.quotientKerAlgEquivOfSurjective_mk hq x
  have hKbar : (K.map (Ideal.Quotient.mk LQ)).map eqQ.toRingHom = J := by
    calc
      (K.map (Ideal.Quotient.mk LQ)).map eqQ.toRingHom =
          K.map (eqQ.toRingHom.comp (Ideal.Quotient.mk LQ)) := by rw [Ideal.map_map]
      _ = K.map q.toRingHom := by rw [hqbar]
      _ = J := hK
  let qhat : AdicCompletion K Q →+* AdicCompletion J P :=
    adicCompletionMap q.toRingHom K J (Ideal.map_le_iff_le_comap.mpr le_rfl)
  have hqA : q.toRingHom.comp (algebraMap A Q) = algebraMap A P := by
    ext a
    exact q.commutes a
  have htower : (algebraMap Q (AdicCompletion K Q)).comp (algebraMap A Q) =
      algebraMap A (AdicCompletion K Q) := IsScalarTower.algebraMap_eq A Q _
  have hA : qhat.comp (algebraMap A (AdicCompletion K Q)) =
      algebraMap A (AdicCompletion J P) := by
    show (adicCompletionMap q.toRingHom K J _).comp
      (algebraMap A (AdicCompletion K Q)) = _
    rw [← htower, ← RingHom.comp_assoc, adicCompletionMap_comp_algebraMap]
    rw [RingHom.comp_assoc, hqA]
    exact IsScalarTower.algebraMap_eq A P (AdicCompletion J P)
  let eqComp := completion_quotientRingEquiv K LQ J eqQ.toRingEquiv hKbar
  have heqComp (x : AdicCompletion K Q) :
      eqComp (algebraMap (AdicCompletion K Q)
        (AdicCompletion K Q ⧸ (LQ.map (algebraMap Q (AdicCompletion K Q)))) x) = qhat x := by
    show completion_quotientRingEquiv K LQ J eqQ.toRingEquiv hKbar
        (algebraMap (AdicCompletion K Q)
          (AdicCompletion K Q ⧸ LQ.map (algebraMap Q (AdicCompletion K Q))) x) = _
    rw [completion_quotientRingEquiv_apply]
    calc
      adicCompletionMap (eqQ.toRingHom.comp (Ideal.Quotient.mk LQ)) K J _ x =
          adicCompletionMap q.toRingHom K J _ x :=
            congrArg (fun g => g x) (completionMap_congr hqbar K J _ _)
      _ = qhat x := rfl
  let Lhat : Ideal (AdicCompletion K Q) := L.map (algebraMap A (AdicCompletion K Q))
  have hLhat : LQ.map (algebraMap Q (AdicCompletion K Q)) = Lhat := by
    dsimp [LQ]
    rw [Ideal.map_map]
    rw [← IsScalarTower.algebraMap_eq A Q (AdicCompletion K Q)]
  let eqIdeal : (AdicCompletion K Q ⧸ LQ.map (algebraMap Q (AdicCompletion K Q))) ≃ₐ[
      AdicCompletion K Q] (AdicCompletion K Q ⧸ Lhat) :=
    Ideal.quotientEquivAlgOfEq (AdicCompletion K Q) hLhat
  let eqCompAlg :
      (AdicCompletion K Q ⧸ (LQ.map (algebraMap Q (AdicCompletion K Q)))) ≃ₐ[
        AdicCompletion K Q] AdicCompletion J P :=
    AlgEquiv.ofRingEquiv (f := eqComp) (by
      intro x
      exact (heqComp x).trans (congrArg (fun g => g x) hmap).symm)
  let eqCompAlg' : (AdicCompletion K Q ⧸ Lhat) ≃ₐ[AdicCompletion K Q]
      AdicCompletion J P := eqIdeal.symm.trans eqCompAlg
  let fBase : A →ₐ[A] k :=
    { toRingHom := algebraMap A k
      commutes' := fun _ => rfl }
  let eBase : (A ⧸ L) ≃ₐ[A] k :=
    (Ideal.quotientEquivAlgOfEq A (show L = RingHom.ker fBase by rfl)).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := fBase) hf)
  let eTensor :
      AdicCompletion K Q ⊗[A] k ≃ₐ[AdicCompletion K Q]
        (AdicCompletion K Q ⧸ Lhat) :=
    (AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.congr
        (AlgEquiv.refl : AdicCompletion K Q ≃ₐ[A] AdicCompletion K Q) eBase).symm.toRingEquiv)
      (by intro x; simp)).trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (AdicCompletion K Q) L).symm
  let C := AdicCompletion K Q ⧸ Lhat
  let : Algebra k (AdicCompletion K Q ⊗[A] k) := Algebra.TensorProduct.rightAlgebra
  let : Algebra k C :=
    (eTensor.toRingEquiv.toRingHom.comp
      (algebraMap k (AdicCompletion K Q ⊗[A] k))).toAlgebra
  have htowerC : (algebraMap k C).comp (algebraMap A k) = algebraMap A C := by
    ext a
    apply eTensor.symm.injective
    show eTensor.symm (algebraMap k C (algebraMap A k a)) =
      eTensor.symm (algebraMap A C a)
    rw [IsScalarTower.algebraMap_apply A (AdicCompletion K Q) C a,
      eTensor.symm.commutes]
    calc
      eTensor.symm (algebraMap k C (algebraMap A k a)) =
          algebraMap k (AdicCompletion K Q ⊗[A] k) (algebraMap A k a) := by
            show eTensor.symm (eTensor
              (algebraMap k (AdicCompletion K Q ⊗[A] k) (algebraMap A k a))) = _
            simp
      _ = algebraMap A (AdicCompletion K Q ⊗[A] k) a :=
        (IsScalarTower.algebraMap_apply A k (AdicCompletion K Q ⊗[A] k) a).symm
      _ = algebraMap (AdicCompletion K Q)
          (AdicCompletion K Q ⊗[A] k) (algebraMap A (AdicCompletion K Q) a) := by
            rw [IsScalarTower.algebraMap_apply A (AdicCompletion K Q)
              (AdicCompletion K Q ⊗[A] k) a]
  let : IsScalarTower A k C := IsScalarTower.of_algebraMap_eq' htowerC.symm
  let : Algebra.IsPushout A (AdicCompletion K Q) k
      (AdicCompletion K Q ⊗[A] k) := inferInstance
  have hquot : Algebra.IsPushout A (AdicCompletion K Q) k
      C :=
    Algebra.IsPushout.of_equiv (R := A) (R' := AdicCompletion K Q) (S := k)
      (S' := AdicCompletion K Q ⊗[A] k) eTensor (by
        ext x
        rfl)
  let : Algebra.IsPushout A (AdicCompletion K Q) k C := hquot
  have hmapA : eqCompAlg'.toRingHom.comp (algebraMap A C) =
      algebraMap A (AdicCompletion J P) := by
    rw [IsScalarTower.algebraMap_eq A (AdicCompletion K Q) C,
      ← RingHom.comp_assoc]
    have hQ : eqCompAlg'.toRingHom.comp (algebraMap (AdicCompletion K Q) C) =
        algebraMap (AdicCompletion K Q) (AdicCompletion J P) :=
      RingHom.ext eqCompAlg'.commutes
    rw [hQ]
    exact (IsScalarTower.algebraMap_eq A (AdicCompletion K Q) (AdicCompletion J P)).symm
  have hmapK : eqCompAlg'.toRingHom.comp (algebraMap k C) =
      algebraMap k (AdicCompletion J P) := by
    apply RingHom.ext
    intro x
    obtain ⟨a, ha⟩ := hf x
    rw [← ha]
    show eqCompAlg' (algebraMap k C ((algebraMap A k) a)) =
      algebraMap k (AdicCompletion J P) ((algebraMap A k) a)
    rw [← IsScalarTower.algebraMap_apply A k C a,
      ← IsScalarTower.algebraMap_apply A k (AdicCompletion J P) a]
    exact congrArg (fun f => f a) hmapA
  exact (Algebra.IsPushout.of_equiv (R := A) (R' := AdicCompletion K Q)
    (S := k) (S' := C) eqCompAlg' hmapK).symm

/-- A morphism of deformations commutes with the maps to the special fibre. -/
private theorem comp_map_hom_eq
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {P : Type w} [CommRing P] [Algebra k P]
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P} (f : X ⟶ Y) :
    Y.hom.map.hom.comp f.left.map.hom = X.hom.map.hom :=
  congrArg (fun g : X.left ⟶ residueFieldAlgebra (Λ := Λ) (k := k) P => g.map.hom) (Over.w f)

private theorem deformationMap_completionIdeal_le
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type w) [CommRing P] [Algebra k P] (J : Ideal P)
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P} (f : X ⟶ Y) :
    (J.comap X.hom.map.hom).map f.left.map.hom ≤
      J.comap Y.hom.map.hom := by
  exact map_comap_ideal_le f.left.map.hom Y.hom.map.hom X.hom.map.hom (comp_map_hom_eq f) J

private noncomputable def completedFlatAlgebra
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type w) [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    FlatAlgebraCategory (Λ := Λ) (k := k) where
  base := X.left.base
  fiber := AdicCompletion (J.comap X.hom.map.hom) X.left.fiber
  flat := by
    let : IsNoetherianRing X.left.fiber := deformationFiber_isNoetherian P X
    exact adicCompletion_flat_over_of_flat (J.comap X.hom.map.hom)

private theorem completedSpecialFiber_isPushout
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type w) [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    letI : CommRing X.left.fiber := X.left.commRing
    letI : CommRing (residueFieldAlgebra (Λ := Λ) (k := k) P).fiber :=
      (residueFieldAlgebra (Λ := Λ) (k := k) P).commRing
    let qhat : AdicCompletion (J.comap X.hom.map.hom) X.left.fiber →+*
        AdicCompletion J P := adicCompletionMap X.hom.map.hom
          (J.comap X.hom.map.hom) J (Ideal.map_le_iff_le_comap.mpr le_rfl)
    IsPushout
      (FlatAlgebraCategory.structureMap (completedFlatAlgebra P J X))
      (FlatAlgebraCategory.baseMap X.hom.base)
      (CommRingCat.ofHom qhat)
      (FlatAlgebraCategory.structureMap
        (residueFieldAlgebra (Λ := Λ) (k := k) (AdicCompletion J P))) := by
  let A := X.left.base
  let Q := X.left.fiber
  let : CommRing A := X.left.base.commRing
  let : CommRing Q := X.left.commRing
  let : Algebra A Q := X.left.algebra
  let : Algebra A k := X.hom.base.hom.toRingHom.toAlgebra
  let : Algebra Q P := X.hom.map.hom.toAlgebra
  let : Algebra A P := ((algebraMap k P).comp (algebraMap A k)).toAlgebra
  let q : Q →ₐ[A] P :=
    { toRingHom := X.hom.map.hom
      commutes' := by
        intro a
        have hw := congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of P => f.hom)
          X.hom.cartesian.w
        exact congrArg (fun f : A →+* P => f a) hw }
  let : IsScalarTower A k P := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A Q P := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (q.commutes a).symm)
  let K : Ideal Q := J.comap q.toRingHom
  let qhat : AdicCompletion K Q →+* AdicCompletion J P :=
    adicCompletionMap q.toRingHom K J (Ideal.map_le_iff_le_comap.mpr le_rfl)
  let : Algebra (AdicCompletion K Q) (AdicCompletion J P) := qhat.toAlgebra
  have hA : qhat.comp (algebraMap A (AdicCompletion K Q)) =
      algebraMap A (AdicCompletion J P) := by
    rw [IsScalarTower.algebraMap_eq A Q (AdicCompletion K Q),
      ← RingHom.comp_assoc, adicCompletionMap_comp_algebraMap]
    rw [RingHom.comp_assoc]
    have hq : q.toRingHom.comp (algebraMap A Q) = algebraMap A P := by
      ext a
      exact q.commutes a
    rw [hq]
    exact IsScalarTower.algebraMap_eq A P (AdicCompletion J P)
  let : IsScalarTower A (AdicCompletion K Q) (AdicCompletion J P) :=
    IsScalarTower.of_algebraMap_eq' hA.symm
  obtain ⟨hsurj, hker⟩ := specialFiberMap_surjective P X
  let : IsNoetherianRing Q := deformationFiber_isNoetherian P X
  have hpush : Algebra.IsPushout A k (AdicCompletion K Q) (AdicCompletion J P) :=
    completion_pushout q J hsurj (baseMap_surjective P X) hker rfl
  show IsPushout (CommRingCat.ofHom (algebraMap A (AdicCompletion K Q)))
    (CommRingCat.ofHom (algebraMap A k)) (CommRingCat.ofHom qhat)
    (CommRingCat.ofHom (algebraMap k (AdicCompletion J P)))
  exact ((CommRingCat.isPushout_iff_isPushout (R := A)
    (S := AdicCompletion K Q) (R' := k) (S' := AdicCompletion J P)).mpr hpush).flip

private noncomputable def completedDeformation
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type w) [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    ringDeformationCategory (Λ := Λ) (k := k) (AdicCompletion J P) := by
  refine Over.mk (X := residueFieldAlgebra (Λ := Λ) (k := k) (AdicCompletion J P))
    (Y := completedFlatAlgebra P J X) ?_
  refine ⟨X.hom.base, CommRingCat.ofHom (adicCompletionMap X.hom.map.hom
    (J.comap X.hom.map.hom) J (Ideal.map_le_iff_le_comap.mpr le_rfl)), ?_⟩
  exact completedSpecialFiber_isPushout P J X

private noncomputable def completedHomMap
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type w) [CommRing P] [Algebra k P] (J : Ideal P)
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P} (f : X ⟶ Y) :
    AdicCompletion (J.comap X.hom.map.hom) X.left.fiber →+*
      AdicCompletion (J.comap Y.hom.map.hom) Y.left.fiber :=
  adicCompletionMap f.left.map.hom _ _ (deformationMap_completionIdeal_le P J f)

private theorem completedHomMap_algebraMap
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type w) [CommRing P] [Algebra k P] (J : Ideal P)
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P} (f : X ⟶ Y)
    (q : X.left.fiber) :
    completedHomMap P J f
        (algebraMap X.left.fiber
          (AdicCompletion (J.comap X.hom.map.hom) X.left.fiber) q) =
      algebraMap Y.left.fiber
        (AdicCompletion (J.comap Y.hom.map.hom) Y.left.fiber) (f.left.map.hom q) :=
  DFunLike.congr_fun
    (adicCompletionMap_comp_algebraMap f.left.map.hom _ _
      (deformationMap_completionIdeal_le P J f)) q

private theorem completedHomMap_id
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type w) [CommRing P] [Algebra k P] (J : Ideal P)
    (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    completedHomMap P J (𝟙 X) =
      RingHom.id (AdicCompletion (J.comap X.hom.map.hom) X.left.fiber) := by
  show adicCompletionMap (RingHom.id X.left.fiber) _ _ _ = _
  exact completionMap_id _

private theorem completedHomMap_comp
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type w) [CommRing P] [Algebra k P] (J : Ideal P)
    {X Y Z : ringDeformationCategory (Λ := Λ) (k := k) P}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    completedHomMap P J (f ≫ g) =
      (completedHomMap P J g).comp (completedHomMap P J f) := by
  show adicCompletionMap (g.left.map.hom.comp f.left.map.hom) _ _ _ = _
  exact (completionMap_comp f.left.map.hom g.left.map.hom _ _ _
    (deformationMap_completionIdeal_le P J f)
    (deformationMap_completionIdeal_le P J g)).symm

private theorem finite_of_artinian_local_residue_surjective
    {A B k : Type*} [CommRing A] [CommRing B] [Field k]
    [Algebra A B] [IsArtinianRing B] [IsLocalRing B]
    (r : B →+* k) (hr : Function.Surjective (r.comp (algebraMap A B)))
    (hker : RingHom.ker r = IsLocalRing.maximalIdeal B) :
    Module.Finite A B := by
  have hfinite : Module.Finite A (B ⧸ Ring.jacobson B) := by
    apply Module.Finite.of_surjective (Algebra.linearMap A (B ⧸ Ring.jacobson B))
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha⟩ := hr (r b)
    refine ⟨a, ?_⟩
    show Ideal.Quotient.mk _ (algebraMap A B a) = Ideal.Quotient.mk _ b
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      IsLocalRing.ringJacobson_eq_maximalIdeal, ← hker]
    show r (algebraMap A B a - b) = 0
    change r (algebraMap A B a) = r b at ha
    simpa only [map_sub] using sub_eq_zero.mpr ha
  exact IsSemiprimaryRing.finite_of_isArtinian A B B

private theorem deformationMap_completionIdeal_cofinal
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type w) [CommRing P] [Algebra k P] (J : Ideal P)
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P} (f : X ⟶ Y) :
    ∃ c : ℕ, ∀ n : ℕ,
      (J.comap Y.hom.map.hom) ^ (n + c) ≤
        ((J.comap X.hom.map.hom).map f.left.map.hom) ^ n := by
  obtain ⟨c, hc⟩ := isNilpotent_ker_map P Y
  have hcomp := comp_map_hom_eq f
  have hsup : J.comap Y.hom.map.hom ≤
      (J.comap X.hom.map.hom).map f.left.map.hom ⊔
        RingHom.ker Y.hom.map.hom :=
    comap_le_map_comap_sup_ker f.left.map.hom X.hom.map.hom
      Y.hom.map.hom hcomp (specialFiberMap_surjective P X).1 J
  refine ⟨c, fun n => ?_⟩
  calc
    (J.comap Y.hom.map.hom) ^ (n + c) ≤
        ((J.comap X.hom.map.hom).map f.left.map.hom ⊔
          RingHom.ker Y.hom.map.hom) ^ (n + c) :=
      pow_le_pow_left' hsup _
    _ ≤ ((J.comap X.hom.map.hom).map f.left.map.hom) ^ n ⊔
          (RingHom.ker Y.hom.map.hom) ^ c := Ideal.sup_pow_add_le_pow_sup_pow
    _ = ((J.comap X.hom.map.hom).map f.left.map.hom) ^ n := by
      simp [hc]

private theorem completedHomMap_isPushout
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type w) [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P)
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P} (f : X ⟶ Y) :
    IsPushout
      (FlatAlgebraCategory.structureMap (completedFlatAlgebra P J X))
      (FlatAlgebraCategory.baseMap f.left.base)
      (CommRingCat.ofHom (completedHomMap P J f))
      (FlatAlgebraCategory.structureMap (completedFlatAlgebra P J Y)) := by
  let A := X.left.base
  let B := Y.left.base
  let Q := X.left.fiber
  let T := Y.left.fiber
  let : CommRing A := X.left.base.commRing
  let : CommRing B := Y.left.base.commRing
  let : CommRing Q := X.left.commRing
  let : CommRing T := Y.left.commRing
  let : Algebra A Q := X.left.algebra
  let : Algebra B T := Y.left.algebra
  let : Algebra A B := f.left.base.hom.toRingHom.toAlgebra
  let : Algebra Q T := f.left.map.hom.toAlgebra
  let : Algebra A T := ((algebraMap B T).comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq' rfl
  have hAQ : (algebraMap Q T).comp (algebraMap A Q) = algebraMap A T := by
    have hw := congrArg (fun g : CommRingCat.of A ⟶ CommRingCat.of T => g.hom)
      f.left.cartesian.w
    dsimp [FlatAlgebraCategory.structureMap, FlatAlgebraCategory.baseMap] at hw
    change (f.left.map.hom).comp (algebraMap A Q) =
      (algebraMap B T).comp f.left.base.hom.toRingHom at hw
    exact hw
  let : IsScalarTower A Q T := IsScalarTower.of_algebraMap_eq' hAQ.symm
  have hcat : IsPushout (CommRingCat.ofHom (algebraMap A Q))
      (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (algebraMap Q T))
      (CommRingCat.ofHom (algebraMap B T)) := f.left.cartesian
  have hpush : Algebra.IsPushout A B Q T :=
    (CommRingCat.isPushout_iff_isPushout (R := A) (S := Q)
      (R' := B) (S' := T)).mp hcat.flip
  have hbasecomp : Y.hom.base.hom.toRingHom.comp (algebraMap A B) =
      X.hom.base.hom.toRingHom :=
    congrArg (fun g : X.left ⟶ residueFieldAlgebra (Λ := Λ) (k := k) P =>
      g.base.hom.toRingHom) (Over.w f)
  have hbaseker := ker_base_eq_maximalIdeal P Y
  let r : B →+* k := Y.hom.base.hom.toRingHom
  have hr : Function.Surjective (r.comp (algebraMap A B)) := by
    have h : r.comp (algebraMap A B) = X.hom.base.hom.toRingHom := hbasecomp
    rw [h]
    exact baseMap_surjective P X
  let : Module.Finite A B :=
    finite_of_artinian_local_residue_surjective r hr hbaseker
  let : Algebra.IsPushout A Q B T :=
    (Algebra.IsPushout.comm A B Q T).mp hpush
  let : Module.Finite Q (Q ⊗[A] B) := Module.Finite.base_change A Q B
  let : Module.Finite Q T :=
    Module.Finite.equiv (Algebra.IsPushout.equiv A Q B T).toLinearEquiv
  let I : Ideal Q := J.comap X.hom.map.hom
  let L : Ideal T := I.map (algebraMap Q T)
  let K : Ideal T := J.comap Y.hom.map.hom
  have hLK : L ≤ K := deformationMap_completionIdeal_le P J f
  obtain ⟨c, hcofinal⟩ := deformationMap_completionIdeal_cofinal P J f
  let e : AdicCompletion L T ≃+* AdicCompletion K T :=
    completionCongrOfCofinalPowers L K hLK c hcofinal
  have hId : L.map (RingHom.id T) ≤ K := by simpa using hLK
  have he : e.toRingHom.comp
      (adicCompletionMap (algebraMap Q T) I L le_rfl) =
        completedHomMap P J f := by
    show (adicCompletionMap (RingHom.id T) L K hId).comp
      (adicCompletionMap (algebraMap Q T) I L le_rfl) = _
    rw [completionMap_comp]
    exact completionMap_congr (by rfl) I K _ _
  have heT : e.toRingHom.comp (algebraMap T (AdicCompletion L T)) =
      algebraMap T (AdicCompletion K T) := by
    show (adicCompletionMap (RingHom.id T) L K hId).comp
      (algebraMap T (AdicCompletion L T)) = _
    simpa using adicCompletionMap_comp_algebraMap (RingHom.id T) L K hId
  let : IsNoetherianRing Q := deformationFiber_isNoetherian P X
  have hfinite := completionFinite_isPushout (R := Q) (S := T) I
  have hpaste := hcat.paste_horiz hfinite
  have hpaste' : IsPushout
      (CommRingCat.ofHom (algebraMap A (AdicCompletion I Q)))
      (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (adicCompletionMap (algebraMap Q T) I L le_rfl))
      (CommRingCat.ofHom (algebraMap B (AdicCompletion L T))) := by
    simpa only [← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq] using hpaste
  have heB : e.toRingHom.comp (algebraMap B (AdicCompletion L T)) =
      algebraMap B (AdicCompletion K T) := by
    rw [IsScalarTower.algebraMap_eq B T (AdicCompletion L T),
      ← RingHom.comp_assoc, heT,
      IsScalarTower.algebraMap_eq B T (AdicCompletion K T)]
  show IsPushout
    (CommRingCat.ofHom (algebraMap A (AdicCompletion I Q)))
    (CommRingCat.ofHom (algebraMap A B))
    (CommRingCat.ofHom (completedHomMap P J f))
    (CommRingCat.ofHom (algebraMap B (AdicCompletion K T)))
  refine hpaste'.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      e.toCommRingCatIso (by simp) (by simp) ?_ ?_
  · apply CommRingCat.hom_ext
    simpa using he
  · apply CommRingCat.hom_ext
    simpa using heB

private noncomputable def completedHom
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type w) [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P)
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P} (f : X ⟶ Y) :
    completedFlatAlgebra P J X ⟶ completedFlatAlgebra P J Y where
  base := f.left.base
  map := CommRingCat.ofHom (completedHomMap P J f)
  cartesian := completedHomMap_isPushout P J f

private noncomputable def completedDeformationHom
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type w) [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P)
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P} (f : X ⟶ Y) :
    completedDeformation P J X ⟶ completedDeformation P J Y := by
  refine Over.homMk (completedHom P J f) ?_
  change completedHom P J f ≫ (completedDeformation P J Y).hom =
    (completedDeformation P J X).hom
  apply FlatAlgebraCategory.Hom.ext
  · exact congrArg (fun h : X.left ⟶ residueFieldAlgebra (Λ := Λ) (k := k) P =>
      h.base) (Over.w f)
  · apply CommRingCat.hom_ext
    change (adicCompletionMap Y.hom.map.hom (J.comap Y.hom.map.hom) J
          (Ideal.map_le_iff_le_comap.mpr le_rfl)).comp
        (adicCompletionMap f.left.map.hom (J.comap X.hom.map.hom)
          (J.comap Y.hom.map.hom) (deformationMap_completionIdeal_le P J f)) =
      adicCompletionMap X.hom.map.hom (J.comap X.hom.map.hom) J
        (Ideal.map_le_iff_le_comap.mpr le_rfl)
    rw [completionMap_comp f.left.map.hom Y.hom.map.hom
      (J.comap X.hom.map.hom) (J.comap Y.hom.map.hom) J
      (deformationMap_completionIdeal_le P J f)
      (Ideal.map_le_iff_le_comap.mpr le_rfl)]
    exact completionMap_congr (comp_map_hom_eq f) _ _ _ _

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable (P : Type w) [CommRing P] [Algebra k P] (J : Ideal P)

/-- Completion of deformations, including its identification on fibers and
its compatibility with the canonical maps into those completions. -/
public structure AdicCompletionFunctorData where
  functor : BasedFunctor
    (BasedCategory.ofFunctor
      (Over.forget (residueFieldAlgebra (Λ := Λ) (k := k) P) ⋙
        FlatAlgebraCategory.projection))
    (BasedCategory.ofFunctor
      (Over.forget (residueFieldAlgebra (Λ := Λ) (k := k)
        (AdicCompletion J P)) ⋙ FlatAlgebraCategory.projection))
  fiberEquiv (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    (functor.obj X).left.fiber ≃+*
      AdicCompletion (J.comap X.hom.map.hom) X.left.fiber
  special_comm (X : ringDeformationCategory (Λ := Λ) (k := k) P)
      (q : X.left.fiber) :
    (functor.obj X).hom.map.hom
      ((fiberEquiv X).symm
        (algebraMap X.left.fiber
          (AdicCompletion (J.comap X.hom.map.hom) X.left.fiber) q)) =
      algebraMap P (AdicCompletion J P) (X.hom.map.hom q)
  map_comm {X Y : ringDeformationCategory (Λ := Λ) (k := k) P}
      (f : X ⟶ Y) (q : X.left.fiber) :
    (functor.map f).left.map.hom
      ((fiberEquiv X).symm
        (algebraMap X.left.fiber
          (AdicCompletion (J.comap X.hom.map.hom) X.left.fiber) q)) =
      (fiberEquiv Y).symm
        (algebraMap Y.left.fiber
          (AdicCompletion (J.comap Y.hom.map.hom) Y.left.fiber)
            (f.left.map.hom q))

/-- The completion functor on deformations, with the identity as fibre identification. -/
private noncomputable def completedFunctorData [IsNoetherianRing P] :
    AdicCompletionFunctorData (Λ := Λ) (k := k) P J :=
  let F : ringDeformationCategory (Λ := Λ) (k := k) P ⥤
      ringDeformationCategory (Λ := Λ) (k := k) (AdicCompletion J P) :=
    { obj := completedDeformation P J
      map := fun f => completedDeformationHom P J f
      map_id := by
        intro X
        ext : 1
        show completedHom P J (𝟙 X) = 𝟙 (completedFlatAlgebra P J X)
        apply FlatAlgebraCategory.Hom.ext
        · rfl
        · exact congrArg CommRingCat.ofHom (completedHomMap_id P J X)
      map_comp := by
        intro X Y Z f g
        ext : 1
        show completedHom P J (f ≫ g) =
          completedHom P J f ≫ completedHom P J g
        apply FlatAlgebraCategory.Hom.ext
        · rfl
        · exact congrArg CommRingCat.ofHom (completedHomMap_comp P J f g) }
  { functor := { toFunctor := F, w := rfl }
    fiberEquiv := fun _ => RingEquiv.refl _
    special_comm := fun X q =>
      DFunLike.congr_fun (adicCompletionMap_comp_algebraMap X.hom.map.hom
        (J.comap X.hom.map.hom) J (Ideal.map_le_iff_le_comap.mpr le_rfl)) q
    map_comm := fun f q => completedHomMap_algebraMap P J f q }

/-- The natural functor taking a deformation to its completion at the inverse
image of `J`, over the same Artinian local algebra. -/
public theorem nonempty_adicCompletionFunctorData [IsNoetherianRing P] :
    Nonempty (AdicCompletionFunctorData (Λ := Λ) (k := k) P J) :=
  ⟨completedFunctorData P J⟩

/-- **The base-compatibility clause for a completion functor.** The fibre identification of a
`Deformation.Examples.AdicCompletionFunctorData` carries the structural map of the Artinian base
of the completed deformation to the structural map of the base of the deformation itself, read
through the identification of the two bases that the functor, being a functor over `𝒞_Λ`,
supplies.

The clause does not follow from the others, which constrain the fibre identification only on the
image of the canonical map out of the fibre of the deformation. What it buys is that the
canonical map `Q → Q^` of a deformation `Q` is a map of algebras over the Artinian base; for a
base presented as `k ⊕ V` that makes it a map of `k`-algebras which is moreover semilinear for
the action of the augmentation ideal, which is what a comparison of the two associated
square-zero extensions needs. -/
public def AdicCompletionFunctorData.IsBaseCompatible
    (F : AdicCompletionFunctorData (Λ := Λ) (k := k) P J) : Prop :=
  ∀ (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    (a : ((F.functor.obj X).left.base : Type w)),
    F.fiberEquiv X
        (algebraMap ((F.functor.obj X).left.base : Type w) (F.functor.obj X).left.fiber a)
      = algebraMap ((X.left.base : Type w))
          (AdicCompletion (J.comap X.hom.map.hom) X.left.fiber)
          ((eqToHom (F.functor.w_obj X)).hom a)

/-- **Completion at the inverse image of `J` is a functor over `𝒞_Λ` whose fibre identification
is compatible with the Artinian base.** This is
`Deformation.Examples.nonempty_adicCompletionFunctorData` together with
`Deformation.Examples.AdicCompletionFunctorData.IsBaseCompatible`: the functor constructed there
keeps the base of a deformation untouched and identifies the completed fibre with the completion
by the identity, so the clause holds by definitional unfolding. -/
public theorem nonempty_isBaseCompatible_adicCompletionFunctorData [IsNoetherianRing P] :
    Nonempty { F : AdicCompletionFunctorData (Λ := Λ) (k := k) P J //
      F.IsBaseCompatible } :=
  ⟨⟨completedFunctorData P J, fun _ _ => rfl⟩⟩

/-- **A base-compatible completion functor datum, chosen once and for all.** This is
`Classical.choice` of
`Deformation.Examples.nonempty_isBaseCompatible_adicCompletionFunctorData`, a `Nonempty` of the
*subtype* cut out by `Deformation.Examples.AdicCompletionFunctorData.IsBaseCompatible`; so the
chosen element carries a proof of that clause as its second component.

`Deformation.Examples.adicCompletionFunctor` is its underlying datum, so base-compatibility of
the completion functor is available as
`Deformation.Examples.isBaseCompatible_adicCompletionFunctor` and no statement about completion
of deformations has to carry it as a hypothesis. -/
public noncomputable def baseCompatibleAdicCompletionFunctor [IsNoetherianRing P] :
    { F : AdicCompletionFunctorData (Λ := Λ) (k := k) P J // F.IsBaseCompatible } :=
  Classical.choice (nonempty_isBaseCompatible_adicCompletionFunctorData P J)

/-- **The completion functor on deformations, Stacks 0DYV.** Completion at the inverse image of
`J` is a functor over `𝒞_Λ` together with the identification of its fibres with the adic
completions; this is one such datum, chosen from the base-compatible ones so that
`Deformation.Examples.isBaseCompatible_adicCompletionFunctor` holds of it. -/
@[stacks 0DYV]
public noncomputable def adicCompletionFunctor [IsNoetherianRing P] :
    AdicCompletionFunctorData (Λ := Λ) (k := k) P J :=
  (baseCompatibleAdicCompletionFunctor P J).1

/-- **The completion functor is base-compatible.** Its fibre identification carries the
structural map of the Artinian base of the completed deformation to that of the deformation
itself; `Deformation.Examples.adicCompletionFunctor` is chosen from the subtype cut out by that
clause, so this is its second component. -/
public theorem isBaseCompatible_adicCompletionFunctor [IsNoetherianRing P] :
    (adicCompletionFunctor (Λ := Λ) (k := k) P J).IsBaseCompatible :=
  (baseCompatibleAdicCompletionFunctor P J).2

end Deformation.Examples
