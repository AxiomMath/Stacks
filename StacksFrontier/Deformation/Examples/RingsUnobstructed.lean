module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Geometric.Rings
public import StacksFrontier.Deformation.Smooth.Basic
public import StacksFrontier.Deformation.Smooth.Unobstructed
public import StacksFrontier.RingTheory.CompleteIntersection.Basic
public import StacksFrontier.RingTheory.CompleteIntersection.Defs
public import StacksFrontier.RingTheory.CompleteIntersection.FieldExtension
public import StacksFrontier.RingTheory.Nilpotent.Descent
public import StacksFrontier.RingTheory.Smoothing.LiftingAlongSurjections

/-!
# Unobstructed deformations of a local complete intersection (Stacks 0DZH)

Let `k` be a field and `P` a local complete intersection over `k` (Stacks 00S9 (2)). This file
proves that the deformation category of `P` of Stacks 0DY1 is unobstructed, that is, that its
structure functor to the category of Artinian local algebras is smooth.

## Main definitions

None.

## Main results

* `Deformation.Examples.ringDeformationCategory_isSmooth_of_isLocalCompleteIntersection`: the
  deformation category of a local complete intersection over a field is unobstructed,
  **Stacks 0DZH**.

## Implementation notes

Unobstructedness of a category over `𝒞_Λ` is smoothness of its structure functor regarded as a
morphism of categories over that base, which is `Deformation.IsSmooth` applied to
`Deformation.baseProjection`; see the implementation notes of
`StacksFrontier.Deformation.Smooth.Unobstructed`. The structure functor of the deformation category
of `P` is the composite of `Over.forget` with
`Deformation.Examples.FlatAlgebraCategory.projection`, so the statement is smoothness of
`baseProjection` of that composite.

The argument is the source's. An object of the deformation category is a flat algebra `(R, Q)`
over an Artinian local base together with a cartesian map to `(k, P)`; cartesianness says that
`k ⊗_R Q = P`, so the special fibre of `R → Q` is `P`, and the residue map `R → k` is surjective
with nilpotent kernel `I`. Finite type of `Q` over `R` descends from finite type of `P` over `R`
along the nilpotent thickening `Q → Q/IQ = P`, and over the Noetherian ring `R` finite type
upgrades to finite presentation; flatness is part of the object. Every prime of the Artinian ring
`R` is its maximal ideal, whose residue field is `k`, and the fibre of `Q` there is a pushout of
`P` over that identification, so the fibres of `R → Q` are local complete intersections. Hence
`R → Q` is syntomic (Stacks 00SL). Given a surjection `B → R` in `𝒞_Λ`, Stacks 07M8 lifts the
syntomic algebra `Q` to a syntomic `B`-algebra `A'` whose special fibre is `Q`. Flatness of `A'`
over `B` comes from syntomicity, and the special-fibre identification, transported across the
pushout description of a quotient by an extended ideal, is exactly the cartesian square making
`(B, A') → (R, Q)` a morphism of flat algebras. Composing with the given map to `(k, P)` gives the
required lift, and the comparison morphism over `B` is the identity.

The kernel computation `ker (Q → P) = I·Q` is obtained from the pushout square rather than from
flatness, and the matching `Q/IQ ≃ P` in the other direction is assembled from the pushout
description of `A'/IA'`.

## References

* [Stacks Project, Tag 0DZH](https://stacks.math.columbia.edu/tag/0DZH)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u w

namespace Deformation.Examples

/-- Finite type ascends through a nilpotent thickening when the quotient map is a
surjection and its kernel is extended from the base. -/
private theorem finiteType_of_surjective_of_nilpotent_extended_ideal
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (hf : Function.Surjective f)
    (I : Ideal R) (hker : RingHom.ker f.toRingHom = Ideal.map (algebraMap R S) I)
    (hInil : IsNilpotent I) (hT : Algebra.FiniteType R T) : Algebra.FiniteType R S := by
  let : Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) := inferInstance
  have e : (S ⧸ I.map (algebraMap R S)) ≃ₐ[R] T := by
    rw [← hker]
    exact Ideal.quotientKerAlgEquivOfSurjective hf
  have hq : Algebra.FiniteType R (S ⧸ I.map (algebraMap R S)) := hT.equiv e.symm
  have : IsScalarTower R (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hq' : Algebra.FiniteType (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    hq.of_restrictScalars_finiteType R (R ⧸ I) (S ⧸ I.map (algebraMap R S))
  exact finiteType_of_isNilpotent_quotient_finiteType R I S hInil hq'

/-- A quotient by the extended ideal is the pushout along a quotient of the base. -/
private theorem isPushout_quotientMap
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) :
    Algebra.IsPushout R (R ⧸ I) S (S ⧸ Ideal.map (algebraMap R S) I) := by
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let : Algebra (R ⧸ I) (S ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  refine Algebra.IsPushout.symm ⟨IsBaseChange.of_equiv
    (Ideal.quotMapEquivTensorQuot S).symm ?_⟩
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [LinearEquiv.symm_apply_eq]
  simp [Ideal.quotMapEquivTensorQuot, LinearEquiv.eq_symm_apply, Algebra.smul_def]

/-- The base map of a morphism of `𝒞_Λ` onto the residue field object is surjective. -/
private theorem surjective_hom_residueFieldAlgebra_base
    {Λ : Type u} {k P : Type w} [CommRing Λ] [Field k] [Algebra Λ k] [CommRing P] [Algebra k P]
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A ⟶ (residueFieldAlgebra (Λ := Λ) (k := k) P).base) : Function.Surjective f.hom := by
  intro z
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (A.residueEquiv.symm z)
  refine ⟨r, ?_⟩
  have hc := f.residue_comm r
  change (residueFieldAlgebra (Λ := Λ) (k := k) P).base.residueEquiv
      (IsLocalRing.residue k (f.hom r)) = A.residueEquiv (IsLocalRing.residue A r) at hc
  rw [hr] at hc
  have htarget (a : k) :
      (residueFieldAlgebra (Λ := Λ) (k := k) P).base.residueEquiv
        (IsLocalRing.residue k a) = a := by
    change AlgEquiv.quotientBot Λ k
      (Ideal.quotientEquivAlgOfEq Λ (IsLocalRing.maximalIdeal_eq_bot (R := k))
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal k) a)) = a
    simp only [Ideal.quotientEquivAlgOfEq_mk, AlgEquiv.quotientBot_mk]
  apply (IsLocalRing.residue k).injective
  apply (residueFieldAlgebra (Λ := Λ) (k := k) P).base.residueEquiv.injective
  rw [hc.trans (A.residueEquiv.apply_symm_apply z)]
  exact (htarget z).symm

/-- In a pushout square, a surjection `R → k` base changes to a surjection `S → P`. -/
private theorem surjective_algebraMap_of_isPushout_of_surjective
    {R S k P : Type*} [CommRing R] [CommRing S] [CommRing k] [CommRing P]
    [Algebra R S] [Algebra R k] [Algebra R P] [Algebra S P] [Algebra k P]
    [IsScalarTower R k P] [IsScalarTower R S P] [Algebra.IsPushout R S k P]
    (hk : Function.Surjective (algebraMap R k)) : Function.Surjective (algebraMap S P) := by
  let e : S ⊗[R] k ≃ₐ[S] P := Algebra.IsPushout.equiv R S k P
  have he : ⇑(algebraMap S P) =
      e ∘ Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := k) := by
    funext s
    simp [e, Algebra.IsPushout.equiv_tmul]
  rw [he]
  exact e.surjective.comp (Algebra.TensorProduct.includeLeft_surjective R S hk)

/-- Over an Artinian local ring `R`, an `R`-algebra `S` is of finite type when its base change
`P` along a surjection onto a field `k` is of finite type over `k`. -/
private theorem finiteType_of_isPushout_of_isArtinianRing
    {R S k P : Type*} [CommRing R] [IsArtinianRing R] [IsLocalRing R] [CommRing S] [Field k]
    [CommRing P] [Algebra R S] [Algebra R k] [Algebra R P] [Algebra S P] [Algebra k P]
    [IsScalarTower R k P] [IsScalarTower R S P] [Algebra.IsPushout R S k P]
    (hk : Function.Surjective (algebraMap R k)) (hP : Algebra.FiniteType k P) :
    Algebra.FiniteType R S := by
  have hI : IsNilpotent (RingHom.ker (algebraMap R k)) := by
    rw [IsLocalRing.ker_eq_maximalIdeal _ hk, ← IsLocalRing.ringJacobson_eq_maximalIdeal R,
      ← Ideal.jacobson_bot]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  have hRk : Algebra.FiniteType R k :=
    (inferInstance : Algebra.FiniteType R R).of_surjective (IsScalarTower.toAlgHom R R k) hk
  exact finiteType_of_surjective_of_nilpotent_extended_ideal (IsScalarTower.toAlgHom R S P)
    (surjective_algebraMap_of_isPushout_of_surjective hk) _
    (ker_algebraMap_eq_map_ker_of_pushout R S k P hk) hI (hRk.trans hP)

/-- Over an Artinian local ring `R`, a flat `R`-algebra `S` whose base change along a surjection
onto a field `k` is a local complete intersection over `k` is syntomic. -/
private theorem syntomic_of_isPushout_of_isLocalCompleteIntersection
    {R S k P : Type*} [CommRing R] [IsArtinianRing R] [IsLocalRing R] [CommRing S] [Field k]
    [CommRing P] [Algebra R S] [Algebra R k] [Algebra R P] [Algebra S P] [Algebra k P]
    [IsScalarTower R k P] [IsScalarTower R S P] [Algebra.IsPushout R S k P] [Module.Flat R S]
    (hk : Function.Surjective (algebraMap R k)) (hP : IsLocalCompleteIntersection k P) :
    Algebra.Syntomic R S := by
  obtain ⟨t, ht, hglob⟩ := id hP
  have hft := finiteType_of_isPushout_of_isArtinianRing (S := S) hk
    (Algebra.FiniteType.of_span_eq_top_target t ht fun a ha => (hglob a ha).finiteType)
  have : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp hft
  refine { isLocalCompleteIntersection_fiber := fun p _ => ?_ }
  obtain rfl : p = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime p)
  let φ : R →ₐ[R] k := IsScalarTower.toAlgHom R R k
  have hker : IsLocalRing.maximalIdeal R ≤ RingHom.ker φ :=
    (IsLocalRing.ker_eq_maximalIdeal (algebraMap R k) hk).ge
  have hunit : (IsLocalRing.maximalIdeal R).primeCompl ≤
      (IsUnit.submonoid k).comap φ := fun r hr =>
    (IsLocalRing.notMem_maximalIdeal.mp hr).map φ
  let e := Ideal.ResidueField.liftₐ _ φ hker hunit
  let K := (IsLocalRing.maximalIdeal R).ResidueField
  let : Algebra K k := e.toRingHom.toAlgebra
  have : IsScalarTower R K k := IsScalarTower.of_algebraMap_eq fun r =>
    (Ideal.ResidueField.liftₐ_algebraMap _ φ hker hunit r).symm
  let : Algebra K P := Algebra.compHom P (algebraMap K k)
  have : IsScalarTower K k P := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let eP : K →ₐ[R] P := (IsScalarTower.toAlgHom R k P).comp e
  let F := (IsLocalRing.maximalIdeal R).Fiber S
  let : Algebra S F := Algebra.TensorProduct.rightAlgebra
  let eF : F →ₐ[R] P :=
    Algebra.TensorProduct.lift eP (IsScalarTower.toAlgHom R S P) fun _ _ => Commute.all _ _
  let : Algebra F P := eF.toRingHom.toAlgebra
  have : IsScalarTower R K P := IsScalarTower.of_algebraMap_eq fun r => (eP.commutes r).symm
  have : IsScalarTower R F P := IsScalarTower.of_algebraMap_eq fun r => (eF.commutes r).symm
  have : IsScalarTower K F P := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap k P (e a) = eF (algebraMap K F a)
    rw [Algebra.TensorProduct.algebraMap_apply]
    change algebraMap k P (e a) = eF (a ⊗ₜ[R] (1 : S))
    dsimp [eF]
    rw [Algebra.TensorProduct.lift_tmul]
    simp [eP]
  have : IsScalarTower S F P := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap S P a = eF (algebraMap S F a)
    rw [Algebra.TensorProduct.right_algebraMap_apply]
    dsimp [eF]
    rw [Algebra.TensorProduct.lift_tmul]
    simp
  have : Algebra.IsPushout K k F P := (Algebra.IsPushout.comp_iff (R := R) (S := K) (R' := S)
    (S' := F) (T := k) (T' := P)).mp (Algebra.IsPushout.symm inferInstance)
  exact (Algebra.IsPushout.isLocalCompleteIntersection_iff K k F P).mp hP

/-- Let `B → R` be surjective with kernel `I`, `S` an `R`-algebra and `A` a `B`-algebra with
`S ≃ A/IA` compatibly with `A`. Then `S` is the pushout of `A` along `B → R`. -/
private theorem isPushout_of_ringEquiv_quotient_map_ker
    {B R S A : Type*} [CommRing B] [CommRing R] [CommRing S] [CommRing A]
    [Algebra B R] [Algebra R S] [Algebra B S] [IsScalarTower B R S] [Algebra B A] [Algebra A S]
    [IsScalarTower B A S] (hsurj : Function.Surjective (algebraMap B R))
    (e : S ≃+* A ⧸ Ideal.map (algebraMap B A) (RingHom.ker (algebraMap B R)))
    (heA : ∀ a, e (algebraMap A S a) = Ideal.Quotient.mk _ a) :
    Algebra.IsPushout B R A S := by
  let I : Ideal B := RingHom.ker (algebraMap B R)
  let J : Ideal A := Ideal.map (algebraMap B A) I
  let Q := A ⧸ J
  let : Algebra (B ⧸ I) Q := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have he (b : B) : e (algebraMap R S (algebraMap B R b)) = algebraMap B Q b := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B A S, heA]
    rfl
  let eAQ : S ≃ₐ[A] Q := AlgEquiv.ofRingEquiv (f := e) heA
  let eB : (B ⧸ I) ≃ₐ[B] R :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId B R) hsurj
  let eTensor := Algebra.TensorProduct.congr (show A ≃ₐ[A] A from AlgEquiv.refl) eB.symm
  have : Algebra.IsPushout B A (B ⧸ I) Q := (isPushout_quotientMap B A I).symm
  let : Algebra R Q := Algebra.compHom Q eB.symm.toRingHom
  have : IsScalarTower B R Q := IsScalarTower.of_algebraMap_eq fun b => by
    change Ideal.Quotient.mk J (algebraMap B A b) =
      algebraMap (B ⧸ I) Q (eB.symm (algebraMap B R b))
    rw [eB.symm.commutes]
    rfl
  let ePO : A ⊗[B] (B ⧸ I) ≃ₐ[A] Q := Algebra.IsPushout.equiv B A (B ⧸ I) Q
  let eTotal : A ⊗[B] R ≃+* S :=
    eTensor.toRingEquiv.trans (ePO.toRingEquiv.trans eAQ.symm.toRingEquiv)
  let eComm : R ⊗[B] A ≃+* A ⊗[B] R := (Algebra.TensorProduct.comm B R A).toRingEquiv
  have heR (r : R) : e (algebraMap R S r) = algebraMap R Q r := by
    obtain ⟨b, rfl⟩ := hsurj r
    exact (he b).trans (IsScalarTower.algebraMap_apply B R Q b)
  let eBase : R ⊗[B] A ≃+* S := eComm.trans eTotal
  let eBaseAlg : R ⊗[B] A ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := eBase) fun r => by
    apply e.injective
    rw [heR]
    simp only [AlgEquiv.symm_toRingEquiv, RingEquiv.symm_mk, AlgEquiv.toEquiv_eq_coe,
      AlgEquiv.ofRingEquiv_toEquiv, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, RingEquiv.coe_trans, RingEquiv.coe_mk,
      EquivLike.coe_coe, Function.comp_apply, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom, Algebra.TensorProduct.map_tmul,
      AlgEquiv.coe_toAlgHom, Algebra.IsPushout.equiv_tmul, map_one, one_mul, eBase, eComm,
      eTotal, eTensor, eB, ePO, eAQ]
    change e (e.symm (algebraMap (B ⧸ I) Q (eB.symm r))) = algebraMap R Q r
    rw [e.apply_symm_apply]
    rfl
  refine ⟨IsBaseChange.of_equiv eBaseAlg.toLinearEquiv fun a => ?_⟩
  apply e.injective
  change e (eBaseAlg (1 ⊗ₜ[B] a)) = e (algebraMap A S a)
  rw [heA]
  simp only [AlgEquiv.symm_toRingEquiv, RingEquiv.symm_mk, AlgEquiv.toEquiv_eq_coe,
    AlgEquiv.ofRingEquiv_toEquiv, AlgEquiv.ofRingEquiv_apply, RingEquiv.coe_trans, RingEquiv.coe_mk,
    EquivLike.coe_coe, Function.comp_apply, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom, Algebra.TensorProduct.map_tmul,
    AlgHom.coe_id, id_eq, map_one, Algebra.IsPushout.equiv_tmul, mul_one,
    eBaseAlg, eBase, eComm, eTotal, eTensor, eB, ePO, eAQ]
  change e (e.symm (algebraMap A Q a)) = algebraMap A Q a
  exact e.apply_symm_apply _

/-- **Stacks 0DZH.** In the setting of Stacks 0DY1, the deformation category of a local
complete intersection `P` over a field `k` is unobstructed: the structure functor of
`Deformation.Examples.ringDeformationCategory P` to the category of Artinian local `Λ`-algebras
with residue field `k` is smooth. -/
@[stacks 0DZH]
public theorem ringDeformationCategory_isSmooth_of_isLocalCompleteIntersection
    {Λ : Type u} {k P : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    [CommRing P] [Algebra k P]
    (hP : IsLocalCompleteIntersection k P) :
    IsSmooth
      (baseProjection
        (Over.forget (residueFieldAlgebra (Λ := Λ) (k := k) P) ⋙
          FlatAlgebraCategory.projection (Λ := Λ) (k := k))) := by
  classical
  intro B A f hf y x g hg
  let _ : (BasedCategory.ofFunctor
      (𝟭 (ArtinianLocalAlgCat.{u, w, w} Λ k))).p.IsHomLift f g := hg
  subst_hom_lift (BasedCategory.ofFunctor
    (𝟭 (ArtinianLocalAlgCat.{u, w, w} Λ k))).p f g
  rcases x with ⟨X, χ, fχ⟩
  cases χ
  let R := (X.base : Type w)
  have hsq (r : R) : fχ.map.hom (algebraMap R X.fiber r) =
      algebraMap k P (fχ.base.hom r) :=
    congrArg (fun e : CommRingCat.of R ⟶ CommRingCat.of P => e r) fχ.cartesian.w
  let : Algebra R k := fχ.base.hom.toRingHom.toAlgebra
  let : Algebra R P := Algebra.compHom P (algebraMap R k)
  let : Algebra X.fiber P := fχ.map.hom.toAlgebra
  have : IsScalarTower R k P := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R X.fiber P := IsScalarTower.of_algebraMap_eq fun r => (hsq r).symm
  have : Algebra.IsPushout R X.fiber k P := CommRingCat.isPushout_iff_isPushout.mp fχ.cartesian
  have : Module.Flat R X.fiber := X.flat
  have hsyn : Algebra.Syntomic R X.fiber :=
    syntomic_of_isPushout_of_isLocalCompleteIntersection (P := P)
      (surjective_hom_residueFieldAlgebra_base fχ.base) hP
  let Bobj : ArtinianLocalAlgCat.{u, w, w} Λ k := y
  let B0 : Type w := Bobj.carrier
  let : CommRing B0 := Bobj.commRing
  let : Algebra Λ B0 := Bobj.algebra
  let gAlg : B0 →ₐ[Λ] R := g.hom
  let : Algebra B0 R := gAlg.toRingHom.toAlgebra
  let : Algebra B0 X.fiber := Algebra.compHom X.fiber (algebraMap B0 R)
  have : IsScalarTower B0 R X.fiber := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hsurj : Function.Surjective (algebraMap B0 R) := hf
  obtain ⟨A', hAcomm, aB, hA'syn, e, he⟩ :=
    Stacks.Smoothing.exists_syntomic_lift_of_surjective B0 R X.fiber hsurj hsyn
  let : CommRing A' := hAcomm
  let : Algebra B0 A' := aB
  let q : A' →+* X.fiber := e.symm.toRingHom.comp (Ideal.Quotient.mk _)
  let : Algebra A' X.fiber := q.toAlgebra
  have hqe (a : A') : e (q a) = Ideal.Quotient.mk _ a := by simp [q]
  have : IsScalarTower B0 A' X.fiber :=
    IsScalarTower.of_algebraMap_eq fun b => e.injective <| (he b).trans (hqe _).symm
  have hcart : Algebra.IsPushout B0 R A' X.fiber :=
    isPushout_of_ringEquiv_quotient_map_ker hsurj e hqe
  let X' : FlatAlgebraCategory.{u, w} Λ k :=
    { base := y
      fiber := A'
      commRing := hAcomm
      algebra := aB
      flat := hA'syn.flat }
  let hX : FlatAlgebraCategory.Hom X' X :=
    { base := g
      map := CommRingCat.ofHom q
      cartesian := CommRingCat.isPushout_iff_isPushout.mpr hcart.symm }
  let x' : ringDeformationCategory (Λ := Λ) (k := k) P := Over.mk (hX ≫ fχ)
  let h : x' ⟶ (Over.mk fχ) := Over.homMk hX (by simp [x'])
  exact ⟨x', h, 𝟙 y, IsHomLift.map _ h, IsHomLift.id rfl, (Category.id_comp g).symm⟩

end Deformation.Examples

end
