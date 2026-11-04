module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.Quotient
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.FieldTheory.Separable.PerfectField
public import StacksFrontier.FieldTheory.Separable.TFAE
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.RingTheory.FormallySmooth.Adic
public import StacksFrontier.RingTheory.FormallySmooth.BaseChange
public import StacksFrontier.RingTheory.FormallySmooth.Field
public import StacksFrontier.RingTheory.FormallySmooth.RegularLocal
public import StacksFrontier.RingTheory.FormallySmooth.SpecialFibre
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# Formally smooth extensions of discrete valuation rings

Let `A → B` be an extension of discrete valuation rings. This file proves that `A → B` is
formally smooth for the `m_B`-adic topology if and only if it is weakly unramified — that is,
its ramification index is one — and the induced residue-field extension is separable.

Both directions go through the special fibre `κ_A ⊗[A] B`, where `κ_A` is the residue field of
`A`. Weak unramifiedness says exactly that the special fibre is the residue field of `B`: the
extended maximal ideal `m_A B` is `m_B` precisely when the ramification index is one. Once that
is known the special fibre is a field, adic formal smoothness over it degenerates to
`Algebra.FormallySmooth`, and for a field extension that is separability.

For the forward direction, adic formal smoothness base changes to the special fibre, which makes
the special fibre a regular local ring, hence a domain, hence reduced; so `m_A B` is radical,
which for a discrete valuation ring `B` pins the ramification index to one. The backward
direction is `RingHom.FormallySmoothNAdic.of_flat_of_specialFibre`, the implication (2) ⟹ (3) of
Tag 07NQ; its flatness hypothesis is automatic, since a torsion-free module over a discrete
valuation ring is flat.

## Main results

* `IsDiscreteValuationRing.formallySmooth_iff_weaklyUnramified_and_isSeparableExtension`: the
  characterization of adic formal smoothness for an extension of discrete valuation rings.

## Implementation notes

The residue-field extension is formed using the canonical map induced by the local algebra map.
Separability is expressed by `Algebra.IsSeparableExtension`, which allows the residue-field
extension to be nonalgebraic.

## References

* [Stacks Project, Tag 07NQ](https://stacks.math.columbia.edu/tag/07NQ)
* [Stacks Project, Tag 09E7](https://stacks.math.columbia.edu/tag/09E7)
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

namespace IsDiscreteValuationRing

universe u v w

private lemma map_maximalIdeal_eq_iff (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B] :
    (maximalIdeal A).map (algebraMap A B) = maximalIdeal B ↔
      IsWeaklyUnramified A B := by
  obtain ⟨_, hpow, hunique, _⟩ := ramificationIndex_characterization A B
  constructor
  · intro h
    exact (hunique 1 (by lia) (by simpa using h)).symm
  · intro h
    change ramificationIndex A B = 1 at h
    simpa [h] using hpow

private noncomputable def specialFiber_algEquiv (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ResidueField A ⊗[A] B ≃ₐ[ResidueField A] ResidueField B := by
  let e₁ : ResidueField A ⊗[A] B ≃+*
      (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B
      (maximalIdeal A)).symm.toRingEquiv
  let e₂ : (B ⧸ (maximalIdeal A).map (algebraMap A B)) ≃+* ResidueField B :=
    (Ideal.quotientEquivAlgOfEq A h).toRingEquiv
  let e : ResidueField A ⊗[A] B ≃+* ResidueField B := e₁.trans e₂
  let φ : ResidueField A ⊗[A] B →ₐ[ResidueField A] ResidueField B :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      (IsScalarTower.toAlgHom A B (ResidueField B)) fun _ _ ↦ .all _ _
  have key : ∀ x : B, e ((1 : ResidueField A) ⊗ₜ[A] x) = residue B x := fun x ↦ by
    have hq : (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B
        (maximalIdeal A)).symm (1 ⊗ₜ[A] x) = Ideal.Quotient.mk _ x := by
      simpa only [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk] using
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B
          (maximalIdeal A)).symm_apply_apply (Ideal.Quotient.mk _ x)
    change e₂ ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B
      (maximalIdeal A)).symm (1 ⊗ₜ[A] x)) = _
    rw [hq]
    rfl
  have he : φ.toRingHom = e.toRingHom := by
    ext x
    · obtain ⟨a, rfl⟩ := residue_surjective x
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.lift_tmul,
        Algebra.ofId_apply, ResidueField.algebraMap_residue, map_one, mul_one,
        RingEquiv.toRingHom_eq_coe, φ]
      change residue B (algebraMap A B a) = e (residue A a ⊗ₜ[A] (1 : B))
      rw [← key]
      change _ = e (algebraMap A (ResidueField A) a ⊗ₜ[A] 1)
      rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul,
        map_one, IsScalarTower.coe_toAlgHom', ResidueField.algebraMap_eq, one_mul,
        RingEquiv.toRingHom_eq_coe, φ]
      exact (key x).symm
  have hφ : ⇑φ = ⇑e := congrArg DFunLike.coe he
  exact AlgEquiv.ofBijective φ (hφ ▸ e.bijective)

/-- The base change of an adically formally smooth extension of discrete valuation rings to the
residue field of the source is adically formally smooth over that residue field. -/
private theorem formallySmoothNAdic_specialFiber (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    (h : RingHom.FormallySmoothNAdic.{max u v} (algebraMap A B) (maximalIdeal B)) :
    letI : Algebra (ResidueField A) (B ⊗[A] ResidueField A) := Algebra.TensorProduct.rightAlgebra
    haveI : IsLocalRing (B ⊗[A] ResidueField A) :=
      (Algebra.TensorProduct.comm A (ResidueField A) B).toRingEquiv.isLocalRing
    RingHom.FormallySmoothNAdic.{max u v} (algebraMap (ResidueField A) (B ⊗[A] ResidueField A))
      (maximalIdeal (B ⊗[A] ResidueField A)) := by
  let : Algebra (ResidueField A) (B ⊗[A] ResidueField A) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalRing (B ⊗[A] ResidueField A) :=
    (Algebra.TensorProduct.comm A (ResidueField A) B).toRingEquiv.isLocalRing
  have hsurj : Function.Surjective
      (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := ResidueField A)) :=
    Algebra.TensorProduct.includeLeft_surjective A B residue_surjective
  have hbase := RingHom.FormallySmoothNAdic.baseChange
    (R := A) (S := B) (R' := ResidueField A) (maximalIdeal B) h
  have hmax : (maximalIdeal B).map
      (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B)
        (B := ResidueField A)).toRingHom = maximalIdeal (B ⊗[A] ResidueField A) :=
    map_maximalIdeal_of_surjective _ hsurj
  rwa [← hmax]

set_option backward.isDefEq.respectTransparency false in
-- Rewriting the `Algebra (ResidueField A) (B ⊗[A] ResidueField A)` instance underneath the
-- base-changed adic formal smoothness needs the pre-4.34 transparency behaviour of `isDefEq`.
/-- An adically formally smooth extension of discrete valuation rings extends the maximal ideal
of the source to the maximal ideal of the target. -/
private theorem map_maximalIdeal_eq_of_formallySmoothNAdic (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    (h : RingHom.FormallySmoothNAdic.{max u v} (algebraMap A B) (maximalIdeal B)) :
    (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
  let k := ResidueField A
  let C := B ⊗[A] k
  let C' := k ⊗[A] B
  let : Algebra k C := Algebra.TensorProduct.rightAlgebra
  let e : C' ≃+* C := (Algebra.TensorProduct.comm A k B).toRingEquiv
  have : IsLocalRing C := e.isLocalRing
  have hsurj : Function.Surjective
      (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := k)) :=
    Algebra.TensorProduct.includeLeft_surjective A B residue_surjective
  have : IsNoetherianRing C :=
    isNoetherianRing_of_surjective B C
      (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := k)).toRingHom
      hsurj
  have hbase' : RingHom.FormallySmoothNAdic.{max u v} (algebraMap k C) (maximalIdeal C) :=
    formallySmoothNAdic_specialFiber A B h
  have : IsRegularLocalRing C := by
    apply RingHom.FormallySmoothTop.isRegularLocalRing_of_maximalIdeal (k := k) (A := C)
    let : TopologicalSpace k := ⊥
    have : DiscreteTopology k := ⟨rfl⟩
    let : TopologicalSpace C := (maximalIdeal C).adicTopology
    have : IsTopologicalRing C := (maximalIdeal C).ringFilterBasis.isTopologicalRing
    exact (RingHom.formallySmoothTop_iff_formallySmoothNAdic (algebraMap k C) _ rfl).mpr hbase'
  have : IsDomain C := IsRegularLocalRing.isDomain C
  have hrad : ((maximalIdeal A).map (algebraMap A B)).IsRadical := by
    let eqv : (B ⧸ (maximalIdeal A).map (algebraMap A B)) ≃+* C :=
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B
        (maximalIdeal A)).toRingEquiv.trans e
    exact (Ideal.isRadical_iff_quotient_reduced _).mpr
      (isReduced_of_injective eqv.toRingHom eqv.injective)
  obtain ⟨hepos, hpow, _, _⟩ := ramificationIndex_characterization A B
  have hpowrad : ((maximalIdeal B) ^ ramificationIndex A B).IsRadical := hpow ▸ hrad
  have heq : (maximalIdeal B) ^ ramificationIndex A B = maximalIdeal B := calc
    _ = ((maximalIdeal B) ^ ramificationIndex A B).radical := hpowrad.radical.symm
    _ = (maximalIdeal B).radical := Ideal.radical_pow _ (by lia)
    _ = maximalIdeal B := (maximalIdeal.isMaximal B).isPrime.radical
  exact hpow.trans heq

/-- An extension of discrete valuation rings is formally smooth for the maximal-ideal-adic
topology if and only if it is weakly unramified and its possibly nonalgebraic residue-field
extension is separable. -/
@[stacks 09E7]
theorem formallySmooth_iff_weaklyUnramified_and_isSeparableExtension
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B] :
    RingHom.FormallySmoothNAdic.{max u v} (algebraMap A B)
        (IsLocalRing.maximalIdeal B) ↔
      IsWeaklyUnramified A B ∧
        Algebra.IsSeparableExtension (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField B) := by
  constructor
  · intro hsmooth
    have hm := map_maximalIdeal_eq_of_formallySmoothNAdic A B hsmooth
    refine ⟨(map_maximalIdeal_eq_iff A B).mp hm, ?_⟩
    -- Base change to the residue field of `A`, then identify the special fibre.
    let k := ResidueField A
    let C := B ⊗[A] k
    let : Algebra k C := Algebra.TensorProduct.rightAlgebra
    have : IsLocalRing C := (Algebra.TensorProduct.comm A k B).toRingEquiv.isLocalRing
    have hbase' : RingHom.FormallySmoothNAdic.{max u v} (algebraMap k C) (maximalIdeal C) :=
      formallySmoothNAdic_specialFiber A B hsmooth
    -- `C = B ⊗[A] κ_A` is the special fibre written on the other side; commute and identify.
    let ecomm : C ≃ₐ[k] k ⊗[A] B :=
      { (Algebra.TensorProduct.comm A B k).toRingEquiv with
        commutes' := fun x => by
          show Algebra.TensorProduct.comm A B k ((1 : B) ⊗ₜ[A] x) = x ⊗ₜ[A] (1 : B)
          simp }
    have hres := RingHom.FormallySmoothNAdic.of_algEquiv
      (ecomm.trans (specialFiber_algEquiv A B hm)) hbase'
    rw [maximalIdeal_eq_bot] at hres
    exact (Algebra.FormallySmooth.iff_isSeparableExtension _ _).mp
      (RingHom.formallySmoothNAdic_bot_iff.mp hres)
  · rintro ⟨hweak, hsep⟩
    have hm := (map_maximalIdeal_eq_iff A B).mpr hweak
    have hfs : Algebra.FormallySmooth (ResidueField A) (ResidueField B) :=
      (Algebra.FormallySmooth.iff_isSeparableExtension _ _).mpr hsep
    have hbot : RingHom.FormallySmoothNAdic.{max u v}
        (algebraMap (ResidueField A) (ResidueField B))
        (maximalIdeal (ResidueField B)) := by
      rw [maximalIdeal_eq_bot]
      exact RingHom.formallySmoothNAdic_bot_iff.mpr hfs
    exact RingHom.FormallySmoothNAdic.of_flat_of_specialFibre A B
      (.of_algEquiv (specialFiber_algEquiv A B hm).symm hbot)

/-- A field extension that maps into a separable one is itself separable: if `L/k` is separable
and there is a `k`-algebra map `K →ₐ[k] L`, then `K/k` is separable. -/
theorem isSeparableExtension_of_algHom
    {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra.IsSeparableExtension k L] (f : K →ₐ[k] L) :
    Algebra.IsSeparableExtension k K := by
  have : Algebra.IsGeometricallyReduced k L :=
    ((Algebra.isSeparableExtension_tfae k L (ringExpChar k)).out 1 4).mp
      (show Algebra.IsSeparableExtension k L from inferInstance)
  exact ((Algebra.isSeparableExtension_tfae k K (ringExpChar k)).out 1 4).mpr
    (Algebra.IsGeometricallyReduced.of_injective f f.injective)

/-- Separability of possibly nonalgebraic field extensions is transitive: if `K/k` and `K'/K`
are separable, so is `K'/k`. -/
theorem isSeparableExtension_trans (k K K' : Type*) [Field k] [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K']
    [Algebra.IsSeparableExtension k K] [Algebra.IsSeparableExtension K K'] :
    Algebra.IsSeparableExtension k K' := by
  have : Algebra.FormallySmooth k K :=
    (Algebra.FormallySmooth.iff_isSeparableExtension k K).mpr inferInstance
  have : Algebra.FormallySmooth K K' :=
    (Algebra.FormallySmooth.iff_isSeparableExtension K K').mpr inferInstance
  exact (Algebra.FormallySmooth.iff_isSeparableExtension k K').mp
    (Algebra.FormallySmooth.comp k K K')

/-- Adic formal smoothness descends to the bottom step of a tower of extensions of discrete
valuation rings: if `A → C` is formally smooth, then so is `A → B`. -/
theorem formallySmoothNAdic_tower_bot (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [IsExtension A B]
    [IsExtension B C] [IsExtension A C]
    (h : RingHom.FormallySmoothNAdic.{max u w} (algebraMap A C) (IsLocalRing.maximalIdeal C)) :
    RingHom.FormallySmoothNAdic.{max u v} (algebraMap A B) (IsLocalRing.maximalIdeal B) := by
  obtain ⟨h1, h2⟩ :=
    (formallySmooth_iff_weaklyUnramified_and_isSeparableExtension A C).mp h
  refine (formallySmooth_iff_weaklyUnramified_and_isSeparableExtension A B).mpr
    ⟨isWeaklyUnramified_tower_bot A B C h1, ?_⟩
  exact isSeparableExtension_of_algHom
    (IsScalarTower.toAlgHom (ResidueField A) (ResidueField B) (ResidueField C))

/-- Adic formal smoothness is transitive for extensions of discrete valuation rings: if `A → B`
and `B → C` are formally smooth, then so is `A → C`. -/
theorem formallySmoothNAdic_trans (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [IsExtension A B]
    [IsExtension B C] [IsExtension A C]
    (hAB : RingHom.FormallySmoothNAdic.{max u v} (algebraMap A B) (IsLocalRing.maximalIdeal B))
    (hBC : RingHom.FormallySmoothNAdic.{max v w} (algebraMap B C) (IsLocalRing.maximalIdeal C)) :
    RingHom.FormallySmoothNAdic.{max u w} (algebraMap A C) (IsLocalRing.maximalIdeal C) := by
  obtain ⟨h1, h2⟩ :=
    (formallySmooth_iff_weaklyUnramified_and_isSeparableExtension A B).mp hAB
  obtain ⟨h1', h2'⟩ :=
    (formallySmooth_iff_weaklyUnramified_and_isSeparableExtension B C).mp hBC
  refine (formallySmooth_iff_weaklyUnramified_and_isSeparableExtension A C).mpr
    ⟨isWeaklyUnramified_trans A B C h1 h1', ?_⟩
  exact isSeparableExtension_trans _ (ResidueField B) _

end IsDiscreteValuationRing
