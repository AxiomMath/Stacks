module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Data.Fintype.Option
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Tower
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationBranches
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Branches under extension of the ground field

For a scheme locally of finite type over a field, extending the ground field does not change the
number of geometric branches at a point lying above the original point; in particular it does not
change whether the scheme is geometrically unibranch there. The count is read on the
normalization: it is the weighted fibre cardinality in which a point of the normalization
contributes the separable degree of its residue field, and the comparison morphism between the
normalization of the base change and the base change of the normalization is a universal
homeomorphism, so it preserves that count.

## Main results

* `AlgebraicGeometry.numberOfGeometricBranches_baseChange_fieldExtension`: invariance of the
  number of geometric branches under a field extension.
* `AlgebraicGeometry.isGeometricallyUnibranchAt_iff_of_fieldExtension`: geometric unibranchness
  at a point is likewise invariant.

## Implementation notes

The base change `X_K` is the categorical pullback of the structure morphism `X ⟶ Spec k` along
`Spec K ⟶ Spec k`. The hypothesis on the points records that the first pullback projection maps
the chosen point of `X_K` to the chosen point of `X`. The weighted fibre cardinality is taken in
`Cardinal` and compared there, so that the étale-algebra computation of separable degrees over a
residue field can be carried out without passing through `ℕ∞`.

## References

* [Stacks Project, Tag 0C40](https://stacks.math.columbia.edu/tag/0C40)
* [Stacks Project, Tag 0C55](https://stacks.math.columbia.edu/tag/0C55)
-/

public section

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

private theorem sepDegree_eq_of_isPurelyInseparable_tower
    (k l m : Type u) [Field k] [Field l] [Field m]
    [Algebra k l] [Algebra l m] [Algebra k m] [IsScalarTower k l m]
    [IsPurelyInseparable k l] [Algebra.IsAlgebraic l m] :
    Field.sepDegree k m = Field.sepDegree l m := by
  rw [← Field.sepDegree_mul_sepDegree_of_isAlgebraic k l m,
    IsPurelyInseparable.sepDegree_eq_one, one_mul]

private theorem sepDegree_eq_of_isPurelyInseparable_top
    (k l m : Type u) [Field k] [Field l] [Field m]
    [Algebra k l] [Algebra l m] [Algebra k m] [IsScalarTower k l m]
    [Algebra.IsAlgebraic k l] [IsPurelyInseparable l m] :
    Field.sepDegree k l = Field.sepDegree k m := by
  let : Algebra.IsAlgebraic l m := IsPurelyInseparable.isAlgebraic l m
  rw [← Field.sepDegree_mul_sepDegree_of_isAlgebraic k l m,
    IsPurelyInseparable.sepDegree_eq_one l m, mul_one]

private theorem residueFieldMap_isPurelyInseparable_of_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : UniversallyInjective f) (x : X) :
    ((f.residueFieldMap x).hom).IsPurelyInseparable := by
  have hpi : Function.Injective f ∧ ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable :=
    ((AlgebraicGeometry.tfae_universallyInjective f).out 1 3).mp hf
  exact hpi.2 x

private theorem residueFieldMap_congr
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    {f g : R →+* S} (hf : IsLocalHom f) (hg : IsLocalHom g) (h : f = g) :
    IsLocalRing.ResidueField.map f = IsLocalRing.ResidueField.map g := by
  let := hf
  let := hg
  subst g
  rfl

private noncomputable def fiberPointEquiv
    {α β γ : Type*} (h : α → β) (f : β → γ) (g : α → γ)
    (hcomp : (fun x => f (h x)) = g) (hbij : Function.Bijective h) (y : γ) :
    {x : α // g x = y} ≃ {z : β // f z = y} := by
  have hmap (x : α) : f (h x) = g x := congrFun hcomp x
  let φ : {x : α // g x = y} → {z : β // f z = y} := fun x =>
    ⟨h x.1, (hmap x.1).trans x.2⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun x x' he => Subtype.ext (hbij.1 (congrArg Subtype.val he)), fun z => ?_⟩
    obtain ⟨x, hx⟩ := hbij.2 z.1
    exact ⟨⟨x, (hmap x).symm.trans ((congrArg f hx).trans z.2)⟩, Subtype.ext hx⟩
  exact Equiv.ofBijective φ hφ

private theorem finite_normalization_fiber
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) :
    Finite {z : normalizationSchemeOverField k f //
      normalizationOverField k f z = x} := by
  let N := normalizationSchemeOverField k f
  let ν := normalizationOverField k f
  let : IsFinite ν := isFinite_normalizationOverField k f
  let : Finite {z : N // z ∈ ν.base ⁻¹' ({x} : Set X)} :=
    (ν.finite_preimage_singleton x).to_subtype
  apply Finite.of_equiv {z : N // z ∈ ν.base ⁻¹' ({x} : Set X)}
  exact Equiv.ofBijective
    (fun z : {z : N // ν z = x} =>
      (⟨z.1, by simpa using z.2⟩ : {z : N // z ∈ ν.base ⁻¹' ({x} : Set X)}))
    ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h),
      fun z => ⟨⟨z.1, by simpa using z.2⟩, rfl⟩⟩

-- Prime-by-prime residue field comparison across the separable closure uses a large tensor map.
private noncomputable def residueFieldAlgEquivOfField
    (k L : Type u) [Field k] [Field L] [Algebra k L] :
    L ≃ₐ[k] IsLocalRing.ResidueField L := by
  have hbij : Function.Bijective (IsLocalRing.residue L) := by
    refine ⟨(RingHom.injective_iff_ker_eq_bot (IsLocalRing.residue L)).mpr ?_,
      IsLocalRing.residue_surjective⟩
    rw [IsLocalRing.ker_residue, IsLocalRing.maximalIdeal_eq_bot]
  rw [← IsLocalRing.ResidueField.algebraMap_eq] at hbij
  exact AlgEquiv.ofBijective (IsScalarTower.toAlgHom k L (IsLocalRing.ResidueField L)) hbij

private theorem sepDegree_eq_finrank_localization_of_etale
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
    [Algebra.Etale k A] (p : PrimeSpectrum A) :
    letI : IsArtinianRing A := IsArtinianRing.of_finite k A
    letI : Algebra.FormallyUnramified k A := inferInstance
    letI : _root_.IsReduced A := Algebra.FormallyUnramified.isReduced_of_field k A
    let L := Localization.AtPrime p.asIdeal
    letI : Algebra A L := inferInstance
    letI : Algebra k L := inferInstance
    letI : IsScalarTower k A L := inferInstance
    letI : IsArtinianRing L := IsArtinianRing.localization_artinian p.asIdeal.primeCompl L
    letI : _root_.IsReduced L := inferInstance
    letI : Field L := (IsArtinianRing.isField_of_isReduced_of_isLocalRing L).toField
    ∃ _ : L ≃ₐ[k] p.asIdeal.ResidueField,
      Field.sepDegree k L = Module.finrank k L := by
  dsimp
  let : IsArtinianRing A := IsArtinianRing.of_finite k A
  let : Algebra.FormallyUnramified k A := inferInstance
  let : _root_.IsReduced A := Algebra.FormallyUnramified.isReduced_of_field k A
  let L := Localization.AtPrime p.asIdeal
  let : Algebra A L := inferInstance
  let : Algebra k L := inferInstance
  let : IsScalarTower k A L := inferInstance
  let : Module.Finite A L := Module.Finite.of_surjective (Algebra.linearMap A L)
    (IsArtinianRing.localization_surjective p.asIdeal.primeCompl L)
  let : Module.Finite k L := Module.Finite.trans (R := k) A L
  let : IsArtinianRing L := IsArtinianRing.localization_artinian p.asIdeal.primeCompl L
  let : _root_.IsReduced L := inferInstance
  let : Field L := (IsArtinianRing.isField_of_isReduced_of_isLocalRing L).toField
  let : Algebra.FormallyEtale k L := inferInstance
  let : Algebra.IsSeparable k L := (Algebra.FormallyEtale.iff_isSeparable k L).mp inferInstance
  refine ⟨residueFieldAlgEquivOfField k L, ?_⟩
  rw [Algebra.IsSeparable.sepDegree_eq, Module.finrank_eq_rank]

private theorem sepDegree_sum_residueField_of_etale
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
    [Algebra.Etale k A] :
    letI : IsArtinianRing A := IsArtinianRing.of_finite k A
    letI : Fintype (PrimeSpectrum A) := Fintype.ofFinite (PrimeSpectrum A)
    Module.rank k A = ∑ p : PrimeSpectrum A, Field.sepDegree k p.asIdeal.ResidueField := by
  let : IsArtinianRing A := IsArtinianRing.of_finite k A
  let : Algebra.FormallyUnramified k A := inferInstance
  let : _root_.IsReduced A := Algebra.FormallyUnramified.isReduced_of_field k A
  let : Fintype (PrimeSpectrum A) := Fintype.ofFinite (PrimeSpectrum A)
  have hdim : Module.finrank k A =
      ∑ p : PrimeSpectrum A, Module.finrank k (Localization.AtPrime p.asIdeal) :=
    IsArtinianRing.finrank_eq_sum_primeSpectrum A k
  calc
    Module.rank k A = (Module.finrank k A : Cardinal) := (Module.finrank_eq_rank k A).symm
    _ = (∑ p : PrimeSpectrum A,
        Module.finrank k (Localization.AtPrime p.asIdeal) : Cardinal) := by
          exact_mod_cast hdim
    _ = ∑ p : PrimeSpectrum A, Field.sepDegree k p.asIdeal.ResidueField := by
      apply Finset.sum_congr rfl
      intro p hp
      let L := Localization.AtPrime p.asIdeal
      let : Algebra A L := inferInstance
      let : Algebra k L := inferInstance
      let : IsScalarTower k A L := inferInstance
      let : Module.Finite A L := Module.Finite.of_surjective (Algebra.linearMap A L)
        (IsArtinianRing.localization_surjective p.asIdeal.primeCompl L)
      let : Module.Finite k L := Module.Finite.trans (R := k) A L
      let : IsArtinianRing L := IsArtinianRing.localization_artinian p.asIdeal.primeCompl L
      let : _root_.IsReduced L := inferInstance
      let : Field L := (IsArtinianRing.isField_of_isReduced_of_isLocalRing L).toField
      let : Algebra.FormallyEtale k L := inferInstance
      obtain ⟨e, hdeg⟩ := sepDegree_eq_finrank_localization_of_etale k A p
      have heq : Field.sepDegree k L =
          Field.sepDegree k p.asIdeal.ResidueField :=
        Field.sepDegree_eq_of_equiv k L p.asIdeal.ResidueField e
      simpa [L] using hdeg.symm.trans heq

private theorem sepDegree_sum_residueField_tensor_of_isSeparable
    (k l m : Type u) [Field k] [Field l] [Field m]
    [Algebra k l] [Algebra k m] [FiniteDimensional k m]
    [Algebra.IsSeparable k m] :
    letI : IsArtinianRing (TensorProduct k l m) :=
      IsArtinianRing.of_finite l (TensorProduct k l m)
    letI : Fintype (PrimeSpectrum (TensorProduct k l m)) :=
      Fintype.ofFinite (PrimeSpectrum (TensorProduct k l m))
    Field.sepDegree k m =
      ∑ p : PrimeSpectrum (TensorProduct k l m),
        Field.sepDegree l p.asIdeal.ResidueField := by
  let A := TensorProduct k l m
  let : Module.FinitePresentation k m := Module.finitePresentation_of_finite k m
  let : Algebra.FinitePresentation k m :=
    Algebra.FinitePresentation.of_finitePresentation k m
  let : Algebra.Etale k m := {
    formallyEtale := (Algebra.FormallyEtale.iff_isSeparable k m).mpr inferInstance
    finitePresentation := inferInstance }
  let : Algebra.FormallyEtale l A := inferInstance
  let : Module.Finite l A := inferInstance
  let : Algebra.Etale l A := {
    formallyEtale := inferInstance
    finitePresentation := inferInstance }
  let : IsArtinianRing A := IsArtinianRing.of_finite l A
  let : Fintype (PrimeSpectrum A) := Fintype.ofFinite (PrimeSpectrum A)
  have hrank : Module.rank l A = Module.rank k m := by
    dsimp [A]
    rw [Module.rank_baseChange]
    simp
  rw [Algebra.IsSeparable.sepDegree_eq, hrank.symm]
  exact sepDegree_sum_residueField_of_etale l A

private noncomputable def tensorFlipOverSecondFactor
    (k l m : Type u) [Field k] [Field l] [Field m]
    [Algebra k l] [Algebra k m] :
    letI : Algebra l (TensorProduct k m l) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra l (TensorProduct k l m) := Algebra.TensorProduct.leftAlgebra
    TensorProduct k m l ≃ₐ[l] TensorProduct k l m := by
  let : Algebra l (TensorProduct k m l) := Algebra.TensorProduct.rightAlgebra
  let : Algebra l (TensorProduct k l m) := Algebra.TensorProduct.leftAlgebra
  refine { toRingEquiv := (Algebra.TensorProduct.comm k m l).toRingEquiv, commutes' := ?_ }
  intro a
  change (Algebra.TensorProduct.comm k m l) (1 ⊗ₜ[k] a) = a ⊗ₜ[k] 1
  rw [Algebra.TensorProduct.comm_tmul]

/-- The tensor product of a finite extension `m` of `k` with `l`, viewed over `l`, is finite. -/
private theorem finite_tensor_rightAlgebra
    (k l m : Type u) [Field k] [Field l] [Field m]
    [Algebra k l] [Algebra k m] [Module.Finite k m] :
    letI : Algebra l (TensorProduct k m l) := Algebra.TensorProduct.rightAlgebra
    Module.Finite l (TensorProduct k m l) := by
  let : Algebra l (TensorProduct k m l) := Algebra.TensorProduct.rightAlgebra
  let : Algebra l (TensorProduct k l m) := Algebra.TensorProduct.leftAlgebra
  exact Module.Finite.of_surjective (tensorFlipOverSecondFactor k l m).symm.toLinearMap
    (tensorFlipOverSecondFactor k l m).symm.surjective

/-- A finite separable field extension is étale. -/
private theorem etale_of_finite_isSeparable
    (k m : Type u) [Field k] [Field m] [Algebra k m] [Module.Finite k m]
    [Algebra.IsSeparable k m] : Algebra.Etale k m := by
  let : Module.FinitePresentation k m := Module.finitePresentation_of_finite k m
  let : Algebra.FinitePresentation k m :=
    Algebra.FinitePresentation.of_finitePresentation k m
  exact { formallyEtale := (Algebra.FormallyEtale.iff_isSeparable k m).mpr inferInstance
          finitePresentation := inferInstance }

private theorem sepDegree_sum_residueField_tensor_flip_of_isSeparable
    (k l m : Type u) [Field k] [Field l] [Field m]
    [Algebra k l] [Algebra k m] [FiniteDimensional k m]
    [Algebra.IsSeparable k m] :
    letI : Algebra l (TensorProduct k m l) := Algebra.TensorProduct.rightAlgebra
    letI : Module.Finite l (TensorProduct k m l) := finite_tensor_rightAlgebra k l m
    letI : IsArtinianRing (TensorProduct k m l) :=
      IsArtinianRing.of_finite l (TensorProduct k m l)
    letI : Fintype (PrimeSpectrum (TensorProduct k m l)) :=
      Fintype.ofFinite (PrimeSpectrum (TensorProduct k m l))
    Field.sepDegree k m =
      ∑ p : PrimeSpectrum (TensorProduct k m l),
        Field.sepDegree l p.asIdeal.ResidueField := by
  let : Algebra l (TensorProduct k m l) := Algebra.TensorProduct.rightAlgebra
  let A := TensorProduct k m l
  let B := TensorProduct k l m
  let : Algebra.Etale k m := etale_of_finite_isSeparable k m
  let : Algebra l B := Algebra.TensorProduct.leftAlgebra
  let : Algebra.Etale l B := inferInstance
  let : Module.Finite l B := inferInstance
  let e : A ≃ₐ[l] B := tensorFlipOverSecondFactor k l m
  let : Algebra.Etale l A := Algebra.Etale.of_equiv (R := l) e.symm
  let : Module.Finite l A :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  let : IsArtinianRing A := IsArtinianRing.of_finite l A
  let : Fintype (PrimeSpectrum A) := Fintype.ofFinite (PrimeSpectrum A)
  have hrank : Module.rank l A = Module.rank k m := by
    calc
      Module.rank l A = Module.rank l B := e.toLinearEquiv.rank_eq
      _ = Module.rank k m := by
        dsimp [B]
        rw [Module.rank_baseChange]
        simp
  rw [Algebra.IsSeparable.sepDegree_eq, hrank.symm]
  exact sepDegree_sum_residueField_of_etale l A

private noncomputable def specResidueFieldRingEquiv
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) :
    (Spec (CommRingCat.of R)).residueField p ≃+* p.asIdeal.ResidueField :=
  (Scheme.Spec.residueFieldIso (CommRingCat.of R) p).commRingCatIsoToRingEquiv

private theorem tensorMap_pow_mem_range
    (k l L m : Type u) [Field k] [Field l] [Field L] [Field m]
    [Algebra k l] [Algebra k L] [Algebra L m] [Algebra k m]
    [IsScalarTower k L m]
    [IsPurelyInseparable L m]
    (a : TensorProduct k m l) :
    ∃ n : ℕ, ∃ b : TensorProduct k L l,
      (Algebra.TensorProduct.map ((Algebra.ofId L m).restrictScalars k) (AlgHom.id k l)) b =
        a ^ (ringExpChar L) ^ n := by
  let B := TensorProduct k L l
  let C := TensorProduct L B m
  let D := TensorProduct L m B
  let e : TensorProduct k m l ≃ₐ[L] D :=
    (Algebra.TensorProduct.cancelBaseChange k L L m l).symm
  let : Algebra m D := Algebra.TensorProduct.leftAlgebra
  let : Algebra m C := Algebra.TensorProduct.rightAlgebra
  let e₂ : D ≃ₐ[m] C := {
    toRingEquiv := (Algebra.TensorProduct.comm L m B).toRingEquiv
    commutes' := by
      intro x
      show (Algebra.TensorProduct.comm L m B) (x ⊗ₜ[L] 1) = 1 ⊗ₜ[L] x
      rw [Algebra.TensorProduct.comm_tmul] }
  let ι : B →ₐ[L] C := IsScalarTower.toAlgHom L B C
  have hmap :
      (Algebra.TensorProduct.map ((Algebra.ofId L m).restrictScalars k)
        (AlgHom.id k l)).toRingHom = e.symm.toRingEquiv.toRingHom.comp
      (e₂.symm.toRingEquiv.toRingHom.comp (algebraMap B C)) := by
    apply RingHom.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp
    · intro x y
      simp [e, e₂, B, C, D, Algebra.smul_def]
    · intro z₁ z₂ hz₁ hz₂
      rw [map_add, map_add, hz₁, hz₂]
  let q := ringExpChar L
  obtain ⟨n, c, hc⟩ := IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar
    (R := B) q (e₂ (e a))
  refine ⟨n, c, ?_⟩
  have hh := congrArg (fun z => e.symm (e₂.symm z)) hc
  calc
    (Algebra.TensorProduct.map ((Algebra.ofId L m).restrictScalars k)
        (AlgHom.id k l)) c = e.symm (e₂.symm (algebraMap B C c)) :=
          congrArg (fun f => f c) hmap
    _ = a ^ (ringExpChar L) ^ n := by
      show e.symm (e₂.symm (c ⊗ₜ[L] (1 : m))) = a ^ (ringExpChar L) ^ n
      simpa [q] using hh


private theorem universallyInjective_specMap_of_pow_mem_range
    (k A B : Type u) [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B)
    (hpow : ∀ b : B, ∃ n : ℕ, ∃ a : A,
      f a = b ^ (ringExpChar k) ^ n) :
    UniversallyInjective (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
  apply ((AlgebraicGeometry.tfae_universallyInjective
    (Spec.map (CommRingCat.ofHom f.toRingHom))).out 1 2).mpr
  intro T _ g₁ g₂ hcomp
  let ψ₁ := Spec.preimage g₁
  let ψ₂ := Spec.preimage g₂
  have hψ : CommRingCat.ofHom f.toRingHom ≫ ψ₁ =
      CommRingCat.ofHom f.toRingHom ≫ ψ₂ := by
    apply Spec.map_injective
    simpa [ψ₁, ψ₂] using hcomp
  have hψ' : ψ₁.hom.comp f.toRingHom = ψ₂.hom.comp f.toRingHom :=
    congrArg (fun g => g.hom) hψ
  rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂, Spec.map_inj]
  ext b
  obtain ⟨n, a, ha⟩ := hpow b
  let φ : k →+* T := ψ₁.hom.comp (f.toRingHom.comp (algebraMap k A))
  let : Algebra k T := φ.toAlgebra
  have hF : Function.Injective (algebraMap k T) := φ.injective
  have hexp : ExpChar T (ringExpChar k) :=
    expChar_of_injective_algebraMap hF (ringExpChar k)
  apply iterateFrobenius_inj T (ringExpChar k) n
  calc
    ψ₁ b ^ (ringExpChar k) ^ n = ψ₁ (b ^ (ringExpChar k) ^ n) := by simp
    _ = ψ₁ (f a) := by rw [ha]
    _ = ψ₂ (f a) := by
      show ψ₁.hom (f.toRingHom a) = ψ₂.hom (f.toRingHom a)
      simpa only [RingHom.comp_apply] using
        congrArg (fun h : A →+* T => h a) hψ'
    _ = ψ₂ (b ^ (ringExpChar k) ^ n) := by rw [ha]
    _ = ψ₂ b ^ (ringExpChar k) ^ n := by simp

/-- A morphism of affine schemes whose residue-field map at a point is purely inseparable gives
a purely inseparable extension of the ideal-theoretic residue fields at that point and its
image. -/
private theorem isPurelyInseparable_residueField_of_residueFieldMap
    (l : Type u) [Field l] (R S : Type u) [CommRing R] [CommRing S] [Algebra l R] [Algebra l S]
    (β : R →ₐ[l] S) (p : PrimeSpectrum S)
    (hpure : RingHom.IsPurelyInseparable
      ((Spec.map (CommRingCat.ofHom β.toRingHom)).residueFieldMap p).hom) :
    letI : Algebra (PrimeSpectrum.comap β.toRingHom p).asIdeal.ResidueField
        p.asIdeal.ResidueField :=
      (Ideal.ResidueField.mapₐ (PrimeSpectrum.comap β.toRingHom p).asIdeal p.asIdeal β
        rfl).toRingHom.toAlgebra
    IsPurelyInseparable (PrimeSpectrum.comap β.toRingHom p).asIdeal.ResidueField
      p.asIdeal.ResidueField := by
  let q := PrimeSpectrum.comap β.toRingHom p
  let qScheme : Spec (CommRingCat.of R) := (Spec.map (CommRingCat.ofHom β.toRingHom)).base p
  let ψₐ : q.asIdeal.ResidueField →ₐ[l] p.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ q.asIdeal p.asIdeal β rfl
  let ψ := ψₐ.toRingHom
  let : Algebra q.asIdeal.ResidueField p.asIdeal.ResidueField := ψ.toAlgebra
  -- The scheme residue field map is the ideal residue field map under `Spec.residueFieldIso`.
  let e₁Iso := Scheme.Spec.residueFieldIso (CommRingCat.of (R)) qScheme
  let e₂Iso := Scheme.Spec.residueFieldIso (CommRingCat.of (S)) p
  let e₁ := e₁Iso.hom
  let : IsLocalRing ((Spec (CommRingCat.of (R))).presheaf.stalk q) :=
    (Spec.locallyRingedSpaceObj (CommRingCat.of (R))).isLocalRing q
  let : IsLocalRing ((Spec (CommRingCat.of (S))).presheaf.stalk p) :=
    (Spec.locallyRingedSpaceObj (CommRingCat.of (S))).isLocalRing p
  let : IsLocalHom
      (CommRingCat.Hom.hom ((Spec.map (CommRingCat.ofHom β.toRingHom)).stalkMap p)) :=
    (Spec.map (CommRingCat.ofHom β.toRingHom)).prop p
  let : IsLocalHom
      (CommRingCat.Hom.hom (Spec.stalkIso (CommRingCat.of (R)) q).hom) :=
    (EquivLike.surjective
      (Spec.stalkIso (CommRingCat.of (R)) q).commRingCatIsoToRingEquiv).isLocalHom
  let : IsLocalHom
      (Localization.localRingHom q.asIdeal p.asIdeal β.toRingHom rfl) :=
    Localization.isLocalHom_localRingHom (J := p.asIdeal) (f := β.toRingHom)
      (hIJ := PrimeSpectrum.comap_asIdeal β.toRingHom p)
  let : IsLocalHom
      (CommRingCat.Hom.hom (Spec.stalkIso (CommRingCat.of (S)) p).inv) :=
    (EquivLike.surjective
      (Spec.stalkIso (CommRingCat.of (S)) p).symm.commRingCatIsoToRingEquiv).isLocalHom
  have heq :
      ((Spec.map (CommRingCat.ofHom β.toRingHom)).residueFieldMap p).hom =
        (e₁ ≫ CommRingCat.ofHom ψ ≫ e₂Iso.inv).hom := by
    have hlocal := congrArg CommRingCat.Hom.hom
      (Scheme.localRingHom_comp_stalkIso (CommRingCat.ofHom β.toRingHom) p)
    let : IsLocalHom
        (CommRingCat.Hom.hom
          ((Spec.stalkIso (CommRingCat.of (R))
              (PrimeSpectrum.comap β.toRingHom p)).hom ≫
            CommRingCat.ofHom (Localization.localRingHom
              (PrimeSpectrum.comap β.toRingHom p).asIdeal
              p.asIdeal β.toRingHom (PrimeSpectrum.comap_asIdeal β.toRingHom p)) ≫
            (Spec.stalkIso (CommRingCat.of (S)) p).inv)) :=
      hlocal.symm ▸ (Spec.map (CommRingCat.ofHom β.toRingHom)).prop p
    have hmaps := residueFieldMap_congr
      (hlocal.symm ▸ (Spec.map (CommRingCat.ofHom β.toRingHom)).prop p)
      ((Spec.map (CommRingCat.ofHom β.toRingHom)).prop p) hlocal
    show IsLocalRing.ResidueField.map
        (CommRingCat.Hom.hom ((Spec.map (CommRingCat.ofHom β.toRingHom)).stalkMap p)) = _
    have hcomp :
        IsLocalRing.ResidueField.map
            (CommRingCat.Hom.hom
              ((Spec.stalkIso (CommRingCat.of (R)) q).hom ≫
                CommRingCat.ofHom (Localization.localRingHom q.asIdeal p.asIdeal β.toRingHom rfl) ≫
                (Spec.stalkIso (CommRingCat.of (S)) p).inv)) =
          CommRingCat.Hom.hom (e₁ ≫ CommRingCat.ofHom ψ ≫ e₂Iso.inv) := by
      simp only [CommRingCat.hom_comp, IsLocalRing.ResidueField.map_comp]
      rfl
    exact hmaps.symm.trans hcomp
  let S₁ := (Spec (CommRingCat.of (R))).residueField qScheme
  let S₂ := (Spec (CommRingCat.of (S))).residueField p
  let e₁r := e₁Iso.commRingCatIsoToRingEquiv
  let e₂r := e₂Iso.commRingCatIsoToRingEquiv
  let : Nontrivial S₁ := e₁r.toRingHom.domain_nontrivial
  let : Nontrivial S₂ := e₂r.toRingHom.domain_nontrivial
  let : Field S₁ := (e₁r.toMulEquiv.isField (Field.toIsField _)).toField
  let : Field S₂ := (e₂r.toMulEquiv.isField (Field.toIsField _)).toField
  let fR : S₁ →+* S₂ := by
    dsimp only [S₁, S₂, qScheme]
    exact CommRingCat.Hom.hom
      ((Spec.map (CommRingCat.ofHom β.toRingHom)).residueFieldMap p)
  let : Algebra S₁ S₂ := fR.toAlgebra
  have hpureScheme : IsPurelyInseparable S₁ S₂ :=
    RingHom.isPurelyInseparable_algebraMap_iff.mp hpure
  have hpowScheme :=
    (isPurelyInseparable_iff_pow_mem S₁ (ringExpChar S₁)).mp hpureScheme
  let : ExpChar q.asIdeal.ResidueField (ringExpChar S₁) :=
    expChar_of_injective_ringHom e₁r.injective (ringExpChar S₁)
  have hpoint (a : S₁) : e₂r (fR a) = ψ (e₁r a) := by
    have hv : fR a = e₂r.symm (ψ (e₁r a)) := by
      convert congrArg (fun h : S₁ →+* S₂ => h a) heq using 1
      · simp [fR, S₁, S₂, qScheme]
      · rfl
    rw [hv, RingEquiv.apply_symm_apply]
  rw [isPurelyInseparable_iff_pow_mem q.asIdeal.ResidueField (ringExpChar S₁)]
  intro b
  obtain ⟨n, c, hc⟩ := hpowScheme (e₂r.symm b)
  refine ⟨n, e₁r c, ?_⟩
  calc
    algebraMap q.asIdeal.ResidueField p.asIdeal.ResidueField (e₁r c) = ψ (e₁r c) := rfl
    _ = e₂r (fR c) := (hpoint c).symm
    _ = e₂r (algebraMap S₁ S₂ c) := rfl
    _ = e₂r ((e₂r.symm b) ^ ringExpChar S₁ ^ n) := by rw [hc]
    _ = b ^ ringExpChar S₁ ^ n := by simp

private theorem sepDegree_eq_sum_residueField_tensor
    (k l m : Type u) [Field k] [Field l] [Field m]
    [Algebra k l] [Algebra k m] [FiniteDimensional k m] :
    letI : Algebra l (TensorProduct k m l) := Algebra.TensorProduct.rightAlgebra
    letI : Module.Finite l (TensorProduct k m l) := finite_tensor_rightAlgebra k l m
    letI : IsArtinianRing (TensorProduct k m l) :=
      IsArtinianRing.of_finite l (TensorProduct k m l)
    letI : Fintype (PrimeSpectrum (TensorProduct k m l)) :=
      Fintype.ofFinite (PrimeSpectrum (TensorProduct k m l))
    Field.sepDegree k m =
      ∑ p : PrimeSpectrum (TensorProduct k m l),
        Field.sepDegree l p.asIdeal.ResidueField := by
  let E := separableClosure k m
  let : Algebra E m := E.val.toRingHom.toAlgebra
  let : IsScalarTower k E m := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.IsAlgebraic k m := inferInstance
  let : Algebra.IsAlgebraic E m := Algebra.IsAlgebraic.tower_top (K := k) E
  let : Module.Finite k E := inferInstance
  let : IsPurelyInseparable E m := (separableClosure.eq_bot_iff (F := E) (E := m)).mp
    (separableClosure.separableClosure_eq_bot k m)
  let i : E →ₐ[k] m := (Algebra.ofId E m).restrictScalars k
  let : CommRing (TensorProduct k E l) := Algebra.TensorProduct.instCommRing
  let : CommRing (TensorProduct k m l) := Algebra.TensorProduct.instCommRing
  have hchar : ringExpChar E = ringExpChar k := by
    let : ExpChar E (ringExpChar k) :=
      expChar_of_injective_algebraMap (algebraMap k E).injective (ringExpChar k)
    exact ringExpChar.eq E (ringExpChar k)
  let β₀ : TensorProduct k E l →ₐ[k] TensorProduct k m l :=
    Algebra.TensorProduct.map i (AlgHom.id k l)
  let : Algebra l (TensorProduct k E l) := Algebra.TensorProduct.rightAlgebra
  let : Algebra l (TensorProduct k m l) := Algebra.TensorProduct.rightAlgebra
  let β : TensorProduct k E l →ₐ[l] TensorProduct k m l := {
    toRingHom := β₀.toRingHom
    commutes' := by
      intro z
      simp [β₀, Algebra.TensorProduct.right_algebraMap_apply] }
  let : Module.Finite l (TensorProduct k E l) := finite_tensor_rightAlgebra k l E
  let : Module.Finite l (TensorProduct k m l) := finite_tensor_rightAlgebra k l m
  have hpow : ∀ b : TensorProduct k m l, ∃ n : ℕ, ∃ a : TensorProduct k E l,
      β₀ a = b ^ (ringExpChar k) ^ n := by
    intro b
    obtain ⟨n, a, ha⟩ := tensorMap_pow_mem_range k l E m b
    refine ⟨n, a, ?_⟩
    simpa [β₀, hchar] using ha
  let : IsArtinianRing (TensorProduct k E l) :=
    IsArtinianRing.of_finite l (TensorProduct k E l)
  let : Fintype (PrimeSpectrum (TensorProduct k E l)) :=
    Fintype.ofFinite (PrimeSpectrum (TensorProduct k E l))
  let : IsArtinianRing (TensorProduct k m l) :=
    IsArtinianRing.of_finite l (TensorProduct k m l)
  let : Fintype (PrimeSpectrum (TensorProduct k m l)) :=
    Fintype.ofFinite (PrimeSpectrum (TensorProduct k m l))
  have hbij : Function.Bijective (PrimeSpectrum.comap β.toRingHom) := by
    have hβ : β.toRingHom =
        (Algebra.TensorProduct.map (Algebra.ofId E m) (AlgHom.id k l)).toRingHom := by
      ext x <;> simp [β, β₀, i, AlgHom.coe_restrictScalars]
    rw [hβ]
    exact (PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable
      (R := k) E l m).bijective
  have hUI : UniversallyInjective (Spec.map (CommRingCat.ofHom β.toRingHom)) :=
    universallyInjective_specMap_of_pow_mem_range k (TensorProduct k E l)
      (TensorProduct k m l) β₀ hpow
  have hsep : Field.sepDegree k m = Field.sepDegree k E :=
    (sepDegree_eq_of_isPurelyInseparable_top k E m).symm
  have hE : Field.sepDegree k E =
      ∑ q : PrimeSpectrum (TensorProduct k E l),
        Field.sepDegree l q.asIdeal.ResidueField :=
    sepDegree_sum_residueField_tensor_flip_of_isSeparable k l E
  classical
  rw [hsep, hE]
  apply (Fintype.sum_equiv (Equiv.ofBijective (PrimeSpectrum.comap β.toRingHom) hbij)
    (fun p => Field.sepDegree l p.asIdeal.ResidueField)
    (fun q => Field.sepDegree l q.asIdeal.ResidueField) ?_).symm
  intro p
  let q := PrimeSpectrum.comap β.toRingHom p
  let qScheme : Spec (CommRingCat.of (TensorProduct k E l)) :=
    (Spec.map (CommRingCat.ofHom β.toRingHom)).base p
  have hpure : RingHom.IsPurelyInseparable
      ((Spec.map (CommRingCat.ofHom β.toRingHom)).residueFieldMap p).hom := by
    exact residueFieldMap_isPurelyInseparable_of_universallyInjective _ hUI p
  let ψₐ : q.asIdeal.ResidueField →ₐ[l] p.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ q.asIdeal p.asIdeal β rfl
  let ψ := ψₐ.toRingHom
  let : Algebra q.asIdeal.ResidueField p.asIdeal.ResidueField := ψ.toAlgebra
  have hpure' : IsPurelyInseparable q.asIdeal.ResidueField p.asIdeal.ResidueField :=
    isPurelyInseparable_residueField_of_residueFieldMap l _ _ β p hpure
  let : IsScalarTower l q.asIdeal.ResidueField p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun z => (ψₐ.commutes z).symm
  let : IsPurelyInseparable q.asIdeal.ResidueField p.asIdeal.ResidueField := hpure'
  let : CommRing (TensorProduct k E l) := Algebra.TensorProduct.instCommRing
  let : CommRing (TensorProduct k l E) := Algebra.TensorProduct.instCommRing
  let A := TensorProduct k E l
  let : Algebra.Etale k E := etale_of_finite_isSeparable k E
  let B := TensorProduct k l E
  let : Algebra l B := Algebra.TensorProduct.leftAlgebra
  let : Algebra.FormallyEtale l B := inferInstance
  let eAB : A ≃ₐ[l] B := tensorFlipOverSecondFactor k l E
  let : Algebra.FormallyEtale l A :=
    Algebra.FormallyEtale.of_equiv (R := l) eAB.symm
  let : Module.FinitePresentation l A := Module.finitePresentation_of_finite l A
  let : Algebra.FinitePresentation l A :=
    Algebra.FinitePresentation.of_finitePresentation l A
  let : Algebra.Etale l A := {
    formallyEtale := inferInstance
    finitePresentation := inferInstance }
  obtain ⟨e, _⟩ := sepDegree_eq_finrank_localization_of_etale l A q
  let L := Localization.AtPrime q.asIdeal
  let : Algebra A L := inferInstance
  let : Algebra l L := inferInstance
  let : IsScalarTower l A L := inferInstance
  let : Module.Finite A L := Module.Finite.of_surjective (Algebra.linearMap A L)
    (IsArtinianRing.localization_surjective q.asIdeal.primeCompl L)
  let : Module.Finite l L := Module.Finite.trans (R := l) A L
  let : Module.Finite l q.asIdeal.ResidueField :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  have halg : Algebra.IsAlgebraic l q.asIdeal.ResidueField :=
    Algebra.IsAlgebraic.of_finite l q.asIdeal.ResidueField
  exact (sepDegree_eq_of_isPurelyInseparable_top l q.asIdeal.ResidueField
    p.asIdeal.ResidueField).symm

private theorem finite_residueField_of_quasiFiniteAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (h : f.QuasiFiniteAt x) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (Y.residueField (f x)) (X.residueField x) := by
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  let φ := (f.stalkMap x).hom
  let : Algebra R S := φ.toAlgebra
  let : Algebra.QuasiFinite R S := h
  let K := Y.residueField (f x)
  let L := X.residueField x
  let : Algebra S L := (X.residue x).hom.toAlgebra
  let : Algebra R L := ((X.residue x).hom.comp φ).toAlgebra
  let : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq' rfl
  have hqf : Algebra.QuasiFinite R L :=
    Algebra.QuasiFinite.of_surjective_algHom
      (Ideal.Quotient.mkₐ R (IsLocalRing.maximalIdeal S)) Ideal.Quotient.mk_surjective
  let : Algebra K L := (f.residueFieldMap x).hom.toAlgebra
  let : Algebra R K := (Y.residue (f x)).hom.toAlgebra
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' (by
    ext a
    show (f.residueFieldMap x).hom ((Y.residue (f x)).hom a) =
      (X.residue x).hom (φ a)
    have h := congrArg (fun g : CommRingCat.Hom R L => g.hom a)
      (Scheme.residue_residueFieldMap (f := f) x)
    simpa [CommRingCat.hom_comp, φ] using h)
  let : Algebra.QuasiFinite K L := Algebra.QuasiFinite.of_restrictScalars R K L
  exact Module.Finite.of_quasiFinite

private noncomputable abbrev fiberSepDegree {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (z : {z : X // f z = y}) : Cardinal.{u} :=
  let := (((Y.residueFieldCongr z.2).inv ≫ f.residueFieldMap z.1).hom).toAlgebra
  Field.sepDegree (Y.residueField y) (X.residueField z.1)

private theorem spec_fiberMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (z : {z : X // f z = y}) :
    Spec.map ((Y.residueFieldCongr z.2).inv ≫ f.residueFieldMap z.1) ≫
      Y.fromSpecResidueField y = X.fromSpecResidueField z.1 ≫ f := by
  simp [Spec.map_comp, Scheme.residueFieldCongr_inv]

private theorem fiberSepDegree_eq_of_spec {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (A : CommRingCat.{u}) (i : Y.residueField y ⟶ A)
    (j : Spec A ⟶ X) (hj : j ≫ f = Spec.map i ≫ Y.fromSpecResidueField y)
    (p : Spec A) (hp : f (j p) = y)
    [IsIso (j.residueFieldMap p ≫ (Scheme.Spec.residueFieldIso A p).hom)] :
    letI : p.asIdeal.IsPrime := p.isPrime
    fiberSepDegree f y ⟨j p, hp⟩ =
      letI := i.hom.toAlgebra
      Field.sepDegree (Y.residueField y) p.asIdeal.ResidueField := by
  let : p.asIdeal.IsPrime := p.isPrime
  let q := (Y.residueFieldCongr hp).inv ≫ f.residueFieldMap (j p)
  let e := asIso (j.residueFieldMap p ≫ (Scheme.Spec.residueFieldIso A p).hom)
  have he : q ≫ e.hom = i ≫ CommRingCat.ofHom (algebraMap A p.asIdeal.ResidueField) := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecResidueField y)).mp
    simp only [Spec.map_comp, Category.assoc]
    rw [spec_fiberMap f y ⟨j p, hp⟩]
    dsimp [e]
    simp only [Spec.map_comp, Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]
    rw [hj]
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField A p]
    simp only [Category.assoc]
    rw [← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
  let := q.hom.toAlgebra
  let := i.hom.toAlgebra
  let ea : X.residueField (j p) ≃ₐ[Y.residueField y] p.asIdeal.ResidueField :=
    { e.commRingCatIsoToRingEquiv with
      commutes' := fun a => congrArg (fun h : Y.residueField y ⟶
        CommRingCat.of p.asIdeal.ResidueField => h.hom a) he }
  exact Field.sepDegree_eq_of_equiv _ _ _ ea

private noncomputable abbrev fiberDegreeCard {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :=
  Cardinal.mk (Σ z : {z : X // f z = y}, (fiberSepDegree f y z).ord.ToType)

private theorem finite_fiber_residueField {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] (y : Y) (z : {z : X // f z = y}) :
    letI := (((Y.residueFieldCongr z.2).inv ≫ f.residueFieldMap z.1).hom).toAlgebra
    Module.Finite (Y.residueField y) (X.residueField z.1) := by
  rcases z with ⟨z, rfl⟩
  convert finite_residueField_of_quasiFiniteAt f z (Scheme.Hom.quasiFiniteAt f z) using 1
  congr 2

private theorem fiberSepDegree_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyQuasiFinite g]
    (hf : UniversallyInjective f) (z : Z) (x : {x : X // (f ≫ g) x = z}) :
    fiberSepDegree (f ≫ g) z x = fiberSepDegree g z ⟨f x.1, x.2⟩ := by
  let : Algebra (Z.residueField z) (Y.residueField (f x.1)) :=
    (((Z.residueFieldCongr x.2).inv ≫ g.residueFieldMap (f x.1)).hom).toAlgebra
  let : Algebra (Y.residueField (f x.1)) (X.residueField x.1) :=
    (f.residueFieldMap x.1).hom.toAlgebra
  let : Algebra (Z.residueField z) (X.residueField x.1) :=
    (((Z.residueFieldCongr x.2).inv ≫ (f ≫ g).residueFieldMap x.1).hom).toAlgebra
  let : IsScalarTower (Z.residueField z) (Y.residueField (f x.1))
      (X.residueField x.1) := IsScalarTower.of_algebraMap_eq fun a => by
    show (((Z.residueFieldCongr x.2).inv ≫ (f ≫ g).residueFieldMap x.1).hom) a =
      (f.residueFieldMap x.1).hom
        ((((Z.residueFieldCongr x.2).inv ≫ g.residueFieldMap (f x.1)).hom) a)
    have h : (Z.residueFieldCongr x.2).inv ≫ (f ≫ g).residueFieldMap x.1 =
        ((Z.residueFieldCongr x.2).inv ≫ g.residueFieldMap (f x.1)) ≫
          f.residueFieldMap x.1 := by
      rw [Scheme.residueFieldMap_comp]
      exact (Category.assoc _ _ _).symm
    exact congrArg (fun h : Z.residueField z ⟶ X.residueField x.1 => h.hom a) h
  let : IsPurelyInseparable (Y.residueField (f x.1)) (X.residueField x.1) :=
    RingHom.isPurelyInseparable_algebraMap_iff.mp
      (residueFieldMap_isPurelyInseparable_of_universallyInjective f hf x.1)
  let : Module.Finite (Z.residueField z) (Y.residueField (f x.1)) :=
    finite_fiber_residueField g z ⟨f x.1, x.2⟩
  exact (sepDegree_eq_of_isPurelyInseparable_top (Z.residueField z)
    (Y.residueField (f x.1)) (X.residueField x.1)).symm

private theorem fiberDegreeCard_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyQuasiFinite g]
    (hf : UniversallyInjective f) (hbij : Function.Bijective f) (z : Z) :
    fiberDegreeCard (f ≫ g) z = fiberDegreeCard g z := by
  apply Cardinal.mk_sigma_congr (fiberPointEquiv f g (f ≫ g) rfl hbij z)
  intro x
  simp only [Cardinal.mk_toType, Cardinal.card_ord]
  convert fiberSepDegree_comp f g hf z x using 1
  congr 2

private noncomputable abbrev tripletTensorRing {X Y S : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} (T : Scheme.Pullback.Triplet f g) : CommRingCat.{u} :=
  let := (((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom).toAlgebra
  let := (((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom).toAlgebra
  .of (TensorProduct (S.residueField T.s) (X.residueField T.x) (Y.residueField T.y))

private noncomputable def tripletTensorIso {X Y S : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} (T : Scheme.Pullback.Triplet f g) :
    letI := (((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom).toAlgebra
    letI := (((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom).toAlgebra
    CommRingCat.of (TensorProduct (S.residueField T.s)
      (X.residueField T.x) (Y.residueField T.y)) ≅ T.tensor := by
  let := (((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom).toAlgebra
  let := (((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom).toAlgebra
  exact (CommRingCat.isPushout_tensorProduct (S.residueField T.s)
    (X.residueField T.x) (Y.residueField T.y)).isoPushout

private noncomputable def tripletTensorTo {X Y S : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} (T : Scheme.Pullback.Triplet f g) :
    letI := (((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom).toAlgebra
    letI := (((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom).toAlgebra
    Spec (.of (TensorProduct (S.residueField T.s)
      (X.residueField T.x) (Y.residueField T.y))) ⟶ pullback f g :=
  Spec.map (tripletTensorIso T).inv ≫ T.SpecTensorTo

private theorem tripletTensorTo_snd {X Y S : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} (T : Scheme.Pullback.Triplet f g) :
    letI := (((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom).toAlgebra
    letI := (((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom).toAlgebra
    tripletTensorTo T ≫ pullback.snd f g =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := S.residueField T.s) (A := X.residueField T.x) (B := Y.residueField T.y)).toRingHom) ≫
        Y.fromSpecResidueField T.y := by
  let := (((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom).toAlgebra
  let := (((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom).toAlgebra
  dsimp [tripletTensorTo]
  rw [Category.assoc, Scheme.Pullback.Triplet.specTensorTo_snd, ← Spec.map_comp_assoc]
  congr 2
  exact (CommRingCat.isPushout_tensorProduct (S.residueField T.s)
    (X.residueField T.x) (Y.residueField T.y)).inr_isoPushout_inv

private theorem tripletTensorTo_fst_apply {X Y S : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} (T : Scheme.Pullback.Triplet f g)
    (p : Spec (tripletTensorRing T)) :
    pullback.fst f g (tripletTensorTo T p) = T.x :=
  T.fst_SpecTensorTo_apply _

private theorem tripletTensorTo_snd_apply {X Y S : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} (T : Scheme.Pullback.Triplet f g)
    (p : Spec (tripletTensorRing T)) :
    pullback.snd f g (tripletTensorTo T p) = T.y :=
  T.snd_SpecTensorTo_apply _

private theorem tripletTensorTo_injective {X Y S : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} (T : Scheme.Pullback.Triplet f g) :
    Function.Injective (tripletTensorTo T) := by
  intro p q h
  have h' : (⟨T, Spec.map (tripletTensorIso T).inv p⟩ :
      Σ T : Scheme.Pullback.Triplet f g, Spec T.tensor) =
        ⟨T, Spec.map (tripletTensorIso T).inv q⟩ :=
    Scheme.Pullback.carrierEquiv.symm.injective h
  exact (Spec.map (tripletTensorIso T).inv).homeomorph.injective
    (eq_of_heq (Sigma.mk.inj h').2)

private theorem tripletTensorTo_isIso_residueFieldMap {X Y S : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} (T : Scheme.Pullback.Triplet f g)
    (p : Spec (tripletTensorRing T)) :
    IsIso ((tripletTensorTo T).residueFieldMap p ≫
      (Scheme.Spec.residueFieldIso (tripletTensorRing T) p).hom) := by
  let q := Spec.map (tripletTensorIso T).inv p
  let : IsIso (T.SpecTensorTo.residueFieldMap q) :=
    (isIso_comp_right_iff _ _).mp
      (Scheme.Pullback.isIso_residueFieldMap_specTensorTo_comp_residueFieldIso T q)
  have : IsIso ((Spec.map (tripletTensorIso T).inv).residueFieldMap p) := inferInstance
  have : IsIso (T.SpecTensorTo.residueFieldMap (Spec.map (tripletTensorIso T).inv p)) :=
    inferInstanceAs (IsIso (T.SpecTensorTo.residueFieldMap q))
  dsimp only [tripletTensorTo]
  rw [Scheme.residueFieldMap_comp]
  apply IsIso.comp_isIso'
  · apply IsIso.comp_isIso'
    · exact inferInstanceAs (IsIso (T.SpecTensorTo.residueFieldMap q))
    · exact inferInstanceAs (IsIso ((Spec.map (tripletTensorIso T).inv).residueFieldMap p))
  · infer_instance

private noncomputable def pullbackFiberEquiv {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (y : Y) :
    (Σ z : {z : X // f z = g y},
      Spec (tripletTensorRing (Scheme.Pullback.Triplet.mk' z.1 y z.2))) ≃
        {w : (pullback f g : Scheme.{u}) // pullback.snd f g w = y} := by
  classical
  let F : (Σ z : {z : X // f z = g y},
      Spec (tripletTensorRing (Scheme.Pullback.Triplet.mk' z.1 y z.2))) →
        {w : (pullback f g : Scheme.{u}) // pullback.snd f g w = y} := fun z =>
    ⟨tripletTensorTo (Scheme.Pullback.Triplet.mk' z.1.1 y z.1.2) z.2,
      tripletTensorTo_snd_apply _ _⟩
  apply Equiv.ofBijective F
  constructor
  · rintro ⟨z, p⟩ ⟨z', p'⟩ h
    have hz : z = z' := by
      apply Subtype.ext
      have hfst := congrArg (fun w => pullback.fst f g w.1) h
      simpa only [F, tripletTensorTo_fst_apply, Scheme.Pullback.Triplet.mk'_x] using hfst
    subst z'
    congr 1
    exact tripletTensorTo_injective _ (congrArg Subtype.val h)
  · rintro ⟨w, hw⟩
    obtain ⟨⟨T, p⟩, hp⟩ := Scheme.Pullback.carrierEquiv.symm.surjective w
    have hTy : T.y = y := by
      rw [← hp] at hw
      exact (T.snd_SpecTensorTo_apply p).symm.trans hw
    let z : {z : X // f z = g y} :=
      ⟨T.x, T.hx.trans (T.hy.symm.trans (congrArg g hTy))⟩
    have hT : T = Scheme.Pullback.Triplet.mk' z.1 y z.2 :=
      Scheme.Pullback.Triplet.ext rfl hTy
    obtain ⟨a, ha⟩ := (Spec.map (tripletTensorIso T).inv).homeomorph.surjective p
    clear_value z
    subst T
    simp only [Scheme.Hom.homeomorph_apply] at ha
    refine ⟨⟨z, a⟩, Subtype.ext ?_⟩
    change (Scheme.Pullback.Triplet.mk' z.1 y z.2).SpecTensorTo
      (Spec.map (tripletTensorIso _).inv a) = w
    rw [ha]
    exact hp

private theorem pullbackFiberEquiv_apply {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (y : Y) (z : {z : X // f z = g y})
    (p : Spec (tripletTensorRing (Scheme.Pullback.Triplet.mk' z.1 y z.2))) :
    pullbackFiberEquiv f g y ⟨z, p⟩ =
      ⟨tripletTensorTo (Scheme.Pullback.Triplet.mk' z.1 y z.2) p,
        tripletTensorTo_snd_apply _ _⟩ := by
  apply Subtype.ext
  rfl

private theorem tripletTensorTo_sepDegree {X Y S : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} (T : Scheme.Pullback.Triplet f g)
    (p : Spec (tripletTensorRing T)) :
    letI : p.asIdeal.IsPrime := p.isPrime
    letI := (((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom).toAlgebra
    letI := (((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom).toAlgebra
    letI : Algebra (Y.residueField T.y) (tripletTensorRing T) :=
      Algebra.TensorProduct.rightAlgebra
    fiberSepDegree (pullback.snd f g) T.y
        ⟨tripletTensorTo T p, tripletTensorTo_snd_apply T p⟩ =
      Field.sepDegree (Y.residueField T.y) p.asIdeal.ResidueField := by
  let : p.asIdeal.IsPrime := p.isPrime
  let := (((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom).toAlgebra
  let := (((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom).toAlgebra
  let := tripletTensorTo_isIso_residueFieldMap T p
  exact fiberSepDegree_eq_of_spec (pullback.snd f g) T.y (tripletTensorRing T)
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
      (R := S.residueField T.s) (A := X.residueField T.x)
      (B := Y.residueField T.y)).toRingHom)
    (tripletTensorTo T) (tripletTensorTo_snd T) p (tripletTensorTo_snd_apply T p)

private theorem mk_sigma_fintype (ι : Type u) [Fintype ι] (A : ι → Type u) :
    Cardinal.mk (Σ i, A i) = ∑ i, Cardinal.mk (A i) := by
  classical
  revert A
  refine Fintype.induction_empty_option (P := fun ι _ => ∀ A : ι → Type u,
    Cardinal.mk (Σ i, A i) = ∑ i, Cardinal.mk (A i)) ?_ ?_ ?_ ι
  · intro α β _ e ih A
    let : Fintype α := Fintype.ofEquiv β e.symm
    calc
      Cardinal.mk (Σ b, A b) = Cardinal.mk (Σ a, A (e a)) :=
        (Cardinal.mk_congr (Equiv.sigmaCongr e (fun _ => Equiv.refl _))).symm
      _ = ∑ a, Cardinal.mk (A (e a)) := ih _
      _ = ∑ b, Cardinal.mk (A b) := Fintype.sum_equiv e _ _ (fun _ => rfl)
  · intro A
    simp
  · intro α _ ih A
    let e : (Σ a, A a) ≃ A none ⊕ (Σ a, A (some a)) := {
      toFun := fun | ⟨none, a⟩ => .inl a | ⟨some i, a⟩ => .inr ⟨i, a⟩
      invFun := fun | .inl a => ⟨none, a⟩ | .inr ⟨i, a⟩ => ⟨some i, a⟩
      left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
      right_inv := by rintro (_ | ⟨_, _⟩) <;> rfl }
    rw [Cardinal.mk_congr e, Cardinal.mk_sum, Fintype.sum_option]
    simp only [Cardinal.lift_id]
    rw [ih]

private theorem mk_sigma_sigma_of_equiv {α : Type u} {β : α → Type u} {γ : Type u}
    (e : (Σ a, β a) ≃ γ) (D : γ → Type*) :
    Cardinal.mk (Σ a, Σ b, D (e ⟨a, b⟩)) = Cardinal.mk (Σ c, D c) := by
  rw [← Cardinal.mk_congr (Equiv.sigmaAssoc (fun a b => D (e ⟨a, b⟩)))]
  apply Cardinal.mk_sigma_congr e
  rintro ⟨a, b⟩
  rfl

/-- The weight that a prime of the triplet tensor algebra contributes to the degree count of
the base-changed morphism: a type whose cardinality is the separable degree at the
corresponding point of the fibre. -/
private noncomputable abbrev tripletWeight {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (y : Y) (z : {z : X // f z = g y})
    (p : Spec (tripletTensorRing (Scheme.Pullback.Triplet.mk' z.1 y z.2))) : Type u :=
  (fiberSepDegree (pullback.snd f g) y (pullbackFiberEquiv f g y ⟨z, p⟩)).ord.ToType

/-- The weight that a prime of the triplet tensor algebra contributes to the degree count is
the separable degree, over the residue field at `y`, of the residue field at that prime. -/
private theorem tripletWeight_eq_sepDegree {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (y : Y) (z : {z : X // f z = g y})
    (p : Spec (tripletTensorRing (Scheme.Pullback.Triplet.mk' z.1 y z.2))) :
    letI T := Scheme.Pullback.Triplet.mk' z.1 y z.2
    letI : p.asIdeal.IsPrime := p.isPrime
    letI := (((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom).toAlgebra
    letI := (((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom).toAlgebra
    letI : Algebra (Y.residueField T.y) (tripletTensorRing T) :=
      Algebra.TensorProduct.rightAlgebra
    Cardinal.mk (tripletWeight f g y z p) =
      Field.sepDegree (Y.residueField T.y) p.asIdeal.ResidueField := by
  simp only [tripletWeight, Cardinal.mk_toType, Cardinal.card_ord]
  rw [pullbackFiberEquiv_apply f g y z p]
  exact tripletTensorTo_sepDegree (Scheme.Pullback.Triplet.mk' z.1 y z.2) p

/-- `tripletWeight_eq_sepDegree` with the prime named as a prime of the tensor product of the
residue fields rather than as a point of its spectrum.  The two spellings agree definitionally;
restating the equation once here is what lets the degree count below be matched against
`sepDegree_eq_sum_residueField_tensor` without unfolding either side again. -/
private theorem mk_tripletWeight {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (y : Y) (z : {z : X // f z = g y}) :
    letI : Algebra (S.residueField (g y)) (X.residueField z.1) :=
      (((S.residueFieldCongr z.2).inv ≫ f.residueFieldMap z.1).hom).toAlgebra
    letI : Algebra (S.residueField (g y)) (Y.residueField y) :=
      (((S.residueFieldCongr (show g y = g y from rfl)).inv ≫
        g.residueFieldMap y).hom).toAlgebra
    letI : Algebra (Y.residueField y) (TensorProduct (S.residueField (g y))
        (X.residueField z.1) (Y.residueField y)) := Algebra.TensorProduct.rightAlgebra
    ∀ p : PrimeSpectrum (TensorProduct (S.residueField (g y)) (X.residueField z.1)
        (Y.residueField y)),
      Cardinal.mk (tripletWeight f g y z p) =
        Field.sepDegree (Y.residueField y) p.asIdeal.ResidueField := by
  intro p
  exact tripletWeight_eq_sepDegree f g y z p

/-- At one point of the fibre of `f` over `g y`, the weight contributed to the degree count is
the sum of the weights of the points of the fibre of `pullback.snd f g` over `y` that lie above
it: the triplet tensor algebra of the two residue fields over the base one is artinian, so its
spectrum is finite, and the separable degree is the sum of the separable degrees of the residue
fields at its primes. -/
private theorem mk_fiberSepDegree_eq_mk_sigma_tripletTensor {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [LocallyQuasiFinite f] (y : Y) (z : {z : X // f z = g y}) :
    Cardinal.mk (fiberSepDegree f (g y) z).ord.ToType =
      Cardinal.mk (Σ p : Spec (tripletTensorRing (Scheme.Pullback.Triplet.mk' z.1 y z.2)),
        tripletWeight f g y z p) := by
  classical
  let k := S.residueField (g y)
  let l := Y.residueField y
  let m := X.residueField z.1
  let : Algebra k m :=
    (((S.residueFieldCongr z.2).inv ≫ f.residueFieldMap z.1).hom).toAlgebra
  let : Algebra k l :=
    (((S.residueFieldCongr (show g y = g y from rfl)).inv ≫
      g.residueFieldMap y).hom).toAlgebra
  let : Module.Finite k m := finite_fiber_residueField f (g y) z
  let : Algebra l (TensorProduct k m l) := Algebra.TensorProduct.rightAlgebra
  let : Module.Finite l (TensorProduct k m l) := finite_tensor_rightAlgebra k l m
  let : IsArtinianRing (TensorProduct k m l) :=
    IsArtinianRing.of_finite l (TensorProduct k m l)
  let : Fintype (PrimeSpectrum (TensorProduct k m l)) :=
    Fintype.ofFinite (PrimeSpectrum (TensorProduct k m l))
  refine Eq.trans ?_ (mk_sigma_fintype (PrimeSpectrum (TensorProduct k m l))
    (fun p => tripletWeight f g y z p)).symm
  rw [Finset.sum_congr rfl (fun p _ => mk_tripletWeight f g y z p)]
  simp only [Cardinal.mk_toType, Cardinal.card_ord]
  exact sepDegree_eq_sum_residueField_tensor k l m

/-- The weighted fibre count of a locally quasi-finite morphism is unchanged by base change. -/
private theorem fiberDegreeCard_pullback {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [LocallyQuasiFinite f] (y : Y) :
    fiberDegreeCard f (g y) = fiberDegreeCard (pullback.snd f g) y := by
  classical
  let e := pullbackFiberEquiv f g y
  calc
    fiberDegreeCard f (g y) = Cardinal.mk (Σ z, Σ p, tripletWeight f g y z p) :=
      Cardinal.mk_sigma_congrRight (fun z => mk_fiberSepDegree_eq_mk_sigma_tripletTensor f g y z)
    _ = fiberDegreeCard (pullback.snd f g) y :=
      mk_sigma_sigma_of_equiv e
        (fun z => (fiberSepDegree (pullback.snd f g) y z).ord.ToType)

/-- The number of geometric branches at a point of a scheme locally of finite type over a field
is unchanged after extending the ground field and choosing a point above it. -/
@[stacks 0C40]
public theorem numberOfGeometricBranches_baseChange_fieldExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : X)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x) :
    AlgebraicGeometry.numberOfGeometricBranches X x =
      AlgebraicGeometry.numberOfGeometricBranches
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) y := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : LocallyOfFiniteType (pullback.snd f g) := by infer_instance
  let OX : Over (Spec (.of k)) := Over.mk f
  let : LocallyOfFiniteType OX.hom := inferInstanceAs (LocallyOfFiniteType f)
  let OY := (Over.pullback g).obj OX
  let : LocallyOfFiniteType OY.hom := by
    dsimp [OY, OX, g]
    infer_instance
  have hYscheme : OY.left = pullback f g := rfl
  let yY : OY.left := hYscheme.symm ▸ y
  let hX := finite_irreducibleComponents_of_locallyOfFiniteType k OX.hom
  let hY := finite_irreducibleComponents_of_locallyOfFiniteType K OY.hom
  have hYtransport : numberOfGeometricBranches OY.left yY =
      numberOfGeometricBranches (pullback f g : Scheme.{u}) y := by
    cases hYscheme
    rfl
  rw [numberOfGeometricBranches_eq_card_sigma_sepDegree_normalization X hX x, ← hYtransport,
    numberOfGeometricBranches_eq_card_sigma_sepDegree_normalization OY.left hY yY]
  let νX := Scheme.normalization X hX
  let νY := Scheme.normalization OY.left hY
  let c := normalizationBaseChangeComparison (k := k) (K := K) OX
  have hc : c ≫ baseChangeNormalization OX = νY :=
    normalizationBaseChangeComparison_comp_baseChangeNormalization (k := k) (K := K) OX
  have hcuh : UniversalHomeomorphism c :=
    normalizationBaseChangeComparison_isUniversalHomeomorphism
      (k := k) (K := K) OX
  let φ := baseChangeNormalization (k := k) (K := K) OX
  have hhomeo : IsHomeomorph c :=
    hcuh.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
  have hbij : Function.Bijective c.base := hhomeo.bijective
  have hUI : UniversallyInjective c := by
    rw [universallyInjective_iff]
    intro X' OY.left' i₁ i₂ f' hpull
    exact (hcuh.universally_isHomeomorph i₁ i₂ f' hpull).injective
  have hXeq : hX = finite_irreducibleComponents_of_locallyOfFiniteType k f :=
    Subsingleton.elim _ _
  let : IsFinite νX := by
    dsimp [νX]
    rw [hXeq]
    exact isFinite_normalizationOverField k f
  let e := pullbackRightPullbackFstIso OX.hom g νX
  have he : e.hom ≫ φ = pullback.snd νX (pullback.fst OX.hom g) := by
    have hφfst : φ ≫ pullback.fst OX.hom g =
        pullback.fst (νX ≫ OX.hom) g ≫ νX := by
      dsimp [φ, baseChangeNormalization]
      exact pullback.lift_fst _ _ _
    have hφsnd : φ ≫ pullback.snd OX.hom g = pullback.snd (νX ≫ OX.hom) g := by
      dsimp [φ, baseChangeNormalization]
      exact pullback.lift_snd _ _ _
    apply pullback.hom_ext
    · calc
        e.hom ≫ φ ≫ pullback.fst OX.hom g =
            e.hom ≫ (φ ≫ pullback.fst OX.hom g) := rfl
        _ = e.hom ≫ (pullback.fst (νX ≫ OX.hom) g ≫ νX) := by rw [hφfst]
        _ = (e.hom ≫ pullback.fst (νX ≫ OX.hom) g) ≫ νX := by
          rw [Category.assoc]
        _ = pullback.fst νX (pullback.fst OX.hom g) ≫ νX := by
          rw [pullbackRightPullbackFstIso_hom_fst]
        _ = pullback.snd νX (pullback.fst OX.hom g) ≫ pullback.fst OX.hom g :=
          pullback.condition
    · calc
        e.hom ≫ φ ≫ pullback.snd OX.hom g =
            e.hom ≫ (φ ≫ pullback.snd OX.hom g) := rfl
        _ = e.hom ≫ pullback.snd (νX ≫ OX.hom) g := by rw [hφsnd]
        _ = pullback.snd νX (pullback.fst OX.hom g) ≫ pullback.snd OX.hom g :=
          pullbackRightPullbackFstIso_hom_snd OX.hom g νX
  let : IsFinite φ := by
    have : IsFinite (e.hom ≫ φ) := by
      rw [he]
      infer_instance
    simpa using (inferInstance : IsFinite (e.inv ≫ e.hom ≫ φ))
  have hcards : fiberDegreeCard νY yY = fiberDegreeCard φ yY := by
    rw [← hc]
    exact fiberDegreeCard_comp c φ hUI hbij yY
  have hcards' : fiberDegreeCard φ yY =
      fiberDegreeCard (pullback.snd νX (pullback.fst OX.hom g)) yY := by
    rw [← he]
    exact (fiberDegreeCard_comp e.hom φ inferInstance e.hom.homeomorph.bijective yY).symm
  show Cardinal.toENat (fiberDegreeCard νX x) = Cardinal.toENat (fiberDegreeCard νY yY)
  rw [hcards, hcards', ← fiberDegreeCard_pullback]
  congr 2
  exact hy.symm

/-- **Stacks Project, Tag 0C55.** Geometric unibranchness at a point is invariant under
extension of the ground field for a scheme locally of finite type over that field. -/
@[stacks 0C55, ega "IV 6.15.7" "loc. finite type, at x"]
public theorem isGeometricallyUnibranchAt_iff_of_fieldExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : X)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x) :
    IsGeometricallyUnibranchAt X x ↔
      IsGeometricallyUnibranchAt
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) y := by
  simp_rw [← numberOfGeometricBranches_eq_one_iff]
  rw [numberOfGeometricBranches_baseChange_fieldExtension k K X f x y hy]


end AlgebraicGeometry
