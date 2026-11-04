module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.LocalFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.SyntomicBaseChange.CompleteIntersection
public import StacksFrontier.AlgebraicGeometry.SyntomicLocus.Basic
public import StacksFrontier.RingTheory.LocalCompleteIntersection.Basic
public import StacksFrontier.RingTheory.LocalCompleteIntersection.FlatDescent
public import StacksFrontier.RingTheory.Syntomic.SyntomicAt

/-!
# Syntomicity of a faithfully flat factor

Let `X → Y → S` be morphisms of schemes with `f : X ⟶ Y` surjective, flat and locally of finite
presentation. If the composition is syntomic then so is `f`.

This is the half of [Stacks Project, Tag 05B7] about the first factor; the half about the second
factor is `Stacks.Syntomic.syntomic_of_comp_of_fppf`.

## Main results

* `LocalCompleteIntersection.isCompleteIntersection_iff_isCompleteIntersectionRing'`: for a
  Noetherian local ring essentially of finite type over a field, being a complete intersection
  over the field and being a complete intersection ring are the same condition.
* `LocalCompleteIntersection.isCompleteIntersection_residueFibre_of_tower`: the closed fibre of
  the upper step of a tower of local rings is a complete intersection as soon as the closed fibre
  of the composite is.
* `AlgebraicGeometry.syntomic_of_syntomic_comp_of_fppf`: if `f` is surjective, flat and locally of
  finite presentation and `f ≫ q` is syntomic, then `f` is syntomic.
* `AlgebraicGeometry.syntomic_of_syntomic_comp_of_flat`: the same conclusion without the
  surjectivity hypothesis.

## References

* [Stacks Project, Tag 01UE](https://stacks.math.columbia.edu/tag/01UE)
* [Stacks Project, Tag 02KL](https://stacks.math.columbia.edu/tag/02KL)
* [Stacks Project, Tag 02V3](https://stacks.math.columbia.edu/tag/02V3)
* [Stacks Project, Tag 05B7](https://stacks.math.columbia.edu/tag/05B7)
* [Stacks Project, Tag 09Q2](https://stacks.math.columbia.edu/tag/09Q2)
* [Stacks Project, Tag 09Q6](https://stacks.math.columbia.edu/tag/09Q6)
-/

@[expose] public section

open CategoryTheory IsLocalRing

open scoped TensorProduct

universe u v

namespace LocalCompleteIntersection

/-- For a field `k` and a Noetherian local `k`-algebra `A` essentially of finite type over `k`,
`A` is a complete intersection over `k` in the sense of Definition 00SD exactly when it is a
complete intersection ring in the sense of Definition 09Q3. -/
theorem isCompleteIntersection_iff_isCompleteIntersectionRing' (k : Type u) [Field k]
    (A : Type v)
    [CommRing A] [Algebra k A] [IsLocalRing A] [IsNoetherianRing A] [Algebra.EssFiniteType k A] :
    IsCompleteIntersection k A ↔ IsCompleteIntersectionRing A := by
  let T : Subalgebra k A := Algebra.EssFiniteType.subalgebra k A
  let p : Ideal T := (maximalIdeal A).comap (algebraMap T A)
  have : p.IsPrime := Ideal.IsPrime.comap (algebraMap T A)
  have : IsLocalization.AtPrime A p := by
    have hM : Algebra.EssFiniteType.submonoid k A = p.primeCompl :=
      Submonoid.ext fun z ↦ (notMem_maximalIdeal (x := algebraMap T A z)).symm
    rw [IsLocalization.AtPrime, ← hM]
    infer_instance
  have : IsScalarTower k T A := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing k T
  have : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  have : IsLocalRing (Localization.AtPrime p) := IsLocalization.AtPrime.isLocalRing _ p
  let e : Localization.AtPrime p ≃ₐ[T] A :=
    IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) A
  have h := isCompleteIntersection_atPrime_iff_isCompleteIntersectionRing k T p
  refine ⟨fun hA ↦ ?_, fun hA ↦ ?_⟩
  · exact isCompleteIntersectionRing_of_ringEquiv e.toRingEquiv
      (h.mp (hA.of_algEquiv (e.restrictScalars k).symm))
  · exact (h.mpr (isCompleteIntersectionRing_of_ringEquiv e.symm.toRingEquiv hA)).of_algEquiv
      (e.restrictScalars k)

/-- The quotient of a local ring `S` by the extension of the maximal ideal of a local ring `R`
along a local homomorphism `R → S` is again a local ring. -/
private theorem isLocalRing_quotient_map_maximalIdeal {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f] :
    IsLocalRing (S ⧸ (maximalIdeal R).map f) :=
  have := Ideal.Quotient.nontrivial_iff.mpr (map_maximalIdeal_lt_top f).ne
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

/-- Let `R → A → B` be local homomorphisms of local rings, with `A → B` flat and both steps
essentially of finite type. If the closed fibre `κ(R) ⊗_R B` of the composite is a complete
intersection over the residue field of `R`, then the closed fibre `κ(A) ⊗_A B` of the upper step
is a complete intersection over the residue field of `A`. -/
theorem isCompleteIntersection_residueFibre_of_tower (R A B : Type u) [CommRing R] [CommRing A]
    [CommRing B] [IsLocalRing R] [IsLocalRing A] [IsLocalRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B] [IsLocalHom (algebraMap R A)]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B] [Algebra.EssFiniteType R A]
    [Algebra.EssFiniteType A B]
    (h : IsCompleteIntersection (ResidueField R) (ResidueField R ⊗[R] B)) :
    IsCompleteIntersection (ResidueField A) (ResidueField A ⊗[A] B) := by
  have : IsLocalHom (algebraMap R B) := by
    refine ⟨fun a ha ↦ ?_⟩
    rw [IsScalarTower.algebraMap_apply R A B] at ha
    exact IsLocalHom.map_nonunit (f := algebraMap R A) a
      (IsLocalHom.map_nonunit (f := algebraMap A B) _ ha)
  have : Algebra.EssFiniteType R B := Algebra.EssFiniteType.comp R A B
  let IA : Ideal A := (maximalIdeal R).map (algebraMap R A)
  let J : Ideal B := IA.map (algebraMap A B)
  let K : Ideal B := (maximalIdeal A).map (algebraMap A B)
  have hJ : J = (maximalIdeal R).map (algebraMap R B) :=
    (Ideal.map_map (I := maximalIdeal R) (algebraMap R A) (algebraMap A B)).trans
      (congrArg (fun g : R →+* B ↦ Ideal.map g (maximalIdeal R))
        (IsScalarTower.algebraMap_eq R A B).symm)
  have : IsLocalRing (A ⧸ IA) := isLocalRing_quotient_map_maximalIdeal (algebraMap R A)
  let : Algebra (ResidueField R) (A ⧸ IA) := Ideal.Quotient.algebraQuotientMapQuotient
  have : Algebra.EssFiniteType (ResidueField R) (A ⧸ IA) :=
    Algebra.EssFiniteType.quotient_map R A (maximalIdeal R)
  have : IsNoetherianRing (A ⧸ IA) :=
    Algebra.EssFiniteType.isNoetherianRing (ResidueField R) (A ⧸ IA)
  have hcil : IsCompleteIntersectionLocalRing (ResidueField R) (ResidueField R ⊗[R] B) :=
    (Stacks.SyntomicBaseChange.isCompleteIntersectionLocalRing_iff_isCompleteIntersection _ _).mpr h
  have : IsLocalRing (ResidueField R ⊗[R] B) := hcil.isLocalRing
  have : IsNoetherianRing (ResidueField R ⊗[R] B) := hcil.isNoetherianRing
  have : Algebra.EssFiniteType (ResidueField R) (ResidueField R ⊗[R] B) := hcil.essFiniteType
  have hICRBF : IsCompleteIntersectionRing (ResidueField R ⊗[R] B) :=
    (isCompleteIntersection_iff_isCompleteIntersectionRing' _ _).mp h
  have : IsLocalRing (B ⧸ J) := hJ ▸ isLocalRing_quotient_map_maximalIdeal (algebraMap R B)
  let eB : (B ⧸ J) ≃+* (ResidueField R ⊗[R] B) :=
    (Ideal.quotientEquivAlgOfEq (R₁ := ℤ) hJ).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal R)).toRingEquiv
  have : IsNoetherianRing (B ⧸ J) :=
    isNoetherianRing_of_surjective (ResidueField R ⊗[R] B) (B ⧸ J) eB.symm.toRingHom
      eB.symm.surjective
  have hICRQB : IsCompleteIntersectionRing (B ⧸ J) :=
    isCompleteIntersectionRing_of_ringEquiv eB.symm hICRBF
  have hsq : (algebraMap (A ⧸ IA) (B ⧸ J)).comp (Ideal.Quotient.mk IA)
      = (Ideal.Quotient.mk J).comp (algebraMap A B) := by
    ext; rfl
  have : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (algebraMap (A ⧸ IA) (B ⧸ J)) := by
    refine ⟨fun z hz ↦ ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hz' : IsUnit (Ideal.Quotient.mk J (algebraMap A B a)) := hz
    exact (IsLocalHom.map_nonunit (f := algebraMap A B) a
      (IsLocalHom.map_nonunit (f := Ideal.Quotient.mk J) _ hz')).map (Ideal.Quotient.mk IA)
  have : Module.Flat (A ⧸ IA) (B ⧸ J) :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B IA).toLinearEquiv
  have hmaxQA : (maximalIdeal A).map (Ideal.Quotient.mk IA) = maximalIdeal (A ⧸ IA) :=
    map_maximalIdeal_of_surjective (Ideal.Quotient.mk IA) Ideal.Quotient.mk_surjective
  have hmapmax : (maximalIdeal (A ⧸ IA)).map (algebraMap (A ⧸ IA) (B ⧸ J))
      = K.map (Ideal.Quotient.mk J) := by
    rw [← hmaxQA, Ideal.map_map, hsq, ← Ideal.map_map]
  have hle : J ≤ K := Ideal.map_mono (map_maximalIdeal_le (algebraMap R A))
  have : IsLocalRing (B ⧸ K) := isLocalRing_quotient_map_maximalIdeal (algebraMap A B)
  let : Algebra (ResidueField A) (B ⧸ K) := Ideal.Quotient.algebraQuotientMapQuotient
  have : Algebra.EssFiniteType (ResidueField A) (B ⧸ K) :=
    Algebra.EssFiniteType.quotient_map A B (maximalIdeal A)
  have : IsNoetherianRing (B ⧸ K) :=
    Algebra.EssFiniteType.isNoetherianRing (ResidueField A) (B ⧸ K)
  have : IsLocalRing ((B ⧸ J) ⧸ (maximalIdeal (A ⧸ IA)).map (algebraMap (A ⧸ IA) (B ⧸ J))) :=
    isLocalRing_quotient_map_maximalIdeal (algebraMap (A ⧸ IA) (B ⧸ J))
  let eFib : ((B ⧸ J) ⧸ (maximalIdeal (A ⧸ IA)).map (algebraMap (A ⧸ IA) (B ⧸ J)))
      ≃+* (B ⧸ K) :=
    (Ideal.quotientEquivAlgOfEq (R₁ := ℤ) hmapmax).toRingEquiv.trans
      (DoubleQuot.quotQuotEquivQuotOfLE hle)
  have hICRK : IsCompleteIntersectionRing (B ⧸ K) :=
    isCompleteIntersectionRing_of_ringEquiv eFib
      (isCompleteIntersectionRing_quotient_of_flat (A ⧸ IA) (B ⧸ J) hICRQB)
  let eK : (B ⧸ K) ≃ₐ[ResidueField A] (ResidueField A ⊗[A] B) :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A)
  have : IsLocalRing (ResidueField A ⊗[A] B) := eK.toRingEquiv.isLocalRing
  have : IsNoetherianRing (ResidueField A ⊗[A] B) :=
    isNoetherianRing_of_surjective (B ⧸ K) (ResidueField A ⊗[A] B) eK.toRingHom eK.surjective
  have : Algebra.EssFiniteType (ResidueField A) (ResidueField A ⊗[A] B) :=
    Algebra.EssFiniteType.of_surjective eK.toAlgHom eK.surjective
  exact (isCompleteIntersection_iff_isCompleteIntersectionRing' (ResidueField A)
    (ResidueField A ⊗[A] B)).mpr
    (isCompleteIntersectionRing_of_ringEquiv eK.toRingEquiv hICRK)

end LocalCompleteIntersection

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/-- If `f : X ⟶ Y` is surjective, flat and locally of finite presentation and `f ≫ q` is
syntomic, then `f` is syntomic. -/
@[stacks 05B7 "f_syntomic"]
theorem syntomic_of_syntomic_comp_of_fppf (f : X ⟶ Y) (q : Y ⟶ S) [Surjective f] [Flat f]
    [LocallyOfFinitePresentation f] (hcomp : Syntomic (f ≫ q)) : Syntomic f := by
  have : Flat (f ≫ q) := AlgebraicGeometry.flat hcomp
  have : LocallyOfFinitePresentation (f ≫ q) := AlgebraicGeometry.locallyOfFinitePresentation hcomp
  have : LocallyOfFinitePresentation q := locallyOfFinitePresentation_of_comp_of_fppf f q
  intro x
  have hfib : IsCompleteIntersectionFibreAt (f ≫ q) x :=
    (isSyntomicAt_iff_isCompleteIntersectionFibreAt (f ≫ q) x).mp (hcomp x)
  refine (isSyntomicAt_iff_isCompleteIntersectionFibreAt f x).mpr ?_
  let : Algebra (S.presheaf.stalk ((f ≫ q) x)) (Y.presheaf.stalk (f x)) :=
    (q.stalkMap (f x)).hom.toAlgebra
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  let : Algebra (S.presheaf.stalk ((f ≫ q) x)) (X.presheaf.stalk x) :=
    ((f ≫ q).stalkMap x).hom.toAlgebra
  have hcompMap : ((f.stalkMap x).hom).comp ((q.stalkMap (f x)).hom)
      = (((f ≫ q).stalkMap x).hom) :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp f q x).symm
  have : IsScalarTower (S.presheaf.stalk ((f ≫ q) x)) (Y.presheaf.stalk (f x))
      (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' hcompMap.symm
  have : IsLocalHom (algebraMap (S.presheaf.stalk ((f ≫ q) x)) (Y.presheaf.stalk (f x))) :=
    inferInstanceAs (IsLocalHom (q.stalkMap (f x)).hom)
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    RingHom.flat_algebraMap_iff.mp (Flat.stalkMap f x)
  have : Algebra.EssFiniteType (S.presheaf.stalk ((f ≫ q) x)) (Y.presheaf.stalk (f x)) :=
    RingHom.essFiniteType_algebraMap.mp (LocallyOfFiniteType.stalkMap q (f x))
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    RingHom.essFiniteType_algebraMap.mp (LocallyOfFiniteType.stalkMap f x)
  exact LocalCompleteIntersection.isCompleteIntersection_residueFibre_of_tower
    (S.presheaf.stalk ((f ≫ q) x)) (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) hfib

/-- A flat morphism locally of finite presentation whose composite with another morphism is
syntomic is itself syntomic. -/
theorem syntomic_of_syntomic_comp_of_flat (f : X ⟶ Y) (q : Y ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (hcomp : Syntomic (f ≫ q)) : Syntomic f := by
  have : IsZariskiLocalAtTarget (@Syntomic.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Syntomic.{u})
  have : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFinitePresentation.{u})
  have hrr : MorphismProperty.RespectsRight (@Syntomic.{u} : MorphismProperty Scheme.{u})
      (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) :=
    ⟨fun i hi g hg ↦ MorphismProperty.comp_mem _ g i hg
      (have : IsOpenImmersion i := hi; syntomic_of_isOpenImmersion i)⟩
  let V : Y.Opens := ⟨Set.range f.base, f.isOpenMap.isOpen_range⟩
  have : Surjective (f ∣_ V) := ⟨by
    rintro ⟨y, x, rfl⟩
    exact ⟨⟨x, Set.mem_range_self x⟩, Subtype.ext (morphismRestrict_base_coe f V _)⟩⟩
  have : LocallyOfFinitePresentation (f ∣_ V) :=
    IsZariskiLocalAtTarget.restrict (P := @LocallyOfFinitePresentation.{u}) (f := f)
      inferInstance V
  have hcomp' : Syntomic ((f ∣_ V) ≫ (V.ι ≫ q)) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    exact MorphismProperty.comp_mem _ (f ⁻¹ᵁ V).ι (f ≫ q)
      (syntomic_of_isOpenImmersion _) hcomp
  exact IsZariskiLocalAtTarget.of_range_subset_iSup (P := @Syntomic.{u}) (f := f)
    (fun _ : Unit ↦ V) (by simp [V]) fun _ ↦
      syntomic_of_syntomic_comp_of_fppf (f ∣_ V) (V.ι ≫ q) hcomp'

end AlgebraicGeometry

end
