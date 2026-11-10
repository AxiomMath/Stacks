module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective
public import StacksFrontier.Deformation.Examples.Geometric.Smoothing

/-!
# Smoothing a finite complete intersection over a field, as a family of schemes

Let `k` be a field and let `A` be a finite-dimensional `k`-algebra which is a local complete
intersection over `k`. The spectrum of `A` is then the special fibre of a flat, finite and
projective family of schemes over the formal disc `Spec k⟦t⟧` whose generic fibre is smooth.

The family is `Spec B ⟶ Spec k⟦t⟧` for the algebra `B` of
`Deformation.Examples.Smoothing.exists_finite_powerSeries_specialFiber_etale_genericFiber`: it
is finite and flat over `k⟦t⟧`, its special fibre `B / tB` is `A`, and its generic fibre
`k⸨t⸩ ⊗ B` is étale over `k⸨t⸩`. The generic fibre of the family is the fibre at the zero prime
of `k⟦t⟧`, whose residue field is uniquely isomorphic to `k⸨t⸩` over `k⟦t⟧`; the special fibre
is the base change along the constant-coefficient map `k⟦t⟧ → k`, whose kernel is `(t)`.

## Main results

* `Deformation.Examples.Smoothing.exists_flat_finite_projective_smoothing_of_finiteDimensional`:
  the family of schemes, with its four properties.

## Implementation notes

The generic fibre is phrased with `AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField` at the
zero prime. The special fibre is phrased as an isomorphism of `Spec A` with the pullback of the
family along `PowerSeries.constantCoeff`, commuting with the two morphisms to `Spec k`, so that
it is an identification of `k`-schemes rather than of bare schemes.

## References

* [The Stacks Project, Tag 0E7W](https://stacks.math.columbia.edu/tag/0E7W)
* [The Stacks Project, Tag 0E7Y](https://stacks.math.columbia.edu/tag/0E7Y)
* [The Stacks Project, Tag 0E7Z](https://stacks.math.columbia.edu/tag/0E7Z)
* [The Stacks Project, Tag 0E7T](https://stacks.math.columbia.edu/tag/0E7T)
* [The Stacks Project, Tag 0E7X](https://stacks.math.columbia.edu/tag/0E7X)
* [The Stacks Project, Tag 0DZP](https://stacks.math.columbia.edu/tag/0DZP)
* [The Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CommRingCat
open scoped TensorProduct

universe u

namespace Deformation.Examples.Smoothing

/-- Base change of a `k⟦t⟧`-algebra along the constant-coefficient map `k⟦t⟧ → k` is its
special fibre `B / tB`. -/
private theorem nonempty_specialFibre_algEquiv
    (k : Type u) [Field k] (B : Type u) [CommRing B] [Algebra (PowerSeries k) B]
    [Algebra k B] [IsScalarTower k (PowerSeries k) B] :
    letI : Algebra (PowerSeries k) k := (PowerSeries.constantCoeff (R := k)).toAlgebra
    Nonempty ((B ⧸ Ideal.span {algebraMap (PowerSeries k) B (PowerSeries.X : PowerSeries k)})
      ≃ₐ[k] TensorProduct (PowerSeries k) k B) := by
  let : Algebra (PowerSeries k) k := (PowerSeries.constantCoeff (R := k)).toAlgebra
  let I : Ideal (PowerSeries k) := Ideal.span {(PowerSeries.X : PowerSeries k)}
  have hker : RingHom.ker (PowerSeries.constantCoeff (R := k)) = I := by
    rw [PowerSeries.ker_coeff_eq_max_ideal, PowerSeries.maximalIdeal_eq_span_X]
  have hmap : I.map (algebraMap (PowerSeries k) B) =
      Ideal.span {algebraMap (PowerSeries k) B (PowerSeries.X : PowerSeries k)} := by
    rw [show I = Ideal.span {(PowerSeries.X : PowerSeries k)} from rfl, Ideal.map_span]
    simp
  let ek : (PowerSeries k ⧸ I) ≃ₐ[PowerSeries k] k :=
    AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj))
      (fun _ => rfl)
  let e1 : (B ⧸ I.map (algebraMap (PowerSeries k) B)) ≃ₐ[PowerSeries k]
      TensorProduct (PowerSeries k) (PowerSeries k ⧸ I) B :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).restrictScalars (PowerSeries k)
  let e2 : TensorProduct (PowerSeries k) (PowerSeries k ⧸ I) B ≃ₐ[PowerSeries k]
      TensorProduct (PowerSeries k) k B :=
    Algebra.TensorProduct.congr ek AlgEquiv.refl
  have hcomm : ∀ a : k, (e1.trans e2)
      (algebraMap k (B ⧸ I.map (algebraMap (PowerSeries k) B)) a) =
      algebraMap k (TensorProduct (PowerSeries k) k B) a := by
    intro a
    have hB : algebraMap k B a =
        algebraMap (PowerSeries k) B (PowerSeries.C a) := by
      rw [IsScalarTower.algebraMap_apply k (PowerSeries k) B]
      simp
    have hstep : (1 : k) ⊗ₜ[PowerSeries k] algebraMap k B a =
        a ⊗ₜ[PowerSeries k] (1 : B) := by
      rw [hB, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
      congr 1
      rw [Algebra.smul_def, mul_one]
      simp [RingHom.algebraMap_toAlgebra]
    have h1 : (e1.trans e2)
        (algebraMap k (B ⧸ I.map (algebraMap (PowerSeries k) B)) a) =
        (1 : k) ⊗ₜ[PowerSeries k] algebraMap k B a := by
      change (Algebra.TensorProduct.congr ek AlgEquiv.refl)
        ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I)
          (Ideal.Quotient.mk (I.map (algebraMap (PowerSeries k) B))
            (algebraMap k B a))) = _
      rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
      simp
    rw [h1, hstep]
    rfl
  exact ⟨(Ideal.quotientEquivAlgOfEq k hmap.symm).trans
    (AlgEquiv.ofRingEquiv (f := (e1.trans e2).toRingEquiv) hcomm)⟩

/-- A finite-dimensional local complete intersection `A` over a field `k` is the special fibre
of a flat, finite and projective family of schemes over the formal disc whose generic fibre is
smooth.

Concretely: there are a scheme `Y` and a morphism `g : Y ⟶ Spec k⟦t⟧` which is flat, finite and
projective, whose fibre over the zero prime of `k⟦t⟧` is smooth over the residue field there,
and whose base change along `PowerSeries.constantCoeff : k⟦t⟧ → k` is isomorphic to `Spec A`
compatibly with the two morphisms to `Spec k`. -/
public theorem exists_flat_finite_projective_smoothing_of_finiteDimensional
    (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A]
    [FiniteDimensional k A] (hA : IsLocalCompleteIntersection k A) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k))),
      Flat g ∧ IsFinite g ∧ AlgebraicGeometry.IsProjective g ∧
      Smooth (g.fiberToSpecResidueField
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (PowerSeries k))) ∧
      ∃ e : Spec (.of A) ≅
          pullback g (Spec.map (ofHom (PowerSeries.constantCoeff (R := k)))),
        e.hom ≫ pullback.snd g
            (Spec.map (ofHom (PowerSeries.constantCoeff (R := k)))) =
          Spec.map (ofHom (algebraMap k A)) := by
  obtain ⟨B, hB, hPS, hk, htower, hfinite, hflat, hspecial, hetale⟩ :=
    exists_finite_powerSeries_specialFiber_etale_genericFiber k A hA
  let : CommRing B := hB
  let : Algebra (PowerSeries k) B := hPS
  let : Algebra k B := hk
  let : IsScalarTower k (PowerSeries k) B := htower
  let : Module.Finite (PowerSeries k) B := hfinite
  let : Module.Flat (PowerSeries k) B := hflat
  let : Algebra.Etale (LaurentSeries k)
    (TensorProduct (PowerSeries k) (LaurentSeries k) B) := hetale
  have hfin : IsFinite (Spec.map (ofHom (algebraMap (PowerSeries k) B))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  refine ⟨Spec (.of B), Spec.map (ofHom (algebraMap (PowerSeries k) B)),
    ?_, hfin, ?_, ?_, ?_⟩
  · rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · exact Stacks.FiniteMorphismProjective.isProjective_of_isFinite_of_isAffine _
  · let e : (⊥ : Ideal (PowerSeries k)).ResidueField ≃ₐ[PowerSeries k] LaurentSeries k :=
      IsLocalization.algEquiv (nonZeroDivisors (PowerSeries k)) _ _
    let eT : (⊥ : Ideal (PowerSeries k)).Fiber B ≃ₐ[PowerSeries k]
        TensorProduct (PowerSeries k) (LaurentSeries k) B :=
      Algebra.TensorProduct.congr e (AlgEquiv.refl)
    have hcompat : (algebraMap ((⊥ : Ideal (PowerSeries k)).ResidueField)
          ((⊥ : Ideal (PowerSeries k)).Fiber B)) =
        (eT.symm.toRingEquiv.toRingHom.comp
          (algebraMap (LaurentSeries k)
            (TensorProduct (PowerSeries k) (LaurentSeries k) B))).comp
          e.toRingEquiv.toRingHom := by
      apply RingHom.ext
      intro x
      apply eT.injective
      simp [eT, Algebra.TensorProduct.algebraMap_apply]
    have hring : (algebraMap ((⊥ : Ideal (PowerSeries k)).ResidueField)
        ((⊥ : Ideal (PowerSeries k)).Fiber B)).Smooth := by
      have h0 : (algebraMap (LaurentSeries k)
          (TensorProduct (PowerSeries k) (LaurentSeries k) B)).Smooth :=
        RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩
      rw [hcompat]
      exact RingHom.Smooth.respectsIso.2 _ e.toRingEquiv
        (RingHom.Smooth.respectsIso.1 _ eT.symm.toRingEquiv h0)
    let : MorphismProperty.RespectsIso (@Smooth) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    refine (MorphismProperty.arrow_mk_iso_iff (P := @Smooth)
      (Spec.fiberToSpecResidueFieldIso (PowerSeries k) B
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (PowerSeries k)))).mpr ?_
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact hring
  · let : Algebra (PowerSeries k) k := (PowerSeries.constantCoeff (R := k)).toAlgebra
    have hi : (PowerSeries.constantCoeff (R := k)) = algebraMap (PowerSeries k) k :=
      (RingHom.algebraMap_toAlgebra _).symm
    obtain ⟨eS⟩ := nonempty_specialFibre_algEquiv k B
    obtain ⟨eA⟩ := hspecial
    let ec : A ≃ₐ[k] TensorProduct (PowerSeries k) k B := eA.symm.trans eS
    let φ : CommRingCat.of (TensorProduct (PowerSeries k) k B) ⟶ CommRingCat.of A :=
      ofHom ec.symm.toRingEquiv.toRingHom
    have : IsIso φ := ec.symm.toRingEquiv.toCommRingCatIso.isIso_hom
    rw [hi]
    refine ⟨asIso (Spec.map φ) ≪≫ (pullbackSpecIso (PowerSeries k) k B).symm ≪≫
      pullbackSymmetry _ _, ?_⟩
    rw [Iso.trans_hom, Iso.trans_hom, asIso_hom, Category.assoc, Category.assoc,
      pullbackSymmetry_hom_comp_snd, Iso.symm_hom, pullbackSpecIso_inv_fst',
      ← Spec.map_comp]
    congr 1
    ext a
    exact ec.symm.commutes a

end Deformation.Examples.Smoothing

end
