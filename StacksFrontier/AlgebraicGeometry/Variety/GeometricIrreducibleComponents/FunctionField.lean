module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Lemmas
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleLocal
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Defs
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Subalgebra
public import StacksFrontier.RingTheory.GeometricallyIrreducible.TFAE
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Tower

/-!
# Geometric irreducibility and the function field

For an irreducible scheme over a field, geometric irreducibility can be tested on the residue
field at its generic point. It is also equivalent to the base field being separably
algebraically closed in that function field.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_tfae_functionField` gives the three equivalent
  characterizations of geometric irreducibility.

## Implementation notes

The function field is represented by `AlgebraicGeometry.Scheme.residueField` at a generic point.
Its canonical `k`-algebra structure is the composite from `k` to the global sections of `X` and
then evaluation at that point. The three conditions from the source are recorded with
`List.TFAE` in their original order.

Both equivalences are proved on one affine open through the generic point: geometric
irreducibility of the sections there is geometric irreducibility of the residue field at the
corresponding minimal prime, because that residue field is a localization of a quotient by a
nilpotent ideal, and both operations leave the spectrum of every base change unchanged up to
homeomorphism or dense embedding.

## References

* [Stacks Project, Tag 054Q](https://stacks.math.columbia.edu/tag/054Q)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open CommRingCat

namespace AlgebraicGeometry

universe u

section

open scoped TensorProduct

private theorem irreducibleSpace_iff_of_isHomeomorph {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] (f : α → β) (hf : IsHomeomorph f) :
    IrreducibleSpace α ↔ IrreducibleSpace β :=
  (hf.homeomorph f).irreducibleSpace_iff

private theorem irreducibleSpace_iff_of_denseEmbedding {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] (f : α → β) (hf : Topology.IsEmbedding f)
    (hd : DenseRange f) : IrreducibleSpace α ↔ IrreducibleSpace β := by
  refine ⟨fun _ => irreducibleSpace_of_denseRange hf.continuous hd, fun _ => ?_⟩
  have hrange : IsIrreducible (Set.range f) := by
    rw [← isIrreducible_iff_closure, hd.closure_range]
    exact IrreducibleSpace.isIrreducible_univ β
  exact hf.toHomeomorph.irreducibleSpace_iff.mpr (Subtype.irreducibleSpace hrange)

private theorem genericPoint_eq_nilradical (A : Type u) [CommRing A]
    [hA : IrreducibleSpace (Spec (.of A))] :
    genericPoint (Spec (.of A)) = ⟨nilradical A,
      PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hA⟩ := by
  apply (genericPoint_spec (Spec (.of A))).eq
  show closure ({⟨nilradical A,
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp ‹_›⟩} :
      Set (PrimeSpectrum A)) = Set.univ
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    PrimeSpectrum.vanishingIdeal_singleton, ← PrimeSpectrum.zeroLocus_nilradical]

private theorem primeIdealOf_genericPoint_of_irreducible {X : Scheme.{u}}
    [IrreducibleSpace X] {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    [IrreducibleSpace (Spec Γ(X, U))] :
    hU.primeIdealOf ⟨genericPoint X,
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)⟩ =
      genericPoint (Spec Γ(X, U)) := by
  have : IrreducibleSpace U.toScheme := U.ι.isOpenEmbedding.irreducibleSpace
  apply hU.fromSpec.isOpenEmbedding.injective
  rw [hU.fromSpec_primeIdealOf]
  exact (genericPoint_eq_of_isOpenImmersion hU.fromSpec).symm

private noncomputable def residueField_localization_equiv
    (k A S : Type u) [Field k] [CommRing A] [CommRing S] [IsLocalRing S]
    [Algebra k A] [Algebra A S] [Algebra k S] [IsScalarTower k A S]
    (I : Ideal A) [I.IsPrime] [IsLocalization I.primeCompl S] :
    I.ResidueField ≃ₐ[k] IsLocalRing.ResidueField S :=
  (IsLocalRing.ResidueField.mapAlgEquiv
    (IsLocalization.algEquiv I.primeCompl (Localization.AtPrime I) S)).restrictScalars k

private theorem affineSections_stalk_scalarTower
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (ξ : X) (U : X.Opens) (hξU : ξ ∈ U) :
    letI : Algebra k Γ(X, U) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra
    letI : Algebra k (X.presheaf.stalk ξ) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ ξ (by simp)).hom.toAlgebra
    letI : Algebra Γ(X, U) (X.presheaf.stalk ξ) :=
      (X.presheaf.germ U ξ hξU).hom.toAlgebra
    IsScalarTower k Γ(X, U) (X.presheaf.stalk ξ) := by
  let : Algebra k Γ(X, U) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra
  let : Algebra k (X.presheaf.stalk ξ) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ ξ (by simp)).hom.toAlgebra
  let : Algebra Γ(X, U) (X.presheaf.stalk ξ) :=
    (X.presheaf.germ U ξ hξU).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  refine RingHom.ext fun a => ?_
  show X.presheaf.germ ⊤ ξ (by simp)
      ((f.appTop).hom ((Scheme.ΓSpecIso (.of k)).inv.hom a)) =
    X.presheaf.germ U ξ hξU
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        ((f.appTop).hom ((Scheme.ΓSpecIso (.of k)).inv.hom a)))
  exact (X.presheaf.germ_res_apply (homOfLE (show U ≤ ⊤ from le_top)) ξ hξU _).symm

/-- Geometric irreducibility of two `k`-algebras is equivalent once irreducibility of the prime
spectra of their base changes to every field extension agrees. -/
private theorem isGeometricallyIrreducible_iff_of_forall_irreducibleSpace_iff
    (k A B : Type u) [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (h : ∀ (F : Type u) [Field F] [Algebra k F],
      IrreducibleSpace (PrimeSpectrum (A ⊗[k] F)) ↔ IrreducibleSpace (PrimeSpectrum (B ⊗[k] F))) :
    Algebra.IsGeometricallyIrreducible k A ↔ Algebra.IsGeometricallyIrreducible k B := by
  rw [Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct,
    Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct]
  exact ⟨fun hA F _ _ => (h F).mp (hA F), fun hB F _ _ => (h F).mpr (hB F)⟩

/-- **Geometric irreducibility is invariant under an isomorphism of algebras.** Two isomorphic
`k`-algebras are geometrically irreducible over `k` together: the isomorphism survives every base
change, and a bijective algebra map induces a homeomorphism of prime spectra. -/
public theorem isGeometricallyIrreducible_iff_of_algEquiv
    (k A B : Type u) [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B) :
    Algebra.IsGeometricallyIrreducible k A ↔ Algebra.IsGeometricallyIrreducible k B := by
  refine isGeometricallyIrreducible_iff_of_forall_irreducibleSpace_iff k A B fun F _ _ => ?_
  let ψ : A ⊗[k] F →ₐ[k] B ⊗[k] F :=
    Algebra.TensorProduct.map e (AlgEquiv.refl (R := k) (A₁ := F))
  have hbij : Function.Bijective ψ.toRingHom := by
    simpa [ψ] using Algebra.TensorProduct.map_bijective e.bijective
      (AlgEquiv.refl (R := k) (A₁ := F)).bijective
  exact (irreducibleSpace_iff_of_isHomeomorph _
    (PrimeSpectrum.isHomeomorph_comap_of_bijective hbij)).symm

private theorem irreducibleSpace_tensor_quotient_iff_residueField
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] (I : Ideal A) [I.IsPrime]
    (F : Type u) [Field F] [Algebra k F] :
    IrreducibleSpace (PrimeSpectrum ((A ⧸ I) ⊗[k] F)) ↔
      IrreducibleSpace (PrimeSpectrum (I.ResidueField ⊗[k] F)) := by
  let ψ₁ : (A ⧸ I) ⊗[k] F →ₐ[k] I.ResidueField ⊗[k] F :=
    Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom k (A ⧸ I) I.ResidueField) (AlgHom.id k F)
  let M : Submonoid ((A ⧸ I) ⊗[k] F) :=
    Algebra.algebraMapSubmonoid ((A ⧸ I) ⊗[k] F) (nonZeroDivisors (A ⧸ I))
  let : Algebra ((A ⧸ I) ⊗[k] F) (I.ResidueField ⊗[k] F) := ψ₁.toRingHom.toAlgebra
  let : Algebra (A ⧸ I) (I.ResidueField ⊗[k] F) := Algebra.TensorProduct.leftAlgebra
  have : IsScalarTower (A ⧸ I) ((A ⧸ I) ⊗[k] F) (I.ResidueField ⊗[k] F) :=
    IsScalarTower.of_algebraMap_eq'
      (R := A ⧸ I) (S := (A ⧸ I) ⊗[k] F) (A := I.ResidueField ⊗[k] F) (by
        apply Ideal.Quotient.ringHom_ext
        ext x
        show (algebraMap A I.ResidueField) x ⊗ₜ[k] 1 =
          ψ₁ ((Ideal.Quotient.mk I x) ⊗ₜ[k] (1 : F))
        simp [ψ₁, Ideal.algebraMap_quotient_residueField_mk])
  have hcomm :
      (algebraMap ((A ⧸ I) ⊗[k] F) (I.ResidueField ⊗[k] F)).comp
        Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := by
    show ψ₁.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom
    ext x
    simp [ψ₁]
  have : IsLocalization M (I.ResidueField ⊗[k] F) :=
    IsLocalization.tensorProduct_tensorProduct k F (nonZeroDivisors (A ⧸ I))
      I.ResidueField hcomm
  have hemb : Topology.IsEmbedding (PrimeSpectrum.comap ψ₁.toRingHom) := by
    show Topology.IsEmbedding (PrimeSpectrum.comap
      (algebraMap ((A ⧸ I) ⊗[k] F) (I.ResidueField ⊗[k] F)))
    exact PrimeSpectrum.localization_comap_isEmbedding _ M
  have hker₁ : RingHom.ker ψ₁.toRingHom ≤ nilradical ((A ⧸ I) ⊗[k] F) :=
    geomIrred_kernel_residue_denseRange k (A ⧸ I) I.ResidueField
      (IsScalarTower.toAlgHom k (A ⧸ I) I.ResidueField)
      (((RingHom.injective_iff_ker_eq_bot _).mp
        (IsFractionRing.injective (A ⧸ I) I.ResidueField)).le.trans bot_le) F
  exact (irreducibleSpace_iff_of_denseEmbedding _ hemb
    ((PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical ψ₁.toRingHom).mpr hker₁)).symm

private theorem isGeometricallyIrreducible_iff_residueField
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (I : Ideal A) [I.IsPrime] (hI : I = nilradical A) :
    Algebra.IsGeometricallyIrreducible k A ↔
      Algebra.IsGeometricallyIrreducible k I.ResidueField := by
  classical
  let q : A →ₐ[k] A ⧸ I := Ideal.Quotient.mkₐ k I
  have hqker : RingHom.ker q.toRingHom ≤ nilradical A := by
    intro x hx
    change Ideal.Quotient.mk I x = 0 at hx
    rwa [Ideal.Quotient.eq_zero_iff_mem, hI] at hx
  refine isGeometricallyIrreducible_iff_of_forall_irreducibleSpace_iff k A _ fun F _ _ => ?_
  let ψ₀ : A ⊗[k] F →ₐ[k] (A ⧸ I) ⊗[k] F :=
    Algebra.TensorProduct.map q (AlgHom.id k F)
  have hsurj₀ : Function.Surjective ψ₀.toRingHom :=
    TensorProduct.map_surjective Ideal.Quotient.mk_surjective (fun x => ⟨x, rfl⟩)
  have hhomeo₀ : IsHomeomorph (PrimeSpectrum.comap ψ₀.toRingHom) :=
    PrimeSpectrum.isHomeomorph_comap ψ₀.toRingHom
      (by
        intro x
        obtain ⟨y, hy⟩ := hsurj₀ x
        exact ⟨1, by decide, ⟨y, by simpa using hy⟩⟩)
      (geomIrred_kernel_residue_denseRange k A (A ⧸ I) q hqker F)
  exact (irreducibleSpace_iff_of_isHomeomorph _ hhomeo₀).symm.trans
    (irreducibleSpace_tensor_quotient_iff_residueField k A I F)

private theorem affineSections_iff_geometricallyIrreducible_residueField
    (k : Type u) [Field k] {X : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ Spec (.of k)) (U : X.affineOpens) (hU : Nonempty (U : Set X)) :
    letI : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    letI : Algebra k (X.residueField (genericPoint X)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.Γevaluation (genericPoint X)).hom.toAlgebra
    Algebra.IsGeometricallyIrreducible k Γ(X, U.1) ↔
      Algebra.IsGeometricallyIrreducible k (X.residueField (genericPoint X)) := by
  classical
  have : Nonempty U.1 := hU
  have hξU : genericPoint X ∈ U.1 :=
    ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using Set.nonempty_coe_sort.mp hU)
  let xU : U.1 := ⟨genericPoint X, hξU⟩
  have : IrreducibleSpace U.1.toScheme := U.1.ι.isOpenEmbedding.irreducibleSpace
  have : IrreducibleSpace (Spec Γ(X, U.1)) := U.2.isoSpec.hom.homeomorph.irreducibleSpace_iff.mp ‹_›
  let A : Type u := Γ(X, U.1)
  let p : PrimeSpectrum A := U.2.primeIdealOf xU
  have hp : p = genericPoint (Spec (.of A)) :=
    primeIdealOf_genericPoint_of_irreducible U.2
  let I : Ideal A := p.asIdeal
  have : I.IsPrime := p.2
  have hI : I = nilradical A := by
    show p.asIdeal = nilradical A
    rw [hp, genericPoint_eq_nilradical A]
  let : Algebra k A :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
  let : Algebra k (X.residueField (genericPoint X)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.Γevaluation (genericPoint X)).hom.toAlgebra
  let : Algebra k (X.presheaf.stalk (genericPoint X)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) (by simp)).hom.toAlgebra
  let : Algebra A (X.presheaf.stalk (genericPoint X)) :=
    (X.presheaf.germ U.1 (genericPoint X) hξU).hom.toAlgebra
  have : IsScalarTower k A (X.presheaf.stalk (genericPoint X)) :=
    affineSections_stalk_scalarTower k f (genericPoint X) U.1 hξU
  have : IsLocalization I.primeCompl (X.presheaf.stalk (genericPoint X)) :=
    U.2.isLocalization_stalk xU
  let e : I.ResidueField ≃ₐ[k] X.residueField (genericPoint X) :=
    residueField_localization_equiv k A (X.presheaf.stalk (genericPoint X)) I
  exact (isGeometricallyIrreducible_iff_residueField k A I hI).trans
    (isGeometricallyIrreducible_iff_of_algEquiv k _ _ e)

end

/-- **Stacks Project, Tag 054Q.** For an irreducible scheme `X` over a field `k`, the following
are equivalent: `X` is geometrically irreducible over `k`; the residue field at a generic point
is geometrically irreducible over `k`; and the separable closure of `k` in that residue field is
trivial. -/
@[stacks 054Q, ega "IV 4.5.12", ega "IV 4.5.9" "(a) ⇔ (c)"]
public theorem geometricallyIrreducible_tfae_functionField
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IrreducibleSpace X] (ξ : X) (hξ : IsGenericPoint ξ Set.univ) :
    letI : Algebra k (X.residueField ξ) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation ξ).hom.toAlgebra
    List.TFAE [
      GeometricallyIrreducible f,
      Algebra.IsGeometricallyIrreducible k (X.residueField ξ),
      separableClosure k (X.residueField ξ) = ⊥] := by
  obtain rfl : ξ = genericPoint X := hξ.eq (genericPoint_spec X)
  let : Algebra k (X.residueField (genericPoint X)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.Γevaluation (genericPoint X)).hom.toAlgebra
  tfae_have 1 ↔ 2 := by
    have hlocal := (geometricallyIrreducible_tfae_local k f).out 1 2
    refine ⟨fun hf => ?_, fun hK => hlocal.mpr ⟨⟨genericPoint X⟩, fun U hU =>
      (affineSections_iff_geometricallyIrreducible_residueField k f U hU).mpr hK⟩⟩
    let U : X.affineOpens :=
      ⟨(X.affineCover.f (X.affineCover.idx (genericPoint X))).opensRange,
        isAffineOpen_opensRange _⟩
    have hU : Nonempty (U : Set X) := ⟨genericPoint X, X.affineCover.covers (genericPoint X)⟩
    exact (affineSections_iff_geometricallyIrreducible_residueField k f U hU).mp
      ((hlocal.mp hf).2 U hU)
  tfae_have 2 ↔ 3 := by
    show Algebra.IsGeometricallyIrreducible k (X.residueField (genericPoint X)) ↔
      separableClosure k (X.residueField (genericPoint X)) = ⊥
    exact (separableClosure.eq_bot_iff_geometricallyIrreducible k
      (X.residueField (genericPoint X))).symm
  tfae_finish

end AlgebraicGeometry
