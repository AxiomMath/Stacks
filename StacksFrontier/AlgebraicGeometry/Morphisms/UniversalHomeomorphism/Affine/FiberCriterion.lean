module

public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.ResidueField
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# A fibre criterion for integral universal homeomorphisms

An integral ring map induces a universal homeomorphism on spectra if every field-valued fibre
has exactly one prime and the residue field at that prime is purely inseparable over the base
field. If the residue fields of the fibres are unchanged, the original map also induces
isomorphisms on residue fields.

## Main definitions

There are no new definitions.

## Main results

* `universalHomeomorphism_specMap_of_integral_of_fiber_unique_prime_isPurelyInseparable`
  is the fibre criterion for an integral ring map to induce a universal homeomorphism.
* `AlgebraicGeometry.isIso_residueFieldMap_specMap_of_fiber_residueField_bijective` gives the
  corresponding criterion for the maps on residue fields to be isomorphisms.

## Implementation notes

An arbitrary map from the base ring to a field is represented explicitly by a ring
homomorphism. The field structure on a fibre residue field is taken along the composite of the
right inclusion into the tensor product and the canonical map to the residue field. Having
exactly one prime is expressed by nonemptiness and subsingletonness of the prime spectrum, and
the assertion that a fibre residue field equals the base field by bijectivity of this
canonical homomorphism.

The residue-field conclusion needs neither integrality nor uniqueness of the fibre point: base
change to the residue field of its image identifies the residue field at any point with the
residue field at the corresponding point of the fibre.

## References

* [Stacks Project, Tag 0EUI](https://stacks.math.columbia.edu/tag/0EUI), in the proof
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

private lemma exists_comp_eq_of_ker_eq {S K : Type u} [CommRing S] [Field K]
    (g : S →+* K) (q : Ideal S) [q.IsPrime] (hq : RingHom.ker g = q) :
    ∃ σ : q.ResidueField →+* K,
      σ.comp (algebraMap S q.ResidueField) = g := by
  have hu : q.primeCompl ≤ (IsUnit.submonoid K).comap g := fun x hx ↦
    isUnit_iff_ne_zero.mpr fun h ↦ hx (hq ▸ RingHom.mem_ker.mpr h)
  exact ⟨Ideal.ResidueField.lift q g hq.ge hu, RingHom.ext fun x ↦ by simp⟩

private lemma eq_of_fiber_condition
    {A C K : Type u} [CommRing A] [CommRing C] [Algebra A C] [Field K]
    (h : ∀ (k : Type u) [Field k] (g : A →+* k),
      letI : Algebra A k := g.toAlgebra
      (Nonempty (PrimeSpectrum (TensorProduct A C k)) ∧
        Subsingleton (PrimeSpectrum (TensorProduct A C k))) ∧
        ∀ p : PrimeSpectrum (TensorProduct A C k),
          let ι : k →+* p.asIdeal.ResidueField :=
            (algebraMap (TensorProduct A C k) p.asIdeal.ResidueField).comp
              (Algebra.TensorProduct.includeRight :
                k →ₐ[A] TensorProduct A C k).toRingHom
          letI : Algebra k p.asIdeal.ResidueField := ι.toAlgebra
          IsPurelyInseparable k p.asIdeal.ResidueField)
    {g₁ g₂ : C →+* K}
    (hg : g₁.comp (algebraMap A C) = g₂.comp (algebraMap A C)) : g₁ = g₂ := by
  let : Algebra A K := (g₁.comp (algebraMap A C)).toAlgebra
  have hK := h K (g₁.comp (algebraMap A C))
  let F (g : C →+* K) (hg : g.comp (algebraMap A C) = g₁.comp (algebraMap A C)) :
      TensorProduct A C K →ₐ[A] K :=
    Algebra.TensorProduct.lift ⟨g, fun a ↦ RingHom.congr_fun hg a⟩ (AlgHom.id A K)
      (fun _ _ ↦ Commute.all _ _)
  let p : PrimeSpectrum (TensorProduct A C K) :=
    ⟨RingHom.ker (F g₁ rfl).toRingHom, RingHom.ker_isPrime _⟩
  have : p.asIdeal.IsPrime := p.isPrime
  have hker : RingHom.ker (F g₁ rfl).toRingHom = RingHom.ker (F g₂ hg.symm).toRingHom :=
    congrArg PrimeSpectrum.asIdeal
      ((hK.1.2 : Subsingleton (PrimeSpectrum (TensorProduct A C K))).elim p
        ⟨_, RingHom.ker_isPrime (F g₂ hg.symm).toRingHom⟩)
  obtain ⟨σ₁, hσ₁⟩ := exists_comp_eq_of_ker_eq (F g₁ rfl).toRingHom p.asIdeal rfl
  obtain ⟨σ₂, hσ₂⟩ := exists_comp_eq_of_ker_eq (F g₂ hg.symm).toRingHom p.asIdeal hker.symm
  let ι : K →+* p.asIdeal.ResidueField :=
    (algebraMap (TensorProduct A C K) p.asIdeal.ResidueField).comp
      (Algebra.TensorProduct.includeRight :
        K →ₐ[A] TensorProduct A C K).toRingHom
  let : Algebra K p.asIdeal.ResidueField := ι.toAlgebra
  have hpi : IsPurelyInseparable K p.asIdeal.ResidueField := hK.2 p
  have hσ : σ₁.comp ι = σ₂.comp ι := by
    ext x
    let y := (Algebra.TensorProduct.includeRight : K →ₐ[A] TensorProduct A C K) x
    calc
      σ₁ (ι x) = F g₁ rfl y := by simpa [y, ι] using RingHom.congr_fun hσ₁ y
      _ = F g₂ hg.symm y := by simp [y, F]
      _ = σ₂ (ι x) := by simpa [y, ι] using (RingHom.congr_fun hσ₂ y).symm
  have hF : (F g₁ rfl).toRingHom = (F g₂ hg.symm).toRingHom := by
    rw [← hσ₁, ← hσ₂,
      IsPurelyInseparable.injective_comp_algebraMap K p.asIdeal.ResidueField K hσ]
  ext c
  simpa [F] using RingHom.congr_fun hF
    ((Algebra.TensorProduct.includeLeft : C →ₐ[A] TensorProduct A C K) c)

private lemma injective_comp_specMap_of_fiber
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (h : ∀ (k : Type u) [Field k] (g : A →+* k),
      letI : Algebra A k := g.toAlgebra
      (Nonempty (PrimeSpectrum (TensorProduct A C k)) ∧
        Subsingleton (PrimeSpectrum (TensorProduct A C k))) ∧
        ∀ p : PrimeSpectrum (TensorProduct A C k),
          let ι : k →+* p.asIdeal.ResidueField :=
            (algebraMap (TensorProduct A C k) p.asIdeal.ResidueField).comp
              (Algebra.TensorProduct.includeRight :
                k →ₐ[A] TensorProduct A C k).toRingHom
          letI : Algebra k p.asIdeal.ResidueField := ι.toAlgebra
          IsPurelyInseparable k p.asIdeal.ResidueField)
    (K : Type u) [Field K] :
    Function.Injective (fun g : Spec (.of K) ⟶ Spec (.of C) ↦
      g ≫ Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) := by
  intro g₁ g₂ heq
  have hfpre : Spec.preimage (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) =
      CommRingCat.ofHom (algebraMap A C) := by
    simp
  have hpre := congrArg Spec.preimage heq
  rw [Spec.preimage_comp, Spec.preimage_comp, hfpre] at hpre
  have hring : ((Spec.preimage g₁).hom).comp (algebraMap A C) =
      ((Spec.preimage g₂).hom).comp (algebraMap A C) := by
    simpa [CommRingCat.ofHom] using
      congrArg (fun φ : CommRingCat.of A ⟶ CommRingCat.of K => φ.hom) hpre
  exact Spec.homEquiv.injective (CommRingCat.hom_ext (eq_of_fiber_condition h hring))

/-- If every fibre of `PrimeSpectrum.comap (algebraMap A C)` is nonempty, then this map is
surjective. -/
public lemma comap_algebraMap_surjective_of_nonempty_fiber
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (h : ∀ p : PrimeSpectrum A,
      Nonempty (PrimeSpectrum (TensorProduct A C p.asIdeal.ResidueField))) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A C)) := fun p ↦ by
  have : Nontrivial (TensorProduct A C p.asIdeal.ResidueField) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp (h p)
  exact (PrimeSpectrum.nontrivial_iff_mem_rangeComap p).mp
    (Algebra.TensorProduct.comm A C _).injective.nontrivial

/-- If an integral ring map has a unique point in every field-valued fibre and that
point's residue field is purely inseparable over the field, then the induced map on spectra
is a universal homeomorphism. -/
public lemma
    universalHomeomorphism_specMap_of_integral_of_fiber_unique_prime_isPurelyInseparable
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] [Algebra.IsIntegral A C]
    (h : ∀ (k : Type u) [Field k] (g : A →+* k),
      letI : Algebra A k := g.toAlgebra
      (Nonempty (PrimeSpectrum (TensorProduct A C k)) ∧
        Subsingleton (PrimeSpectrum (TensorProduct A C k))) ∧
        ∀ p : PrimeSpectrum (TensorProduct A C k),
          let ι : k →+* p.asIdeal.ResidueField :=
            (algebraMap (TensorProduct A C k) p.asIdeal.ResidueField).comp
              (Algebra.TensorProduct.includeRight :
                k →ₐ[A] TensorProduct A C k).toRingHom
          letI : Algebra k p.asIdeal.ResidueField := ι.toAlgebra
          IsPurelyInseparable k p.asIdeal.ResidueField) :
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) := by
  let f := Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op
  have hsurjComap :=
    comap_algebraMap_surjective_of_nonempty_fiber (A := A) (C := C) fun p ↦ by
      have hk := h p.asIdeal.ResidueField (algebraMap A p.asIdeal.ResidueField)
      rw [toAlgebra_algebraMap] at hk
      exact hk.1.1
  have hsurj : Surjective f := ⟨fun p ↦ by
    let p' : PrimeSpectrum A :=
      (primeSpectrumOrderIsoSpec A).symm (OrderDual.toDual p)
    obtain ⟨q, hq⟩ := hsurjComap p'
    let q' : Spec (.of C) :=
      OrderDual.ofDual (primeSpectrumOrderIsoSpec C q)
    refine ⟨q', ?_⟩
    have hmap : f q' = OrderDual.ofDual
        (primeSpectrumOrderIsoSpec A (PrimeSpectrum.comap (algebraMap A C) q)) := by
      simp only [Scheme.Spec_obj, Scheme.Spec_map, Quiver.Hom.unop_op, primeSpectrumOrderIsoSpec,
        Spec.map_apply, ConcreteCategory.hom_ofHom, f, q']
      rfl
    have hp' : OrderDual.ofDual (primeSpectrumOrderIsoSpec A p') = p := by
      simp [p', primeSpectrumOrderIsoSpec]
    rw [hmap, hq, hp']⟩
  exact (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mpr
    ⟨IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance),
      ((tfae_universallyInjective f).out 1 2).mpr (injective_comp_specMap_of_fiber h), hsurj⟩

private lemma residueFieldMap_bijective_of_fiber
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (q : PrimeSpectrum C)
    (h : ∀ r : PrimeSpectrum
        (TensorProduct A C (q.comap (algebraMap A C)).asIdeal.ResidueField),
      Function.Bijective
        ((algebraMap _ r.asIdeal.ResidueField).comp
          (Algebra.TensorProduct.includeRight :
            (q.comap (algebraMap A C)).asIdeal.ResidueField →ₐ[A]
              TensorProduct A C (q.comap (algebraMap A C)).asIdeal.ResidueField).toRingHom)) :
    Function.Bijective (Ideal.ResidueField.map
      (q.comap (algebraMap A C)).asIdeal q.asIdeal (algebraMap A C) rfl) := by
  let p := q.comap (algebraMap A C)
  let φ : p.asIdeal.ResidueField →ₐ[A] q.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId A C) rfl
  let f : TensorProduct A C p.asIdeal.ResidueField →ₐ[A] q.asIdeal.ResidueField :=
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A C q.asIdeal.ResidueField)
      φ (fun _ _ ↦ Commute.all _ _)
  let r : PrimeSpectrum (TensorProduct A C p.asIdeal.ResidueField) :=
    ⟨RingHom.ker f.toRingHom, RingHom.ker_isPrime _⟩
  have : r.asIdeal.IsPrime := r.isPrime
  have hq : q.asIdeal = r.asIdeal.comap
      (Algebra.TensorProduct.includeLeft : C →ₐ[A]
        TensorProduct A C p.asIdeal.ResidueField).toRingHom := by
    ext c
    simp [r, f]
  let ψ := Ideal.ResidueField.map q.asIdeal r.asIdeal
    (Algebra.TensorProduct.includeLeft : C →ₐ[A]
      TensorProduct A C p.asIdeal.ResidueField).toRingHom hq
  have square : ψ.comp φ.toRingHom =
      (algebraMap _ r.asIdeal.ResidueField).comp
        (Algebra.TensorProduct.includeRight : p.asIdeal.ResidueField →ₐ[A]
          TensorProduct A C p.asIdeal.ResidueField).toRingHom := by
    apply Ideal.ResidueField.ringHom_ext
    ext a
    simp [ψ, φ, IsScalarTower.algebraMap_apply A C q.asIdeal.ResidueField]
  refine ⟨RingHom.injective _, fun y ↦ ?_⟩
  obtain ⟨a, ha⟩ := (h r).surjective (ψ y)
  exact ⟨a, ψ.injective ((RingHom.congr_fun square a).trans ha)⟩

/-- If every prime in every field-valued fibre has residue field canonically isomorphic to
the base field, then the original map induces isomorphisms on all residue fields. -/
public lemma isIso_residueFieldMap_specMap_of_fiber_residueField_bijective
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (h : ∀ (k : Type u) [Field k] (g : A →+* k),
      letI : Algebra A k := g.toAlgebra
      ∀ p : PrimeSpectrum (TensorProduct A C k),
        let ι : k →+* p.asIdeal.ResidueField :=
          (algebraMap (TensorProduct A C k) p.asIdeal.ResidueField).comp
            (Algebra.TensorProduct.includeRight :
              k →ₐ[A] TensorProduct A C k).toRingHom
        Function.Bijective ι) :
    ∀ x : Spec (.of C),
      IsIso ((Scheme.Spec.map
        (CommRingCat.ofHom (algebraMap A C)).op).residueFieldMap x) := by
  intro x
  apply specResidueFieldMap_isIso_of_idealResidueFieldMap
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  apply residueFieldMap_bijective_of_fiber
  have hx := h (x.comap (algebraMap A C)).asIdeal.ResidueField
    (algebraMap A (x.comap (algebraMap A C)).asIdeal.ResidueField)
  rw [toAlgebra_algebraMap] at hx
  convert! hx

end AlgebraicGeometry

end
