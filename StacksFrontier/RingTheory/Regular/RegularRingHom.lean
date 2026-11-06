module

public import Mathlib
public import Mathlib.Algebra.Category.AlgCat.FilteredColimits
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Smooth.Basic
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.RingTheory.CompleteIntersection.FieldGlobalToRingMap
public import StacksFrontier.RingTheory.Etale.IndEtaleFibres
public import StacksFrontier.RingTheory.Flat.DirectLimit
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterion
public import StacksFrontier.RingTheory.FormallySmooth.Field
public import StacksFrontier.RingTheory.GeometricallyReduced.TFAE
public import StacksFrontier.RingTheory.GeometricallyRegular.BaseFieldExtension
public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.GeometricallyRegular.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.GeometricallyRegular.FieldExtension
public import StacksFrontier.RingTheory.GeometricallyRegular.Reduced
public import StacksFrontier.RingTheory.RegularLocalRing.Colimit
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.Serre.FlatAscent
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing

@[expose] public section

/-!
# Regular ring maps

A ring homomorphism `f : R →+* S` is *regular* if it is flat and, for every prime `p` of `R`, the
fibre `p.Fiber S = p.ResidueField ⊗[R] S` is Noetherian and geometrically regular over
`p.ResidueField`. Regularity is local on the target, is preserved by finite type base change and
by composition when the composite has Noetherian fibres, descends along flat maps surjective on
prime spectra, holds for a filtered colimit of smooth algebras with Noetherian fibres, and for a
field extension is equivalent to separability.

## Main definitions

* `IsRegularRingHom`: the predicate that a ring homomorphism is regular.

## Main results

* `isRegularRingHom_algebraMap_iff`: regularity of an algebra map in terms of the fibres formed
  with the ambient algebra structure.
* `Algebra.IsGeometricallyRegular.isNoetherianRing`: a geometrically regular algebra over a field
  is Noetherian.
* `Algebra.IsGeometricallyRegular.of_isLocalization`: geometric regularity of a `k`-algebra
  passes to every localization of it.
* `IsRegularRingHom.comp_ringEquiv`: a regular ring map composed with a ring equivalence is
  regular.
* `isRegularRingHom_tfae_localizations`: for a ring homomorphism with Noetherian target,
  regularity can be checked on the induced maps of local rings at corresponding prime ideals, or
  only at maximal ideals of the target and their contractions.
* `isRegularRingHom_baseChange`: regularity is preserved by finite type base change.
* `isRegularRingHom_comp`: the composite of two regular ring homomorphisms is regular when the
  composite has Noetherian fibres.
* `isRegularRingHom_of_filteredColimit_smooth`: a filtered colimit of smooth algebras with
  Noetherian fibres is regular over the base.
* `isRegularRingHom_iff_isSeparableExtension`: a field extension is regular if and only if it is
  separable.
* `isRegularRingHom_of_comp_of_flat_of_surjectiveOnSpec`: regularity descends through a flat map
  that is surjective on prime spectra.
* `Stacks.RegularRingHom.isRegularRingHom_of_ringEquiv`: regularity of a structure morphism
  transports along compatible ring isomorphisms of the base and of the algebra.

## References

* [Stacks Project, Tag 07BZ](https://stacks.math.columbia.edu/tag/07BZ)
* [Stacks Project, Tag 07C0](https://stacks.math.columbia.edu/tag/07C0)
* [Stacks Project, Tag 07C1](https://stacks.math.columbia.edu/tag/07C1)
* [Stacks Project, Tag 07QI](https://stacks.math.columbia.edu/tag/07QI)
* [Stacks Project, Tag 07EP](https://stacks.math.columbia.edu/tag/07EP)
* [Stacks Project, Tag 07EQ](https://stacks.math.columbia.edu/tag/07EQ)
* [Stacks Project, Tag 07NT](https://stacks.math.columbia.edu/tag/07NT)
-/

/-! ### Regular ring homomorphisms -/

section

@[expose] public section

universe u v

/-- A ring homomorphism is *regular* if it is flat and, over every prime of its source, its
residue-field fibre is Noetherian and geometrically regular over that residue field. -/
@[stacks 07BZ]
public def IsRegularRingHom {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  f.Flat ∧ ∀ (p : Ideal R) [p.IsPrime],
    IsNoetherianRing (p.Fiber S) ∧
      Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber S)

/-- For an algebra map, regularity can be checked using the fibres formed with the ambient
algebra structure. -/
public theorem isRegularRingHom_algebraMap_iff
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] :
    IsRegularRingHom (algebraMap R S) ↔
      (algebraMap R S).Flat ∧ ∀ (p : Ideal R) [p.IsPrime],
        IsNoetherianRing (p.Fiber S) ∧
          Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber S) := by
  unfold IsRegularRingHom
  rw [toAlgebra_algebraMap]

/-- A ring homomorphism equal to the algebra map is regular if and only if it is flat and its
fibres, formed with the ambient algebra structure, are Noetherian and geometrically regular. -/
public theorem isRegularRingHom_iff_of_eq_algebraMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (f : R →+* S) (hf : f = algebraMap R S) :
    IsRegularRingHom f ↔ f.Flat ∧ ∀ (p : Ideal R) [p.IsPrime],
      IsNoetherianRing (p.Fiber S) ∧
        Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber S) := by
  subst f
  exact isRegularRingHom_algebraMap_iff

end

/-! ### Regularity is local on the target -/

section

section

public section

universe u v w

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A geometrically regular algebra over a field is Noetherian. -/
theorem Algebra.IsGeometricallyRegular.isNoetherianRing {k B : Type*} [Field k] [CommRing B]
    [Algebra k B] (h : Algebra.IsGeometricallyRegular k B) : IsNoetherianRing B :=
  isNoetherianRing_of_surjective _ _ (Algebra.TensorProduct.lid k B).toRingEquiv.toRingHom
    (Algebra.TensorProduct.lid k B).surjective

/-- A regular ring map stays regular after composition with a ring equivalence. -/
theorem IsRegularRingHom.comp_ringEquiv {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S} (hf : IsRegularRingHom f) (e : S ≃+* T) :
    IsRegularRingHom (e.toRingHom.comp f) := by
  let : Algebra R S := f.toAlgebra
  let : Algebra R T := (e.toRingHom.comp f).toAlgebra
  refine ⟨RingHom.Flat.comp hf.1 (RingHom.Flat.of_bijective e.bijective), fun p _ ↦ ?_⟩
  let ea : S ≃ₐ[R] T := AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl
  let ep : p.Fiber S ≃ₐ[p.ResidueField] p.Fiber T :=
    Algebra.TensorProduct.congr (AlgEquiv.refl) ea
  have hreg : Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber T) := by
    refine ⟨fun K _ _ _ ↦ ?_⟩
    have := (hf.2 p).2.isRegularRing_tensorProduct K
    exact IsRegularRing.of_ringEquiv (R := K ⊗[p.ResidueField] p.Fiber S)
      (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[p.ResidueField] K) ep).toRingEquiv
  exact ⟨hreg.isNoetherianRing, hreg⟩

/-- The algebra structure on the base change `K ⊗[R] B` over `K ⊗[R] A` induced by `A → B`. -/
private abbrev tensorMapAlgebra (R A B K : Type*) [CommRing R] [CommRing A] [CommRing B]
    [CommRing K] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra R K] :
    Algebra (K ⊗[R] A) (K ⊗[R] B) :=
  (Algebra.TensorProduct.map (AlgHom.id R K) (IsScalarTower.toAlgHom R A B)).toRingHom.toAlgebra

/-- The base change `K ⊗[R] B` of a localization `B` of `A` is a localization of `K ⊗[R] A`. -/
private theorem isLocalization_tensorMapAlgebra {R A B K : Type*} [CommRing R] [CommRing A]
    [CommRing B] [CommRing K] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra R K] (M : Submonoid A) [IsLocalization M B] :
    let := tensorMapAlgebra R A B K
    IsScalarTower K (K ⊗[R] A) (K ⊗[R] B) ∧
      IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := R) (A := K))) (K ⊗[R] B) := by
  let := tensorMapAlgebra R A B K
  have : IsScalarTower K (K ⊗[R] A) (K ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by simp [RingHom.algebraMap_toAlgebra]
  exact ⟨this, IsLocalization.tensorProduct_tensorProduct_right R K M B
    (by ext x; simp [RingHom.algebraMap_toAlgebra])⟩

/-- Base change of a Noetherian algebra along an essentially finite type algebra is Noetherian. -/
private theorem isNoetherianRing_tensorProduct_of_essFiniteType {R K A : Type*} [CommRing R]
    [CommRing K] [CommRing A] [Algebra R K] [Algebra R A] [Algebra.EssFiniteType R K]
    [IsNoetherianRing A] : IsNoetherianRing (K ⊗[R] A) := by
  have : Algebra.EssFiniteType A (A ⊗[R] K) := Algebra.EssFiniteType.baseChange R K A
  have : IsNoetherianRing (A ⊗[R] K) := Algebra.EssFiniteType.isNoetherianRing A (A ⊗[R] K)
  exact isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm R A K).toRingEquiv

/-- Localizing at a prime disjoint from `M` is the same as localizing the localization `B` at the
extended prime. -/
private noncomputable def atPrimeAlgEquivMap {A : Type*} [CommRing A] (M : Submonoid A)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B] (q : Ideal A) [q.IsPrime]
    [(q.map (algebraMap A B)).IsPrime] (hdis : Disjoint (M : Set A) (q : Set A)) :
    Localization.AtPrime q ≃ₐ[A] Localization.AtPrime (q.map (algebraMap A B)) :=
  have hQ : (q.map (algebraMap A B)).comap (algebraMap A B) = q :=
    IsLocalization.under_map_of_isPrime_disjoint M B inferInstance hdis
  have : IsLocalization.AtPrime (Localization.AtPrime (q.map (algebraMap A B))) q := by
    simpa only [hQ] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
        (T := Localization.AtPrime (q.map (algebraMap A B))) (q.map (algebraMap A B)))
  IsLocalization.algEquiv q.primeCompl _ _

/-- If `A` is a geometrically regular `k`-algebra and the `k`-algebra `B` is a localization of
`A`, then `B` is geometrically regular over `k`. -/
theorem Algebra.IsGeometricallyRegular.of_isLocalization {k : Type u} {A : Type v}
    {B : Type w} [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [Algebra A B] [IsScalarTower k A B] [Algebra.IsGeometricallyRegular k A]
    (M : Submonoid A) [IsLocalization M B] :
    Algebra.IsGeometricallyRegular k B := by
  refine ⟨fun K _ _ _ ↦ ?_⟩
  let := tensorMapAlgebra k A B K
  have := (isLocalization_tensorMapAlgebra (R := k) (B := B) (K := K) M).2
  exact _root_.IsRegularRing.of_isLocalization
    (M.map (Algebra.TensorProduct.includeRight (R := k) (A := K))) (K ⊗[k] B)

/-- Geometric regularity over a field is invariant under an algebra equivalence. -/
theorem Algebra.IsGeometricallyRegular.of_algEquiv {k : Type u} {A : Type v}
    {B : Type w} [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [Algebra.IsGeometricallyRegular k A] (e : A ≃ₐ[k] B) :
    Algebra.IsGeometricallyRegular k B :=
  ⟨fun K _ _ _ ↦ _root_.IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[k] K) e).toRingEquiv⟩

/-- Regularity of a field base change can be checked after localizing the original algebra at
every prime. -/
private theorem regular_tensor_of_regular_tensor_localizations {k : Type u} {A : Type v}
    [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A]
    (K : Type u) [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
    (h : ∀ (q : Ideal A) [q.IsPrime],
      IsRegularRing (K ⊗[k] Localization.AtPrime q)) :
    IsRegularRing (K ⊗[k] A) := by
  have : IsNoetherianRing (K ⊗[k] A) := isNoetherianRing_tensorProduct_of_essFiniteType
  rw [isRegularRing_iff]
  intro P hP
  let q : Ideal A := P.comap (Algebra.TensorProduct.includeRight (R := k) (A := K)).toRingHom
  let := tensorMapAlgebra k A (Localization.AtPrime q) K
  let M : Submonoid (K ⊗[k] A) :=
    q.primeCompl.map (Algebra.TensorProduct.includeRight (R := k) (A := K))
  have : IsLocalization M (K ⊗[k] Localization.AtPrime q) :=
    (isLocalization_tensorMapAlgebra (R := k) (B := Localization.AtPrime q) (K := K) q.primeCompl).2
  have hdis : Disjoint (M : Set (K ⊗[k] A)) (P : Set (K ⊗[k] A)) :=
    Set.disjoint_left.mpr <| by rintro _ ⟨a, ha, rfl⟩ hxP; exact ha hxP
  let Q : Ideal (K ⊗[k] Localization.AtPrime q) :=
    P.map (algebraMap (K ⊗[k] A) (K ⊗[k] Localization.AtPrime q))
  have : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P inferInstance hdis
  have : IsRegularRing (K ⊗[k] Localization.AtPrime q) := h q
  have : IsRegularLocalRing (Localization.AtPrime Q) :=
    IsRegularRing.isRegularLocalRing_localization Q
  exact IsRegularLocalRing.of_ringEquiv
    (R := Localization.AtPrime Q) (R' := Localization.AtPrime P)
    (atPrimeAlgEquivMap M _ P hdis).symm.toRingEquiv

/-- Geometric regularity of a Noetherian algebra can be tested at all its prime local rings. -/
private theorem geometricallyRegular_of_localizations {k : Type u} {A : Type v}
    [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A]
    (h : ∀ (q : Ideal A) [q.IsPrime],
      Algebra.IsGeometricallyRegular k (Localization.AtPrime q)) :
    Algebra.IsGeometricallyRegular k A := by
  exact ⟨fun K _ _ _ ↦ regular_tensor_of_regular_tensor_localizations K fun q _ ↦
    (h q).isRegularRing_tensorProduct K⟩

/-- Localizing the right factor of a geometrically regular tensor product preserves geometric
regularity over the field on the left. -/
private theorem geometricallyRegular_tensor_of_isLocalization
    {R : Type u} {S : Type v} {S' : Type w} {k : Type u}
    [CommRing R] [CommRing S] [CommRing S'] [Field k]
    [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    [Algebra R k] [Algebra.IsGeometricallyRegular k (k ⊗[R] S)]
    (M : Submonoid S) [IsLocalization M S'] :
    Algebra.IsGeometricallyRegular k (k ⊗[R] S') := by
  let := tensorMapAlgebra R S S' k
  obtain ⟨_, _⟩ := isLocalization_tensorMapAlgebra (R := R) (B := S') (K := k) M
  exact Algebra.IsGeometricallyRegular.of_isLocalization
    (k := k) (A := k ⊗[R] S) (B := k ⊗[R] S')
    (M.map (Algebra.TensorProduct.includeRight (R := R) (A := k)))

/-- Tensoring two algebras over a localization gives the same result as tensoring them over the
original ring, as algebras over the first tensor factor. -/
private noncomputable def tensorOverLocalizationAlgEquiv
    {R R' k : Type u} {T : Type v} [CommRing R] [CommRing R'] [CommRing T]
    [Field k] [Algebra R R'] [Algebra R k] [Algebra R T] [Algebra R' k]
    [Algebra R' T] [IsScalarTower R R' k] [IsScalarTower R R' T]
    (M : Submonoid R) [IsLocalization M R'] :
    (k ⊗[R'] T) ≃ₐ[k] (k ⊗[R] T) := by
  letI : TensorProduct.CompatibleSMul R R' k T :=
    IsLocalization.tensorProduct_compatibleSMul M R' k T
  exact Algebra.TensorProduct.equivOfCompatibleSMul R R' k k T

/-- For a localization `R'` of `R`, geometric regularity of a fibre over a prime `r` of `R'` can be
computed from the fibre of `R` over the contraction of `r`. -/
private theorem geometricallyRegular_fiber_iff_residueField_tensor
    {R R' : Type u} {T : Type v} [CommRing R] [CommRing R'] [CommRing T]
    [Algebra R R'] [Algebra R T] (M : Submonoid R) [IsLocalization M R'] (r : Ideal R')
    [r.IsPrime] :
    Algebra.IsGeometricallyRegular (r.comap (algebraMap R R')).ResidueField
        ((r.comap (algebraMap R R')).Fiber T) ↔
      Algebra.IsGeometricallyRegular r.ResidueField (r.ResidueField ⊗[R] T) := by
  let p : Ideal R := r.comap (algebraMap R R')
  have hbij : Function.Bijective (algebraMap p.ResidueField r.ResidueField) :=
    (RingHom.surjectiveOnStalks_of_isLocalization M R').residueFieldMap_bijective p r rfl
  let e : p.ResidueField ≃ₐ[p.ResidueField] r.ResidueField :=
    AlgEquiv.ofBijective (Algebra.ofId _ _) hbij
  let eF : p.Fiber T ≃ₐ[p.ResidueField] (r.ResidueField ⊗[R] T) :=
    Algebra.TensorProduct.congr e (AlgEquiv.refl : T ≃ₐ[R] T)
  have : Algebra.IsSeparable p.ResidueField r.ResidueField := AlgEquiv.Algebra.isSeparable e
  exact Iff.trans ⟨fun _ ↦ Algebra.IsGeometricallyRegular.of_algEquiv eF,
    fun _ ↦ Algebra.IsGeometricallyRegular.of_algEquiv eF.symm⟩
    (Algebra.isGeometricallyRegular_iff_tower_top_of_isSeparable p.ResidueField r.ResidueField _)

/-- Geometric regularity of fibres is preserved by localizing both the source and target. -/
private theorem geometricallyRegular_fiber_of_localizations
    {R R' : Type u} {S S' : Type v}
    [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R R'] [Algebra R S] [Algebra R S'] [Algebra R' S'] [Algebra S S']
    [IsScalarTower R R' S'] [IsScalarTower R S S']
    (M : Submonoid R) [IsLocalization M R']
    (N : Submonoid S) [IsLocalization N S']
    (r : Ideal R') [r.IsPrime]
    (h : Algebra.IsGeometricallyRegular
      (r.comap (algebraMap R R')).ResidueField
      ((r.comap (algebraMap R R')).Fiber S)) :
    Algebra.IsGeometricallyRegular r.ResidueField (r.Fiber S') := by
  have : Algebra.IsGeometricallyRegular r.ResidueField (r.ResidueField ⊗[R] S) :=
    (geometricallyRegular_fiber_iff_residueField_tensor M r).mp h
  have : Algebra.IsGeometricallyRegular r.ResidueField
      (r.ResidueField ⊗[R] S') :=
    geometricallyRegular_tensor_of_isLocalization N
  exact Algebra.IsGeometricallyRegular.of_algEquiv
    (tensorOverLocalizationAlgEquiv (R := R) (R' := R')
      (k := r.ResidueField) (T := S') M).symm

/-- For a localization of the source, the fibres at corresponding primes agree up to an
isomorphism of residue fields. -/
private theorem geometricallyRegular_fiber_of_localized_source
    {R R' : Type u} {T : Type v} [CommRing R] [CommRing R'] [CommRing T]
    [Algebra R R'] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T]
    (M : Submonoid R) [IsLocalization M R'] (r : Ideal R') [r.IsPrime]
    (h : Algebra.IsGeometricallyRegular r.ResidueField (r.Fiber T)) :
    Algebra.IsGeometricallyRegular
      (r.comap (algebraMap R R')).ResidueField
      ((r.comap (algebraMap R R')).Fiber T) := by
  refine (geometricallyRegular_fiber_iff_residueField_tensor M r).mpr ?_
  exact Algebra.IsGeometricallyRegular.of_algEquiv
    (tensorOverLocalizationAlgEquiv (R := R) (R' := R') (k := r.ResidueField) (T := T) M)

/-- If a localization is geometrically regular, then so is the local ring at any prime that
survives the localization. -/
private theorem geometricallyRegular_atPrime_of_isLocalization
    {k : Type u} {A : Type v} {B : Type w}
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [Algebra A B] [IsScalarTower k A B]
    (M : Submonoid A) [IsLocalization M B]
    [Algebra.IsGeometricallyRegular k B]
    (q : Ideal A) [q.IsPrime] (hdis : Disjoint (M : Set A) (q : Set A)) :
    Algebra.IsGeometricallyRegular k (Localization.AtPrime q) := by
  let Q : Ideal B := q.map (algebraMap A B)
  have : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M B q inferInstance hdis
  have : Algebra.IsGeometricallyRegular k (Localization.AtPrime Q) :=
    Algebra.IsGeometricallyRegular.of_isLocalization Q.primeCompl
  exact Algebra.IsGeometricallyRegular.of_algEquiv
    ((atPrimeAlgEquivMap M B q hdis).restrictScalars k).symm

/-- Geometric regularity of a fibre is unchanged when its indexing prime is rewritten. -/
private theorem geometricallyRegular_fiber_congr
    {R : Type u} {T : Type v} [CommRing R] [CommRing T] [Algebra R T]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (hpq : p = q)
    (h : Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber T)) :
    Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber T) := by
  cases hpq
  exact h

/-- Geometric regularity of every local homomorphism over maximal target ideals implies geometric
regularity of each fibre of the original homomorphism. -/
private theorem geometricallyRegular_fiber_of_maximal_localizations
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsNoetherianRing S]
    (f : R →+* S)
    (h : ∀ (m : Ideal R) [m.IsPrime] (m' : Ideal S) [m'.IsMaximal]
      (hm : m = m'.comap f),
      IsRegularRingHom (Localization.localRingHom m m' f hm))
    (p : Ideal R) [p.IsPrime] :
    letI : Algebra R S := f.toAlgebra
    Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber S) := by
  let : Algebra R S := f.toAlgebra
  let : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  have : IsNoetherianRing (p.Fiber S) := p.isNoetherianRing_fiber S
  refine geometricallyRegular_of_localizations fun Q _ ↦ ?_
  let q : Ideal S := Q.comap
    (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField)).toRingHom
  have : q.LiesOver p :=
    Ideal.LiesOver.of_eq_comap p
      (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField)) rfl
  have hqp : p = q.comap f := q.over_def p
  obtain ⟨m', hm', hqm'⟩ := Ideal.exists_le_maximal q
    (inferInstance : q.IsPrime).ne_top
  have : m'.IsPrime := hm'.isPrime
  let m : Ideal R := m'.comap f
  have hpm : p ≤ m := by rw [hqp]; exact Ideal.comap_mono hqm'
  let r : Ideal (Localization.AtPrime m) := p.map (algebraMap R (Localization.AtPrime m))
  have : r.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime m hpm
  have hr : r.comap (algebraMap R (Localization.AtPrime m)) = p :=
    Ideal.under_map_of_isLocalizationAtPrime m hpm
  let g : Localization.AtPrime m →+* Localization.AtPrime m' :=
    Localization.localRingHom m m' f rfl
  let : Algebra (Localization.AtPrime m) (Localization.AtPrime m') := g.toAlgebra
  have : IsScalarTower R (Localization.AtPrime m) (Localization.AtPrime m') :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (Localization.localRingHom_to_map m m' f rfl x).symm
  have hreg : IsRegularRingHom g := h m m' rfl
  have hgeo : Algebra.IsGeometricallyRegular r.ResidueField
      (r.Fiber (Localization.AtPrime m')) := (hreg.2 r).2
  have : Algebra.IsGeometricallyRegular p.ResidueField
      (p.Fiber (Localization.AtPrime m')) :=
    geometricallyRegular_fiber_congr hr
      (geometricallyRegular_fiber_of_localized_source m.primeCompl r hgeo)
  let := tensorMapAlgebra R S (Localization.AtPrime m') p.ResidueField
  let M : Submonoid (p.Fiber S) :=
    m'.primeCompl.map
      (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField))
  obtain ⟨_, _⟩ := isLocalization_tensorMapAlgebra (R := R) (B := Localization.AtPrime m')
    (K := p.ResidueField) m'.primeCompl
  have hdis : Disjoint (M : Set (p.Fiber S)) (Q : Set (p.Fiber S)) :=
    Set.disjoint_left.mpr <| by rintro _ ⟨s, hs, rfl⟩ hxQ; exact hs (hqm' hxQ)
  exact geometricallyRegular_atPrime_of_isLocalization
    (k := p.ResidueField) (A := p.Fiber S)
    (B := p.Fiber (Localization.AtPrime m')) M Q hdis

/-- A regular homomorphism stays regular after localizing at a corresponding pair of prime
ideals. -/
private theorem regular_localRingHom_of_regular
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) [IsNoetherianRing S]
    (h : IsRegularRingHom f)
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap f) :
    IsRegularRingHom (Localization.localRingHom p q f hpq) := by
  let : Algebra R S := f.toAlgebra
  let g : Localization.AtPrime p →+* Localization.AtPrime q :=
    Localization.localRingHom p q f hpq
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) := g.toAlgebra
  have : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (Localization.localRingHom_to_map p q f hpq x).symm
  exact ⟨RingHom.Flat.localRingHom h.1 q p hpq, fun r _ ↦ ⟨r.isNoetherianRing_fiber _,
    geometricallyRegular_fiber_of_localizations p.primeCompl q.primeCompl r (h.2 _).2⟩⟩

/-- Flatness can be checked on the local homomorphisms at maximal ideals of the target. -/
private theorem flat_of_flat_localRingHom_maximal
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S)
    (h : ∀ (m : Ideal R) [m.IsPrime] (m' : Ideal S) [m'.IsMaximal]
      (hm : m = m'.comap f),
      (Localization.localRingHom m m' f hm).Flat) : f.Flat := by
  let : Algebra R S := f.toAlgebra
  show Module.Flat R S
  apply Module.flat_of_isLocalized_maximal S S
    (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Algebra.linearMap S (Localization.AtPrime P))
  intro P hP
  have : P.IsPrime := hP.isPrime
  let p : Ideal R := P.comap f
  let g : Localization.AtPrime p →+* Localization.AtPrime P :=
    Localization.localRingHom p P f rfl
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime P) := g.toAlgebra
  have : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime P) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (Localization.localRingHom_to_map p P f rfl x).symm
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime P) := h p P rfl
  exact Module.Flat.trans R (Localization.AtPrime p) (Localization.AtPrime P)

/-- A ring homomorphism with Noetherian target is regular if and only if all its induced maps on
local rings at corresponding prime ideals are regular, and if and only if this holds for
maximal ideals of the target and their contractions. -/
@[stacks 07C0]
public theorem isRegularRingHom_tfae_localizations
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) [IsNoetherianRing S] :
    List.TFAE [
      IsRegularRingHom f,
      ∀ (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (h : p = q.comap f),
        IsRegularRingHom (Localization.localRingHom p q f h),
      ∀ (m : Ideal R) [m.IsPrime] (m' : Ideal S) [m'.IsMaximal]
        (h : m = m'.comap f),
        IsRegularRingHom (Localization.localRingHom m m' f h)] :=
  by
    tfae_have 1 → 2 := fun h p _ q _ hpq ↦ regular_localRingHom_of_regular f h p q hpq
    tfae_have 2 → 3 := fun h m _ m' _ hmeq ↦ h m m' hmeq
    tfae_have 3 → 1 := by
      intro h
      let : Algebra R S := f.toAlgebra
      exact ⟨flat_of_flat_localRingHom_maximal f fun m _ m' _ hmeq ↦ (h m m' hmeq).1,
        fun p _ ↦ ⟨p.isNoetherianRing_fiber _,
          geometricallyRegular_fiber_of_maximal_localizations f h p⟩⟩
    tfae_finish

end

end

end

/-! ### Base change -/

section

section

@[expose] public section

open Algebra
open scoped TensorProduct

universe u v w

/-- The fibre of `C ⊗[B] D` at a prime `P` of an essentially finite type `B`-algebra `D` is
geometrically regular if the fibre of `C` at the contraction of `P` is. -/
private theorem isGeometricallyRegular_fiber_tensorProduct_right
    {B : Type u} {C : Type v} {D : Type w}
    [CommRing B] [CommRing C] [CommRing D] [Algebra B C] [Algebra B D]
    [Algebra.EssFiniteType B D] (P : Ideal D) [P.IsPrime]
    (hg : Algebra.IsGeometricallyRegular (P.comap (algebraMap B D)).ResidueField
      ((P.comap (algebraMap B D)).Fiber C)) :
    let : Algebra D (C ⊗[B] D) := Algebra.TensorProduct.rightAlgebra
    Algebra.IsGeometricallyRegular P.ResidueField (P.Fiber (C ⊗[B] D)) := by
  let : Algebra D (C ⊗[B] D) := Algebra.TensorProduct.rightAlgebra
  let q : Ideal B := P.comap (algebraMap B D)
  have : q.IsPrime := Ideal.IsPrime.comap _
  have : P.LiesOver q := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver q P
  let : Algebra q.ResidueField (q.Fiber C) := Algebra.TensorProduct.leftAlgebra
  let e₁ := Algebra.TensorProduct.congr
    (AlgEquiv.refl : P.ResidueField ≃ₐ[D] P.ResidueField)
    (Algebra.TensorProduct.commRight B D C).symm
  let e₂ := (Algebra.TensorProduct.cancelBaseChange B D P.ResidueField
    P.ResidueField C).trans
    (Algebra.TensorProduct.cancelBaseChange B q.ResidueField P.ResidueField
      P.ResidueField C).symm
  let e : P.Fiber (C ⊗[B] D) ≃ₐ[P.ResidueField]
      P.ResidueField ⊗[q.ResidueField] q.Fiber C :=
    AlgEquiv.ofRingEquiv (f := e₁.toRingEquiv.trans e₂.toRingEquiv) (fun x ↦ by
      show e₂ (e₁ (algebraMap P.ResidueField _ x)) = algebraMap P.ResidueField _ x
      rw [show e₁ (algebraMap P.ResidueField _ x) =
          algebraMap P.ResidueField _ x by
        simp [e₁, Algebra.TensorProduct.algebraMap_apply]]
      exact e₂.commutes x)
  have : Algebra.EssFiniteType q.ResidueField P.ResidueField := by
    have : Algebra.EssFiniteType B P.ResidueField := .comp B D _
    exact .of_comp B _ _
  let : CommRing (P.ResidueField ⊗[q.ResidueField] q.Fiber C) :=
    Algebra.TensorProduct.instCommRing
  have : Algebra.IsGeometricallyRegular P.ResidueField
      (P.ResidueField ⊗[q.ResidueField] q.Fiber C) :=
    Stacks.GeometricallyRegular.SeparableBase.isGeometricallyRegular_tensorProduct
      q.ResidueField P.ResidueField (q.Fiber C)
  exact Algebra.IsGeometricallyRegular.of_algEquiv e.symm

set_option backward.isDefEq.respectTransparency false in
/-- A finite-type base change of a regular ring homomorphism is regular. -/
@[stacks 07C1]
public theorem isRegularRingHom_baseChange
    {R : Type u} {Λ : Type v} {R' : Type w}
    [CommRing R] [CommRing Λ] [CommRing R'] [Algebra R Λ] [Algebra R R']
    [Algebra.FiniteType R R']
    (h : IsRegularRingHom (algebraMap R Λ)) :
    IsRegularRingHom
      (Algebra.TensorProduct.includeRight (R := R) (A := Λ) (B := R')).toRingHom := by
  let : Algebra R' (Λ ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  rw [isRegularRingHom_algebraMap_iff] at h
  rw [isRegularRingHom_iff_of_eq_algebraMap _ (by rfl)]
  constructor
  · have : Module.Flat R Λ := RingHom.flat_algebraMap_iff.mp h.1
    show Module.Flat R' (Λ ⊗[R] R')
    exact Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.commRight R R' Λ).symm.toLinearEquiv
  · intro p' _
    have hg := isGeometricallyRegular_fiber_tensorProduct_right (B := R) (C := Λ) p'
      (h.2 (p'.comap (algebraMap R R'))).2
    exact ⟨hg.isNoetherianRing, hg⟩

end

end

end

/-! ### Composition -/

section

section

set_option maxRecDepth 4096

open scoped TensorProduct

universe u v w

set_option backward.isDefEq.respectTransparency false in
/-- Regularity ascends along a flat map with regular fibres and Noetherian target. -/
private theorem isRegularRing_of_flat_of_fibers
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing S] [Module.Flat R S] [IsRegularRing R]
    (hfib : ∀ (p : Ideal R) [p.IsPrime], IsRegularRing (p.Fiber S)) :
    IsRegularRing S := by
  rw [isRegularRing_iff]
  intro q hq
  let p : Ideal R := q.comap (algebraMap R S)
  have : p.IsPrime := Ideal.IsPrime.comap _
  have : q.LiesOver p := ⟨rfl⟩
  have hq_mem : q ∈ p.primesOver S := ⟨hq, inferInstance⟩
  let P : PrimeSpectrum (p.Fiber S) :=
    PrimeSpectrum.primesOverOrderIsoFiber R S p ⟨q, hq_mem⟩
  let e : (S ⊗[R] IsLocalRing.ResidueField (Localization.AtPrime p)) ≃ₐ[R] p.Fiber S :=
    Algebra.TensorProduct.comm R S (IsLocalRing.ResidueField (Localization.AtPrime p))
  let q' : Ideal (S ⊗[R] IsLocalRing.ResidueField (Localization.AtPrime p)) :=
    P.asIdeal.comap e.toRingHom
  have : q'.IsPrime := Ideal.IsPrime.comap _
  have hrq : q'.comap
      (algebraMap S (S ⊗[R] IsLocalRing.ResidueField (Localization.AtPrime p))) = q := by
    have hP : P.asIdeal.comap (Algebra.TensorProduct.includeRight
        (R := R) (A := IsLocalRing.ResidueField (Localization.AtPrime p)) (B := S)) = q := by
      have hsymm := (PrimeSpectrum.primesOverOrderIsoFiber R S p).symm_apply_apply ⟨q, hq_mem⟩
      have h1 := PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply_coe
        (R := R) (S := S) (p := p) P
      apply SetLike.ext'
      rw [Ideal.coe_comap, ← h1]
      exact congrArg (fun (x : p.primesOver S) ↦ ((x : Ideal S) : Set S)) hsymm
    have hcomp : e.toRingHom.comp
        (algebraMap S (S ⊗[R] IsLocalRing.ResidueField (Localization.AtPrime p))) =
        (Algebra.TensorProduct.includeRight
          (R := R) (A := IsLocalRing.ResidueField (Localization.AtPrime p))
          (B := S)).toRingHom := by
      ext s
      simp [e]
    show (P.asIdeal.comap e.toRingHom).comap _ = q
    rwa [Ideal.comap_comap, hcomp]
  have : IsRegularRing (p.Fiber S) := hfib p
  have : IsRegularRing (S ⊗[R] IsLocalRing.ResidueField (Localization.AtPrime p)) :=
    IsRegularRing.of_ringEquiv e.symm.toRingEquiv
  have : IsRegularRing (Localization.AtPrime q') :=
    IsRegularRing.of_isLocalization q'.primeCompl (Localization.AtPrime q')
  have hclosed : IsRegularLocalRing
      ((Localization.AtPrime q) ⧸
        Ideal.map (algebraMap S (Localization.AtPrime q))
          (Ideal.map (algebraMap R S) p)) :=
    IsRegularLocalRing.of_ringEquiv (fibreAlgEquivAux₂ p q' q hrq).toRingEquiv
  let algRpSq : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q (algebraMap R S) rfl).toAlgebra
  have hAM : algebraMap (Localization.AtPrime p) (Localization.AtPrime q) =
      Localization.localRingHom p q (algebraMap R S) rfl := rfl
  have hST : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ by
      rw [hAM, Localization.localRingHom_to_map, ← IsScalarTower.algebraMap_apply])
  have hFlat : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    inferInstance
  have hLocalHom : IsLocalHom
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    rw [hAM]
    infer_instance
  have hST2 : IsScalarTower R S (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have hidealeq :
      Ideal.map (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
          (IsLocalRing.maximalIdeal (Localization.AtPrime p)) =
        Ideal.map (algebraMap S (Localization.AtPrime q))
          (Ideal.map (algebraMap R S) p) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq R (Localization.AtPrime p) (Localization.AtPrime q),
      IsScalarTower.algebraMap_eq R S (Localization.AtPrime q), ← Ideal.map_map]
  rw [← hidealeq] at hclosed
  exact isRegularLocalRing_of_flat_of_regular_closedFibre
    (Localization.AtPrime p) (Localization.AtPrime q)
    (_root_.IsRegularRing.isRegularLocalRing_of_isLocalization p _) hclosed

/-- Fibres of an essentially finite-type base change of a regular map are regular. -/
private theorem isRegularRing_fiber_baseChange_of_essFiniteType
    {B : Type u} {C : Type v} {D : Type*}
    [CommRing B] [CommRing C] [CommRing D] [Algebra B C] [Algebra B D]
    [Algebra.EssFiniteType B D]
    (hg : IsRegularRingHom (algebraMap B C))
    (P : Ideal D) [P.IsPrime] :
    let : Algebra D (C ⊗[B] D) := Algebra.TensorProduct.rightAlgebra
    IsRegularRing (P.Fiber (C ⊗[B] D)) := by
  let : Algebra D (C ⊗[B] D) := Algebra.TensorProduct.rightAlgebra
  have := isGeometricallyRegular_fiber_tensorProduct_right (B := B) (C := C) P
    ((isRegularRingHom_algebraMap_iff.mp hg).2 _).2
  exact IsRegularRing.of_ringEquiv
    ((Algebra.TensorProduct.lid P.ResidueField (P.Fiber (C ⊗[B] D))).toRingEquiv)

/-- Base change of a regular map to an essentially finite-type regular algebra has regular
target when that target is Noetherian. -/
private theorem isRegularRing_baseChange_of_essFiniteType
    {B : Type u} {C : Type v} {D : Type*}
    [CommRing B] [CommRing C] [CommRing D] [Algebra B C] [Algebra B D]
    [Algebra.EssFiniteType B D] [IsRegularRing D] [IsNoetherianRing (C ⊗[B] D)]
    (hg : IsRegularRingHom (algebraMap B C)) :
    IsRegularRing (C ⊗[B] D) := by
  let : Algebra D (C ⊗[B] D) := Algebra.TensorProduct.rightAlgebra
  have : Module.Flat B C := RingHom.flat_algebraMap_iff.mp hg.1
  have : Module.Flat D (C ⊗[B] D) :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.commRight B D C).symm.toLinearEquiv
  exact isRegularRing_of_flat_of_fibers D (C ⊗[B] D)
    (isRegularRing_fiber_baseChange_of_essFiniteType hg)

set_option backward.isDefEq.respectTransparency false in
/-- The composite of two regular ring homomorphisms is regular if all its fibres are
Noetherian. -/
@[stacks 07QI]
public theorem isRegularRingHom_comp
    {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hf : IsRegularRingHom f) (hg : IsRegularRingHom g)
    (hNoetherian : ∀ (p : Ideal A) [p.IsPrime],
      let : Algebra A C := (g.comp f).toAlgebra
      IsNoetherianRing (p.Fiber C)) :
    IsRegularRingHom (g.comp f) := by
  let : Algebra A B := f.toAlgebra
  let : Algebra B C := g.toAlgebra
  let : Algebra A C := (g.comp f).toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  refine ⟨RingHom.Flat.comp hf.1 hg.1, fun p _ ↦ ⟨hNoetherian p, ?_⟩⟩
  let : Algebra B (p.Fiber B) := Algebra.TensorProduct.rightAlgebra
  have : Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber B) := (hf.2 p).2
  refine ⟨fun K _ _ _ ↦ ?_⟩
  let : CommRing (K ⊗[p.ResidueField] p.Fiber B) :=
    Algebra.TensorProduct.instCommRing
  let : Algebra (p.Fiber B) (K ⊗[p.ResidueField] p.Fiber B) :=
    Algebra.TensorProduct.rightAlgebra
  let hBD : B →+* (K ⊗[p.ResidueField] p.Fiber B) :=
    ((Algebra.TensorProduct.includeRight
        (R := p.ResidueField) (A := K) (B := p.Fiber B)).toRingHom.comp
      (algebraMap B (p.Fiber B)))
  let : Algebra B (K ⊗[p.ResidueField] p.Fiber B) := hBD.toAlgebra
  have : IsRegularRing (K ⊗[p.ResidueField] p.Fiber B) :=
    Algebra.IsGeometricallyRegular.isRegularRing_tensorProduct K
  have : Algebra.EssFiniteType B (p.Fiber B) :=
    (Algebra.EssFiniteType.iff_of_algEquiv
      (Algebra.TensorProduct.commRight A B p.ResidueField)).mp inferInstance
  have : Algebra.EssFiniteType (p.Fiber B)
      (K ⊗[p.ResidueField] p.Fiber B) := by
    let : CommRing (p.Fiber B ⊗[p.ResidueField] K) :=
      Algebra.TensorProduct.instCommRing
    apply (Algebra.EssFiniteType.iff_of_algEquiv
      (Algebra.TensorProduct.commRight p.ResidueField (p.Fiber B) K)).mp
    infer_instance
  have : IsScalarTower B (p.Fiber B) (K ⊗[p.ResidueField] p.Fiber B) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : Algebra.EssFiniteType B (K ⊗[p.ResidueField] p.Fiber B) := .comp B (p.Fiber B) _
  let : Algebra A K :=
    ((algebraMap p.ResidueField K).comp (algebraMap A p.ResidueField)).toAlgebra
  have : IsScalarTower A p.ResidueField K :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let eDB : (K ⊗[p.ResidueField] p.Fiber B) ≃ₐ[B] B ⊗[A] K :=
    AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.cancelBaseChange A p.ResidueField K K B).toRingEquiv.trans
        (Algebra.TensorProduct.comm A K B).toRingEquiv) (fun b ↦ by
          show (Algebra.TensorProduct.comm A K B)
            ((Algebra.TensorProduct.cancelBaseChange A p.ResidueField K K B)
              (1 ⊗ₜ[p.ResidueField] (1 ⊗ₜ[A] b))) = b ⊗ₜ[A] 1
          simp)
  let e : (C ⊗[B] (K ⊗[p.ResidueField] p.Fiber B)) ≃+*
      K ⊗[p.ResidueField] p.Fiber C :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[B] C) eDB).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange A B C C K).toRingEquiv.trans
        ((Algebra.TensorProduct.comm A C K).toRingEquiv.trans
          (Algebra.TensorProduct.cancelBaseChange A p.ResidueField K K C).symm.toRingEquiv))
  have : IsNoetherianRing (p.Fiber C) := hNoetherian p
  have : IsNoetherianRing (K ⊗[p.ResidueField] p.Fiber C) :=
    isNoetherianRing_tensorProduct_of_essFiniteType
  have : IsNoetherianRing (C ⊗[B] (K ⊗[p.ResidueField] p.Fiber B)) :=
    isNoetherianRing_of_ringEquiv _ e.symm
  have : IsRegularRing (C ⊗[B] (K ⊗[p.ResidueField] p.Fiber B)) :=
    isRegularRing_baseChange_of_essFiniteType hg
  exact IsRegularRing.of_ringEquiv e

end

end

/-! ### Filtered colimits of smooth algebras -/

section

section

set_option maxRecDepth 4096

open CategoryTheory Limits
open scoped TensorProduct

universe u v w

private lemma app_algebraMap_eq {R : Type u} [CommRing R] {J : Type w}
    [Category J] [IsFiltered J] {F : J ⥤ CommAlgCat.{v} R}
    (s : Cocone (F ⋙ forget₂ (CommAlgCat.{v} R) CommRingCat.{v})) (j k : J) (r : R) :
    (s.ι.app j).hom (algebraMap R (F.obj j) r) =
      (s.ι.app k).hom (algebraMap R (F.obj k) r) := by
  have h : ∀ (i : J) (l : i ⟶ IsFiltered.max j k) (x : F.obj i), (s.ι.app i).hom x =
      (s.ι.app (IsFiltered.max j k)).hom ((F.map l).hom x) := by
    intro i l x
    conv_lhs => rw [← s.w l]
    simp
  rw [h j (IsFiltered.leftToMax j k), h k (IsFiltered.rightToMax j k)]
  simp

private noncomputable def isColimitForget₂
    {R : Type u} [CommRing R] {J : Type w} [Category J] [IsFiltered J]
    {A : CommAlgCat.{v} R} (pres : ColimitPresentation J A) :
    IsColimit ((forget₂ (CommAlgCat.{v} R) CommRingCat.{v}).mapCocone pres.cocone) := by
  classical
  have key : ∀ s : Cocone (pres.diag ⋙ forget₂ (CommAlgCat.{v} R) CommRingCat.{v}),
      ∃! l : ((forget₂ (CommAlgCat.{v} R) CommRingCat.{v}).mapCocone pres.cocone).pt ⟶ s.pt,
        ∀ j, ((forget₂ (CommAlgCat.{v} R) CommRingCat.{v}).mapCocone pres.cocone).ι.app j ≫ l =
          s.ι.app j := by
    intro s
    have hw : ∀ {j k : J} (f : j ⟶ k) (x : pres.diag.obj j),
        (s.ι.app k).hom ((pres.diag.map f).hom x) = (s.ι.app j).hom x := by
      intro j k f x
      conv_rhs => rw [← s.w f]
      simp
    obtain ⟨j₀⟩ : Nonempty J := IsFiltered.nonempty
    let _algs : Algebra R s.pt :=
      ((s.ι.app j₀).hom.comp (algebraMap R (pres.diag.obj j₀))).toAlgebra
    have hmap : ∀ (j : J) (r : R),
        (s.ι.app j).hom (algebraMap R (pres.diag.obj j) r) = algebraMap R s.pt r := fun j r ↦ by
      simpa [RingHom.algebraMap_toAlgebra] using app_algebraMap_eq s j j₀ r
    let t : Cocone pres.diag :=
      { pt := CommAlgCat.of R s.pt
        ι := { app := fun j ↦ CommAlgCat.ofHom { __ := (s.ι.app j).hom, commutes' := hmap j }
               naturality := fun j k f ↦ by ext x; simpa using hw f x } }
    refine ⟨(forget₂ (CommAlgCat.{v} R) CommRingCat.{v}).map (pres.isColimit.desc t), ?_, ?_⟩
    · intro j
      simp only [Functor.mapCocone_ι_app, ← Functor.map_comp]
      rw [pres.isColimit.fac t j]
      rfl
    · intro m hm
      have hmj : ∀ (j : J) (x : pres.diag.obj j),
          m.hom ((pres.ι.app j).hom x) = (s.ι.app j).hom x := by
        intro j x
        simpa [Functor.mapCocone_ι_app] using
          DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (hm j)) x
      have hcomm : ∀ r : R, m.hom (algebraMap R A r) = algebraMap R s.pt r := fun r ↦ by
        have h1 : (algebraMap R A) r =
            (pres.ι.app j₀).hom (algebraMap R (pres.diag.obj j₀) r) :=
          ((pres.ι.app j₀).hom.commutes r).symm
        rw [h1]
        conv_rhs => rw [← hmap j₀ r]
        exact hmj j₀ _
      have huniq := pres.isColimit.uniq t
        (CommAlgCat.ofHom { __ := m.hom, commutes' := hcomm }) fun j ↦ by
          ext x; exact hmj j x
      exact congrArg (forget₂ (CommAlgCat.{v} R) CommRingCat.{v}).map huniq
  choose l hl hl' using key
  exact ⟨l, hl, hl'⟩

private theorem flat_of_isColimit
    {R : Type u} [CommRing R]
    {J : Type w} [Preorder J] [IsDirectedOrder J] [Nonempty J]
    (F : J ⥤ CommAlgCat.{v} R) (c : Cocone F) (hc : IsColimit c)
    [PreservesColimit (F ⋙ forget₂ (CommAlgCat.{v} R) CommRingCat.{v})
      (forget CommRingCat.{v})]
    (hflat : ∀ j, Module.Flat R (F.obj j)) : Module.Flat R c.pt := by
  classical
  let G : J → Type v := fun j ↦ F.obj j
  let f : (i j : J) → i ≤ j → G i →ₗ[R] G j :=
    fun i j h ↦ (F.map (homOfLE h)).hom.toLinearMap
  have : DirectedSystem G (fun i j h ↦ f i j h) := by
    constructor
    · intro i x
      show (F.map (homOfLE (le_refl i))).hom x = x
      simp
    · intro i j k hij hjk x
      show (F.map (homOfLE hjk)).hom ((F.map (homOfLE hij)).hom x) =
        (F.map (homOfLE (hij.trans hjk))).hom x
      rw [← CommAlgCat.comp_apply, ← F.map_comp]
      rfl
  let ψ : Module.DirectLimit G f →ₗ[R] c.pt :=
    Module.DirectLimit.lift R J G f (fun i ↦ (c.ι.app i).hom.toLinearMap)
      fun i j hij x ↦ congr($(c.w (homOfLE hij)) x)
  have hforget : IsColimit ((forget CommRingCat.{v}).mapCocone
      ((forget₂ (CommAlgCat.{v} R) CommRingCat.{v}).mapCocone c)) :=
    isColimitOfPreserves _ (isColimitForget₂
      ({ diag := F, ι := c.ι, isColimit := hc } : ColimitPresentation J c.pt))
  have hsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨i, y, hy⟩ := Types.jointly_surjective_of_isColimit hforget x
    refine ⟨Module.DirectLimit.of R J G f i y, ?_⟩
    simpa [ψ] using hy
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨i, y, rfl⟩ := Module.DirectLimit.exists_of x
    have hy : (c.ι.app i).hom y = (c.ι.app i).hom 0 := by simpa [ψ] using hx
    obtain ⟨j, a, hab⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hforget y 0).mp hy
    have hz : (F.map a).hom y = 0 := by simpa using hab
    have ha : a = homOfLE (leOfHom a) := Subsingleton.elim _ _
    calc
      Module.DirectLimit.of R J G f i y =
          Module.DirectLimit.of R J G f j (f i j (leOfHom a) y) :=
        (Module.DirectLimit.of_f (R := R) (f := f) (hij := leOfHom a)).symm
      _ = 0 := by
        show Module.DirectLimit.of R J G f j
          ((F.map (homOfLE (leOfHom a))).hom y) = 0
        rw [← ha, hz, map_zero]
  have : Module.Flat R (Module.DirectLimit G f) :=
    directLimit_flat f hflat
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm

/-- A colimit computed on elements has its universal property for algebras in any universe. -/
private theorem exists_algHom_of_isColimit
    {R : Type u} [CommRing R] {J : Type w} [Category J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{v} R} {c : Cocone F}
    (hc : IsColimit ((forget (CommAlgCat.{v} R)).mapCocone c))
    {S : Type*} [CommRing S] [Algebra R S]
    (g : ∀ j, F.obj j →ₐ[R] S)
    (hg : ∀ {i j} (a : i ⟶ j) x, g j ((F.map a).hom x) = g i x) :
    ∃ l : c.pt →ₐ[R] S, ∀ j x, l ((c.ι.app j).hom x) = g j x := by
  classical
  choose i x hx using Types.jointly_surjective_of_isColimit hc
  let l : c.pt → S := fun y ↦ g (i y) (x y)
  have hl (j : J) (y : F.obj j) : l ((c.ι.app j).hom y) = g j y := by
    obtain ⟨k, a, b, hab⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hc).mp
      (hx ((c.ι.app j).hom y))
    exact (hg a _).symm.trans ((congrArg (g k) hab).trans (hg b _))
  have hpair (a b : c.pt) : ∃ (j : J) (a' b' : F.obj j),
      (c.ι.app j).hom a' = a ∧ (c.ι.app j).hom b' = b := by
    let k := IsFiltered.max (i a) (i b)
    refine ⟨k, (F.map (IsFiltered.leftToMax (i a) (i b))).hom (x a),
      (F.map (IsFiltered.rightToMax (i a) (i b))).hom (x b), ?_, ?_⟩
    · exact (congr($(c.w (IsFiltered.leftToMax (i a) (i b))) (x a))).trans (hx a)
    · exact (congr($(c.w (IsFiltered.rightToMax (i a) (i b))) (x b))).trans (hx b)
  let j₀ : J := Classical.choice IsFiltered.nonempty
  refine ⟨{ toFun := l
            map_zero' := by simpa using hl j₀ 0
            map_one' := by simpa using hl j₀ 1
            map_add' := ?_
            map_mul' := ?_
            commutes' := fun r ↦ by
              simpa using hl j₀ (algebraMap R (F.obj j₀) r) }, hl⟩
  · intro a b
    obtain ⟨j, a, b, rfl, rfl⟩ := hpair a b
    rw [← map_mul, hl, hl, hl, map_mul]
  · intro a b
    obtain ⟨j, a, b, rfl, rfl⟩ := hpair a b
    rw [← map_add, hl, hl, hl, map_add]

section BaseChange

variable {R : Type u} [CommRing R] {J : Type w} [Category J]
  (K : Type*) [CommRing K] [Algebra R K]

private noncomputable abbrev baseChangeFunctor : CommAlgCat.{v} R ⥤ CommAlgCat K where
  obj A := CommAlgCat.of K (K ⊗[R] A)
  map f := CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id K K) f.hom)
  map_id A := by ext : 1; ext x; simp
  map_comp f g := by ext : 1; ext x; simp

private noncomputable def isColimit_baseChange [IsFiltered J]
    {F : J ⥤ CommAlgCat.{v} R} {c : Cocone F}
    (hc : IsColimit ((forget (CommAlgCat.{v} R)).mapCocone c)) :
    IsColimit ((baseChangeFunctor K).mapCocone c) := by
  classical
  have hdesc (s : Cocone (F ⋙ baseChangeFunctor K)) :
      ∃ l : K ⊗[R] c.pt →ₐ[K] s.pt,
        ∀ j, l.comp (Algebra.TensorProduct.map (AlgHom.id K K) (c.ι.app j).hom) =
          (s.ι.app j).hom := by
    let : Algebra R s.pt := ((algebraMap K s.pt).comp (algebraMap R K)).toAlgebra
    have : IsScalarTower R K s.pt := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let g : ∀ j, F.obj j →ₐ[R] s.pt := fun j ↦ (AlgHom.liftEquiv R K _ _).symm (s.ι.app j).hom
    obtain ⟨l, hl⟩ := exists_algHom_of_isColimit hc g fun a x ↦ congr($(s.w a) (1 ⊗ₜ[R] x))
    refine ⟨AlgHom.liftEquiv R K _ _ l, fun j ↦ ?_⟩
    apply Algebra.TensorProduct.ext_ring
    ext x
    simpa [g] using hl j x
  choose l hl using hdesc
  refine ⟨fun s ↦ CommAlgCat.ofHom (l s), fun s j ↦ CommAlgCat.hom_ext (hl s j), ?_⟩
  · intro s m hm
    apply CommAlgCat.hom_ext
    let : Algebra R s.pt := ((algebraMap K s.pt).comp (algebraMap R K)).toAlgebra
    have : IsScalarTower R K s.pt := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    apply Algebra.TensorProduct.ext_ring
    ext x
    obtain ⟨j, y, rfl⟩ := Types.jointly_surjective_of_isColimit hc x
    exact congr($(hm j) (1 ⊗ₜ[R] y)).trans (AlgHom.congr_fun (hl s j) (1 ⊗ₜ[R] y)).symm

end BaseChange

section Localization

variable {J : Type w} [Category J]
  {F : J ⥤ CommRingCat.{v}} (c : Cocone F) (q : Ideal c.pt) [q.IsPrime]

private abbrev prime (j : J) : Ideal (F.obj j) := q.comap (c.ι.app j).hom

omit [q.IsPrime] in
private lemma prime_map {i j : J} (a : i ⟶ j) :
    prime c q i = (prime c q j).comap (F.map a).hom := by
  ext x
  show (c.ι.app i).hom x ∈ q ↔ (c.ι.app j).hom ((F.map a).hom x) ∈ q
  rw [← CommRingCat.comp_apply, c.w a]

private noncomputable abbrev localDiagram : J ⥤ CommRingCat.{v} where
  obj j := CommRingCat.of (Localization.AtPrime (prime c q j))
  map a := CommRingCat.ofHom (Localization.localRingHom _ _ (F.map a).hom (prime_map c q a))
  map_id j := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (prime c q j).primeCompl
    apply RingHom.ext
    intro x
    simp
  map_comp := fun {X Y Z} a b ↦ by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (prime c q X).primeCompl
    apply RingHom.ext
    intro x
    simp [Localization.localRingHom_to_map]

private noncomputable abbrev localCocone : Cocone (localDiagram c q) where
  pt := CommRingCat.of (Localization.AtPrime q)
  ι := { app := fun j ↦ CommRingCat.ofHom
          (Localization.localRingHom _ _ (c.ι.app j).hom rfl)
         naturality := fun i j a ↦ by
           apply CommRingCat.hom_ext
           apply IsLocalization.ringHom_ext (prime c q i).primeCompl
           apply RingHom.ext
           intro x
           change Localization.localRingHom _ _ (c.ι.app j).hom rfl
             (Localization.localRingHom _ _ (F.map a).hom (prime_map c q a)
               (algebraMap (F.obj i) (Localization.AtPrime (prime c q i)) x)) =
             Localization.localRingHom _ _ (c.ι.app i).hom rfl
               (algebraMap (F.obj i) (Localization.AtPrime (prime c q i)) x)
           simp only [Localization.localRingHom_to_map]
           exact congrArg (algebraMap c.pt (Localization.AtPrime q))
             (congr($(c.w a) x)) }

private noncomputable abbrev unlocalizedCocone (s : Cocone (localDiagram c q)) : Cocone F where
  pt := s.pt
  ι := { app := fun j ↦ CommRingCat.ofHom
          ((s.ι.app j).hom.comp (algebraMap (F.obj j) (Localization.AtPrime (prime c q j))))
         naturality := fun i j a ↦ by
           apply CommRingCat.hom_ext
           apply RingHom.ext
           intro x
           have h := congr($(s.w a) (algebraMap (F.obj i)
             (Localization.AtPrime (prime c q i)) x))
           change (s.ι.app j).hom
             ((Localization.localRingHom _ _ (F.map a).hom (prime_map c q a))
               (algebraMap (F.obj i) (Localization.AtPrime (prime c q i)) x)) = _ at h
           rw [Localization.localRingHom_to_map] at h
           exact h }

private lemma baseDesc_units (hc : IsColimit c)
    [PreservesColimit F (forget CommRingCat.{v})] (s : Cocone (localDiagram c q)) :
    ∀ y : q.primeCompl, IsUnit ((hc.desc (unlocalizedCocone c q s)).hom y) := by
  intro y
  have hforget := isColimitOfPreserves (forget CommRingCat.{v}) hc
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit hforget (y : c.pt)
  have hxq : x ∉ prime c q j := fun h ↦ y.property (hx ▸ h)
  have hu : IsUnit (algebraMap (F.obj j) (Localization.AtPrime (prime c q j)) x) :=
    IsLocalization.map_units (Localization.AtPrime (prime c q j))
      (⟨x, hxq⟩ : (prime c q j).primeCompl)
  have hfac := congr($(hc.fac (unlocalizedCocone c q s) j) x)
  have hfac' : (hc.desc (unlocalizedCocone c q s)).hom y = (s.ι.app j).hom
      (algebraMap (F.obj j) (Localization.AtPrime (prime c q j)) x) := by
    rw [← hx]
    exact hfac
  exact hfac'.symm ▸ hu.map (s.ι.app j).hom

private noncomputable abbrev localDesc (hc : IsColimit c)
    [PreservesColimit F (forget CommRingCat.{v})] (s : Cocone (localDiagram c q)) :
    (localCocone c q).pt ⟶ s.pt :=
  CommRingCat.ofHom (IsLocalization.lift (baseDesc_units c q hc s))

private noncomputable def isColimit_localCocone (hc : IsColimit c)
    [PreservesColimit F (forget CommRingCat.{v})] : IsColimit (localCocone c q) := by
  classical
  refine ⟨localDesc c q hc, ?_, ?_⟩
  · intro s j
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (prime c q j).primeCompl
    apply RingHom.ext
    intro x
    change (localDesc c q hc s).hom
      ((Localization.localRingHom _ _ (c.ι.app j).hom rfl)
        (algebraMap (F.obj j) (Localization.AtPrime (prime c q j)) x)) = _
    rw [Localization.localRingHom_to_map]
    change IsLocalization.lift (baseDesc_units c q hc s)
      (algebraMap c.pt (Localization.AtPrime q) ((c.ι.app j).hom x)) = _
    rw [IsLocalization.lift_eq]
    exact congr($(hc.fac (unlocalizedCocone c q s) j) x)
  · intro s m hm
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext q.primeCompl
    have H : CommRingCat.ofHom (m.hom.comp (algebraMap c.pt (Localization.AtPrime q))) =
        hc.desc (unlocalizedCocone c q s) := by
      apply hc.hom_ext
      intro j
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      simpa [localCocone, localDiagram, Localization.localRingHom_to_map] using
        congr($(hm j) (algebraMap (F.obj j) (Localization.AtPrime (prime c q j)) x))
    calc
      m.hom.comp (algebraMap c.pt (Localization.AtPrime q)) =
          (hc.desc (unlocalizedCocone c q s)).hom := congrArg CommRingCat.Hom.hom H
      _ = (localDesc c q hc s).hom.comp (algebraMap c.pt (Localization.AtPrime q)) :=
        RingHom.ext fun x ↦ (IsLocalization.lift_eq (baseDesc_units c q hc s) x).symm

end Localization

/-- Forgetting a small directed system of rings preserves its colimit. -/
private theorem preservesColimitsOfShape_forget
    {J : Type w} [Preorder J] [IsDirectedOrder J] [Nonempty J] [Small.{v} J] :
    PreservesColimitsOfShape J (forget CommRingCat.{v}) := by
  classical
  let : Preorder (Shrink.{v} J) := Preorder.lift (equivShrink J).symm
  let e : Shrink.{v} J ≃o J :=
    { toEquiv := (equivShrink J).symm, map_rel_iff' := Iff.rfl }
  have : IsDirectedOrder (Shrink.{v} J) := ⟨fun a b ↦ by
    obtain ⟨k, ha, hb⟩ := exists_ge_ge (e a) (e b)
    exact ⟨e.symm k, by simpa using e.symm.map_rel_iff.mpr ha,
      by simpa using e.symm.map_rel_iff.mpr hb⟩⟩
  have : Nonempty (Shrink.{v} J) := ⟨equivShrink J (Classical.arbitrary J)⟩
  exact preservesColimitsOfShape_of_equiv e.equivalence (forget CommRingCat.{v})

/-- Regularity of all the local rings passes to a Noetherian directed colimit. -/
private theorem isRegularRing_of_isColimit
    {J : Type w} [Preorder J] [IsDirectedOrder J] [Nonempty J] [Small.{v} J]
    {F : J ⥤ CommRingCat.{v}} {c : Cocone F} (hc : IsColimit c)
    [IsNoetherianRing c.pt] (hreg : ∀ j, IsRegularRing (F.obj j)) :
    IsRegularRing c.pt := by
  have : PreservesColimitsOfShape J (forget CommRingCat.{v}) := preservesColimitsOfShape_forget
  refine ⟨fun q _ ↦ ?_⟩
  apply CommRingCat.isRegularLocalRing_pt_of_forall_isRegularLocalRing_of_forall_isLocalHom
    (F := localDiagram c q) (c := localCocone c q)
  · intro j
    have := hreg j
    exact IsRegularRing.isRegularLocalRing_localization (prime c q j)
  · intro i j a
    show IsLocalHom (Localization.localRingHom _ _ (F.map a).hom (prime_map c q a))
    infer_instance
  · exact isColimit_localCocone c q hc

private theorem geometricallyRegular_fibre_of_isColimit
    {R : Type u} [CommRing R]
    {J : Type w} [Preorder J] [IsDirectedOrder J] [Nonempty J] [Small.{max u v} J]
    (F : J ⥤ CommAlgCat.{v} R) (c : Cocone F) (hc : IsColimit c)
    [PreservesColimit (F ⋙ forget₂ (CommAlgCat.{v} R) CommRingCat.{v})
      (forget CommRingCat.{v})]
    (hsm : ∀ j, Algebra.Smooth R (F.obj j))
    (p : Ideal R) [p.IsPrime] [IsNoetherianRing (p.Fiber c.pt)] :
    Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber c.pt) := by
  have hforget : IsColimit ((forget (CommAlgCat.{v} R)).mapCocone c) :=
    isColimitOfPreserves (forget CommRingCat.{v}) (isColimitForget₂
      ({ diag := F, ι := c.ι, isColimit := hc } : ColimitPresentation J c.pt))
  refine ⟨fun K _ _ _ ↦ ?_⟩
  let : Algebra R K := ((algebraMap p.ResidueField K).comp
    (algebraMap R p.ResidueField)).toAlgebra
  have : IsScalarTower R p.ResidueField K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let e := Algebra.TensorProduct.cancelBaseChange R p.ResidueField K K c.pt
  have : IsNoetherianRing (K ⊗[p.ResidueField] p.Fiber c.pt) :=
    isNoetherianRing_tensorProduct_of_essFiniteType
  have : IsNoetherianRing (K ⊗[R] c.pt) := isNoetherianRing_of_ringEquiv _ e.toRingEquiv
  let d := (baseChangeFunctor K).mapCocone c
  have hd := isColimit_baseChange K hforget
  have hd' : IsColimit ((forget₂ (CommAlgCat K) CommRingCat).mapCocone d) :=
    isColimitForget₂ ({ diag := F ⋙ baseChangeFunctor K, ι := d.ι, isColimit := hd } :
      ColimitPresentation J d.pt)
  have : IsNoetherianRing ((forget₂ (CommAlgCat K) CommRingCat).mapCocone d).pt :=
    ‹IsNoetherianRing (K ⊗[R] c.pt)›
  have : IsRegularRing (K ⊗[R] c.pt) := isRegularRing_of_isColimit hd' (fun j ↦ by
    show IsRegularRing (K ⊗[R] F.obj j)
    have := hsm j
    have : Algebra.Smooth K (K ⊗[R] F.obj j) := inferInstance
    have : IsNoetherianRing (K ⊗[R] F.obj j) :=
      Algebra.FiniteType.isNoetherianRing K (K ⊗[R] F.obj j)
    exact ⟨fun q _ ↦ (Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing
      (k := K) (S := K ⊗[R] F.obj j) ⟨q, ‹q.IsPrime›⟩
      (Localization.AtPrime q)).2 inferInstance⟩)
  exact IsRegularRing.of_ringEquiv e.symm.toRingEquiv

/-- The colimit of a small nonempty directed system of smooth `R`-algebras, computed on
underlying sets, whose residue-field fibres are Noetherian is regular over `R`. -/
@[stacks 07EP]
public theorem isRegularRingHom_of_filteredColimit_smooth
    {R : Type u} [CommRing R]
    {J : Type w} [Preorder J] [IsDirectedOrder J] [Nonempty J] [Small.{max u v} J]
    (F : J ⥤ CommAlgCat.{v} R) (c : Cocone F) (hc : IsColimit c)
    [PreservesColimit (F ⋙ forget₂ (CommAlgCat.{v} R) CommRingCat.{v})
      (forget CommRingCat.{v})]
    (hsm : ∀ j, Algebra.Smooth R (F.obj j))
    (hnoeth : ∀ (p : Ideal R) [p.IsPrime], IsNoetherianRing (p.Fiber c.pt)) :
    IsRegularRingHom (algebraMap R c.pt) := by
  rw [isRegularRingHom_algebraMap_iff]
  refine ⟨?_, fun p _ ↦ ⟨hnoeth p, ?_⟩⟩
  · exact RingHom.flat_algebraMap_iff.mpr (flat_of_isColimit F c hc fun j ↦ by
      have := hsm j
      infer_instance)
  · have := hnoeth p
    exact geometricallyRegular_fibre_of_isColimit F c hc hsm p

end

end

/-! ### Field extensions -/

section

section

open scoped TensorProduct
open Stacks.GeometricallyReduced.Separability

universe u v

private theorem isRegularRing_of_isField (R : Type*) [CommRing R] (h : IsField R) :
    IsRegularRing R := by
  let := h.toField
  infer_instance

private theorem isGeometricallyRegular_of_isSeparableExtension
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparableExtension k K] : Algebra.IsGeometricallyRegular k K := by
  exact ⟨fun L _ _ _ ↦
    (Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
      k K).2 (fun k' _ _ _ _ ↦ isRegularRing_of_isField _
        (isField_tensorProduct_of_isSeparableExtension_of_isPurelyInseparable k K k')) L⟩

private noncomputable def fiberAlgEquivOfField (k K : Type*) [Field k] [Field K] [Algebra k K]
    (p : Ideal k) [p.IsPrime] : p.Fiber K ≃ₐ[k] K :=
  (Algebra.TensorProduct.congr (p.algEquivResidueFieldOfField.symm)
    (AlgEquiv.refl : K ≃ₐ[k] K)).trans (Algebra.TensorProduct.lid k K)

private theorem isField_fiberOfField (k K : Type*) [Field k] [Field K] [Algebra k K]
    (p : Ideal k) [p.IsPrime] : IsField (p.Fiber K) :=
  MulEquiv.isField (Field.toIsField K) (fiberAlgEquivOfField' K p).toRingEquiv.toMulEquiv

private theorem isSeparableExtension_of_isRegularRingHom (k K : Type*) [Field k] [Field K]
    [Algebra k K] (h : IsRegularRingHom (algebraMap k K)) :
    Algebra.IsSeparableExtension k K := by
  let oldAlg : Algebra k K := inferInstance
  let f : k →+* K := algebraMap k K
  let : AddCommGroup K := (Field.toCommRing : CommRing K).toAddCommGroup
  let : Algebra k K := f.toAlgebra
  let p : Ideal k := ⊥
  have : p.IsPrime := by dsimp [p]; infer_instance
  have : Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber K) := (h.2 p).2
  let : Field (p.Fiber K) := (isField_fiberOfField k K p).toField
  have hgred : Algebra.IsGeometricallyReduced p.ResidueField (p.Fiber K) :=
    Algebra.isGeometricallyReduced_of_isGeometricallyRegular p.ResidueField (p.Fiber K)
  have hsep : Algebra.IsSeparableExtension p.ResidueField (p.Fiber K) :=
    ((Algebra.isSeparableExtension_of_charZero_and_tfae
      p.ResidueField (p.Fiber K)).2.out 3 1).mp hgred
  have hsmoothκ : Algebra.FormallySmooth p.ResidueField (p.Fiber K) :=
    (Algebra.FormallySmooth.iff_isSeparableExtension p.ResidueField (p.Fiber K)).2 hsep
  have hsmoothBase : Algebra.FormallySmooth k p.ResidueField :=
    Algebra.FormallySmooth.of_equiv p.algEquivResidueFieldOfField
  have hsmoothFib : Algebra.FormallySmooth k (p.Fiber K) :=
    Algebra.FormallySmooth.comp k p.ResidueField (p.Fiber K)
  have hsmoothK : Algebra.FormallySmooth k K :=
    Algebra.FormallySmooth.of_equiv (fiberAlgEquivOfField' K p)
  have hsep' := (Algebra.FormallySmooth.iff_isSeparableExtension k K).1 hsmoothK
  have halg : f.toAlgebra = oldAlg := by
    let : Algebra k K := oldAlg
    exact toAlgebra_algebraMap (R := k) (S := K)
  change @Algebra.IsSeparableExtension k K _ _ f.toAlgebra at hsep'
  rwa [halg] at hsep'

private theorem isRegularRingHom_of_isSeparableExtension (k K : Type*) [Field k] [Field K]
    [Algebra k K] (hsep : Algebra.IsSeparableExtension k K) :
    IsRegularRingHom (algebraMap k K) := by
  let oldAlg : Algebra k K := inferInstance
  let f : k →+* K := algebraMap k K
  have halg : f.toAlgebra = oldAlg := by
    let : Algebra k K := oldAlg
    exact toAlgebra_algebraMap (R := k) (S := K)
  change @Algebra.IsSeparableExtension k K _ _ oldAlg at hsep
  rw [← halg] at hsep
  let : AddCommGroup K := (Field.toCommRing : CommRing K).toAddCommGroup
  let : Algebra k K := f.toAlgebra
  have hsmooth : Algebra.FormallySmooth k K :=
    (Algebra.FormallySmooth.iff_isSeparableExtension k K).2 hsep
  show f.Flat ∧ ∀ (p : Ideal k) [p.IsPrime],
    IsNoetherianRing (p.Fiber K) ∧
      Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber K)
  refine ⟨RingHom.Flat.of_isField (Field.toIsField k) f, fun p _ ↦ ?_⟩
  let : Field (p.Fiber K) := (isField_fiberOfField k K p).toField
  have hsm : Algebra.FormallySmooth p.ResidueField (p.Fiber K) := inferInstance
  have : Algebra.IsSeparableExtension p.ResidueField (p.Fiber K) :=
    (Algebra.FormallySmooth.iff_isSeparableExtension p.ResidueField (p.Fiber K)).1 hsm
  exact ⟨inferInstance, isGeometricallyRegular_of_isSeparableExtension p.ResidueField (p.Fiber K)⟩

/-- A field extension is a regular ring map if and only if it is separable. -/
@[stacks 07EQ]
public theorem isRegularRingHom_iff_isSeparableExtension (k : Type u) (K : Type v)
    [Field k] [Field K] [Algebra k K] :
    IsRegularRingHom (algebraMap k K) ↔ Algebra.IsSeparableExtension k K :=
  ⟨isSeparableExtension_of_isRegularRingHom k K, isRegularRingHom_of_isSeparableExtension k K⟩

end

end

/-! ### Descent along flat maps surjective on spectra -/

section

section

universe u v w

open TensorProduct

/-- If a composite ring homomorphism is regular and the second homomorphism is flat and
surjective on prime spectra, then the first homomorphism is regular. -/
@[stacks 07NT]
public theorem isRegularRingHom_of_comp_of_flat_of_surjectiveOnSpec
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hgf : IsRegularRingHom (g.comp f))
    (hgflat : g.Flat)
    (hgsurj : Function.Surjective (PrimeSpectrum.comap g)) :
    IsRegularRingHom f := by
  let : Algebra A B := f.toAlgebra
  let : Algebra B C := g.toAlgebra
  let : Algebra A C := (g.comp f).toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Flat B C := hgflat
  have : Module.FaithfullyFlat B C := by
    apply Module.FaithfullyFlat.of_comap_surjective
    simpa only [g.algebraMap_toAlgebra] using hgsurj
  have : Module.Flat A C := hgf.1
  refine ⟨Stacks.Flatness.NilpotentFibreCriterion.flat_of_flat_of_faithfullyFlat (R := A) (S := B)
      C, fun p _ ↦ ?_⟩
  have := (hgf.2 p).2
  let : Algebra B (p.Fiber B) := Algebra.TensorProduct.rightAlgebra
  let D := TensorProduct B (p.Fiber B) C
  let e : D ≃ₐ[p.ResidueField] p.Fiber C :=
    Algebra.IsPushout.cancelBaseChangeAlg A p.ResidueField B (p.Fiber B) C
  have : Algebra.IsGeometricallyRegular p.ResidueField D :=
    Algebra.IsGeometricallyRegular.of_algEquiv e.symm
  have hregB : Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber B) :=
    Algebra.IsGeometricallyRegular.of_faithfullyFlat D
  exact ⟨hregB.isNoetherianRing, hregB⟩

end

end

end

namespace Stacks.RegularRingHom

/-- Regularity of the structure morphism of an algebra transports along a pair of ring
isomorphisms of the base and of the algebra which are compatible with the structure morphisms. -/
public theorem isRegularRingHom_of_ringEquiv
    {R A S B : Type*} [CommRing R] [CommRing A] [CommRing S] [CommRing B]
    [Algebra R A] [Algebra S B] (e : R ≃+* S) (f : A ≃+* B)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap S B (e r))
    (h : IsRegularRingHom (algebraMap R A)) :
    IsRegularRingHom (algebraMap S B) := by
  rw [isRegularRingHom_algebraMap_iff] at h ⊢
  have hmap : algebraMap S B =
      f.toRingHom.comp ((algebraMap R A).comp e.symm.toRingHom) := by
    ext s
    simpa using (hf (e.symm s)).symm
  refine ⟨?_, fun q hq ↦ ?_⟩
  · rw [hmap]
    exact (RingHom.Flat.comp (RingHom.Flat.of_bijective e.symm.bijective) h.1).comp
      (RingHom.Flat.of_bijective f.bijective)
  · let p := q.comap e.toRingHom
    let ek := Ideal.residueFieldRingEquiv p q e rfl
    obtain ⟨E, hE⟩ := Stacks.FormalFibres.exists_fiber_ringEquiv e f hf q
    let : Algebra p.ResidueField q.ResidueField := ek.toRingHom.toAlgebra
    let : Algebra q.ResidueField (q.Fiber B) := Algebra.TensorProduct.leftAlgebra
    let : Algebra p.ResidueField (q.Fiber B) :=
      Algebra.compHom (q.Fiber B) (algebraMap p.ResidueField q.ResidueField)
    have hTower : IsScalarTower p.ResidueField q.ResidueField (q.Fiber B) :=
      IsScalarTower.of_algebraMap_eq (R := p.ResidueField) (S := q.ResidueField)
        (A := q.Fiber B) fun _ ↦ rfl
    let ek' : p.ResidueField ≃ₐ[p.ResidueField] q.ResidueField :=
      { ek with commutes' := fun _ ↦ rfl }
    have hSep : Algebra.IsSeparable p.ResidueField q.ResidueField :=
      AlgEquiv.Algebra.isSeparable ek'
    let E' : p.Fiber A ≃ₐ[p.ResidueField] q.Fiber B :=
      { E with commutes' := hE }
    have : Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber A) := (h.2 p).2
    have : Algebra.IsGeometricallyRegular p.ResidueField (q.Fiber B) :=
      Algebra.IsGeometricallyRegular.of_algEquiv E'
    have hiff := @Algebra.isGeometricallyRegular_iff_tower_top_of_isSeparable
      p.ResidueField q.ResidueField (q.Fiber B)
      (inferInstance : Field p.ResidueField) (inferInstance : Field q.ResidueField)
      (inferInstance : CommRing (q.Fiber B))
      (inferInstance : Algebra p.ResidueField q.ResidueField)
      (inferInstance : Algebra p.ResidueField (q.Fiber B))
      (inferInstance : Algebra q.ResidueField (q.Fiber B)) hTower hSep
    have : IsNoetherianRing (p.Fiber A) := (h.2 p).1
    exact ⟨isNoetherianRing_of_ringEquiv (p.Fiber A) E, hiff.mp inferInstance⟩

end Stacks.RegularRingHom
