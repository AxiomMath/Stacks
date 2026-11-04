module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Etale.IndEtaleFibres
public import StacksFrontier.RingTheory.FormalFibres.HenselizationShared
public import StacksFrontier.RingTheory.FormalFibres.Localization
public import StacksFrontier.RingTheory.FormallySmooth.Regularity
public import StacksFrontier.RingTheory.GRing.Defs
public import StacksFrontier.RingTheory.GeometricallyRegular.BaseFieldExtension
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.Pair.Henselization
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties
public import StacksFrontier.RingTheory.Regular.RegularRingHom
public import StacksFrontier.RingTheory.Flat.Nilpotent
public import StacksFrontier.RingTheory.Ideal.SmulTop

@[expose] public section

/-!
# G-rings, completion and henselization

The G-ring property of a Noetherian ring can be checked at its maximal ideals, the canonical map
from a G-ring to any of its adic completions is regular, and G-rings are preserved by
henselization along an ideal and, for local rings, by henselization and strict henselization.

## Main results

* `isGRing_iff_isRegularRingHom_adicCompletion_at_maximal`: a Noetherian ring is a G-ring if and
  only if the completion map of its localization at every maximal ideal is regular.
* `isRegularRingHom_algebraMap_adicCompletion`: the canonical map from a G-ring to its
  completion with respect to any ideal is regular.
* `isRegularRingHom_of_isLocalization`: a localization map to a Noetherian ring is regular.
* `isGRing_henselization`: the henselization of a G-ring along an ideal is a G-ring.
* `isGRing_iff_isRegularRingHom_completion`: a Noetherian local ring is a G-ring if and only if
  the map to its completion at the maximal ideal is regular.
* `isGRing_henselization_and_strictHenselization`: the henselization and strict henselization of
  a local G-ring are G-rings.

## References

* [H. Matsumura, *Commutative Algebra*, Theorem 79][MatCA]
* [S. Greco, *Two theorems on excellent rings*, Theorem 5.3(i)][Greco]
* [Stacks Project, Tag 07PT](https://stacks.math.columbia.edu/tag/07PT)
* [Stacks Project, Tag 0AH2](https://stacks.math.columbia.edu/tag/0AH2)
* [Stacks Project, Tag 0AH3](https://stacks.math.columbia.edu/tag/0AH3)
* [Stacks Project, Tag 07QR](https://stacks.math.columbia.edu/tag/07QR)
-/

/-! ### Detecting G-rings at maximal ideals -/

section

section

open scoped TensorProduct

universe u v

private lemma geometricallyRegularProperty_holds_iff
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] :
    geometricallyRegularProperty.Holds.{u, u, u, u} (algebraMap k A) ↔
      Algebra.IsGeometricallyRegular k A := by
  rw [RingMapProperty.geometricallyRegular_holds_iff, toAlgebra_algebraMap]

/-- A flat ring map whose fibres are geometrically regular over the residue fields of the source
is a regular ring homomorphism. -/
public lemma isRegularRingHom_algebraMap_of_geometricallyRegular_fibers
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B]
    (h : ∀ p : PrimeSpectrum A,
      Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber B)) :
    IsRegularRingHom (algebraMap A B) := by
  rw [isRegularRingHom_algebraMap_iff]
  refine ⟨?_, fun p _ => ⟨(h ⟨p, inferInstance⟩).isNoetherianRing,
    h ⟨p, inferInstance⟩⟩⟩
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

private lemma geometricallyRegular_fibers_comp
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing C] [Module.Flat A B] [Module.Flat B C]
    (hAB : ∀ p : PrimeSpectrum A,
      geometricallyRegularProperty.Holds.{u, u, u, u}
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B)))
    (hBC : ∀ q : PrimeSpectrum B,
      Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber C)) :
    ∀ p : PrimeSpectrum A,
      geometricallyRegularProperty.Holds.{u, u, u, u}
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C)) := by
  have hf := isRegularRingHom_algebraMap_of_geometricallyRegular_fibers
    (fun p => geometricallyRegularProperty_holds_iff.mp (hAB p))
  have hg := isRegularRingHom_algebraMap_of_geometricallyRegular_fibers hBC
  have h := isRegularRingHom_comp (algebraMap A B) (algebraMap B C) hf hg
    (by
      intro p _
      rw [← IsScalarTower.algebraMap_eq A B C, toAlgebra_algebraMap]
      exact p.isNoetherianRing_fiber _)
  rw [← IsScalarTower.algebraMap_eq A B C,
    isRegularRingHom_algebraMap_iff] at h
  intro p
  exact geometricallyRegularProperty_holds_iff.mpr (h.2 p.asIdeal |>.2)

private lemma geometricallyRegular_fibers_of_comp
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Flat A B] [Module.FaithfullyFlat B C]
    (hAC : ∀ p : PrimeSpectrum A,
      geometricallyRegularProperty.Holds.{u, u, u, u}
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C))) :
    ∀ p : PrimeSpectrum A,
      geometricallyRegularProperty.Holds.{u, u, u, u}
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B)) := by
  let : Module.Flat A C := Module.Flat.trans A B C
  have hgf := isRegularRingHom_algebraMap_of_geometricallyRegular_fibers
    (fun p => geometricallyRegularProperty_holds_iff.mp (hAC p))
  rw [IsScalarTower.algebraMap_eq A B C] at hgf
  have h := isRegularRingHom_of_comp_of_flat_of_surjectiveOnSpec
    (algebraMap A B) (algebraMap B C) hgf
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  rw [isRegularRingHom_algebraMap_iff] at h
  intro p
  exact geometricallyRegularProperty_holds_iff.mpr (h.2 p.asIdeal |>.2)

namespace Stacks.GRing

/-- For a Noetherian local ring `A`, the formal fibres of `A` being geometrically regular is the
same as the map from `A` to its completion at the maximal ideal being a regular ring
homomorphism, for any choice of the two auxiliary universes of `FormalFibersHaveAt`. -/
public lemma formalFibersHaveAt_iff_isRegularRingHom
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    FormalFibersHaveAt.{u, v, v}
      (RingMapProperty.geometricallyRegular :
        RingMapProperty.{max u v, max u v}) A ↔
      IsRegularRingHom
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  show (∀ q : PrimeSpectrum A,
    RingMapProperty.geometricallyRegular.Holds.{u, u, v, v}
      (Algebra.TensorProduct.includeRight (R := A) (A := C)
        (B := q.asIdeal.ResidueField)).toRingHom) ↔ _
  constructor
  · refine fun h ↦ isRegularRingHom_algebraMap_of_geometricallyRegular_fibers fun q ↦ ?_
    let : Algebra q.asIdeal.ResidueField (C ⊗[A] q.asIdeal.ResidueField) :=
      Algebra.TensorProduct.rightAlgebra
    exact @Algebra.IsGeometricallyRegular.of_algEquiv _ _ _ _ _ _ _ _
      ((RingMapProperty.geometricallyRegular_holds_iff _).mp (h q))
      (Algebra.TensorProduct.commRight A q.asIdeal.ResidueField C).symm
  · intro h q
    rw [isRegularRingHom_algebraMap_iff] at h
    let : Algebra q.asIdeal.ResidueField (C ⊗[A] q.asIdeal.ResidueField) :=
      Algebra.TensorProduct.rightAlgebra
    exact (RingMapProperty.geometricallyRegular_holds_iff _).mpr <|
      @Algebra.IsGeometricallyRegular.of_algEquiv _ _ _ _ _ _ _ _ (h.2 q.asIdeal |>.2)
      (Algebra.TensorProduct.commRight A q.asIdeal.ResidueField C)

end Stacks.GRing

private lemma isGRing_iff_isPRingAt_geometricallyRegular
    (R : Type u) [CommRing R] :
    IsGRing R ↔
      IsPRingAt.{u, u, u} geometricallyRegularProperty R := by
  constructor
  · rintro ⟨hN, h⟩
    let := hN
    exact ⟨hN, fun p =>
      (Stacks.GRing.formalFibersHaveAt_iff_isRegularRingHom _).mpr (h p.asIdeal)⟩
  · rintro ⟨hN, h⟩
    let := hN
    exact ⟨hN, fun p _ =>
      (Stacks.GRing.formalFibersHaveAt_iff_isRegularRingHom _).mp (h ⟨p, inferInstance⟩)⟩

/-- A Noetherian ring is a G-ring if and only if the completion map of its localization at every
maximal ideal is regular. -/
@[stacks 07PT]
public theorem isGRing_iff_isRegularRingHom_adicCompletion_at_maximal
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsGRing R ↔
      ∀ (m : Ideal R) [m.IsMaximal],
        IsRegularRingHom
          (algebraMap (Localization.AtPrime m)
            (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime m))
              (Localization.AtPrime m))) := by
  rw [isGRing_iff_isPRingAt_geometricallyRegular,
    isPRing_iff_formalFibersHave_localization_maximal
      geometricallyRegularProperty
      (fun A B C _ _ _ _ _ _ _ _ _ _ _ _ => geometricallyRegular_fibers_comp A B C)
      (fun A B C _ _ _ _ _ _ _ _ _ _ _ _ => geometricallyRegular_fibers_of_comp A B C)]
  exact forall_congr' fun m => forall_congr' fun _ =>
    Stacks.GRing.formalFibersHaveAt_iff_isRegularRingHom (Localization.AtPrime m)

end

end

/-! ### Completions of G-rings -/

section

section

open IsLocalRing
open scoped TensorProduct

universe u

/-- The canonical map from a G-ring to its completion with respect to any ideal is regular. -/
@[stacks 0AH2]
public theorem isRegularRingHom_algebraMap_adicCompletion
    {A : Type u} [CommRing A] (hA : IsGRing A) (I : Ideal A) :
    IsRegularRingHom (algebraMap A (AdicCompletion I A)) := by
  let : IsNoetherianRing A := hA.1
  let : IsNoetherianRing (AdicCompletion I A) := inferInstance
  apply ((isRegularRingHom_tfae_localizations
    (algebraMap A (AdicCompletion I A))).out 3 1).mp
  intro p hp q hq h
  subst p
  let p := q.under A
  let R := Localization.AtPrime p
  let S := Localization.AtPrime q
  let : Algebra R S := Localization.AtPrime.algebraOfLiesOver p q
  have hb := Stacks.FormalFibres.localized_completion_bridge I q
  let : Module.Flat R S := hb.1
  obtain ⟨e, he⟩ := exists_adicCompletion_ringEquiv_of_flat
    (A := R) (B := S) (maximalIdeal R).fg_of_isNoetherianRing hb.2.1 hb.2.2
  let T := AdicCompletion (maximalIdeal S) S
  have hregR : IsRegularRingHom
      (algebraMap R (AdicCompletion (maximalIdeal R) R)) := hA.2 p
  have hregT : IsRegularRingHom
      ((algebraMap S T).comp (algebraMap R S)) := by
    convert hregR.comp_ringEquiv e using 1
    exact RingHom.ext fun r ↦ (he r).symm
  have hff : Module.FaithfullyFlat S T :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson
      (maximalIdeal S) (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal])
  have hflat : (algebraMap S T).Flat :=
    RingHom.flat_algebraMap_iff.mpr hff.toFlat
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap S T)) := by
    let : Module.FaithfullyFlat S T := hff
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
  exact isRegularRingHom_of_comp_of_flat_of_surjectiveOnSpec
    (algebraMap R S) (algebraMap S T) hregT hflat hsurj

end

end

/-! ### G-rings and henselizations of pairs -/

section

universe u v w x y

open IsLocalRing
open scoped TensorProduct

private theorem exists_sub_mem_of_quotientMap_surjective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (I : Ideal A)
    (h : Function.Surjective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map))
    (b : B) : ∃ a : A, b - f a ∈ I.map f := by
  obtain ⟨a, ha⟩ := h (Ideal.Quotient.mk (I.map f) b)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨a, Ideal.Quotient.eq.mp ha.symm⟩

private theorem map_comap_eq_of_quotientMap_surjective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (I : Ideal A)
    (h : Function.Surjective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map))
    (q : Ideal B) (hIq : I.map f ≤ q) : (q.comap f).map f = q := by
  apply le_antisymm Ideal.map_comap_le
  intro b hb
  obtain ⟨a, ha⟩ := exists_sub_mem_of_quotientMap_surjective f I h b
  have hfa : f a ∈ q := by simpa only [sub_sub_cancel] using q.sub_mem hb (hIq ha)
  have hI : I.map f ≤ (q.comap f).map f :=
    Ideal.map_mono (Ideal.map_le_iff_le_comap.mp hIq)
  simpa only [sub_add_cancel] using
    ((q.comap f).map f).add_mem (hI ha) (Ideal.mem_map_of_mem f hfa)

private theorem residueFieldMap_bijective_of_quotientMap_surjective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A)
    (h : Function.Surjective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    (q : Ideal B) [q.IsMaximal] (hIq : I.map (algebraMap A B) ≤ q) :
    Function.Bijective
      (Ideal.ResidueField.map (q.under A) q (algebraMap A B) rfl) := by
  refine ⟨RingHom.injective _, fun z ↦ ?_⟩
  obtain ⟨b, rfl⟩ := q.algebraMap_residueField_surjective z
  obtain ⟨a, ha⟩ := exists_sub_mem_of_quotientMap_surjective (algebraMap A B) I h b
  refine ⟨algebraMap A (q.under A).ResidueField a, ?_⟩
  rw [Ideal.ResidueField.map_algebraMap]
  have hz := Ideal.algebraMap_residueField_eq_zero.mpr (hIq ha)
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

private theorem exists_localized_adicCompletion_ringEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [Algebra A B] [Module.Flat A B]
    (I : Ideal A)
    (h : Function.Surjective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    (q : Ideal B) [q.IsMaximal] (hIq : I.map (algebraMap A B) ≤ q) :
    let p := q.under A
    let R := Localization.AtPrime p
    let S := Localization.AtPrime q
    let : Algebra R S := Localization.AtPrime.algebraOfLiesOver p q
    ∃ e : AdicCompletion (maximalIdeal R) R ≃+* AdicCompletion (maximalIdeal S) S,
      ∀ a : R, e (algebraMap R (AdicCompletion (maximalIdeal R) R) a) =
        algebraMap S (AdicCompletion (maximalIdeal S) S) (algebraMap R S a) := by
  dsimp only
  let p := q.under A
  let R := Localization.AtPrime p
  let S := Localization.AtPrime q
  let : Algebra R S := Localization.AtPrime.algebraOfLiesOver p q
  have hmax : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S := by
    calc
      _ = p.map (algebraMap A S) := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
          ← IsScalarTower.algebraMap_eq]
      _ = q.map (algebraMap B S) := by
        rw [IsScalarTower.algebraMap_eq A B S, ← Ideal.map_map,
          map_comap_eq_of_quotientMap_surjective (algebraMap A B) I h q hIq]
      _ = _ := Localization.AtPrime.map_eq_maximalIdeal
  exact exists_adicCompletion_ringEquiv_of_flat
    (maximalIdeal R).fg_of_isNoetherianRing hmax
    (residueFieldMap_bijective_of_quotientMap_surjective I h q hIq)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem isFilteredColimitEtale_of_algEquiv
    {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (e : B ≃ₐ[A] C)
    (h : IsFilteredColimitEtale.{u, v, x, y} A B) :
    IsFilteredColimitEtale.{u, w, x, y} A C := by
  obtain ⟨ι, _, _, _, G, _, _, hG, f, hf, g, hg, hsurj, hinj⟩ := h
  refine ⟨ι, inferInstance, inferInstance, inferInstance, G, inferInstance, inferInstance,
    hG, f, hf, fun i ↦ e.toAlgHom.comp (g i), fun i j hij a ↦ congrArg e (hg i j hij a),
    fun c ↦ ?_, fun i a b hab ↦ hinj i a b (e.injective hab)⟩
  obtain ⟨i, b, hb⟩ := hsurj (e.symm c)
  exact ⟨i, b, by simp [hb]⟩

/-- If `B` is a Noetherian localization of `A`, then the localization map `A → B` is a regular
ring homomorphism. -/
public theorem isRegularRingHom_of_isLocalization
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing B] (M : Submonoid A) [IsLocalization M B] :
    IsRegularRingHom (algebraMap A B) := by
  rw [isRegularRingHom_algebraMap_iff]
  refine ⟨RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B M), fun p _ ↦
    ⟨p.isNoetherianRing_fiber _, ⟨fun K _ _ _ ↦ ?_⟩⟩⟩
  let : Algebra A K := ((algebraMap p.ResidueField K).comp
    (algebraMap A p.ResidueField)).toAlgebra
  have : IsScalarTower A p.ResidueField K := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra B (K ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid K M) (K ⊗[A] B) := by
    apply (Algebra.isLocalization_iff_isPushout M B).mpr
    infer_instance
  have : IsRegularRing (K ⊗[A] B) :=
    IsRegularRing.of_isLocalization (Algebra.algebraMapSubmonoid K M) _
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange A p.ResidueField K K B).symm.toRingEquiv

private theorem exists_isLocalization_away_of_surjective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsSemisimpleRing R]
    (h : Function.Surjective (algebraMap R S)) :
    ∃ e : R, IsLocalization.Away e S := by
  obtain ⟨e, he, hker⟩ := IsSemisimpleRing.ideal_eq_span_idempotent
    (RingHom.ker (algebraMap R S))
  exact ⟨1 - e, IsLocalization.away_of_isIdempotentElem he.one_sub
    (by simpa only [sub_sub_cancel] using hker) h⟩

/-- If the fibre over `q.under A` decomposes as a finite product of residue fields as in
`IsFilteredColimitEtale.exists_fiber_algEquiv_pi_residueField`, then it is semisimple and the
residue field extension at `q` is separable. -/
private theorem semisimple_fiber_and_isSeparable_of_decomposition
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (q : Ideal B) [q.IsPrime]
    (h : ∃ (n : ℕ) (qs : Fin n → Ideal B) (hqs : ∀ i, (qs i).IsPrime)
        (hlo : ∀ i, (qs i).LiesOver (q.under A)),
      (letI : ∀ i, (qs i).IsPrime := hqs
       letI : ∀ i, Algebra (q.under A).ResidueField (qs i).ResidueField := fun i ↦
         (Ideal.ResidueField.map (q.under A) (qs i) (algebraMap A B) (hlo i).over).toAlgebra
       Nonempty (TensorProduct A (q.under A).ResidueField B ≃ₐ[(q.under A).ResidueField]
           (∀ i, (qs i).ResidueField)) ∧
         (∀ i, Algebra.IsSeparable (q.under A).ResidueField (qs i).ResidueField) ∧
         (∀ i, Algebra.IsAlgebraic (q.under A).ResidueField (qs i).ResidueField)) ∧
      Function.Injective qs ∧
      (∀ q' : Ideal B, ∀ _ : q'.IsPrime, q'.LiesOver (q.under A) ↔ ∃ i, qs i = q')) :
    let p := q.under A
    let : Algebra p.ResidueField q.ResidueField :=
      (Ideal.ResidueField.map p q (algebraMap A B) rfl).toAlgebra
    IsSemisimpleRing (p.Fiber B) ∧ Algebra.IsSeparable p.ResidueField q.ResidueField := by
  dsimp only
  obtain ⟨n, qs, hqs, hlo, hdecomp, _, hall⟩ := h
  let : ∀ i, (qs i).IsPrime := hqs
  let : ∀ i, Algebra (q.under A).ResidueField (qs i).ResidueField := fun i ↦
    (Ideal.ResidueField.map (q.under A) (qs i) (algebraMap A B) (hlo i).over).toAlgebra
  obtain ⟨⟨e⟩, hsep, _⟩ := hdecomp
  refine ⟨e.symm.toRingEquiv.isSemisimpleRing, ?_⟩
  obtain ⟨i, hi⟩ := (hall q inferInstance).mp (inferInstance : q.LiesOver (q.under A))
  cases hi
  exact hsep i

private theorem fiber_map_surjective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (q : Ideal B) [q.IsPrime] [IsSemisimpleRing ((q.under A).Fiber B)] :
    Function.Surjective (Algebra.TensorProduct.lift
      (Ideal.ResidueField.mapₐ (q.under A) q (Algebra.ofId A B) rfl)
      (IsScalarTower.toAlgHom A B q.ResidueField) (fun _ _ ↦ Commute.all _ _)) := by
  let p := q.under A
  let f : p.Fiber B →ₐ[A] q.ResidueField := Algebra.TensorProduct.lift
    (Ideal.ResidueField.mapₐ p q (Algebra.ofId A B) rfl)
    (IsScalarTower.toAlgHom A B q.ResidueField) (fun _ _ ↦ Commute.all _ _)
  let R := f.toRingHom.range
  have : (RingHom.ker f.toRingHom).IsPrime := RingHom.ker_isPrime _
  have : (RingHom.ker f.toRingHom).IsMaximal := IsArtinianRing.isPrime_iff_isMaximal _ |>.mp
    inferInstance
  let : Field (p.Fiber B ⧸ RingHom.ker f.toRingHom) := Ideal.Quotient.field _
  let e := RingHom.quotientKerEquivRange f.toRingHom
  have hR : IsField R := e.symm.toMulEquiv.isField (Field.toIsField _)
  let : Field R := hR.toField
  let g : B →+* R := f.toRingHom.rangeRestrict.comp
    (Algebra.TensorProduct.includeRight (R := A) (A := p.ResidueField)).toRingHom
  have hg (b : B) : (g b : q.ResidueField) = algebraMap B q.ResidueField b := by
    show f (1 ⊗ₜ[A] b) = algebraMap B q.ResidueField b
    simp only [f, Algebra.TensorProduct.lift_tmul, map_one, one_mul,
      IsScalarTower.toAlgHom_apply]
  have hgker : RingHom.ker g = q := by
    ext b
    show g b = 0 ↔ b ∈ q
    rw [← Subtype.coe_inj]
    simpa only [hg, Subring.coe_zero] using
      (Ideal.algebraMap_residueField_eq_zero (I := q) (x := b))
  let l : q.ResidueField →+* R := Ideal.ResidueField.lift q g hgker.ge (by
    intro b hb
    show IsUnit (g b)
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact hb (hgker ▸ hz : b ∈ q))
  have hl : R.subtype.comp l = RingHom.id _ := by
    apply Ideal.ResidueField.ringHom_ext
    ext b
    simp [l, hg]
  intro z
  obtain ⟨t, ht⟩ := (l z).property
  exact ⟨t, ht.trans (DFunLike.congr_fun hl z)⟩


private theorem isRegularRingHom_of_semisimple_fibers
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [IsNoetherianRing B] [IsNoetherianRing C]
    [Module.Flat B C]
    (hB : ∀ (q : Ideal B) [q.IsPrime],
      let p := q.under A
      let : Algebra p.ResidueField q.ResidueField :=
        (Ideal.ResidueField.map p q (algebraMap A B) rfl).toAlgebra
      IsSemisimpleRing (p.Fiber B) ∧ Algebra.IsSeparable p.ResidueField q.ResidueField)
    (hC : IsRegularRingHom (algebraMap A C)) :
    IsRegularRingHom (algebraMap B C) := by
  rw [isRegularRingHom_algebraMap_iff] at hC ⊢
  refine ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, fun q _ ↦
    ⟨q.isNoetherianRing_fiber _, ?_⟩⟩
  let p := q.under A
  let k := p.ResidueField
  let L := q.ResidueField
  let T := p.Fiber B
  let : Algebra k L := (Ideal.ResidueField.map p q (algebraMap A B) rfl).toAlgebra
  have hs := hB q
  have : IsSemisimpleRing T := hs.1
  have : Algebra.IsSeparable k L := hs.2
  let fA : T →ₐ[A] L := Algebra.TensorProduct.lift
    (Ideal.ResidueField.mapₐ p q (Algebra.ofId A B) rfl)
    (IsScalarTower.toAlgHom A B L) (fun _ _ ↦ Commute.all _ _)
  let f : T →ₐ[B] L :=
    { fA.toRingHom with
      commutes' := by
        intro b
        show fA (1 ⊗ₜ[A] b) = algebraMap B L b
        dsimp only [fA, T, k, L]
        simp only [Algebra.TensorProduct.lift_tmul, map_one, one_mul,
          IsScalarTower.toAlgHom_apply] }
  have hf_k (b : k) : f (b ⊗ₜ[A] 1) = algebraMap k L b := by
    show fA (b ⊗ₜ[A] 1) = algebraMap k L b
    dsimp only [fA, T, k, L]
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  let : Algebra T L := f.toRingHom.toAlgebra
  have : IsScalarTower B T L := IsScalarTower.of_algebraMap_eq fun b ↦ (f.commutes b).symm
  have hsurj : Function.Surjective (algebraMap T L) := fiber_map_surjective (A := A) q
  obtain ⟨a, ha⟩ := exists_isLocalization_away_of_surjective hsurj
  have : IsLocalization.Away a L := ha
  let : Algebra k (C ⊗[B] T) := Algebra.compHom (C ⊗[B] T) (algebraMap k T)
  let : Algebra k (C ⊗[B] L) := Algebra.compHom (C ⊗[B] L) (algebraMap k L)
  let g : (C ⊗[B] T) →ₐ[B] (C ⊗[B] L) := Algebra.TensorProduct.map (AlgHom.id B C) f
  have hg_tmul (c : C) (t : T) : g (c ⊗ₜ[B] t) = c ⊗ₜ[B] f t :=
    Algebra.TensorProduct.map_tmul _ _ _ _
  let : Algebra (C ⊗[B] T) (C ⊗[B] L) := g.toRingHom.toAlgebra
  have : IsScalarTower k (C ⊗[B] T) (C ⊗[B] L) := by
    apply IsScalarTower.of_algebraMap_eq (R := k) (S := (C ⊗[B] T)) (A := (C ⊗[B] L))
    intro b
    show (1 ⊗ₜ[B] algebraMap k L b) = g (1 ⊗ₜ[B] (b ⊗ₜ[A] 1))
    rw [hg_tmul, hf_k]
  have : IsScalarTower C (C ⊗[B] T) (C ⊗[B] L) := by
    apply IsScalarTower.of_algebraMap_eq (R := C) (S := (C ⊗[B] T)) (A := (C ⊗[B] L))
    intro c
    show (c ⊗ₜ[B] 1) = g (c ⊗ₜ[B] 1)
    rw [hg_tmul, map_one]
  have : IsScalarTower k L (C ⊗[B] L) :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := L) (A := (C ⊗[B] L)) fun _ ↦ rfl
  have hlocal := IsLocalization.tensorProduct_tensorProduct_right B C (Submonoid.powers a) L
    (RingHom.ext fun t ↦ hg_tmul 1 t)
  have hlocal' : IsLocalization (R := C ⊗[B] T)
      (Algebra.algebraMapSubmonoid (C ⊗[B] T) (Submonoid.powers a)) (C ⊗[B] L) := by
    convert hlocal using 1
    rfl
  let e₁ := Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[B] C)
    (Algebra.TensorProduct.commRight A B k).symm
  let e₂ := Algebra.TensorProduct.cancelBaseChange A B C C k
  let e₃ := Algebra.TensorProduct.comm A C k
  let eD : (C ⊗[B] T) ≃ₐ[k] p.Fiber C :=
    { e₁.toRingEquiv.trans (e₂.toRingEquiv.trans e₃.toRingEquiv) with
      commutes' := by
        intro b
        show e₃ (e₂ (e₁ (1 ⊗ₜ[B] (b ⊗ₜ[A] 1)))) = b ⊗ₜ[A] 1
        simp [e₁, e₂, e₃] }
  have : Algebra.IsGeometricallyRegular k (C ⊗[B] T) :=
    @Algebra.IsGeometricallyRegular.of_algEquiv k _ _ _ _ _ _ _ (hC.2 p).2 eD.symm
  have : Algebra.IsGeometricallyRegular k (C ⊗[B] L) :=
    Algebra.IsGeometricallyRegular.of_isLocalization (k := k) (A := (C ⊗[B] T))
      (B := (C ⊗[B] L))
      (Algebra.algebraMapSubmonoid (C ⊗[B] T) (Submonoid.powers a))
  have : Algebra.IsGeometricallyRegular L (C ⊗[B] L) :=
    (Algebra.isGeometricallyRegular_iff_tower_top_of_isSeparable k L (C ⊗[B] L)).mp inferInstance
  exact Algebra.IsGeometricallyRegular.of_algEquiv
    (Algebra.TensorProduct.commRight B L C).symm

private theorem isRegularRingHom_localization_to_localRing
    {B : Type u} {C : Type v} [CommRing B] [CommRing C] [IsLocalRing C]
    [IsNoetherianRing C] [Algebra B C]
    (m : Ideal B) [m.IsPrime] [Algebra (Localization.AtPrime m) C]
    [IsScalarTower B (Localization.AtPrime m) C]
    [IsLocalHom (algebraMap (Localization.AtPrime m) C)]
    (h : IsRegularRingHom (algebraMap B C)) :
    IsRegularRingHom (algebraMap (Localization.AtPrime m) C) := by
  have hm : m = (maximalIdeal C).comap (algebraMap B C) := by
    rw [IsScalarTower.algebraMap_eq B (Localization.AtPrime m) C,
      ← Ideal.comap_comap, maximalIdeal_comap]
    exact Localization.AtPrime.under_maximalIdeal.symm
  have hloc := ((isRegularRingHom_tfae_localizations (algebraMap B C)).out
    1 2 rfl rfl).mp h m (maximalIdeal C) hm
  let e : Localization.AtPrime (maximalIdeal C) ≃ₐ[C] C :=
    (IsLocalization.atUnits C (maximalIdeal C).primeCompl
      (fun _ hx ↦ not_not.mp hx)).symm
  have hr := hloc.comp_ringEquiv e.toRingEquiv
  convert hr using 1
  apply IsLocalization.ringHom_ext m.primeCompl
  ext b
  show algebraMap (Localization.AtPrime m) C (algebraMap B _ b) =
    e (Localization.localRingHom m (maximalIdeal C) (algebraMap B C) hm
      (algebraMap B _ b))
  rw [Localization.localRingHom_to_map, e.commutes,
    ← IsScalarTower.algebraMap_apply B (Localization.AtPrime m) C]
  rfl

/-- The henselization of a G-ring along an ideal is a G-ring. -/
@[stacks 0AH3]
public theorem isGRing_henselization
    {A : Type u} [CommRing A] (hA : IsGRing A) (I : Ideal A)
    (Ah : Type v) [CommRing Ah] [Algebra A Ah]
    (hh : HenselianPair Ah (I.map (algebraMap A Ah)))
    (hι : ∀ (B : Type (max u v)) (_ : CommRing B) (J : Ideal B),
      HenselianPair B J →
        ∀ f : A →+* B, I ≤ J.comap f →
          ∃! g : Ah →+* B,
            g.comp (algebraMap A Ah) = f ∧ I.map (algebraMap A Ah) ≤ J.comap g) :
    IsGRing Ah := by
  have : IsNoetherianRing A := hA.1
  have hcompletion :=
    henselization_isNoetherian_and_completion_equiv A I Ah hh hι
  have : IsNoetherianRing Ah := hcompletion.2.1
  obtain ⟨hflat, hmod⟩ :=
    flat_henselization_and_bijective_quotientMap A I Ah hh hι
  have : Module.Flat A Ah := hflat
  have hmodI : Function.Surjective (Ideal.quotientMap (I.map (algebraMap A Ah))
      (algebraMap A Ah) Ideal.le_comap_map) := by
    have h := hmod 1
    rw [pow_one] at h
    exact h.2
  obtain ⟨eH⟩ := nonempty_algEquiv_henselization A I Ah hh hι
  have hind := isFilteredColimitEtale_of_algEquiv eH
    (Stacks.Henselization.Shared.isFilteredColimitEtale_of_ind A _ (ind_henselization A I))
  refine (isGRing_iff_isRegularRingHom_adicCompletion_at_maximal Ah).2 fun m hm ↦ ?_
  have hIm : I.map (algebraMap A Ah) ≤ m := hh.1.trans (by
    simpa only [Ideal.jacobson_bot] using Ring.jacobson_le_of_isMaximal m)
  let p := m.under A
  let R := Localization.AtPrime p
  let S := Localization.AtPrime m
  let C := AdicCompletion (maximalIdeal S) S
  let : Algebra R S := Localization.AtPrime.algebraOfLiesOver p m
  let : Algebra R C := ((algebraMap S C).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨e, he⟩ := exists_localized_adicCompletion_ringEquiv I hmodI m hIm
  have hRC : IsRegularRingHom (algebraMap R C) := by
    have hr := (hA.2 p).comp_ringEquiv e
    convert hr using 1
    exact RingHom.ext fun a ↦ (he a).symm
  have hAC : IsRegularRingHom (algebraMap A C) := by
    have hr := isRegularRingHom_comp (algebraMap A R) (algebraMap R C)
      (isRegularRingHom_of_isLocalization p.primeCompl) hRC
      (fun q _ ↦ by
        let : Algebra A C := ((algebraMap R C).comp (algebraMap A R)).toAlgebra
        exact q.isNoetherianRing_fiber _)
    convert hr using 1
    apply RingHom.ext
    intro a
    show algebraMap A C a = algebraMap S C (algebraMap R S (algebraMap A R a))
    rw [← IsScalarTower.algebraMap_apply A R S, ← IsScalarTower.algebraMap_apply A S C]
  have : Module.Flat Ah C := Module.Flat.trans Ah S C
  exact isRegularRingHom_localization_to_localRing m
    (isRegularRingHom_of_semisimple_fibers
      (fun q _ ↦ semisimple_fiber_and_isSeparable_of_decomposition q
        (hind.exists_fiber_algEquiv_pi_residueField _)) hAC)

end

/-! ### G-rings and henselizations of local rings -/

section

section

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u v w x

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A Noetherian local ring is a G-ring if and only if the map to its completion at the maximal
ideal is regular. -/
public theorem isGRing_iff_isRegularRingHom_completion
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsGRing R ↔ IsRegularRingHom
      (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  let e : Localization.AtPrime (maximalIdeal R) ≃ₐ[R] R :=
    (IsLocalization.atUnits R (maximalIdeal R).primeCompl
      (fun _ hx => not_not.mp hx)).symm
  constructor
  · intro h
    let : Algebra (Localization.AtPrime (maximalIdeal R))
        (AdicCompletion (maximalIdeal (Localization.AtPrime (maximalIdeal R)))
          (Localization.AtPrime (maximalIdeal R))) := inferInstance
    exact Stacks.RegularRingHom.isRegularRingHom_of_ringEquiv e.toRingEquiv
      (Stacks.FormalFibres.completionRingEquiv e.toRingEquiv)
      (Stacks.FormalFibres.completionRingEquiv_algebraMap e.toRingEquiv)
      (h.2 (maximalIdeal R))
  · refine fun h ↦
      (isGRing_iff_isRegularRingHom_adicCompletion_at_maximal R).mpr fun m hm ↦ ?_
    obtain rfl := IsLocalRing.eq_maximalIdeal hm
    exact Stacks.RegularRingHom.isRegularRingHom_of_ringEquiv e.symm.toRingEquiv
      (Stacks.FormalFibres.completionRingEquiv e.symm.toRingEquiv)
      (Stacks.FormalFibres.completionRingEquiv_algebraMap e.symm.toRingEquiv) h

/-- The residue map of an ordinary henselization is surjective. -/
private theorem residueFieldMap_surjective_of_isHenselization
    (R Rh : Type u) [CommRing R] [IsLocalRing R]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [IsHenselization R (ResidueField R) Rh]
    [IsLocalHom (algebraMap R Rh)] :
    Function.Surjective (ResidueField.map (algebraMap R Rh)) := by
  obtain ⟨e, he⟩ := IsHenselization.exists_residueFieldEquiv
    (R := R) (L := ResidueField R) (Rh := Rh)
  have heq : ResidueField.map (algebraMap R Rh) = e.toRingHom := RingHom.ext fun z ↦ by
    obtain ⟨r, rfl⟩ := residue_surjective z
    simpa using (he r).symm
  rw [heq]
  exact e.surjective

/-- The henselization and the strict henselization of a Noetherian local G-ring, both in the
universe of the ring, are G-rings. -/
private lemma isGRing_henselizations_sameUniverse
    (R Rh Rsh : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    (κsep : Type v) [Field κsep] [Algebra (ResidueField R) κsep]
    [IsSepClosure (ResidueField R) κsep]
    [IsHenselization R (ResidueField R) Rh]
    [IsHenselization R κsep Rsh]
    (hR : IsGRing R) :
    IsGRing Rh ∧ IsGRing Rsh := by
  have hn := isNoetherianRing_iff_henselizations R Rh Rsh κsep
  have : IsNoetherianRing Rh := hn.1.mp inferInstance
  have : IsNoetherianRing Rsh := hn.2.mp inferInstance
  have : IsLocalHom (algebraMap R Rh) :=
    IsHenselization.isLocalHom (L := ResidueField R)
  have : IsLocalHom (algebraMap R Rsh) := IsHenselization.isLocalHom (L := κsep)
  have : HenselianLocalRing Rsh := IsHenselization.henselian (R := R) (L := κsep)
  let j : Rh →ₐ[R] Rsh := HenselianLocalRing.indEtaleAlgHom
    (Sh := Rsh)
    (IsHenselization.ind_etale (R := R) (L := ResidueField R) (Rh := Rh))
    (residueFieldMap_surjective_of_isHenselization R Rh)
  have hj : IsLocalHom j := HenselianLocalRing.isLocalHom_indEtaleAlgHom
    (Sh := Rsh)
    (IsHenselization.ind_etale (R := R) (L := ResidueField R) (Rh := Rh))
    (residueFieldMap_surjective_of_isHenselization R Rh)
  let : Algebra Rh Rsh := j.toRingHom.toAlgebra
  have : IsScalarTower R Rh Rsh := IsScalarTower.of_algebraMap_eq fun r => (j.commutes r).symm
  have : IsLocalHom (algebraMap Rh Rsh) := ⟨hj.map_nonunit⟩
  obtain ⟨_, hc⟩ :=
    isNoetherianRing_iff_henselizations_and_completion_properties.{u, v, u}
      R Rh Rsh κsep
  obtain ⟨h₁, h₂, h₃, _, _, _, _, e, he, hflat, hflatsh, ⟨f, hf, hfs⟩, _⟩ :=
    hc inferInstance
  let C := AdicCompletion (maximalIdeal R) R
  let Ch := AdicCompletion (maximalIdeal Rh) Rh
  let Csh := AdicCompletion (maximalIdeal Rsh) Rsh
  have hRC := (isGRing_iff_isRegularRingHom_completion R).mp hR
  have hRh : IsRegularRingHom (algebraMap R Ch) := by
    have hr := hRC.comp_ringEquiv e
    convert hr using 1
    exact RingHom.ext fun r => (he r).symm
  have hflocal : IsLocalHom f := by
    apply ((IsLocalRing.local_hom_TFAE f).out 3 1).mp
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map]
    have hcomp : f.comp (algebraMap R C) =
        (algebraMap Rsh Csh).comp (algebraMap R Rsh) := RingHom.ext hf
    rw [hcomp, ← Ideal.map_map]
    exact (Ideal.map_mono (map_maximalIdeal_le (algebraMap R Rsh))).trans
      (AdicCompletion.maximalIdeal_eq_map (R := Rsh)).ge
  have hregf : IsRegularRingHom f :=
    ((isRegularRingHom_flat_geometricallyRegular_specialFiber_formallySmooth_tfae
      f).out 4 1).mp
      (Stacks.Henselization.Shared.formallySmoothNAdic_of_isFormallySmooth f (maximalIdeal C)
        (maximalIdeal Csh) hfs)
  have hRsh : IsRegularRingHom (algebraMap R Csh) := by
    have hr := isRegularRingHom_comp (algebraMap R C) f hRC hregf
      (fun p _ => by
        let : Algebra R Csh := (f.comp (algebraMap R C)).toAlgebra
        exact p.isNoetherianRing_fiber _)
    convert hr using 1
    exact RingHom.ext fun r => (hf r).symm
  have hsemih (q : Ideal Rh) [q.IsPrime] :=
    semisimple_fiber_and_isSeparable_of_decomposition (A := R) q
      (henselization_fibres_equiv_pi_residueFields R Rh Rsh κsep (q.under R)).1
  have hsemish (q : Ideal Rsh) [q.IsPrime] :=
    semisimple_fiber_and_isSeparable_of_decomposition (A := R) q
      (henselization_fibres_equiv_pi_residueFields R Rh Rsh κsep (q.under R)).2
  exact ⟨(isGRing_iff_isRegularRingHom_completion Rh).mpr
      (isRegularRingHom_of_semisimple_fibers hsemih hRh),
    (isGRing_iff_isRegularRingHom_completion Rsh).mpr
      (isRegularRingHom_of_semisimple_fibers hsemish hRsh)⟩

private theorem isGRing_of_local_ringEquiv
    {R : Type u} {S : Type w} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (e : R ≃+* S) (h : IsGRing R) :
    IsGRing S := by
  have : IsNoetherianRing R := h.1
  have : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
  exact (isGRing_iff_isRegularRingHom_completion S).mpr <|
    Stacks.RegularRingHom.isRegularRingHom_of_ringEquiv e
    (Stacks.FormalFibres.completionRingEquiv e)
    (Stacks.FormalFibres.completionRingEquiv_algebraMap e)
    ((isGRing_iff_isRegularRingHom_completion R).mp h)

private theorem isGRing_henselization_07qr
    (R : Type u) (H : Type w)
    [CommRing R] [IsLocalRing R]
    [CommRing H] [IsLocalRing H] [Algebra R H]
    [IsHenselization R (ResidueField R) H]
    (hR : IsGRing R) :
    IsGRing H := by
  let R' := ULift.{w} R
  let H' := ULift.{u} H
  let eR : R' ≃+* R := ULift.ringEquiv
  let eH : H' ≃+* H := ULift.ringEquiv
  have : IsLocalRing R' := eR.symm.isLocalRing
  have : IsLocalRing H' := eH.symm.isLocalRing
  have hR' : IsGRing R' := isGRing_of_local_ringEquiv eR.symm hR
  have : IsNoetherianRing R' := hR'.1
  let : Algebra R' H' := ((algebraMap R H').comp eR.toRingHom).toAlgebra
  let : Algebra (ResidueField R') (ResidueField R) :=
    (ResidueField.mapEquiv eR).toRingHom.toAlgebra
  have : IsHenselization R' (ResidueField R) H' :=
    Stacks.Henselization.Shared.isHenselization_ulift R (ResidueField R) H
  have : IsHenselization R' (ResidueField R') H' :=
    Stacks.Henselization.Shared.isHenselization_of_residueFieldEquiv R' (ResidueField R)
      (ResidueField R') H' (ResidueField.mapEquiv eR) (fun _ => rfl)
  have : IsLocalHom (algebraMap R' H') := IsHenselization.isLocalHom (L := ResidueField R')
  obtain ⟨Hsh, _, _, _, _, _, _, hh, _, hi, _, hr⟩ :=
    exists_strictHenselization R' H'
      (IsHenselization.ind_etale_of_universe_le.{max u w, max u w, 0}
        (R := R') (ResidueField R') (Rh := H'))
      (residueFieldMap_surjective_of_isHenselization R' H')
      (SeparableClosure (ResidueField R'))
  have : IsHenselization R' (SeparableClosure (ResidueField R')) Hsh :=
    IsHenselization.of_ind_etale.{max u w, max u w, 0} hh hi hr
  exact isGRing_of_local_ringEquiv eH
    (isGRing_henselizations_sameUniverse R' H' Hsh (SeparableClosure (ResidueField R')) hR').1

private theorem isGRing_strictHenselization
    (R : Type u) (L : Type v) (H : Type w)
    [CommRing R] [IsLocalRing R] [Field L] [Algebra (ResidueField R) L]
    [IsSepClosure (ResidueField R) L]
    [CommRing H] [IsLocalRing H] [Algebra R H] [IsHenselization R L H]
    (hR : IsGRing R) : IsGRing H := by
  let R' := ULift.{w} R
  let H' := ULift.{u} H
  let eR : R' ≃+* R := ULift.ringEquiv
  let eH : H' ≃+* H := ULift.ringEquiv
  have : IsLocalRing R' := eR.symm.isLocalRing
  have : IsLocalRing H' := eH.symm.isLocalRing
  have hR' : IsGRing R' := isGRing_of_local_ringEquiv eR.symm hR
  have : IsNoetherianRing R' := hR'.1
  let : Algebra R' H' := ((algebraMap R H').comp eR.toRingHom).toAlgebra
  let : Algebra (ResidueField R') L :=
    ((algebraMap (ResidueField R) L).comp (ResidueField.mapEquiv eR).toRingHom).toAlgebra
  have : IsHenselization R' L H' := Stacks.Henselization.Shared.isHenselization_ulift R L H
  have : IsSepClosure (ResidueField R') L :=
    { sep_closed := IsSepClosure.sep_closed (ResidueField R)
      separable := Algebra.IsSeparable.of_equiv_equiv
        (ResidueField.mapEquiv eR).symm (RingEquiv.refl L) (by
          ext a
          show algebraMap (ResidueField R) L
            ((ResidueField.mapEquiv eR) ((ResidueField.mapEquiv eR).symm a)) = _
          rw [RingEquiv.apply_symm_apply]
          rfl) }
  obtain ⟨Rh, _, _, _, hh⟩ := IsLocalRing.exists_isHenselization_residueField R'
  have := hh
  exact isGRing_of_local_ringEquiv eH
    (isGRing_henselizations_sameUniverse R' Rh H' L hR').2

/-- The henselization and strict henselization of a local G-ring are G-rings. -/
@[stacks 07QR]
public theorem isGRing_henselization_and_strictHenselization
    (R : Type u) (Rh : Type w) (Rsh : Type x)
    [CommRing R] [IsLocalRing R]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    (κsep : Type v) [Field κsep] [Algebra (ResidueField R) κsep]
    [IsSepClosure (ResidueField R) κsep]
    [IsHenselization R (ResidueField R) Rh]
    [IsHenselization R κsep Rsh]
    (hR : IsGRing R) :
    IsGRing Rh ∧ IsGRing Rsh :=
  ⟨isGRing_henselization_07qr R Rh hR, isGRing_strictHenselization R κsep Rsh hR⟩

end

end

end

end
