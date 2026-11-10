module

public import Mathlib
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.FormalFibres.RingMapProperty
public import StacksFrontier.RingTheory.GRing.Criteria
public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.Regular.RegularRingHom
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.Rig.AdicCompletionMap

@[expose] public section

/-!
# Formal fibre properties and localization

Let `P` be a property of ring maps. If `P` ascends through regular maps and descends through
faithfully flat maps, a Noetherian ring is a `P`-ring if and only if the formal fibres of its
localizations at maximal ideals have `P`. If `P` is local on the target and descends in towers
whose second map is faithfully flat, then for a Noetherian `P`-ring `A` every fibre of the map
from `A` to any adic completion of `A` has `P`.

## Main definitions

* `RegularAscent`: the property `P` ascends through regular maps.
* `FaithfullyFlatDescent`: the property `P` descends through faithfully flat maps.

## Main results

* `isPRing_iff_formalFibersHave_localization_maximal`: the formal-fibre property can be checked
  at the localizations at maximal ideals.
* `fibersHaveProperty_adicCompletion_of_isPRing`: every fibre of the map to an adic completion
  of a `P`-ring has property `P`.

## References

* [Stacks Project, Tag 0BIU](https://stacks.math.columbia.edu/tag/0BIU)
* [Stacks Project, Tag 0BK9](https://stacks.math.columbia.edu/tag/0BK9)
-/

/-! ### Checking formal-fibre properties at maximal ideals -/

section

section

universe u v w

end

section

open IsLocalRing
open scoped TensorProduct

universe u v w x

namespace Stacks.FormalFibres

/-- The map of adic completions at the maximal ideals induced by a local homomorphism of
Noetherian local rings is again local. -/
public lemma adicCompletionMap_isLocalHom {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B) [IsLocalHom f] :
    IsLocalHom (adicCompletionMap f (maximalIdeal A) (maximalIdeal B)
      (map_maximalIdeal_le f)) := by
  apply ((IsLocalRing.local_hom_TFAE _).out 3 1).mp
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map,
    adicCompletionMap_comp_algebraMap, ← Ideal.map_map]
  exact (Ideal.map_mono (map_maximalIdeal_le f)).trans
    (AdicCompletion.maximalIdeal_eq_map (R := B)).ge

/-- A property of ring maps transports along a commuting square of ring isomorphisms: if `P`
holds of `f : A →+* B` and the isomorphisms `e : A ≃+* C`, `E : B ≃+* D` carry `f` to
`g : C →+* D`, then `P` holds of `g`. The universes of the two maps are independent of one
another. -/
public lemma holds_of_equiv
    (P : RingMapProperty.{max u v w, max u v w x})
    {A B : Type u} {C D : Type v}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : C →+* D) (e : A ≃+* C) (E : B ≃+* D)
    (h : E.toRingHom.comp f = g.comp e.toRingHom)
    (hf : P.Holds.{u, u, max v w, x} f) : P.Holds.{v, v, max u w, x} g := by
  let e' : ULift.{max u v w} C ≃+* ULift.{max u v w} A :=
    ULift.ringEquiv.trans (e.symm.trans ULift.ringEquiv.symm)
  let E' : ULift.{max u v w x} B ≃+* ULift.{max u v w x} D :=
    ULift.ringEquiv.trans (E.trans ULift.ringEquiv.symm)
  have hh := P.respectsIso.2 _ e' (P.respectsIso.1 _ E' hf)
  have heq : (E'.toRingHom.comp (RingHom.ulift.{max u v w, max u v w x} f)).comp
      e'.toRingHom = RingHom.ulift.{max u v w, max u v w x} g := by
    apply RingHom.ext
    intro c
    apply ULift.ext
    exact (congrArg (fun t : A →+* D => t (e.symm c.down)) h).trans
      (by simp)
  change P (RingHom.ulift.{max u v w, max u v w x} g)
  rw [← heq]
  exact hh

/-- The formal fibres of a local ring `A` have `P` exactly when `P` holds of the map from the
residue field at each prime `q` of `A` into the fibre at `q` of the adic completion of `A` at
its maximal ideal. -/
public lemma formalFibersHaveAt_iff
    (P : RingMapProperty.{max u v, max u v w})
    (A : Type u) [CommRing A] [IsLocalRing A] :
    FormalFibersHaveAt.{u, v, w} P A ↔
      ∀ q : PrimeSpectrum A,
        P.Holds.{u, u, v, w} (algebraMap q.asIdeal.ResidueField
          (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A))) := by
  constructor <;> intro h q <;>
    exact holds_of_equiv.{u, u, v, w} P _ _ (RingEquiv.refl _)
      (Algebra.TensorProduct.comm A _ _).toRingEquiv (by ext a; rfl) (h q)

/-- The isomorphism of adic completions at the maximal ideals induced by an isomorphism of local
rings. -/
public noncomputable def completionRingEquiv {A B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B := by
  letI : IsLocalHom e.toRingHom := isLocalHom_of_leftInverse e.symm e.left_inv
  letI : IsLocalHom e.symm.toRingHom := isLocalHom_of_leftInverse e e.right_inv
  exact RingEquiv.ofRingHom
    (adicCompletionMap e.toRingHom _ _ (map_maximalIdeal_le e.toRingHom))
    (adicCompletionMap e.symm.toRingHom _ _
      (map_maximalIdeal_le e.symm.toRingHom))
    (by
      rw [Rig.adicCompletionMap_comp _ _ _ _ _ _ _ (by simp)]
      simpa using Rig.adicCompletionMap_id (maximalIdeal B) _)
    (by
      rw [Rig.adicCompletionMap_comp _ _ _ _ _ _ _ (by simp)]
      simpa using Rig.adicCompletionMap_id (maximalIdeal A) _)

/-- `completionRingEquiv e` is compatible with the maps from the uncompleted rings. -/
public lemma completionRingEquiv_algebraMap {A B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (a : A) :
    completionRingEquiv e (algebraMap A _ a) = algebraMap B _ (e a) := by
  let : IsLocalHom e.toRingHom := isLocalHom_of_leftInverse e.symm e.left_inv
  exact congrArg (fun f : A →+* AdicCompletion (maximalIdeal B) B => f a)
    (adicCompletionMap_comp_algebraMap e.toRingHom _ _ (map_maximalIdeal_le e.toRingHom))

/-- Having `P` formal fibres transports along an isomorphism of local rings. -/
public lemma formalFibersHaveAt_of_ringEquiv
    (P : RingMapProperty.{max u v w, max u v w x})
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B)
    (h : FormalFibersHaveAt.{u, max v w, x} P A) :
    FormalFibersHaveAt.{v, max u w, x} P B := by
  rw [formalFibersHaveAt_iff] at h ⊢
  intro q
  let p : PrimeSpectrum A := ⟨q.asIdeal.comap e.toRingHom, inferInstance⟩
  obtain ⟨E, hE⟩ := exists_fiber_ringEquiv e (completionRingEquiv e)
    (completionRingEquiv_algebraMap e) q.asIdeal
  exact holds_of_equiv.{u, v, w, x} P _ _ (Ideal.residueFieldRingEquiv p.asIdeal q.asIdeal e rfl) E
    (RingHom.ext hE) (h p)

/-- The fibre of a localization over a prime of the base is geometrically regular over the
residue field there. -/
@[ega "IV 7.3.19" "more general"]
public lemma isGeometricallyRegular_fiber_of_isLocalization
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (p : PrimeSpectrum R) :
    Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
  constructor
  intro K _ _ _
  let : Algebra R K := ((algebraMap p.asIdeal.ResidueField K).comp
    (algebraMap R p.asIdeal.ResidueField)).toAlgebra
  let : IsScalarTower R p.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra S (K ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let : IsLocalization (Algebra.algebraMapSubmonoid K M) (K ⊗[R] S) :=
    (Algebra.isLocalization_iff_isPushout M S).mpr inferInstance
  let : IsRegularRing (K ⊗[R] S) :=
    IsRegularRing.of_isLocalization (Algebra.algebraMapSubmonoid K M) _
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange R p.asIdeal.ResidueField K K S).symm.toRingEquiv

end Stacks.FormalFibres

private lemma fibersHave_of_isLocalization
    (P : RingMapProperty.{u, max u v})
    {R T S : Type u} [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S]
    (M : Submonoid R) [IsLocalization M T]
    (h : ∀ p : PrimeSpectrum R,
      P.Holds.{u, u, 0, v} (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))) :
    ∀ q : PrimeSpectrum T,
      P.Holds.{u, u, 0, v} (algebraMap q.asIdeal.ResidueField (q.asIdeal.Fiber S)) := by
  intro q
  let p : PrimeSpectrum R := ⟨q.asIdeal.comap (algebraMap R T), inferInstance⟩
  let f : p.asIdeal.ResidueField →ₐ[R] q.asIdeal.ResidueField :=
    { Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R T) rfl with
      commutes' := fun r => by
        change Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R T) rfl
          (algebraMap R p.asIdeal.ResidueField r) = algebraMap R q.asIdeal.ResidueField r
        rw [Ideal.ResidueField.map_algebraMap, ← IsScalarTower.algebraMap_apply] }
  let e := AlgEquiv.ofBijective f
    ((RingHom.surjectiveOnStalks_of_isLocalization M T).residueFieldMap_bijective
      p.asIdeal q.asIdeal rfl)
  let E := (Algebra.TensorProduct.congr e (AlgEquiv.refl : S ≃ₐ[R] S)).toRingEquiv.trans
    (IsLocalization.algebraTensorEquiv M T q.asIdeal.ResidueField S).symm.toRingEquiv
  exact Stacks.FormalFibres.holds_of_equiv.{u, u, 0, v} P _ _ e.toRingEquiv E
    (by ext a; rfl) (h p)

/-- The property `P` ascends through regular maps: for a tower `A → B → C` of flat maps of
Noetherian rings whose formal fibres over `A` have `P` for `B` and all of whose fibres over `B`
are geometrically regular, the formal fibres over `A` have `P` for `C` as well. The target
universe `max u v` is the one in which the fibres live. -/
public abbrev RegularAscent (P : RingMapProperty.{u, max u v}) : Prop :=
  ∀ (A B C : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Module.Flat A B] [Module.Flat B C],
    (∀ p : PrimeSpectrum A,
      P.Holds.{u, u, 0, v} (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))) →
    (∀ q : PrimeSpectrum B,
      Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber C)) →
    ∀ p : PrimeSpectrum A,
      P.Holds.{u, u, 0, v} (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C))

/-- The property `P` descends through faithfully flat maps: for a tower `A → B → C` of
Noetherian rings with `B` flat over `A` and `C` faithfully flat over `B`, if the formal fibres
over `A` have `P` for `C` then they have `P` for `B` as well. The target universe `max u v` is
the one in which the fibres live. -/
@[ega "IV 7.3.4" "special case"]
public abbrev FaithfullyFlatDescent (P : RingMapProperty.{u, max u v}) : Prop :=
  ∀ (A B C : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Module.Flat A B] [Module.FaithfullyFlat B C],
    (∀ p : PrimeSpectrum A,
      P.Holds.{u, u, 0, v} (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C))) →
    ∀ p : PrimeSpectrum A,
      P.Holds.{u, u, 0, v} (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))

private lemma formalFibersHaveAt_localization
    (P : RingMapProperty.{u, max u v})
    (hC : RegularAscent P) (hD : FaithfullyFlatDescent P)
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : FormalFibersHaveAt.{u, 0, v} P A) (p : PrimeSpectrum A) :
    FormalFibersHaveAt.{u, 0, v} P (Localization.AtPrime p.asIdeal) := by
  let B := AdicCompletion (maximalIdeal A) A
  let : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨q, hq⟩ := (PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B)) p
  have hqp : p.asIdeal = q.asIdeal.under A := (congrArg PrimeSpectrum.asIdeal hq).symm
  let : q.asIdeal.LiesOver p.asIdeal := ⟨hqp⟩
  let Ap := Localization.AtPrime p.asIdeal
  let Bq := Localization.AtPrime q.asIdeal
  let T := AdicCompletion (maximalIdeal Bq) Bq
  let : Algebra Ap Bq := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  let : Algebra Ap T := ((algebraMap Bq T).comp (algebraMap Ap Bq)).toAlgebra
  let : IsScalarTower Ap Bq T := IsScalarTower.of_algebraMap_eq' rfl
  let hApt : IsScalarTower A Ap T := IsScalarTower.to₁₂₄ A Ap Bq T
  have hBq := hC A B Bq ((Stacks.FormalFibres.formalFibersHaveAt_iff P A).mp hA)
    (Stacks.FormalFibres.isGeometricallyRegular_fiber_of_isLocalization
      q.asIdeal.primeCompl)
  have hreg := (isGRing_of_isPrecomplete_maximalIdeal B).2 q.asIdeal
  rw [isRegularRingHom_algebraMap_iff] at hreg
  have hT := hC A Bq T hBq (fun r => (hreg.2 r.asIdeal).2)
  have hpT := @fibersHave_of_isLocalization P A Ap T _ _ _ _ _ _ hApt
    p.asIdeal.primeCompl _ hT
  let f : Ap →+* Bq := algebraMap Ap Bq
  let D := AdicCompletion (maximalIdeal Ap) Ap
  let g : D →+* T := adicCompletionMap f (maximalIdeal Ap) (maximalIdeal Bq)
    (map_maximalIdeal_le f)
  let : Algebra D T := g.toAlgebra
  let hAdt : IsScalarTower Ap D T := IsScalarTower.of_algebraMap_eq'
    (adicCompletionMap_comp_algebraMap f _ _ _).symm
  let : Module.Flat D T := (RingHom.flat_algebraMap_iff).mp
    ((adicCompletionMap_flat_iff f).mpr
      (RingHom.flat_algebraMap_iff.mpr inferInstance))
  let : IsLocalHom (algebraMap D T) := Stacks.FormalFibres.adicCompletionMap_isLocalHom f
  let : Module.FaithfullyFlat D T := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact (Stacks.FormalFibres.formalFibersHaveAt_iff P Ap).mpr
    (@hD Ap D T _ _ _ _ _ _ hAdt _ _ _ _ _ hpT)

private lemma isPRingAt_of_formalFibersHaveAt_maximal
    (P : RingMapProperty.{u, max u v})
    (hC : RegularAscent P) (hD : FaithfullyFlatDescent P)
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      FormalFibersHaveAt.{u, 0, v} P (Localization.AtPrime m)) :
    IsPRingAt.{u, 0, v} P R := by
  refine ⟨inferInstance, fun p => ?_⟩
  obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
  let : m.IsMaximal := hm
  let A := Localization.AtPrime m
  let q : Ideal A := p.asIdeal.map (algebraMap R A)
  let : q.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime m (S := A) hpm
  have hqp : q.comap (algebraMap R A) = p.asIdeal :=
    Ideal.under_map_of_isLocalizationAtPrime m (S := A) hpm
  let Aq := Localization.AtPrime q
  let : IsLocalization.AtPrime Aq p.asIdeal := by
    simpa only [hqp] using IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      m.primeCompl (T := Aq) q
  let e : Aq ≃+* Localization.AtPrime p.asIdeal :=
    (IsLocalization.algEquiv p.asIdeal.primeCompl Aq (Localization.AtPrime p.asIdeal)).toRingEquiv
  exact Stacks.FormalFibres.formalFibersHaveAt_of_ringEquiv.{u, u, 0, v} P e
    (formalFibersHaveAt_localization P hC hD A (h m) ⟨q, inferInstance⟩)

/-- For a property of ring maps satisfying ascent through regular maps and
faithfully flat descent, a Noetherian ring is a `P`-ring exactly when the formal fibres of its
localizations at maximal ideals have `P`. -/
@[stacks 0BIU]
public theorem isPRing_iff_formalFibersHave_localization_maximal
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (P : RingMapProperty.{max u v, max u v w})
    (hC : ∀ (A B C : Type (max u v))
      [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.Flat B C],
      (∀ p : PrimeSpectrum A,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))) →
      (∀ q : PrimeSpectrum B,
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber C)) →
      ∀ p : PrimeSpectrum A,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C)))
    (hD : ∀ (A B C : Type (max u v))
      [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.FaithfullyFlat B C],
      (∀ p : PrimeSpectrum A,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C))) →
      ∀ p : PrimeSpectrum A,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))) :
    IsPRingAt.{u, v, w} P R ↔
      ∀ (m : Ideal R) [m.IsMaximal],
        FormalFibersHaveAt.{u, v, w} P
          (Localization.AtPrime m) := by
  constructor
  · exact fun h m hm ↦ h.2 ⟨m, hm.isPrime⟩
  · intro h
    let R' := ULift.{v} R
    let e : R' ≃+* R := ULift.ringEquiv
    let : IsNoetherianRing R' :=
      isNoetherianRing_of_surjective R R' e.symm.toRingHom e.symm.surjective
    have h' : ∀ (m : Ideal R') [m.IsMaximal],
        FormalFibersHaveAt.{max u v, 0, w} P (Localization.AtPrime m) := by
      intro m hm
      let m₀ : Ideal R := m.comap e.symm.toRingHom
      let : m₀.IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
      exact Stacks.FormalFibres.formalFibersHaveAt_of_ringEquiv.{u, max u v, 0, w} P
        (Localization.localRingEquiv m₀ m e.symm rfl) (h m₀)
    have hR' := isPRingAt_of_formalFibersHaveAt_maximal P hC hD R' h'
    refine ⟨inferInstance, fun p => ?_⟩
    let p' : PrimeSpectrum R' := PrimeSpectrum.comap e.toRingHom p
    exact Stacks.FormalFibres.formalFibersHaveAt_of_ringEquiv.{max u v, u, 0, w} P
      (Localization.localRingEquiv p'.asIdeal p.asIdeal e rfl) (hR'.2 p')

end

section

universe u v w

end

end

/-! ### Fibres of adic completions -/

section

section

universe u

end

section

open IsLocalRing
open scoped TensorProduct

universe u

private theorem fibers_congr
    (P : RingMapProperty.{u, u})
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [IsNoetherianRing S] [IsNoetherianRing T]
    (e : S ≃ₐ[R] T) :
    FibersHaveProperty (fun f ↦ P f) R S →
      FibersHaveProperty (fun f ↦ P f) R T := by
  intro h p hp
  let ep : p.Fiber S ≃ₐ[p.ResidueField] p.Fiber T :=
    Algebra.TensorProduct.congr (AlgEquiv.refl) e
  convert P.respectsIso.1 _ ep.toRingEquiv (h p) using 1
  ext
  simp [ep]

private theorem formalFibersHave_to_fibersHaveProperty
    (P : RingMapProperty.{u, u})
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h : FormalFibersHave P R) :
    FibersHaveProperty (fun f ↦ P f) R
      (AdicCompletion (maximalIdeal R) R) := by
  intro p hp
  let e : AdicCompletion (maximalIdeal R) R ⊗[R] p.ResidueField ≃+*
      p.Fiber (AdicCompletion (maximalIdeal R) R) :=
    (Algebra.TensorProduct.comm R _ _).toRingEquiv
  have heq : algebraMap p.ResidueField
      (p.Fiber (AdicCompletion (maximalIdeal R) R)) =
      e.toRingHom.comp (Algebra.TensorProduct.includeRight).toRingHom :=
    congrArg AlgHom.toRingHom
      (Algebra.TensorProduct.comm_comp_includeRight R
        (AdicCompletion (maximalIdeal R) R) p.ResidueField).symm
  rw [heq]
  exact P.respectsIso.1 _ e (h ⟨p, hp⟩)

/-- The projection of the image of `a : A` in the `I`-adic completion to `A ⧸ I` is its class. -/
private theorem evalOneₐ_algebraMap {A : Type u} [CommRing A] (I : Ideal A) (a : A) :
    AdicCompletion.evalOneₐ I (algebraMap A (AdicCompletion I A) a) = Ideal.Quotient.mk I a :=
  rfl

/-- The kernel of the projection of the `I`-adic completion to `A ⧸ I` lies in any ideal `q`
containing the image of `I`. -/
private theorem ker_evalOneₐ_le_of_map_le {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (q : Ideal (AdicCompletion I A)) (h : I.map (algebraMap A _) ≤ q) :
    RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom ≤ q := by
  rw [AdicCompletion.ker_evalOneₐ_eq_map I I.fg_of_isNoetherianRing]
  exact h

namespace Stacks.FormalFibres

/-- A maximal ideal `q` of the `I`-adic completion of a Noetherian ring `A` contracts to a
maximal ideal `p` of `A` containing `I`, and `q` is recovered as the image of `p`. -/
public theorem completion_maximal_bridge
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (q : Ideal (AdicCompletion I A)) [q.IsMaximal] :
    let p := q.under A
    p.IsMaximal ∧ I ≤ p ∧
      p.map (algebraMap A (AdicCompletion I A)) = q := by
  dsimp only
  let p := q.under A
  have hcomplete := AdicCompletion.isAdicComplete_self I I.fg_of_isNoetherianRing
  have hIq : I.map (algebraMap A (AdicCompletion I A)) ≤ q :=
    (IsAdicComplete.le_jacobson_bot _).trans (by
      simpa [Ideal.jacobson_bot] using Ring.jacobson_le_of_isMaximal q)
  have hIp : I ≤ p := Ideal.map_le_iff_le_comap.mp hIq
  let ev := (AdicCompletion.evalOneₐ I).toRingHom
  let qbar := q.map ev
  have hqbar : qbar.IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le
      (AdicCompletion.evalOneₐ_surjective I) (ker_evalOneₐ_le_of_map_le I q hIq)
  have hq_comap : qbar.comap ev = q := by
    rw [Ideal.comap_map_of_surjective' ev (AdicCompletion.evalOneₐ_surjective I),
      sup_eq_left]
    exact ker_evalOneₐ_le_of_map_le I q hIq
  have hp_eq : p = qbar.comap (Ideal.Quotient.mk I) := by
    ext a
    change algebraMap A (AdicCompletion I A) a ∈ q ↔ Ideal.Quotient.mk I a ∈ qbar
    rw [← hq_comap]
    exact Iff.rfl
  have hp : p.IsMaximal := by
    rw [hp_eq]
    exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hpmap : (p.map (algebraMap A (AdicCompletion I A))).IsMaximal :=
    AdicCompletion.isMaximal_map_of_le I p hIp I.fg_of_isNoetherianRing
  have hpmap_le : p.map (algebraMap A (AdicCompletion I A)) ≤ q :=
    Ideal.map_le_iff_le_comap.mpr le_rfl
  exact ⟨hp, hIp,
    hpmap.eq_of_le (show q ≠ ⊤ from (inferInstance : q.IsMaximal).ne_top) hpmap_le⟩

/-- Localizing a Noetherian ring and its `I`-adic completion at a maximal ideal `q` of the
completion and its contraction gives a flat local map which identifies the maximal ideals and
the residue fields. -/
@[ega "IV 7.3.19" "partial"]
public theorem localized_completion_bridge
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (q : Ideal (AdicCompletion I A)) [q.IsMaximal] :
    let p := q.under A
    let R := Localization.AtPrime p
    let S := Localization.AtPrime q
    letI : Algebra R S := Localization.AtPrime.algebraOfLiesOver p q
    Module.Flat R S ∧
      Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S ∧
      Function.Bijective (ResidueField.map (algebraMap R S)) := by
  dsimp only
  let p := q.under A
  have hp : p.IsMaximal := (Stacks.FormalFibres.completion_maximal_bridge I q).1
  let : p.IsPrime := hp.isPrime
  let R := Localization.AtPrime p
  let S := Localization.AtPrime q
  let : Algebra R S := Localization.AtPrime.algebraOfLiesOver p q
  have hflat : Module.Flat R S := inferInstance
  have hmax : Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S := by
    calc
      Ideal.map (algebraMap R S) (maximalIdeal R) =
          p.map (algebraMap A S) := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
          ← IsScalarTower.algebraMap_eq]
      _ = q.map (algebraMap (AdicCompletion I A) S) := by
        rw [IsScalarTower.algebraMap_eq A (AdicCompletion I A) S,
          ← Ideal.map_map, (completion_maximal_bridge I q).2.2]
      _ = maximalIdeal S := Localization.AtPrime.map_eq_maximalIdeal
  refine ⟨hflat, hmax, ⟨RingHom.injective _, ?_⟩⟩
  have hker := ker_evalOneₐ_le_of_map_le I q
    ((Ideal.map_mono (completion_maximal_bridge I q).2.1).trans
      (completion_maximal_bridge I q).2.2.le)
  change Function.Surjective
    (Ideal.ResidueField.map p q (algebraMap A (AdicCompletion I A)) rfl)
  intro y
  obtain ⟨b, rfl⟩ := q.algebraMap_residueField_surjective y
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((AdicCompletion.evalOneₐ I) b)
  refine ⟨algebraMap A p.ResidueField a, ?_⟩
  rw [Ideal.ResidueField.map_algebraMap]
  have hmem : b - algebraMap A (AdicCompletion I A) a ∈ q := hker (by
    change (AdicCompletion.evalOneₐ I) (b - algebraMap A (AdicCompletion I A) a) = 0
    rw [map_sub, evalOneₐ_algebraMap, ha, sub_self])
  have hs := (Ideal.algebraMap_residueField_eq_zero).2 hmem
  rw [map_sub] at hs
  exact (sub_eq_zero.mp hs).symm

end Stacks.FormalFibres

private theorem completion_fibers_of_localization
    (P : RingMapProperty.{u, u})
    (hdescent : ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
      [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
      [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]
      [Module.Flat R S] [Module.FaithfullyFlat S T],
      FibersHaveProperty (fun f ↦ P f) R T →
        FibersHaveProperty (fun f ↦ P f) R S)
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (hA : IsPRing P A) (I : Ideal A)
    (q : Ideal (AdicCompletion I A)) [q.IsMaximal] :
    let p := q.under A
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver p q
    FibersHaveProperty (fun f ↦ P f)
      (Localization.AtPrime p) (Localization.AtPrime q) := by
  dsimp only
  let p := q.under A
  have hp : p.IsMaximal := (Stacks.FormalFibres.completion_maximal_bridge I q).1
  let : p.IsPrime := hp.isPrime
  let R := Localization.AtPrime p
  let S := Localization.AtPrime q
  let : Algebra R S := Localization.AtPrime.algebraOfLiesOver p q
  have hb := Stacks.FormalFibres.localized_completion_bridge I q
  let : Module.Flat R S := hb.1
  obtain ⟨e, he⟩ := exists_adicCompletion_ringEquiv_of_flat
    (A := R) (B := S) (maximalIdeal R).fg_of_isNoetherianRing hb.2.1 hb.2.2
  let T := AdicCompletion (maximalIdeal S) S
  let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hff : Module.FaithfullyFlat S T :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson
      (maximalIdeal S) (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal])
  let : Module.FaithfullyFlat S T := hff
  let e' : AdicCompletion (maximalIdeal R) R ≃ₐ[R] T :=
    { e with commutes' := he }
  have hTower : IsScalarTower R S T := inferInstance
  exact @hdescent R S T inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance hTower inferInstance inferInstance inferInstance hb.1 hff
    (fibers_congr P e' (formalFibersHave_to_fibersHaveProperty P (hA.2 ⟨p, inferInstance⟩)))

/-- If `A` is a `P`-ring, `P` is local for localization, and `P` descends
along faithfully flat maps in flat towers of Noetherian rings, then all fibres of the map from
`A` to its completion along any ideal have property `P`. -/
@[stacks 0BK9, ega "IV 7.4.6"]
public theorem fibersHaveProperty_adicCompletion_of_isPRing
    (P : RingMapProperty.{u, u})
    (hlocal : IsLocalForLocalization (fun f => P f))
    (hdescent : ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
      [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
      [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]
      [Module.Flat R S] [Module.FaithfullyFlat S T],
      FibersHaveProperty (fun f => P f) R T →
        FibersHaveProperty (fun f => P f) R S)
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (hA : IsPRing P A) (I : Ideal A) :
    FibersHaveProperty (fun f => P f) A (AdicCompletion I A) := by
  let hPiso : RespectsIsomorphisms (fun f => P f) :=
    ⟨fun f e h ↦ P.respectsIso.1 f e h, fun f e h ↦ P.respectsIso.2 f e h⟩
  rw [(fibersHaveProperty_iff_localizations_at_primes_and_maximals
    (fun f => P f) hPiso hlocal A (AdicCompletion I A)).1,
    (fibersHaveProperty_iff_localizations_at_primes_and_maximals
    (fun f => P f) hPiso hlocal A (AdicCompletion I A)).2]
  exact fun q hq ↦ completion_fibers_of_localization P hdescent hA I q

end

section

universe u

end

end

end
