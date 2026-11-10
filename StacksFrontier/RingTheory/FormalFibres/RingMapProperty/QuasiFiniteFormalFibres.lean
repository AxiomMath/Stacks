module

public import Mathlib
public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.Algebra.Category.Ring.Instances
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Field.ULift
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.RingTheory.AdicCompletion.QuotientCompletionMap
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.RingTheory.RingHomProperties
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Tactic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.QuasiFinite
public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.Kaehler.SmoothRingMapsInTheNoetherianCase

@[expose] public section

/-!
# Quasi-finite maps and properties of formal fibers

Stacks Project, Chapter 15 "More on Algebra", Tag 0BIT.

A property of homomorphisms from fields to Noetherian rings which is preserved by finitely
generated extensions of the ground field and can be checked after localization passes from the
formal fibers of a Noetherian ring to those of a finite-type algebra at a quasi-finite prime. In
particular, quasi-finite algebras over rings having the property on all formal fibers again have
that property on all formal fibers.

## Main definitions

* `RingMapProperty` is an isomorphism-invariant property of
  commutative-ring homomorphisms.
* `RingMapProperty.geometricallyRegular` extends geometric regularity from field maps
  to that interface; `geometricallyRegular_holds_iff` identifies its lifted interpretation with
  geometric regularity of the original map in independent universes.
* `FormalFibersHave` says that every fiber of the completion map of a local ring has a
  given property.
* `IsPRing` says that a ring is Noetherian and the formal fibers of all its local rings
  have a given property.

## Main results

* `quasiFinite_preserves_formalFiberProperty` gives the pointwise, local, and global
  preservation statements for a finite-type map which is quasi-finite at the chosen prime.

## Implementation notes

The property is represented as a predicate on ring homomorphisms and is required to respect
isomorphisms, as is implicit for a property of ring maps. Fibers use the canonical map from the
residue field into the tensor product. The primes downstairs are represented canonically by the
contractions of the chosen primes upstairs.

The canonical field structure on `ULift k` comes from `Mathlib.Algebra.Field.ULift` and extends
its canonical ring structure. The geometric-regularity specialization quantifies over field
presentations of the source, so it does not choose a field structure on an arbitrary ring.
Its coherence theorem also transports test fields between universes: an essentially finite type
field extension is small in the universe of its base, since it is a localization of a finite-type
subalgebra. Thus using `Holds` does not change which field extensions test geometric regularity.

## References

* [Stacks Project, Tag 0BIT](https://stacks.math.columbia.edu/tag/0BIT)

-/

/-! ### Stacks Tag 0BIT -/

section

section

open IsLocalRing
open scoped TensorProduct

universe u v w x

@[expose] public section

/-- An isomorphism-invariant property of homomorphisms of commutative rings, with independent
universes for the source and target. -/
public structure RingMapProperty where
  property : ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B], (A →+* B) → Prop
  respectsIso :
    (∀ {A : Type u} {B C : Type v} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (e : B ≃+* C), property f → property (e.toRingHom.comp f)) ∧
    (∀ {A B : Type u} {C : Type v} [CommRing A] [CommRing B] [CommRing C]
      (f : B →+* C) (e : A ≃+* B), property f → property (f.comp e.toRingHom))

/-- A `RingMapProperty` coerces to its underlying predicate on ring homomorphisms. -/
public instance : CoeFun (RingMapProperty.{u, v}) fun _ =>
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B], (A →+* B) → Prop :=
  ⟨RingMapProperty.property⟩

/-- Interpret a property on a map whose rings lie in arbitrary universes. The canonical
`ULift` ring equivalences preserve the chosen presentation up to isomorphism. For field sources,
`ULift.field` extends the canonical lifted ring structure; see `geometricallyRegular_holds_iff`
for the geometric-regularity specialization across independent universes. -/
public def RingMapProperty.Holds
    (P : RingMapProperty.{max u v w, max u v w x})
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  P (RingHom.ulift.{max u v w, max u v w x} f)

/-- At the original universe level, interpreting a property through `ULift` does not change it. -/
public theorem RingMapProperty.ulift_iff
    (P : RingMapProperty.{u, v})
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) :
    P (RingHom.ulift.{u, v} f) ↔ P f := by
  constructor
  · intro h
    simpa only [RingHom.comp_ulift_eq] using P.respectsIso.1 _ ULift.ringEquiv
      (P.respectsIso.2 (RingHom.ulift.{u, v} f) ULift.ringEquiv.symm h)
  · intro h
    exact P.respectsIso.1 _ ULift.ringEquiv.symm
      (P.respectsIso.2 f ULift.ringEquiv h)

namespace Stacks.FormalFibres

/-- **Geometric regularity is a universe-independent condition.** If `A` is geometrically regular
over `k`, then `K ⊗[k] A` is a regular ring for every essentially finite type `k`-algebra `K`
which is a field, in any universe, whereas `Algebra.IsGeometricallyRegular` asserts this only for
a test field in the universe of `k`. The test ring carries `IsField` as a hypothesis rather than a
`Field` instance, so that it also applies to a ring whose field structure is the conclusion of a
lemma rather than an instance.

This is `Stacks.GeometricallyRegular.SeparableBase.isRegularRing_tensorProduct`, which is not
reachable from this module; the two proofs differ, this one shrinking the test field to the
universe of `k` and that one moving it into `AlgebraicClosure k`. -/
public lemma geometricallyRegular_tensorProduct
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (h : Algebra.IsGeometricallyRegular k A)
    (K : Type w) [CommRing K] [Algebra k K] [Algebra.EssFiniteType k K] (hK : IsField K) :
    IsRegularRing (K ⊗[k] A) := by
  let _fieldK : Field K := hK.toField
  let : Small.{u} (Algebra.EssFiniteType.subalgebra k K) := Algebra.FiniteType.small (R := k)
  let : Small.{u} K := small_of_surjective
    (IsLocalization.mk'_surjective (Algebra.EssFiniteType.submonoid k K))
  let _ : Field (Shrink.{u} K) := inferInstance
  let _ : Algebra k (Shrink.{u} K) := inferInstance
  let e : Shrink.{u} K ≃ₐ[k] K := Shrink.algEquiv k K
  let : Algebra.EssFiniteType k (Shrink.{u} K) :=
    Algebra.EssFiniteType.of_surjective e.symm.toAlgHom e.symm.surjective
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.congr e (AlgEquiv.refl : A ≃ₐ[k] A)).toRingEquiv

end Stacks.FormalFibres

private lemma geometricallyRegular_comp_ringEquiv
    {R : Type u} {S : Type v} {A : Type w} [Field R] [Field S] [CommRing A]
    (f : S →+* A) (e : R ≃+* S)
    (h : @Algebra.IsGeometricallyRegular S A _ _ f.toAlgebra) :
    @Algebra.IsGeometricallyRegular R A _ _ (f.comp e.toRingHom).toAlgebra := by
  let _ : Algebra R A := (f.comp e.toRingHom).toAlgebra
  refine { isRegularRing_tensorProduct := ?_ }
  intro K _ _ _
  let _ : Algebra R S := e.toRingHom.toAlgebra
  let _ : Algebra S A := f.toAlgebra
  let _ : Algebra S K := ((algebraMap R K).comp e.symm.toRingHom).toAlgebra
  let _ : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change algebraMap R K x = algebraMap R K (e.symm (e x))
    rw [e.symm_apply_apply])
  let _ : Algebra.EssFiniteType S K := Algebra.EssFiniteType.of_comp R S K
  let _ : TensorProduct.CompatibleSMul R S K A := by
    constructor
    intro s k a
    obtain ⟨r, rfl⟩ := e.surjective s
    change (algebraMap S K (e r) * k) ⊗ₜ[R] a =
      k ⊗ₜ[R] (algebraMap S A (e r) * a)
    rw [show algebraMap S K (e r) = algebraMap R K r from
        (IsScalarTower.algebraMap_apply R S K r).symm,
      show algebraMap S A (e r) = algebraMap R A r from
        (IsScalarTower.algebraMap_apply R S A r).symm,
      ← Algebra.smul_def, ← Algebra.smul_def]
    exact TensorProduct.smul_tmul r k a
  let E := Algebra.TensorProduct.equivOfCompatibleSMul R S S K A
  let _ : IsRegularRing (K ⊗[S] A) :=
    Stacks.FormalFibres.geometricallyRegular_tensorProduct h K (Field.toIsField K)
  exact IsRegularRing.of_ringEquiv E.toRingEquiv

private lemma geometricallyRegular_comp_ringEquiv_target
    {R : Type u} {S : Type v} {T : Type w} [Field R] [CommRing S] [CommRing T]
    (f : R →+* S) (e : S ≃+* T)
    (h : @Algebra.IsGeometricallyRegular R S _ _ f.toAlgebra) :
    @Algebra.IsGeometricallyRegular R T _ _ (e.toRingHom.comp f).toAlgebra := by
  let _ : Algebra R T := (e.toRingHom.comp f).toAlgebra
  refine { isRegularRing_tensorProduct := ?_ }
  intro K _ _ _
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra R T := (e.toRingHom.comp f).toAlgebra
  let ea : S ≃ₐ[R] T := AlgEquiv.ofRingEquiv (f := e) fun _ => rfl
  let E := Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[R] K) ea
  let _ : IsRegularRing (K ⊗[R] S) := h.isRegularRing_tensorProduct K
  exact IsRegularRing.of_ringEquiv E.toRingEquiv

/-- Geometric regularity as a property of ring maps. Quantifying over field presentations of the
source avoids choosing any field structure on an arbitrary commutative ring. -/
public def RingMapProperty.geometricallyRegular : RingMapProperty.{u, v} where
  property := fun {R A} _ _ f =>
    ∀ (k : Type u) [Field k] (e : k ≃+* R),
      @Algebra.IsGeometricallyRegular k A _ _ (f.comp e.toRingHom).toAlgebra
  respectsIso := by
    constructor
    · intro R S T _ _ _ f e h k _ ek
      exact geometricallyRegular_comp_ringEquiv_target (f.comp ek.toRingHom) e (h k ek)
    · intro R S T _ _ _ f e h k _ ek
      convert h k (ek.trans e) using 1
      exact Algebra.algebra_ext _ _ fun _ => rfl

/-- On a field map, the geometric-regularity property uses the original field structure. -/
public theorem RingMapProperty.geometricallyRegular_iff
    {k : Type u} {A : Type v} [Field k] [CommRing A] (f : k →+* A) :
    RingMapProperty.geometricallyRegular f ↔
      @Algebra.IsGeometricallyRegular k A _ _ f.toAlgebra := by
  constructor
  · intro h
    convert h k (RingEquiv.refl k) using 1
    exact Algebra.algebra_ext _ _ fun _ => rfl
  · intro h K _ e
    exact geometricallyRegular_comp_ringEquiv f e h

/-- Lifting a field map to the universes of the property preserves geometric regularity.
The field structure and finitely generated test extensions are transported by equivalences. -/
public theorem RingMapProperty.geometricallyRegular_holds_iff
    {k : Type u} {A : Type v} [Field k] [CommRing A] (f : k →+* A) :
    RingMapProperty.geometricallyRegular.Holds.{u, v, w, x} f ↔
      @Algebra.IsGeometricallyRegular k A _ _ f.toAlgebra := by
  rw [RingMapProperty.Holds, RingMapProperty.geometricallyRegular_iff]
  constructor
  · intro h
    have h' := geometricallyRegular_comp_ringEquiv (RingHom.ulift f)
      ULift.ringEquiv.symm h
    have h'' := geometricallyRegular_comp_ringEquiv_target _ ULift.ringEquiv h'
    convert h'' using 1
    exact Algebra.algebra_ext _ _ fun _ => rfl
  · intro h
    exact geometricallyRegular_comp_ringEquiv_target _ ULift.ringEquiv.symm
      (geometricallyRegular_comp_ringEquiv f ULift.ringEquiv h)

/-- Formal fibres with a property interpreted at an independent universe level. -/
public def FormalFibersHaveAt (P : RingMapProperty.{max u w, max u w x}) (A : Type u)
    [CommRing A] [IsLocalRing A] : Prop :=
  ∀ q : PrimeSpectrum A,
    P.Holds (Algebra.TensorProduct.includeRight (R := A)
      (A := AdicCompletion (maximalIdeal A) A) (B := q.asIdeal.ResidueField)).toRingHom

/-- A `P`-ring with its property interpreted at an independent universe level. -/
public def IsPRingAt (P : RingMapProperty.{max u w, max u w x}) (R : Type u)
    [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ p : PrimeSpectrum R, FormalFibersHaveAt P (Localization.AtPrime p.asIdeal)

/-- Every fiber of the completion map of the local ring `A` has property `P`. -/
public def FormalFibersHave (P : RingMapProperty.{u, u}) (A : Type u)
    [CommRing A] [IsLocalRing A] : Prop :=
  ∀ q : PrimeSpectrum A,
    P (Algebra.TensorProduct.includeRight (R := A)
      (A := AdicCompletion (maximalIdeal A) A) (B := q.asIdeal.ResidueField)).toRingHom

/-- The defining pointwise characterization of `FormalFibersHave`. -/
@[simp]
public theorem formalFibersHave_iff (P : RingMapProperty.{u, u}) (A : Type u)
    [CommRing A] [IsLocalRing A] :
    FormalFibersHave P A ↔ ∀ q : PrimeSpectrum A,
      P (Algebra.TensorProduct.includeRight (R := A)
        (A := AdicCompletion (maximalIdeal A) A) (B := q.asIdeal.ResidueField)).toRingHom :=
  Iff.rfl

/-- A `P`-ring is a Noetherian ring whose local rings have property `P` on all formal fibers. -/
public def IsPRing (P : RingMapProperty.{u, u}) (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ p : PrimeSpectrum R, FormalFibersHave P (Localization.AtPrime p.asIdeal)

/-- The defining characterization of a `P`-ring. -/
@[simp]
public theorem isPRing_iff (P : RingMapProperty.{u, u}) (R : Type u) [CommRing R] :
    IsPRing P R ↔ IsNoetherianRing R ∧
      ∀ p : PrimeSpectrum R, FormalFibersHave P (Localization.AtPrime p.asIdeal) :=
  Iff.rfl

end

end

section

open IsLocalRing
open scoped TensorProduct

universe u v w x a b c d

private lemma holds_of_equiv
    (P : RingMapProperty.{max a b c d w, max a b c d w x})
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : C →+* D) (e : A ≃+* C) (E : B ≃+* D)
    (h : E.toRingHom.comp f = g.comp e.toRingHom)
    (hf : P.Holds.{a, b, max c d w, x} f) :
    P.Holds.{c, d, max a b w, x} g := by
  let e' : ULift.{max a b c d w} C ≃+* ULift.{max a b c d w} A :=
    ULift.ringEquiv.trans (e.symm.trans ULift.ringEquiv.symm)
  let E' : ULift.{max a b c d w x} B ≃+* ULift.{max a b c d w x} D :=
    ULift.ringEquiv.trans (E.trans ULift.ringEquiv.symm)
  have hh := P.respectsIso.2 _ e' (P.respectsIso.1 _ E' hf)
  have heq : (E'.toRingHom.comp (RingHom.ulift f)).comp e'.toRingHom =
      RingHom.ulift.{max a b c d w, max a b c d w x} g := by
    apply RingHom.ext
    intro z
    apply ULift.ext
    exact (congrArg (fun t : A →+* D => t (e.symm z.down)) h).trans (by simp)
  change P (RingHom.ulift g)
  rw [← heq]
  exact hh

/-- Commuting a tensor product turns `includeRight` into `algebraMap` without changing whether
the property holds. -/
private lemma holds_includeRight_iff_algebraMap
    (P : RingMapProperty.{max b c w, max b c w x})
    (R : Type a) (A : Type b) (B : Type c) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    P.Holds.{c, max b c, w, x}
        (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom ↔
      P.Holds.{c, max b c, w, x} (algebraMap B (B ⊗[R] A)) :=
  ⟨holds_of_equiv.{w, x, c, max b c, c, max b c} P _ _ (RingEquiv.refl _)
      (Algebra.TensorProduct.comm R A B).toRingEquiv (RingHom.ext fun _ => rfl),
    holds_of_equiv.{w, x, c, max b c, c, max b c} P _ _ (RingEquiv.refl _)
      (Algebra.TensorProduct.comm R B A).toRingEquiv (RingHom.ext fun _ => rfl)⟩

/-- The property holds on the structure map of an algebra and of any algebra isomorphic to it. -/
private lemma holds_of_algEquiv
    (P : RingMapProperty.{max a b d w, max a b d w x})
    {K : Type a} {B : Type b} {D : Type d} [CommRing K] [CommRing B] [CommRing D]
    [Algebra K B] [Algebra K D] (E : B ≃ₐ[K] D)
    (h : P.Holds.{a, b, max d w, x} (algebraMap K B)) :
    P.Holds.{a, d, max b w, x} (algebraMap K D) :=
  holds_of_equiv.{w, x, a, b, a, d} P _ _ (RingEquiv.refl _) E.toRingEquiv
    E.toAlgHom.comp_algebraMap h

namespace Stacks.FormalFibres

/-- A property of maps out of fields which can be checked after localizing at every prime of the
target passes along a localization of Noetherian algebras over a field. -/
public lemma property_of_isLocalization
    (P : RingMapProperty.{u, v})
    (hlocal : ∀ (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
      [IsNoetherianRing A],
      (∀ q : PrimeSpectrum A, P (algebraMap k (Localization.AtPrime q.asIdeal))) ↔
        P (algebraMap k A))
    (k : Type u) (A B : Type v) [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (M : Submonoid A) [IsLocalization M B] (h : P (algebraMap k A)) :
    P (algebraMap k B) := by
  apply (hlocal k B).mp
  intro q
  let p : PrimeSpectrum A := ⟨q.asIdeal.comap (algebraMap A B), inferInstance⟩
  let : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) p.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q.asIdeal) q.asIdeal
  let e := (IsLocalization.algEquiv p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).restrictScalars k
  have hh := P.respectsIso.1 _ e.toRingEquiv ((hlocal k A).mpr h p)
  have heq : e.toRingEquiv.toRingHom.comp (algebraMap k _) = algebraMap k _ :=
    e.toAlgHom.comp_algebraMap
  exact heq ▸ hh

end Stacks.FormalFibres

attribute [local instance] ULift.algebra'

private lemma holds_prod_fst
    (P : RingMapProperty.{max u v w a, max u v w a x})
    (hlocal : ∀ (k : Type (max u v w a)) (A : Type (max u v w a x))
      [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A],
      (∀ q : PrimeSpectrum A, P (algebraMap k (Localization.AtPrime q.asIdeal))) ↔
        P (algebraMap k A))
    (k : Type u) (A : Type v) (B : Type w) [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsNoetherianRing (A × B)]
    (h : P.Holds.{u, max v w, a, x} (algebraMap k (A × B))) :
    P.Holds.{u, v, max w a, x} (algebraMap k A) := by
  let k' := ULift.{max u v w a} k
  let A' := ULift.{max u v w a x} A
  let B' := ULift.{max u v w a x} B
  let E : ULift.{max u v w a x} (A × B) ≃+* A' × B' :=
    ULift.ringEquiv.trans (RingEquiv.prodCongr ULift.ringEquiv.symm ULift.ringEquiv.symm)
  let : IsNoetherianRing (A' × B') :=
    isNoetherianRing_of_ringEquiv (A × B)
      (RingEquiv.prodCongr ULift.ringEquiv.symm ULift.ringEquiv.symm)
  let : IsNoetherianRing A' := isNoetherianRing_of_surjective (A' × B') A'
    (RingHom.fst A' B') Prod.fst_surjective
  have hh : P (algebraMap k' (A' × B')) := P.respectsIso.1 _ E h
  let : Algebra (A' × B') A' := (RingHom.fst A' B').toAlgebra
  let : IsScalarTower k' (A' × B') A' := IsScalarTower.of_algebraMap_eq' rfl
  exact Stacks.FormalFibres.property_of_isLocalization P hlocal k' (A' × B') A'
    (Submonoid.powers (1, 0)) hh

private lemma holds_baseChange
    (P : RingMapProperty.{max u v w, max u v w x})
    (hbaseChange : ∀ (k K : Type (max u v w)) (A : Type (max u v w x))
      [Field k] [Field K] [CommRing A] [Algebra k K] [Algebra k A]
      [IsNoetherianRing A] [Algebra.EssFiniteType k K]
      [IsNoetherianRing (A ⊗[k] K)], P (algebraMap k A) →
        P (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := K)).toRingHom)
    (k A : Type u) (K : Type v) [Field k] [CommRing A] [Field K]
    [Algebra k A] [Algebra k K] [IsNoetherianRing A] [Algebra.EssFiniteType k K]
    [IsNoetherianRing (K ⊗[k] A)]
    (h : P.Holds.{u, u, max v w, x} (algebraMap k A)) :
    P.Holds.{v, max u v, w, x} (algebraMap K (K ⊗[k] A)) := by
  let k' := ULift.{max u v w} k
  let K' := ULift.{max u v w} K
  let A' := ULift.{max u v w x} A
  let : IsNoetherianRing A' := isNoetherianRing_of_ringEquiv A ULift.ringEquiv.symm
  let : Algebra.EssFiniteType k K' :=
    Algebra.EssFiniteType.of_surjective (ULift.algEquiv.symm : K ≃ₐ[k] K').toAlgHom
      ULift.ringEquiv.symm.surjective
  let : Algebra.FiniteType k' k :=
    Algebra.FiniteType.of_surjective (Algebra.ofId k' k) ULift.down_surjective
  let : IsScalarTower k' k K' := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.EssFiniteType k' K' := Algebra.EssFiniteType.comp k' k K'
  let E : K' ⊗[k'] A' ≃+* ULift.{max u v w x} (K ⊗[k] A) :=
    (Algebra.TensorProduct.uliftEquiv k k K A).symm.toRingEquiv
  let : IsNoetherianRing (K' ⊗[k'] A') :=
    isNoetherianRing_of_ringEquiv (K ⊗[k] A) (E.trans ULift.ringEquiv).symm
  let : IsNoetherianRing (A' ⊗[k'] K') :=
    isNoetherianRing_of_ringEquiv (K' ⊗[k'] A')
      (Algebra.TensorProduct.comm k' K' A').toRingEquiv
  have hh := hbaseChange k' K' A' h
  exact P.respectsIso.1 _ ((Algebra.TensorProduct.comm k' A' K').toRingEquiv.trans E) hh

namespace Stacks.FormalFibres

/-- A tensor product `A ⊗[R] B` is Noetherian when `A` is essentially of finite type over `R`
and `B` is Noetherian. -/
public lemma isNoetherianRing_tensorProduct_right
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.EssFiniteType R A] [IsNoetherianRing B] :
    IsNoetherianRing (A ⊗[R] B) := by
  let : IsNoetherianRing (B ⊗[R] A) :=
    Algebra.EssFiniteType.isNoetherianRing B (B ⊗[R] A)
  exact isNoetherianRing_of_ringEquiv (B ⊗[R] A)
    (Algebra.TensorProduct.comm R B A).toRingEquiv

end Stacks.FormalFibres

private lemma holds_fiber_localization_iff
    (P : RingMapProperty.{max u w, max u w x})
    (R L C : Type u) [CommRing R] [CommRing L] [CommRing C]
    [Algebra R L] [Algebra R C] [Algebra L C] [IsScalarTower R L C]
    (M : Submonoid R) [IsLocalization M L] (q : PrimeSpectrum L) :
    P.Holds.{u, u, w, x} (algebraMap (q.asIdeal.under R).ResidueField
      ((q.asIdeal.under R).ResidueField ⊗[R] C)) ↔
    P.Holds.{u, u, w, x} (algebraMap q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[L] C)) := by
  let p := q.asIdeal.under R
  let f : p.ResidueField →ₐ[R] q.asIdeal.ResidueField :=
    { Ideal.ResidueField.map p q.asIdeal (algebraMap R L) rfl with
      commutes' := fun r => by
        change Ideal.ResidueField.map p q.asIdeal (algebraMap R L) rfl
          (algebraMap R p.ResidueField r) = algebraMap R q.asIdeal.ResidueField r
        rw [Ideal.ResidueField.map_algebraMap, ← IsScalarTower.algebraMap_apply] }
  let e := AlgEquiv.ofBijective f
    ((RingHom.surjectiveOnStalks_of_isLocalization M L).residueFieldMap_bijective
      p q.asIdeal rfl)
  let E := (Algebra.TensorProduct.congr e (AlgEquiv.refl : C ≃ₐ[R] C)).toRingEquiv.trans
    (IsLocalization.algebraTensorEquiv M L q.asIdeal.ResidueField C).symm.toRingEquiv
  have hE : ∀ z, E (algebraMap p.ResidueField (p.ResidueField ⊗[R] C) z) =
      algebraMap q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[L] C) (e z) :=
    fun _ => rfl
  constructor
  · exact holds_of_equiv.{w, x, u, u, u, u} P _ _ e.toRingEquiv E (RingHom.ext hE)
  · apply holds_of_equiv.{w, x, u, u, u, u} P _ _ e.symm.toRingEquiv E.symm
    apply RingHom.ext
    intro z
    apply E.injective
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.apply_symm_apply] using (hE (e.symm z)).symm

private lemma formalFibersHaveAt_localization_iff
    (P : RingMapProperty.{max u w, max u w x})
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :
    FormalFibersHaveAt.{u, w, x} P (Localization.AtPrime p) ↔
      ∀ q : PrimeSpectrum R, q.asIdeal ≤ p →
        P.Holds.{u, u, w, x} (algebraMap q.asIdeal.ResidueField
          (q.asIdeal.ResidueField ⊗[R]
            AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))) := by
  let L := Localization.AtPrime p
  let C := AdicCompletion (maximalIdeal L) L
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso L p
  constructor
  · intro h q hq
    let ql := e.symm ⟨q, hq⟩
    have heq : ql.asIdeal.under R = q.asIdeal :=
      congrArg (fun z => z.val.asIdeal) (e.apply_symm_apply ⟨q, hq⟩)
    have hl : P.Holds.{u, u, w, x}
        (algebraMap ql.asIdeal.ResidueField (ql.asIdeal.ResidueField ⊗[L] C)) :=
      (holds_includeRight_iff_algebraMap.{w, x, u, u, u} P L C _).mp (h ql)
    have hr := (holds_fiber_localization_iff P R L C p.primeCompl ql).mpr hl
    let E := Ideal.residueFieldAlgEquiv (ql.asIdeal.under R) q.asIdeal
      (AlgEquiv.refl : R ≃ₐ[R] R) (heq.trans (by ext; rfl))
    exact holds_of_equiv.{w, x, u, u, u, u} P _ _ E.toRingEquiv
      (Algebra.TensorProduct.congr E (AlgEquiv.refl : C ≃ₐ[R] C)).toRingEquiv
      (RingHom.ext fun _ => rfl) hr
  · intro h ql
    have hr := h ⟨ql.asIdeal.under R, inferInstance⟩ (e ql).property
    have hl := (holds_fiber_localization_iff P R L C p.primeCompl ql).mp hr
    exact (holds_includeRight_iff_algebraMap.{w, x, u, u, u} P L C _).mpr hl

section

variable (P : RingMapProperty.{max u v w, max u v w x})
    (hbaseChange : ∀ (k K : Type (max u v w)) (A : Type (max u v w x))
      [Field k] [Field K] [CommRing A]
      [Algebra k K] [Algebra k A] [IsNoetherianRing A] [Algebra.EssFiniteType k K]
      [IsNoetherianRing (A ⊗[k] K)],
      P (algebraMap k A) →
        P (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := K)).toRingHom)
    (hlocal : ∀ (k : Type (max u v w)) (A : Type (max u v w x))
      [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A],
      (∀ q : PrimeSpectrum A,
        P (algebraMap k (Localization.AtPrime q.asIdeal))) ↔ P (algebraMap k A))

include hbaseChange hlocal

set_option maxHeartbeats 800000 in
-- The iterated tensor products require comparing several canonical scalar-tower structures.
private lemma holds_fiber_of_quasiFiniteAt
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S]
    (q' p' : Ideal S) [q'.IsPrime] [p'.IsPrime] [Algebra.QuasiFiniteAt R p']
    (h : P.Holds.{u, u, max v w, x} (algebraMap (Ideal.under R q').ResidueField
      ((Ideal.under R q').ResidueField ⊗[R]
        AdicCompletion (maximalIdeal (Localization.AtPrime (Ideal.under R p')))
          (Localization.AtPrime (Ideal.under R p'))))) :
    P.Holds.{v, v, max u w, x} (algebraMap q'.ResidueField
      (q'.ResidueField ⊗[S] AdicCompletion (maximalIdeal (Localization.AtPrime p'))
        (Localization.AtPrime p'))) := by
  let q := Ideal.under R q'
  let p := Ideal.under R p'
  let C := AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)
  let D := AdicCompletion (maximalIdeal (Localization.AtPrime p')) (Localization.AtPrime p')
  let k := q.ResidueField
  let K := q'.ResidueField
  let := Localization.AtPrime.algebraOfLiesOver q q'
  let : Algebra.EssFiniteType R K := Algebra.EssFiniteType.comp R S K
  let : IsNoetherianRing (k ⊗[R] C) :=
    Stacks.FormalFibres.isNoetherianRing_tensorProduct_right R k C
  let : IsNoetherianRing (K ⊗[k] (k ⊗[R] C)) :=
    Stacks.FormalFibres.isNoetherianRing_tensorProduct_right k K (k ⊗[R] C)
  have hb := holds_baseChange P hbaseChange k (k ⊗[R] C) K h
  let E₁ : K ⊗[k] (k ⊗[R] C) ≃ₐ[K] K ⊗[R] C :=
    Algebra.TensorProduct.cancelBaseChange R k K K C
  have h₁ : P.Holds.{v, max u v, w, x} (algebraMap K (K ⊗[R] C)) :=
    holds_of_algEquiv.{w, x, v, max u v, max u v} P E₁ hb
  obtain ⟨e, _, ⟨E₂⟩⟩ :=
    AdicCompletion.exists_isIdempotentElem_nonempty_algEquiv_prod_quotient p p'
      (Localization.AtPrime p) (Localization.AtPrime p')
  let B := (S ⊗[R] C) ⧸ Ideal.span {e}
  let : CommRing B := inferInstance
  let : Algebra S B := inferInstance
  let : Algebra K (K ⊗[S] B) := Algebra.TensorProduct.leftAlgebra
  let E₃ : K ⊗[R] C ≃ₐ[K] (K ⊗[S] D) × (K ⊗[S] B) :=
    (Algebra.TensorProduct.cancelBaseChange R S K K C).symm.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) E₂).trans
        (Algebra.TensorProduct.prodRight S K K D B))
  let : IsNoetherianRing (K ⊗[R] C) :=
    Stacks.FormalFibres.isNoetherianRing_tensorProduct_right R K C
  let : IsNoetherianRing ((K ⊗[S] D) × (K ⊗[S] B)) :=
    isNoetherianRing_of_ringEquiv (K ⊗[R] C) E₃.toRingEquiv
  have h₃ : P.Holds.{v, max u v, w, x} (algebraMap K ((K ⊗[S] D) × (K ⊗[S] B))) :=
    holds_of_algEquiv.{w, x, v, max u v, max u v} P E₃ h₁
  exact holds_prod_fst.{v, v, max u v, x, w} P hlocal K (K ⊗[S] D) (K ⊗[S] B) h₃

private lemma formalFibersHaveAt_of_quasiFiniteAt
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S]
    (p' : Ideal S) [p'.IsPrime] [Algebra.QuasiFiniteAt R p']
    (h : FormalFibersHaveAt.{u, max v w, x} P
      (Localization.AtPrime (p'.under R))) :
    FormalFibersHaveAt.{v, max u w, x} P (Localization.AtPrime p') := by
  apply (formalFibersHaveAt_localization_iff.{v, max u w, x} P S p').mpr
  intro q' hq'
  apply holds_fiber_of_quasiFiniteAt.{u, v, w, x} P hbaseChange hlocal (R := R) q'.asIdeal p'
  exact (formalFibersHaveAt_localization_iff.{u, max v w, x} P R (p'.under R)).mp h
    ⟨q'.asIdeal.under R, inferInstance⟩ (Ideal.comap_mono hq')

end

/-- **Stacks 0BIT.** Let `R → S` be a finite-type map of Noetherian rings and let
`q' ⊆ p'` be primes of `S`. If the map is quasi-finite at `p'`, then a property of
field-to-Noetherian-ring maps satisfying base change along finitely generated field extensions
and detection on localizations passes from the relevant formal fiber over `R` to that over `S`.
Consequently it passes between the formal fibers of the two local rings, and a quasi-finite
`R`-algebra over a `P`-ring is a `P`-ring. -/
@[stacks 0BIT]
public theorem quasiFinite_preserves_formalFiberProperty
    (P : RingMapProperty.{max u v w, max u v w x})
    (hbaseChange : ∀ (k K : Type (max u v w)) (A : Type (max u v w x))
      [Field k] [Field K] [CommRing A]
      [Algebra k K] [Algebra k A] [IsNoetherianRing A] [Algebra.EssFiniteType k K]
      [IsNoetherianRing (A ⊗[k] K)],
      P (algebraMap k A) →
        P (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := K)).toRingHom)
    (hlocal : ∀ (k : Type (max u v w)) (A : Type (max u v w x))
      [Field k] [CommRing A] [Algebra k A]
      [IsNoetherianRing A],
      (∀ q : PrimeSpectrum A,
        P (algebraMap k (Localization.AtPrime q.asIdeal))) ↔ P (algebraMap k A))
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.FiniteType R S]
    (q' p' : Ideal S) [q'.IsPrime] [p'.IsPrime] (_hq'p' : q' ≤ p')
    [Algebra.QuasiFiniteAt R p'] :
    (P.Holds.{u, u, max v w, x} (Algebra.TensorProduct.includeRight (R := R)
        (A := AdicCompletion (maximalIdeal (Localization.AtPrime (Ideal.under R p')))
          (Localization.AtPrime (Ideal.under R p')))
        (B := (Ideal.under R q').ResidueField)).toRingHom →
      P.Holds.{v, v, max u w, x} (Algebra.TensorProduct.includeRight (R := S)
        (A := AdicCompletion (maximalIdeal (Localization.AtPrime p'))
          (Localization.AtPrime p')) (B := q'.ResidueField)).toRingHom) ∧
    (FormalFibersHaveAt.{u, max v w, x} P
        (Localization.AtPrime (Ideal.under R p')) →
      FormalFibersHaveAt.{v, max u w, x} P (Localization.AtPrime p')) ∧
    (Algebra.QuasiFinite R S → IsPRingAt.{u, max v w, x} P R →
      IsPRingAt.{v, max u w, x} P S) := by
  refine ⟨?_,
    formalFibersHaveAt_of_quasiFiniteAt.{u, v, w, x} P hbaseChange hlocal (R := R) p', ?_⟩
  · intro h
    have h₂ := holds_fiber_of_quasiFiniteAt.{u, v, w, x} P hbaseChange hlocal (R := R) q' p'
      ((holds_includeRight_iff_algebraMap.{max v w, x, u, u, u} P R _ _).mp h)
    exact (holds_includeRight_iff_algebraMap.{max u w, x, v, v, v} P S _ _).mpr h₂
  · intro hQ hR
    let := hQ
    refine ⟨inferInstance, ?_⟩
    intro p
    exact formalFibersHaveAt_of_quasiFiniteAt.{u, v, w, x} P hbaseChange hlocal (R := R) p.asIdeal
      (hR.2 ⟨p.asIdeal.under R, inferInstance⟩)

end

end

end
