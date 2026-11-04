module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.FormalFibres.Examples
public import StacksFrontier.RingTheory.FormalFibres.Henselization
public import StacksFrontier.RingTheory.FormalFibres.Localization
public import StacksFrontier.RingTheory.GeometricallyReduced.Separable
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties
public import StacksFrontier.RingTheory.Nagata.Defs
public import StacksFrontier.RingTheory.Nagata.Japanese

/-!
# Henselization and strict henselization of a local ring

A henselization and a strict henselization of a local ring inherit reducedness and the Nagata
property from it, and neither changes the Krull dimension. In particular the henselization and
the strict henselization of a reduced one-dimensional Nagata local ring are again reduced,
one-dimensional and Nagata.

## Main results

* `IsLocalRing.IsHenselization.isReduced`, `IsLocalRing.IsHenselization.isNagataRing` and
  `IsLocalRing.IsHenselization.ringKrullDim_eq` treat a henselization.
* `IsLocalRing.strictHenselization_isReduced`,
  `IsLocalRing.strictHenselization_isNagataRing` and
  `IsLocalRing.strictHenselization_ringKrullDim` treat a strict henselization.

## References

* [Stacks Project, Tag 0C3V](https://stacks.math.columbia.edu/tag/0C3V)
-/

@[expose] public section

open CategoryTheory IsLocalRing
open scoped TensorProduct

universe u v w U

namespace IsLocalRing

/-! ### Transporting geometric reducedness -/

/-- Geometric reducedness over a field transports along an isomorphism of algebras. -/
private theorem isGeometricallyReduced_of_algEquiv
    {k : Type u} {A : Type v} {B : Type w} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B)
    (h : Algebra.IsGeometricallyReduced k A) : Algebra.IsGeometricallyReduced k B := by
  rw [Algebra.isGeometricallyReduced_field_iff] at h ⊢
  let E := Algebra.TensorProduct.congr
    (AlgEquiv.refl (R := k) (A₁ := AlgebraicClosure k)) e
  exact isReduced_of_injective E.symm.toRingHom E.symm.injective

/-- Geometric reducedness transports along an isomorphism of the ground field, the algebra
being restricted along that isomorphism. -/
private theorem isGeometricallyReduced_of_fieldEquiv
    {k k' : Type*} {S : Type*} [Field k] [Field k'] [CommRing S]
    [Algebra k S] (e : k' ≃+* k)
    (h : Algebra.IsGeometricallyReduced k S) :
    letI : Algebra k' S := ((algebraMap k S).comp e.toRingHom).toAlgebra
    Algebra.IsGeometricallyReduced k' S := by
  let : Algebra k' k := e.toRingHom.toAlgebra
  let : Algebra k' S := ((algebraMap k S).comp e.toRingHom).toAlgebra
  let : Algebra k S := inferInstance
  let : IsScalarTower k' k S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.IsSeparable k' k :=
    Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl k') e (by ext x; rfl)
  exact (Algebra.isGeometricallyReduced_iff_of_isSeparable k' k S).mpr h

/-- Geometric reducedness only depends on the structure map. -/
private theorem isGeometricallyReduced_toAlgebra_iff {k S : Type*} [Field k] [CommRing S]
    [Algebra k S] (f : k →+* S) (h : ∀ x, algebraMap k S x = f x) :
    @Algebra.IsGeometricallyReduced k S _ _ f.toAlgebra ↔ Algebra.IsGeometricallyReduced k S := by
  rw [Algebra.algebra_ext f.toAlgebra _ fun x => (h x).symm]

/-- Geometric reducedness is insensitive to lifting both the ground field and the algebra to a
larger universe. -/
private theorem isGeometricallyReduced_ulift_iff
    {k S : Type u} [Field k] [CommRing S] [Algebra k S] :
    Algebra.IsGeometricallyReduced k S ↔
      (letI : Algebra (ULift.{max u U} k) (ULift.{max u U} S) :=
        (RingHom.ulift.{max u U, max u U, u, u} (algebraMap k S)).toAlgebra
       Algebra.IsGeometricallyReduced (ULift.{max u U} k) (ULift.{max u U} S)) := by
  let eK : ULift.{max u U} k ≃+* k := ULift.ringEquiv
  let eS : ULift.{max u U} S ≃+* S := ULift.ringEquiv
  let : Algebra (ULift.{max u U} k) S :=
    ((algebraMap k S).comp eK.toRingHom).toAlgebra
  let : Algebra (ULift.{max u U} k) (ULift.{max u U} S) :=
    (RingHom.ulift.{max u U, max u U, u, u} (algebraMap k S)).toAlgebra
  let eAlg : ULift.{max u U} S ≃ₐ[ULift.{max u U} k] S :=
    AlgEquiv.ofRingEquiv (f := eS) (by intro x; rfl)
  refine ⟨fun h => isGeometricallyReduced_of_algEquiv eAlg.symm
    (isGeometricallyReduced_of_fieldEquiv eK h), fun h => ?_⟩
  exact (isGeometricallyReduced_toAlgebra_iff
    ((algebraMap (ULift.{max u U} k) S).comp eK.symm.toRingHom) fun _ => rfl).mp
    (isGeometricallyReduced_of_fieldEquiv eK.symm (isGeometricallyReduced_of_algEquiv eAlg h))

/-! ### Geometric reducedness as a property of ring maps -/

/-- Geometric reducedness of the target over the source, as an isomorphism-invariant property
of a ring homomorphism whose source happens to be a field. -/
private def geometricallyReducedMapProperty : RingMapProperty.{u, u} where
  property := fun {R S} _ _ f =>
    ∀ (k : Type u) [Field k] (e : k ≃+* R),
      @Algebra.IsGeometricallyReduced k S _ _ (f.comp e.toRingHom).toAlgebra
  respectsIso := by
    constructor
    · intro R S T _ _ _ f e h k _ ek
      let : Algebra k S := (f.comp ek.toRingHom).toAlgebra
      let : Algebra k T := (e.toRingHom.comp f).comp ek.toRingHom |>.toAlgebra
      exact isGeometricallyReduced_of_algEquiv (AlgEquiv.ofRingEquiv (f := e) fun _ => rfl)
        (h k ek)
    · intro R S T _ _ _ f e h k _ ek
      exact h k (ek.trans e)

/-- For a map out of a field the property is geometric reducedness of the induced algebra. -/
private theorem geometricallyReducedMapProperty_iff
    (k S : Type u) [Field k] [CommRing S] (f : k →+* S) :
    geometricallyReducedMapProperty f ↔
      @Algebra.IsGeometricallyReduced k S _ _ f.toAlgebra := by
  refine ⟨fun h => h k (RingEquiv.refl k), fun h k' _ e => ?_⟩
  let : Algebra k S := f.toAlgebra
  exact isGeometricallyReduced_of_fieldEquiv e h

/-- The property holds of the structure map of an algebra over a field exactly when that
algebra is geometrically reduced. -/
private theorem geometricallyReducedMapProperty_iff_algebraMap
    (k S : Type u) [Field k] [CommRing S] [Algebra k S] :
    geometricallyReducedMapProperty (algebraMap k S) ↔
      Algebra.IsGeometricallyReduced k S := by
  exact (geometricallyReducedMapProperty_iff k S (algebraMap k S)).trans
    (isGeometricallyReduced_toAlgebra_iff _ fun _ => rfl)

/-- The universe-independent reading of the property, for a map out of a field. -/
private theorem geometricallyReducedMapProperty_holds_iff
    {k S : Type u} [Field k] [CommRing S] (f : k →+* S) :
    (geometricallyReducedMapProperty.{max u U}).Holds.{u, u, U, 0} f ↔
      @Algebra.IsGeometricallyReduced k S _ _ f.toAlgebra := by
  show geometricallyReducedMapProperty.{max u U}
    (RingHom.ulift.{max u U, max u U, u, u} f) ↔ _
  rw [geometricallyReducedMapProperty_iff.{max u U}
    (ULift.{max u U} k) (ULift.{max u U} S)
    (RingHom.ulift.{max u U, max u U, u, u} f)]
  let : Algebra k S := f.toAlgebra
  exact (isGeometricallyReduced_ulift_iff.{u, U} (k := k) (S := S)).symm

/-- The universe-independent reading of the property, for the structure map of an algebra. -/
private theorem geometricallyReducedMapProperty_holds_iff_algebraMap
    {k S : Type u} [Field k] [CommRing S] [Algebra k S] :
    (geometricallyReducedMapProperty.{max u U}).Holds.{u, u, U, 0}
      (algebraMap k S) ↔ Algebra.IsGeometricallyReduced k S := by
  exact (geometricallyReducedMapProperty_holds_iff (algebraMap k S)).trans
    (isGeometricallyReduced_toAlgebra_iff _ fun _ => rfl)

/-- A ring-map property transports along a commuting square of ring isomorphisms. -/
private theorem holds_of_equiv
    (P : RingMapProperty.{max u U, max u U})
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : C →+* D) (e : A ≃+* C) (E : B ≃+* D)
    (h : E.toRingHom.comp f = g.comp e.toRingHom)
    (hf : P.Holds.{u, u, U, 0} f) : P.Holds.{u, u, U, 0} g := by
  let e' : ULift.{max u U} C ≃+* ULift.{max u U} A :=
    ULift.ringEquiv.trans (e.symm.trans ULift.ringEquiv.symm)
  let E' : ULift.{max u U} B ≃+* ULift.{max u U} D :=
    ULift.ringEquiv.trans (E.trans ULift.ringEquiv.symm)
  change P (RingHom.ulift.{max u U, max u U, u, u} f) at hf
  have hh := P.respectsIso.2 _ e' (P.respectsIso.1 _ E' hf)
  have heq : (E'.toRingHom.comp (RingHom.ulift.{max u U, max u U, u, u} f)).comp
      e'.toRingHom = RingHom.ulift.{max u U, max u U, u, u} g :=
    RingHom.ext fun c => ULift.ext _ _
      ((congrArg (fun t : A →+* D => t (e.symm c.down)) h).trans (by simp))
  show P (RingHom.ulift.{max u U, max u U, u, u} g)
  rwa [← heq]

/-- The formal fibres of a local ring may equivalently be described by the structure maps of
the fibres rather than by the inclusions of the second tensor factor. -/
private theorem formalFibersHaveAt_iff
    (P : RingMapProperty.{max u U, max u U}) (A : Type u)
    [CommRing A] [IsLocalRing A] :
    FormalFibersHaveAt.{u, U, U} P A ↔
      ∀ q : PrimeSpectrum A,
        P.Holds.{u, u, U, 0} (algebraMap q.asIdeal.ResidueField
          (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A))) :=
  ⟨fun h q => holds_of_equiv P
    (Algebra.TensorProduct.includeRight (R := A)
      (A := AdicCompletion (maximalIdeal A) A) (B := q.asIdeal.ResidueField)).toRingHom
    (algebraMap q.asIdeal.ResidueField (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A)))
    (RingEquiv.refl _) (Algebra.TensorProduct.comm A _ _).toRingEquiv (by ext a; rfl) (h q),
  fun h q => holds_of_equiv P
    (algebraMap q.asIdeal.ResidueField (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A)))
    (Algebra.TensorProduct.includeRight (R := A)
      (A := AdicCompletion (maximalIdeal A) A) (B := q.asIdeal.ResidueField)).toRingHom
    (RingEquiv.refl _) (Algebra.TensorProduct.comm A _ _).toRingEquiv.symm (by ext a; rfl)
    (h q)⟩

/-! ### Transporting formal fibres along an isomorphism of local rings -/

/-- A property of the formal fibres transports along an isomorphism of local rings. -/
private lemma formalFibersHaveAt_of_ringEquiv
    (P : RingMapProperty.{max u U, max u U}) {A B : Type u}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (h : FormalFibersHaveAt.{u, U, U} P A) :
    FormalFibersHaveAt.{u, U, U} P B := by
  rw [formalFibersHaveAt_iff] at h ⊢
  intro q
  let p : PrimeSpectrum A := ⟨q.asIdeal.comap e.toRingHom, inferInstance⟩
  obtain ⟨E, hE⟩ := Stacks.FormalFibres.exists_fiber_ringEquiv e
    (Stacks.FormalFibres.completionRingEquiv e)
    (Stacks.FormalFibres.completionRingEquiv_algebraMap e) q.asIdeal
  exact holds_of_equiv P _ _
    (Ideal.residueFieldRingEquiv p.asIdeal q.asIdeal e rfl) E
    (RingHom.ext hE) (h p)

/-! ### The five formal-fibre axioms for geometric reducedness -/

/-- Geometric reducedness over a field is detected on localizations at primes. -/
private lemma geometricallyReducedMapProperty_localization_iff
    (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R] :
    (∀ q : PrimeSpectrum R,
        geometricallyReducedMapProperty.{u}
          (algebraMap k (Localization.AtPrime q.asIdeal))) ↔
      geometricallyReducedMapProperty.{u} (algebraMap k R) := by
  have h₀ := (geometricReducedness_satisfies_formalFibre_properties.{u, u, u}).2.1 k R
  exact ⟨fun h => (geometricallyReducedMapProperty_iff_algebraMap k R).2 (h₀.mp fun p hp =>
      (geometricallyReducedMapProperty_iff_algebraMap k (Localization.AtPrime p)).mp
        (h ⟨p, hp⟩)),
    fun h q => (geometricallyReducedMapProperty_iff_algebraMap k
      (Localization.AtPrime q.asIdeal)).mpr
        (h₀.mpr ((geometricallyReducedMapProperty_iff_algebraMap k R).mp h) q.asIdeal)⟩

/-- Geometrically reduced formal fibres ascend along a geometrically regular map. -/
private lemma geometricallyReducedMapProperty_fibre_comp
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]
    [Module.Flat R S] [Module.Flat S T]
    (hS : ∀ p : PrimeSpectrum R,
      (geometricallyReducedMapProperty.{u}).Holds
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)))
    (hT : ∀ q : PrimeSpectrum S,
      Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber T)) :
    ∀ p : PrimeSpectrum R,
      (geometricallyReducedMapProperty.{u}).Holds
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber T)) := by
  intro p
  have hS' : ∀ p : Ideal R, ∀ hp : p.IsPrime,
      Algebra.IsGeometricallyReduced p.ResidueField (p.Fiber S) := by
    intro p hp
    exact (geometricallyReducedMapProperty_holds_iff_algebraMap
      (k := p.ResidueField) (S := p.Fiber S)).mp (hS ⟨p, hp⟩)
  exact (geometricallyReducedMapProperty_holds_iff_algebraMap
    (k := p.asIdeal.ResidueField) (S := p.asIdeal.Fiber T)).mpr
    ((geometricReducedness_satisfies_formalFibre_properties.{u, u, u}).2.2.1
      R S T hS' (fun q hq => hT ⟨q, hq⟩) p.asIdeal)

/-- Geometrically reduced formal fibres descend along a faithfully flat map. -/
private lemma geometricallyReducedMapProperty_fibre_descend
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]
    [Module.Flat R S] [Module.FaithfullyFlat S T]
    (hT : ∀ p : PrimeSpectrum R,
      (geometricallyReducedMapProperty.{u}).Holds
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber T))) :
    ∀ p : PrimeSpectrum R,
      (geometricallyReducedMapProperty.{u}).Holds
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)) := by
  intro p
  have hT' : ∀ p : Ideal R, ∀ hp : p.IsPrime,
      Algebra.IsGeometricallyReduced p.ResidueField (p.Fiber T) := by
    intro p hp
    exact (geometricallyReducedMapProperty_holds_iff_algebraMap
      (k := p.ResidueField) (S := p.Fiber T)).mp (hT ⟨p, hp⟩)
  exact (geometricallyReducedMapProperty_holds_iff_algebraMap
    (k := p.asIdeal.ResidueField) (S := p.asIdeal.Fiber S)).mpr
    ((geometricReducedness_satisfies_formalFibre_properties.{u, u, u}).2.2.2.1
      R S T hT' p.asIdeal)

/-- Geometric reducedness survives a separable algebraic extension of the ground
field. -/
@[ega "IV 18.7.1" "Geometric reducedness"]
private lemma geometricallyReducedMapProperty_baseFieldExtension
    (k K R : Type u) [Field k] [Field K] [CommRing R]
    [Algebra k K] [Algebra K R] [Algebra k R] [IsScalarTower k K R] [IsNoetherianRing R]
    (halg : Algebra.IsAlgebraic k K) (hsep : Algebra.IsSeparable k K)
    (hR : geometricallyReducedMapProperty.{u} (algebraMap k R)) :
    geometricallyReducedMapProperty.{u} (algebraMap K R) := by
  have : Algebra.IsAlgebraic k K := halg
  have : Algebra.IsSeparable k K := hsep
  exact (geometricallyReducedMapProperty_iff_algebraMap K R).mpr
    ((geometricReducedness_satisfies_formalFibre_properties.{u, u, u}).2.2.2.2 k K R
      ((geometricallyReducedMapProperty_iff_algebraMap k R).mp hR))

/-! ### The Nagata property through the formal-fibre calculus -/

/-- A Nagata local ring is a `P`-ring for geometric reducedness. -/
private lemma isPRingAt_of_isNagataRing {A : Type u} [CommRing A] [IsLocalRing A]
    (hNagata : IsNagataRing A) :
    IsPRingAt.{u, max u U, max u U} geometricallyReducedMapProperty.{max u U} A := by
  have : IsNoetherianRing A := hNagata.1
  refine ⟨hNagata.1, fun p => ?_⟩
  let Ap := Localization.AtPrime p.asIdeal
  have hgeo := (isNagataRing_iff_formalFibers_geometricallyReduced Ap).mp
    (isNagata_of_isLocalization A p.asIdeal.primeCompl Ap hNagata)
  exact (formalFibersHaveAt_iff geometricallyReducedMapProperty.{max u U} Ap).2 fun q =>
    geometricallyReducedMapProperty_holds_iff_algebraMap.mpr (hgeo q)

/-- A local `P`-ring for geometric reducedness is Nagata. -/
private lemma isNagataRing_of_isPRingAt {B : Type u} [CommRing B] [IsLocalRing B]
    (h : IsPRingAt.{u, max u U, max u U} geometricallyReducedMapProperty.{max u U} B) :
    IsNagataRing B := by
  have : IsNoetherianRing B := h.1
  have hMax := (isPRing_iff_formalFibersHave_localization_maximal
    geometricallyReducedMapProperty.{max u U}
    (fun R S T _ _ _ _ _ _ _ _ _ _ _ _ =>
      geometricallyReducedMapProperty_fibre_comp R S T)
    (fun R S T _ _ _ _ _ _ _ _ _ _ _ _ =>
      geometricallyReducedMapProperty_fibre_descend R S T)).mp h
  have hAtMax : FormalFibersHaveAt.{u, max u U, max u U}
      geometricallyReducedMapProperty.{max u U}
      (Localization.AtPrime (maximalIdeal B)) := hMax (maximalIdeal B)
  let e : B ≃+* Localization.AtPrime (maximalIdeal B) :=
    (IsLocalization.atUnits B (maximalIdeal B).primeCompl
      (S := Localization.AtPrime (maximalIdeal B)) fun _ hx =>
        notMem_maximalIdeal.mp hx).toRingEquiv
  exact (isNagataRing_iff_formalFibers_geometricallyReduced B).mpr fun q =>
    geometricallyReducedMapProperty_holds_iff_algebraMap.mp
      ((formalFibersHaveAt_iff geometricallyReducedMapProperty.{max u U} B).mp
        (formalFibersHaveAt_of_ringEquiv geometricallyReducedMapProperty.{max u U} e.symm hAtMax)
        q)

/-! ### Ind-étale algebras: reducedness and dimension -/

/-- A local ring with a henselization also has a strict henselization, in the same universe. -/
private lemma exists_strictHenselization_of_isHenselization
    (A Ah : Type u) [CommRing A] [IsLocalRing A] [CommRing Ah] [IsLocalRing Ah]
    [Algebra A Ah] [IsHenselization A (ResidueField A) Ah] :
    ∃ (Ash : Type u) (_ : CommRing Ash) (_ : IsLocalRing Ash) (_ : Algebra A Ash),
      IsHenselization A (SeparableClosure (ResidueField A)) Ash := by
  have : IsLocalHom (algebraMap A Ah) := IsHenselization.isLocalHom (L := ResidueField A)
  obtain ⟨Ash, _, _, _, _, _, _, h, -, hi, -, hr⟩ :=
    IsLocalRing.exists_strictHenselization A Ah
      (IsHenselization.ind_etale_of_universe_le (R := A) (L := ResidueField A) (Rh := Ah))
      (IsHenselization.residueField_map_bijective (R := A) (Rh := Ah)).2
      (SeparableClosure (ResidueField A))
  exact ⟨Ash, inferInstance, inferInstance, inferInstance,
    IsHenselization.of_ind_etale h hi hr⟩

/-- Ind-étaleness transfers to the universe-lifted algebra over the universe-lifted ring. -/
private theorem ind_etale_ulift {A : Type u} {Ash : Type w} [CommRing A] [CommRing Ash]
    [Algebra A Ash] (hind : (CommAlgCat.etale.{max u w} A).ind.{max u w}
      (CommAlgCat.of A (ULift.{u} Ash))) :
    letI : Algebra (ULift.{w} A) (ULift.{u} Ash) :=
      ((ULift.ringEquiv (R := Ash)).symm.toRingHom.comp
        ((algebraMap A Ash).comp (ULift.ringEquiv (R := A)).toRingHom)).toAlgebra
    (CommAlgCat.etale.{max u w} (ULift.{w} A)).ind.{max u w}
      (CommAlgCat.of (ULift.{w} A) (ULift.{u} Ash)) :=
  Stacks.Henselization.Shared.ind_etale_restrictScalars (ULift.ringEquiv (R := A))
    (CommAlgCat.of A (ULift.{u} Ash)) hind

/-! ### Properties of a henselization -/

namespace IsHenselization

variable {A Ah : Type u} [CommRing A] [IsLocalRing A] [CommRing Ah] [IsLocalRing Ah]
  [Algebra A Ah] [hAh : IsHenselization A (ResidueField A) Ah]

include hAh

/-- The henselization of a reduced local ring is reduced. -/
@[stacks 0C3V "henselization_properties", ega "IV 18.6.9" "(i), special case"]
public lemma isReduced [IsReduced A] : IsReduced Ah := by
  obtain ⟨Ash, _, _, _, _⟩ := exists_strictHenselization_of_isHenselization A Ah
  exact ((isReduced_tfae_henselization_strictHenselization A Ah Ash
    (SeparableClosure (ResidueField A))).out 1 2).mp ‹IsReduced A›

/-- The henselization of a Nagata local ring is Nagata. -/
@[stacks 0C3V "henselization_properties", ega "IV 18.7.3" "Forward implication"]
public lemma isNagataRing (hNagata : IsNagataRing A) : IsNagataRing Ah := by
  have : IsNoetherianRing A := hNagata.1
  obtain ⟨Rsh, _, _, _, _⟩ := exists_strictHenselization_of_isHenselization A Ah
  exact isNagataRing_of_isPRingAt.{u, u}
    (isPRing_henselization_and_strictHenselization geometricallyReducedMapProperty.{u}
      (fun k R _ _ _ _ => geometricallyReducedMapProperty_localization_iff k R)
      (fun R S T _ _ _ _ _ _ _ _ _ _ _ _ =>
        geometricallyReducedMapProperty_fibre_comp R S T)
      (fun R S T _ _ _ _ _ _ _ _ _ _ _ _ =>
        geometricallyReducedMapProperty_fibre_descend R S T)
      (fun k K R _ _ _ _ _ _ _ _ => geometricallyReducedMapProperty_baseFieldExtension k K R)
      A Ah Rsh (SeparableClosure (ResidueField A))
      (isPRingAt_of_isNagataRing.{u, u} hNagata)).1

/-- Henselization preserves the Krull dimension of a local ring. -/
@[stacks 0C3V "henselization_properties"]
public lemma ringKrullDim_eq : ringKrullDim Ah = ringKrullDim A := by
  obtain ⟨Ash, _, _, _, _⟩ := exists_strictHenselization_of_isHenselization A Ah
  exact (ringKrullDim_eq_henselization_eq_strictHenselization A Ah Ash
    (SeparableClosure (ResidueField A))).1.symm

end IsHenselization

/-! ### Properties of a strict henselization -/

variable {A : Type u} {Ash : Type w} [CommRing A] [IsLocalRing A]
  [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]

/-- A strict henselization of a reduced local ring is reduced. -/
@[stacks 0C3V "strict_henselization_properties", ega "IV 18.8.12" "(i)"]
public lemma strictHenselization_isReduced
    (ksep : Type v) [Field ksep] [Algebra (IsLocalRing.ResidueField A) ksep]
    [IsSepClosure (IsLocalRing.ResidueField A) ksep]
    [IsLocalRing.IsHenselization A ksep Ash] [IsReduced A] : IsReduced Ash := by
  let A' := ULift.{w} A
  let Ash' := ULift.{u} Ash
  let eA : A' ≃+* A := ULift.ringEquiv
  let eAsh : Ash' ≃+* Ash := ULift.ringEquiv
  have : IsLocalRing A' := eA.symm.isLocalRing
  have : IsLocalRing Ash' := eAsh.symm.isLocalRing
  let : Algebra A' Ash' :=
    (eAsh.symm.toRingHom.comp ((algebraMap A Ash).comp eA.toRingHom)).toAlgebra
  have : IsReduced A' := isReduced_of_injective eA eA.injective
  have hind := ind_etale_ulift
    (IsLocalRing.IsHenselization.ind_etale (R := A) (L := ksep) (Rh := Ash))
  have : IsReduced Ash' := isReduced_of_ind_etale hind
  exact isReduced_of_injective eAsh.symm eAsh.symm.injective

/-- A strict henselization of a Nagata local ring is Nagata. -/
@[stacks 0C3V "strict_henselization_properties"]
public lemma strictHenselization_isNagataRing
    (ksep : Type v) [Field ksep] [Algebra (IsLocalRing.ResidueField A) ksep]
    [IsSepClosure (IsLocalRing.ResidueField A) ksep]
    [IsLocalRing.IsHenselization A ksep Ash]
    (hA : IsNagataRing A) : IsNagataRing Ash := by
  have : IsNoetherianRing A := hA.1
  obtain ⟨Rh, _, _, _, hlocal, hh, hi, _, hbij⟩ := IsLocalRing.exists_henselization A
  let := hlocal
  let : IsHenselization A (ResidueField A) Rh :=
    IsHenselization.of_ind_etale hh hi
      ⟨RingEquiv.ofBijective (ResidueField.map (algebraMap A Rh)) hbij, fun _ => rfl⟩
  exact isNagataRing_of_isPRingAt.{w, max u v}
    (isPRing_henselization_and_strictHenselization
      geometricallyReducedMapProperty.{max u (max v w)}
      (fun k R _ _ _ _ => geometricallyReducedMapProperty_localization_iff k R)
      (fun R S T _ _ _ _ _ _ _ _ _ _ _ _ =>
        geometricallyReducedMapProperty_fibre_comp R S T)
      (fun R S T _ _ _ _ _ _ _ _ _ _ _ _ =>
        geometricallyReducedMapProperty_fibre_descend R S T)
      (fun k K R _ _ _ _ _ _ _ _ => geometricallyReducedMapProperty_baseFieldExtension k K R)
      A Rh Ash ksep (isPRingAt_of_isNagataRing.{u, max v w} hA)).2

/-- A local ring and a strict henselization of it have the same Krull
dimension. -/
@[stacks 0C3V "strict_henselization_properties", sga "5 I 3.1.3" "more general"]
public lemma strictHenselization_ringKrullDim
    (ksep : Type v) [Field ksep] [Algebra (IsLocalRing.ResidueField A) ksep]
    [IsSepClosure (IsLocalRing.ResidueField A) ksep]
    [IsLocalRing.IsHenselization A ksep Ash] : ringKrullDim Ash = ringKrullDim A := by
  have : Module.FaithfullyFlat A Ash :=
    IsLocalRing.IsHenselization.faithfullyFlat (R := A) (L := ksep) (Rh := Ash)
  let A' := ULift.{w} A
  let Ash' := ULift.{u} Ash
  let eA : A' ≃+* A := ULift.ringEquiv
  let eAsh : Ash' ≃+* Ash := ULift.ringEquiv
  have : IsLocalRing A' := eA.symm.isLocalRing
  have : IsLocalRing Ash' := eAsh.symm.isLocalRing
  let : Algebra A' Ash' :=
    (eAsh.symm.toRingHom.comp ((algebraMap A Ash).comp eA.toRingHom)).toAlgebra
  have hind := ind_etale_ulift
    (IsLocalRing.IsHenselization.ind_etale (R := A) (L := ksep) (Rh := Ash))
  refine le_antisymm ?_ (ringKrullDim_le_of_faithfullyFlat A Ash)
  rw [← ringKrullDim_eq_of_ringEquiv eAsh, ← ringKrullDim_eq_of_ringEquiv eA]
  exact ringKrullDim_le_of_ind_etale A' Ash' hind

end IsLocalRing
