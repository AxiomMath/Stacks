module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Data.Set.Card
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.RingTheory.Branches.Henselization
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.Henselization.Existence
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Existence

/-!
# Unibranch schemes and the number of branches at a point

A commutative local ring is *unibranch* when its reduction is a domain and the normalization of
that reduction is local, and *geometrically unibranch* when in addition the induced extension of
residue fields is purely inseparable. A scheme has either property at a point when its local ring
there does, and has it globally when it has it at every point.

The *number of branches* of a local ring is the number of minimal primes of its henselization,
and the *number of geometric branches* is the number of minimal primes of a strict
henselization. Applying these two ring invariants to the local ring of a scheme at a point gives
the number of branches and of geometric branches of the scheme at that point. Each count equals
one exactly when the scheme is unibranch, respectively geometrically unibranch, at the point.
Every normal scheme is geometrically unibranch.

## Main definitions

* `IsUnibranchRing` is the predicate that the reduction is a domain with local normalization.
* `IsGeometricallyUnibranchRing` additionally requires the induced residue-field extension to be
  purely inseparable.
* `numberOfBranchesOfLocalRing` is the number of minimal primes of a henselization.
* `numberOfGeometricBranchesOfLocalRing` is the number of minimal primes of a strict
  henselization.
* `AlgebraicGeometry.IsUnibranchAt`, `AlgebraicGeometry.IsGeometricallyUnibranchAt`,
  `AlgebraicGeometry.IsUnibranch` and `AlgebraicGeometry.IsGeometricallyUnibranch` are the
  corresponding properties of a scheme.
* `AlgebraicGeometry.numberOfBranches` and `AlgebraicGeometry.numberOfGeometricBranches` are the
  two counts at a point of a scheme.

## Main results

* `numberOfBranchesOfLocalRing_eq_one_iff` and `numberOfGeometricBranchesOfLocalRing_eq_one_iff`
  identify the two branch counts of a local ring being one with unibranchness, respectively
  geometric unibranchness.
* `AlgebraicGeometry.isUnibranch_iff_isUnibranchRing` and
  `AlgebraicGeometry.isGeometricallyUnibranch_iff_isGeometricallyUnibranchRing` identify the two
  predicates defined here with `IsUnibranch` and `IsGeometricallyUnibranch`.
* `AlgebraicGeometry.numberOfBranches_eq_one_iff`: a scheme has one branch at a point if and only
  if it is unibranch there.
* `AlgebraicGeometry.numberOfGeometricBranches_eq_one_iff`: likewise for geometric branches and
  geometric unibranchness.
* `AlgebraicGeometry.isGeometricallyUnibranch_of_isNormal`: a normal scheme is geometrically
  unibranch.

## Implementation notes

The reduction of `R` is represented by `R ⧸ nilradical R`, and its normalization by its
`integralClosure` in `FractionRing`. The residue-field extension is induced by the canonical
composite from `R` through its reduction to that normalization.

The branch counts lie in `ℕ∞`; `Set.encard` is the ordinary finite cardinality when the set of
minimal primes is finite and `∞` otherwise. Since the constructions of a henselization and a
strict henselization in the library are existence theorems, `HenselizationData` and
`StrictHenselizationData` package chosen representatives, and their `IsHenselization` fields
record the full characterizing properties. Instances for the carriers of the fixed
representatives are registered, and the two `numberOf...OfLocalRing_eq_encard_minimalPrimes`
lemmas are their characterizing equations. The two scheme-level counts are abbreviations, and the
corresponding `numberOf..._eq_numberOf...OfLocalRing` simp lemmas provide their public interface,
so clients can pass freely between the scheme and local-ring spellings without unfolding a
definition.

## References

* [Stacks Project, Tag 0BPZ](https://stacks.math.columbia.edu/tag/0BPZ)
* [Stacks Project, Tag 0BQ2](https://stacks.math.columbia.edu/tag/0BQ2)
* [Stacks Project, Tag 0BQ3](https://stacks.math.columbia.edu/tag/0BQ3)
* [Stacks Project, Tag 0C26](https://stacks.math.columbia.edu/tag/0C26)
* [Stacks Project, Tag 0C38](https://stacks.math.columbia.edu/tag/0C38)
* [Stacks Project, Tag 0C39](https://stacks.math.columbia.edu/tag/0C39)
* [EGA IV, Chapter 0 (23.2.1)][EGA4]
* [EGA IV, Chapter IV (6.15.1)][EGA4]
-/

@[expose] public section

open IsLocalRing

universe u

/-- A local ring is unibranch if its reduction is a domain and the integral closure of that
reduction in its field of fractions is local. -/
@[ega "0 23.2.1", ega "III 4.3.6"]
public def IsUnibranchRing (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∃ hred : IsDomain (R ⧸ nilradical R),
    letI := hred
    IsLocalRing
      (integralClosure (R ⧸ nilradical R) (FractionRing (R ⧸ nilradical R)))

/-- A local ring is geometrically unibranch if its reduction is a domain, its normalization is
local, and the induced extension from its residue field to the normalization's residue field is
purely inseparable. -/
@[ega "0 23.2.1"]
public def IsGeometricallyUnibranchRing (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∃ hred : IsDomain (R ⧸ nilradical R),
    letI := hred
    let q : R →+* R ⧸ nilradical R := Ideal.Quotient.mk (nilradical R)
    letI : IsLocalRing (R ⧸ nilradical R) :=
      IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
    letI : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
    ∃ hnormal : IsLocalRing
        (integralClosure (R ⧸ nilradical R) (FractionRing (R ⧸ nilradical R))),
      letI := hnormal
      let f : R →+*
          integralClosure (R ⧸ nilradical R) (FractionRing (R ⧸ nilradical R)) :=
        (algebraMap (R ⧸ nilradical R)
          (integralClosure (R ⧸ nilradical R) (FractionRing (R ⧸ nilradical R)))).comp q
      letI : Algebra R
          (integralClosure (R ⧸ nilradical R) (FractionRing (R ⧸ nilradical R))) :=
        f.toAlgebra
      letI : IsLocalHom f := RingHom.isLocalHom_comp _ _
      IsPurelyInseparable (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField
          (integralClosure (R ⧸ nilradical R) (FractionRing (R ⧸ nilradical R))))

/-- A chosen henselization of a local ring, packaged with its characterizing property.

The same-named `private` structure of `StacksFrontier.RingTheory.GRing.EssFiniteType` is a
different object: it has no `IsHenselization` field, recording instead, in two separate fields,
that the carrier is a henselian local ring and that it is an ind-étale `R`-algebra, and all
eight of its fields are explicit rather than instance-implicit. -/
public structure HenselizationData (R : Type u) [CommRing R] [IsLocalRing R] where
  /-- The underlying ring of the henselization. -/
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra R carrier]
  [isLocalRing : IsLocalRing carrier]
  [isLocalHom : IsLocalHom (algebraMap R carrier)]
  [isHenselization : IsHenselization R (ResidueField R) carrier]
  /-- The henselization has the same residue field as the original local ring. -/
  residueFieldMap_bijective : Function.Bijective (ResidueField.map (algebraMap R carrier))

/-- Every local ring admits a henselization. -/
public theorem henselizationData_nonempty (R : Type u) [CommRing R] [IsLocalRing R] :
    Nonempty (HenselizationData R) := by
  obtain ⟨Rh, hCommRing, hAlgebra, hLocalRing, hLocalHom, hhens, hind, -, hres⟩ :=
    exists_henselization R
  let _ := hCommRing; let _ := hAlgebra; let _ := hLocalRing; let _ := hLocalHom
  let hEquiv : ResidueField R ≃+* ResidueField Rh :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap R Rh)) hres
  let hHenselization : IsHenselization R (ResidueField R) Rh :=
    { henselian := hhens
      ind_etale := (CommAlgCat.etale R).ind.prop_of_iso
        (CommAlgCat.isoMk (ULift.algEquiv : ULift.{u} _ ≃ₐ[R] _).symm) hind
      exists_residueFieldEquiv := ⟨hEquiv, fun x => by simp [hEquiv, ResidueField.map_residue]⟩ }
  exact ⟨{ carrier := Rh, residueFieldMap_bijective := hres }⟩

/-- A fixed henselization of a local ring. -/
public noncomputable def henselizationData (R : Type u) [CommRing R] [IsLocalRing R] :
    HenselizationData R :=
  Classical.choice (henselizationData_nonempty R)

/-- The ring structure on the fixed henselization. -/
public noncomputable instance henselizationDataCommRing (R : Type u) [CommRing R]
    [IsLocalRing R] : CommRing (henselizationData R).carrier :=
  (henselizationData R).commRing

/-- The algebra structure on the fixed henselization. -/
public noncomputable instance henselizationDataAlgebra (R : Type u) [CommRing R]
    [IsLocalRing R] : Algebra R (henselizationData R).carrier :=
  (henselizationData R).algebra

/-- The fixed henselization is a local ring. -/
public noncomputable instance henselizationDataIsLocalRing (R : Type u) [CommRing R]
    [IsLocalRing R] : IsLocalRing (henselizationData R).carrier :=
  (henselizationData R).isLocalRing

/-- The structure map to the fixed henselization is local. -/
public noncomputable instance henselizationDataIsLocalHom (R : Type u) [CommRing R]
    [IsLocalRing R] : IsLocalHom (algebraMap R (henselizationData R).carrier) :=
  (henselizationData R).isLocalHom

/-- The fixed representative has the characterizing properties of a henselization. -/
public noncomputable instance henselizationDataIsHenselization (R : Type u) [CommRing R]
    [IsLocalRing R] :
    IsHenselization R (ResidueField R) (henselizationData R).carrier :=
  (henselizationData R).isHenselization

/-- A chosen strict henselization of a local ring, packaged with its characterizing property. -/
public structure StrictHenselizationData (R : Type u) [CommRing R] [IsLocalRing R] where
  /-- The underlying ring of the strict henselization. -/
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra R carrier]
  [isLocalRing : IsLocalRing carrier]
  [isHenselization : IsHenselization R (SeparableClosure (ResidueField R)) carrier]

/-- Every local ring admits a strict henselization. -/
public theorem strictHenselizationData_nonempty (R : Type u) [CommRing R] [IsLocalRing R] :
    Nonempty (StrictHenselizationData R) := by
  let D := henselizationData R; let Rh := D.carrier
  let : CommRing Rh := D.commRing; let : Algebra R Rh := D.algebra
  let : IsLocalRing Rh := D.isLocalRing
  let : IsHenselization R (ResidueField R) Rh := D.isHenselization
  let : IsLocalHom (algebraMap R Rh) := D.isLocalHom
  obtain ⟨Rsh, hCommRing, hLocalRing, hAlgebraR, -, -, -, hhens, -, hind, -, he⟩ :=
    exists_strictHenselization R Rh
      (IsHenselization.ind_etale_of_universe_le (R := R) (L := ResidueField R) (Rh := Rh))
      D.residueFieldMap_bijective.2 (SeparableClosure (ResidueField R))
  let _ := hCommRing; let _ := hLocalRing; let _ := hAlgebraR
  let hHenselization : IsHenselization R (SeparableClosure (ResidueField R)) Rsh :=
    { henselian := hhens
      ind_etale := (CommAlgCat.etale R).ind.prop_of_iso
        (CommAlgCat.isoMk (ULift.algEquiv : ULift.{u} _ ≃ₐ[R] _).symm) hind
      exists_residueFieldEquiv := he }
  exact ⟨{ carrier := Rsh }⟩

/-- A fixed strict henselization of a local ring. -/
public noncomputable def strictHenselizationData (R : Type u) [CommRing R] [IsLocalRing R] :
    StrictHenselizationData R :=
  Classical.choice (strictHenselizationData_nonempty R)

/-- The ring structure on the fixed strict henselization. -/
public noncomputable instance strictHenselizationDataCommRing (R : Type u) [CommRing R]
    [IsLocalRing R] : CommRing (strictHenselizationData R).carrier :=
  (strictHenselizationData R).commRing

/-- The algebra structure on the fixed strict henselization. -/
public noncomputable instance strictHenselizationDataAlgebra (R : Type u) [CommRing R]
    [IsLocalRing R] : Algebra R (strictHenselizationData R).carrier :=
  (strictHenselizationData R).algebra

/-- The fixed strict henselization is a local ring. -/
public noncomputable instance strictHenselizationDataIsLocalRing (R : Type u) [CommRing R]
    [IsLocalRing R] : IsLocalRing (strictHenselizationData R).carrier :=
  (strictHenselizationData R).isLocalRing

/-- The fixed representative has the characterizing properties of a strict henselization. -/
public noncomputable instance strictHenselizationDataIsHenselization (R : Type u) [CommRing R]
    [IsLocalRing R] :
    IsHenselization R (SeparableClosure (ResidueField R))
      (strictHenselizationData R).carrier :=
  (strictHenselizationData R).isHenselization

/-- The number of branches of a local ring: the extended cardinality of the set of minimal
primes of its henselization. -/
public noncomputable def numberOfBranchesOfLocalRing (R : Type u) [CommRing R]
    [IsLocalRing R] : ℕ∞ :=
  Set.encard (minimalPrimes (henselizationData R).carrier)

/-- The number of branches is the extended cardinality of the minimal primes of the fixed
henselization. -/
@[simp]
public theorem numberOfBranchesOfLocalRing_eq_encard_minimalPrimes (R : Type u) [CommRing R]
    [IsLocalRing R] :
    numberOfBranchesOfLocalRing R =
      Set.encard (minimalPrimes (henselizationData R).carrier) :=
  rfl

/-- The number of geometric branches of a local ring: the extended cardinality of the set of
minimal primes of its strict henselization. -/
public noncomputable def numberOfGeometricBranchesOfLocalRing (R : Type u) [CommRing R]
    [IsLocalRing R] : ℕ∞ :=
  Set.encard (minimalPrimes (strictHenselizationData R).carrier)

/-- The number of geometric branches is the extended cardinality of the minimal primes of the
fixed strict henselization. -/
@[simp]
public theorem numberOfGeometricBranchesOfLocalRing_eq_encard_minimalPrimes
    (R : Type u) [CommRing R] [IsLocalRing R] :
    numberOfGeometricBranchesOfLocalRing R =
      Set.encard (minimalPrimes (strictHenselizationData R).carrier) :=
  rfl

namespace AlgebraicGeometry

/-- A scheme is unibranch at a point if its local ring there is unibranch. -/
@[stacks 0BQ2 "unibranch at a point", ega "IV 6.15.1"] public abbrev IsUnibranchAt
    (X : AlgebraicGeometry.Scheme.{u}) (x : X) : Prop :=
  IsUnibranchRing (X.presheaf.stalk x)

/-- A scheme is geometrically unibranch at a point if its local ring there is geometrically
unibranch. -/
@[stacks 0BQ2 "geometrically unibranch at a point",
  ega "IV 6.15.1" "geom. unibranch at x"]
public abbrev IsGeometricallyUnibranchAt
    (X : AlgebraicGeometry.Scheme.{u}) (x : X) : Prop :=
  IsGeometricallyUnibranchRing (X.presheaf.stalk x)

/-- A scheme is unibranch if it is unibranch at every point. -/
@[stacks 0BQ2 "unibranch schemes",
  ega "III 4.3.6" "unibranch point",
  ega "IV 6.15.1" "unibranch, global"]
public abbrev IsUnibranch
    (X : AlgebraicGeometry.Scheme.{u}) : Prop :=
  ∀ x : X, IsUnibranchAt X x

/-- A scheme is geometrically unibranch if it is geometrically unibranch at every point. -/
@[stacks 0BQ2 "geometrically unibranch schemes",
  ega "IV 6.15.1" "geom. unibranch, global", sga "3 X 5.14.0"]
public abbrev IsGeometricallyUnibranch
    (X : AlgebraicGeometry.Scheme.{u}) : Prop :=
  ∀ x : X, IsGeometricallyUnibranchAt X x

/-- The number of branches of a scheme at a point is the number of branches of its local ring at
that point. -/
@[stacks 0C38 "number of branches"]
public noncomputable abbrev numberOfBranches (X : AlgebraicGeometry.Scheme.{u}) (x : X) : ℕ∞ :=
  numberOfBranchesOfLocalRing (X.presheaf.stalk x)

/-- The number of geometric branches of a scheme at a point is the number of geometric branches
of its local ring at that point. -/
@[stacks 0C38 "number of geometric branches"]
public noncomputable abbrev numberOfGeometricBranches
    (X : AlgebraicGeometry.Scheme.{u}) (x : X) : ℕ∞ :=
  numberOfGeometricBranchesOfLocalRing (X.presheaf.stalk x)

/-- The number of branches of a scheme is the branch count of its local ring. -/
@[simp]
public theorem numberOfBranches_eq_numberOfBranchesOfLocalRing
    (X : AlgebraicGeometry.Scheme.{u}) (x : X) :
    numberOfBranches X x = numberOfBranchesOfLocalRing (X.presheaf.stalk x) :=
  rfl

/-- The number of geometric branches of a scheme is the geometric branch count of its local
ring. -/
@[simp]
public theorem numberOfGeometricBranches_eq_numberOfGeometricBranchesOfLocalRing
    (X : AlgebraicGeometry.Scheme.{u}) (x : X) :
    numberOfGeometricBranches X x =
      numberOfGeometricBranchesOfLocalRing (X.presheaf.stalk x) :=
  rfl

/-- Pure inseparability of a ring homomorphism out of a residue field agrees with the
algebra-theoretic notion attached to an algebra structure compatible with it. -/
private lemma ringHom_isPurelyInseparable_iff
    {R E : Type*} [CommRing R] [IsLocalRing R] [Field E]
    (f : IsLocalRing.ResidueField R →+* E) (b : Algebra (IsLocalRing.ResidueField R) E)
    (hfb : ∀ r, f (IsLocalRing.residue R r) = algebraMap _ E (IsLocalRing.residue R r)) :
    f.IsPurelyInseparable ↔ @IsPurelyInseparable _ E _ _ b := by
  have : f.toAlgebra = b := Algebra.algebra_ext _ _ fun x ↦ by
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    exact hfb r
  rw [RingHom.IsPurelyInseparable, this]

/-- The library's unibranch predicate agrees with the one defined here. -/
public theorem isUnibranch_iff_isUnibranchRing
    (R : Type u) [CommRing R] [IsLocalRing R] :
    _root_.IsUnibranch R ↔ IsUnibranchRing R := by
  rw [_root_.IsUnibranch, IsUnibranchRing]
  constructor <;> rintro ⟨hred, hlocal⟩ <;> exact ⟨hred, hlocal⟩

set_option backward.isDefEq.respectTransparency false in
/-- The library's geometrically unibranch predicate agrees with the one defined here. -/
public theorem isGeometricallyUnibranch_iff_isGeometricallyUnibranchRing
    (R : Type u) [CommRing R] [IsLocalRing R] :
    _root_.IsGeometricallyUnibranch R ↔
      IsGeometricallyUnibranchRing R := by
  rw [_root_.IsGeometricallyUnibranch, IsGeometricallyUnibranchRing]
  constructor
  · rintro ⟨⟨hred, hlocal⟩, h⟩
    refine ⟨hred, hlocal, ?_⟩
    refine (ringHom_isPurelyInseparable_iff _ _ ?_).mp (h hred hlocal)
    exact fun _ ↦ rfl
  · rintro ⟨hred, hlocal, h⟩
    refine ⟨⟨hred, hlocal⟩, fun _ _ ↦ ?_⟩
    refine (ringHom_isPurelyInseparable_iff _ _ ?_).mpr h
    exact fun _ ↦ rfl

-- Shared helpers, hoisted here from
-- `StacksFrontier/AlgebraicGeometry/Morphisms/EtaleNeighbourhood/Branches.lean` and
-- `StacksFrontier/AlgebraicGeometry/Properties/PrincipalOpens/GeometricBranches.lean`,
-- which each carried an identical private copy and both import this module.
/-- Along an open embedding, the irreducible components through a point correspond to the
irreducible components through its image. -/
public noncomputable def irreducibleComponentsThrough_equiv_of_isOpenEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : Y → X}
    (hf : Topology.IsOpenEmbedding f) (y : Y) :
    {Z : irreducibleComponents X // f y ∈ (Z : Set X)} ≃
      {W : irreducibleComponents Y // y ∈ (W : Set Y)} := by
  let toFun :
      {Z : irreducibleComponents X // f y ∈ (Z : Set X)} →
        {W : irreducibleComponents Y // y ∈ (W : Set Y)} := fun Z =>
    ⟨⟨f ⁻¹' (Z : Set X), preimage_mem_irreducibleComponents Z.1.property hf
        ⟨f y, Z.2, y, rfl⟩⟩, Z.2⟩
  have hinj : Function.Injective toFun := by
    intro Z Z' h
    apply Subtype.ext
    apply Subtype.ext
    have hpre : f ⁻¹' (Z.1 : Set X) = f ⁻¹' (Z'.1 : Set X) :=
      congrArg (fun W : {W : irreducibleComponents Y // y ∈ (W : Set Y)} =>
        (W.1 : Set Y)) h
    have hZ := isClosed_of_mem_irreducibleComponents _ Z.1.property
    have hZ' := isClosed_of_mem_irreducibleComponents _ Z'.1.property
    have hdense : closure (f '' f ⁻¹' (Z.1 : Set X)) = (Z.1 : Set X) :=
      closure_image_preimage_of_isPreirreducible f hf.isOpenMap _ ⟨y, Z.2⟩
        Z.1.property.1.isPreirreducible hZ
    have hdense' : closure (f '' f ⁻¹' (Z'.1 : Set X)) = (Z'.1 : Set X) :=
      closure_image_preimage_of_isPreirreducible f hf.isOpenMap _ ⟨y, Z'.2⟩
        Z'.1.property.1.isPreirreducible hZ'
    rw [← hdense, ← hdense', hpre]
  let chooseComp :
      (W : {W : irreducibleComponents Y // y ∈ (W : Set Y)}) → Set X := fun W =>
    Classical.choose (exists_mem_irreducibleComponents_subset_of_isIrreducible
      (f '' (W.1 : Set Y)) (W.1.property.1.image f hf.continuous.continuousOn))
  have chooseComp_spec (W : {W : irreducibleComponents Y // y ∈ (W : Set Y)}) :
      chooseComp W ∈ irreducibleComponents X ∧ f '' (W.1 : Set Y) ⊆ chooseComp W :=
    Classical.choose_spec (exists_mem_irreducibleComponents_subset_of_isIrreducible
      (f '' (W.1 : Set Y)) (W.1.property.1.image f hf.continuous.continuousOn))
  let invFun :
      {W : irreducibleComponents Y // y ∈ (W : Set Y)} →
        {Z : irreducibleComponents X // f y ∈ (Z : Set X)} := fun W =>
    ⟨⟨chooseComp W, (chooseComp_spec W).1⟩,
      (chooseComp_spec W).2 ⟨y, W.2, rfl⟩⟩
  have hright : ∀ W, toFun (invFun W) = W := by
    intro W
    apply Subtype.ext
    apply Subtype.ext
    have hpre : f ⁻¹' chooseComp W ∈ irreducibleComponents Y :=
      preimage_mem_irreducibleComponents (chooseComp_spec W).1 hf
        ⟨f y, (chooseComp_spec W).2 ⟨y, W.2, rfl⟩, y, rfl⟩
    have hWle : (W.1 : Set Y) ⊆ f ⁻¹' chooseComp W := fun w hw =>
      (chooseComp_spec W).2 ⟨w, hw, rfl⟩
    exact (hWle.antisymm (W.1.property.2 hpre.1 hWle)).symm
  exact ⟨toFun, invFun, fun Z => hinj (hright (toFun Z)), hright⟩

/-- A ring isomorphism carries minimal primes to minimal primes, bijectively. -/
public noncomputable def minimalPrimes_equiv_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    minimalPrimes R ≃ minimalPrimes S where
  toFun p := ⟨p.1.map e, by
    have hp : Minimal Ideal.IsPrime p.1 := (IsMinimalPrime.iff_minimal p.1).mp p.2
    apply (IsMinimalPrime.iff_minimal _).mpr
    rw [minimal_iff] at hp ⊢
    have : p.1.IsPrime := hp.1
    refine ⟨Ideal.map_isPrime_of_equiv e, ?_⟩
    intro q hq hqle
    have : q.IsPrime := hq
    have hq' : (q.comap e).IsPrime := Ideal.IsPrime.comap e
    have hq'le : q.comap e ≤ p.1 := calc
      q.comap e ≤ (p.1.map e).comap e := e.idealComapOrderIso.monotone hqle
      _ = p.1 := Ideal.comap_map_of_bijective e e.bijective
    calc
      p.1.map e = (q.comap e).map e := congrArg (fun I : Ideal R => I.map e) (hp.2 hq' hq'le)
      _ = q := Ideal.map_comap_of_surjective e e.surjective q
    ⟩
  invFun q := ⟨q.1.comap e, by
    have hq : Minimal Ideal.IsPrime q.1 := (IsMinimalPrime.iff_minimal q.1).mp q.2
    apply (IsMinimalPrime.iff_minimal _).mpr
    rw [minimal_iff] at hq ⊢
    have : q.1.IsPrime := hq.1
    refine ⟨Ideal.IsPrime.comap e, ?_⟩
    intro p hp hple
    have : p.IsPrime := hp
    have hp' : (p.map e).IsPrime := Ideal.map_isPrime_of_equiv e
    have hple' : p.map e ≤ q.1 := calc
      p.map e ≤ (q.1.comap e).map e := e.idealComapOrderIso.symm.monotone hple
      _ = q.1 := Ideal.map_comap_of_surjective e e.surjective q.1
    calc
      q.1.comap e = (p.map e).comap e := congrArg (fun I : Ideal S => I.comap e) (hq.2 hp' hple')
      _ = p := Ideal.comap_map_of_bijective e e.bijective
    ⟩
  left_inv p := Subtype.ext (Ideal.comap_map_of_bijective e e.bijective)
  right_inv q := Subtype.ext (Ideal.map_comap_of_surjective e e.surjective q.1)

/-- The irreducible components containing a point, as a subtype of `irreducibleComponents`
rather than as a subtype of `Set`. -/
public noncomputable def componentThrough_equiv_subtype
    {X : Type*} [TopologicalSpace X] (x : X) :
    {Z : Set X // Z ∈ irreducibleComponents X ∧ x ∈ Z} ≃
      {Z : irreducibleComponents X // x ∈ (Z : Set X)} where
  toFun Z := ⟨⟨Z.1, Z.2.1⟩, Z.2.2⟩
  invFun Z := ⟨Z.1, Z.1.property, Z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end AlgebraicGeometry

/-- A local ring has exactly one branch if and only if it is unibranch. -/
public theorem numberOfBranchesOfLocalRing_eq_one_iff (R : Type u) [CommRing R]
    [IsLocalRing R] :
    numberOfBranchesOfLocalRing R = 1 ↔ IsUnibranchRing R := by
  show _root_.numberOfBranches R (henselizationData R).carrier = 1 ↔ _
  rw [(numberOfBranches_characterizations R (henselizationData R).carrier
    (strictHenselizationData R).carrier
    (SeparableClosure (IsLocalRing.ResidueField R))).2.1]
  exact AlgebraicGeometry.isUnibranch_iff_isUnibranchRing _

/-- A local ring has exactly one geometric branch if and only if it is geometrically
unibranch. -/
public theorem numberOfGeometricBranchesOfLocalRing_eq_one_iff (R : Type u) [CommRing R]
    [IsLocalRing R] :
    numberOfGeometricBranchesOfLocalRing R = 1 ↔ IsGeometricallyUnibranchRing R := by
  show _root_.numberOfGeometricBranches R (SeparableClosure (IsLocalRing.ResidueField R))
    (strictHenselizationData R).carrier = 1 ↔ _
  rw [(numberOfBranches_characterizations R (henselizationData R).carrier
    (strictHenselizationData R).carrier
    (SeparableClosure (IsLocalRing.ResidueField R))).2.2.1]
  exact AlgebraicGeometry.isGeometricallyUnibranch_iff_isGeometricallyUnibranchRing _

namespace AlgebraicGeometry

/-- A scheme has exactly one branch at a point if and only if it is unibranch at that point. -/
@[stacks 0C39 "part (1)"]
public theorem numberOfBranches_eq_one_iff (X : Scheme.{u}) (x : X) :
    numberOfBranches X x = 1 ↔ IsUnibranchAt X x :=
  numberOfBranchesOfLocalRing_eq_one_iff _

/-- A scheme has exactly one geometric branch at a point if and only if it is geometrically
unibranch at that point. -/
@[stacks 0C39 "part (2)"]
public theorem numberOfGeometricBranches_eq_one_iff (X : Scheme.{u}) (x : X) :
    numberOfGeometricBranches X x = 1 ↔ IsGeometricallyUnibranchAt X x :=
  numberOfGeometricBranchesOfLocalRing_eq_one_iff _

/-- A normal local ring is geometrically unibranch. -/
@[ega "0 23.2.1",
  ega "III 4.3.6" "more general",
  sga "4 IX 2.14.1" "special case",
  sga "4 XVII 6.2.6" "special case"]
private theorem isGeometricallyUnibranchRing_of_normal
    {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R]
    (hR : IsIntegrallyClosed R) : IsGeometricallyUnibranchRing R := by
  have hnil : nilradical R = ⊥ := nilradical_eq_bot_iff.mpr inferInstance
  let e : (R ⧸ nilradical R) ≃+* R :=
    (Ideal.quotEquivOfEq hnil).trans (RingEquiv.quotientBot R)
  have : IsDomain (R ⧸ nilradical R) := e.symm.isDomain_iff.mp inferInstance
  have : IsIntegrallyClosed R := hR
  let q : R →+* R ⧸ nilradical R := Ideal.Quotient.mk _
  have : IsLocalRing (R ⧸ nilradical R) :=
    IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  have : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have : IsIntegrallyClosed (R ⧸ nilradical R) := IsIntegrallyClosed.of_equiv e.symm
  let C := integralClosure (R ⧸ nilradical R) (FractionRing (R ⧸ nilradical R))
  have hCsurj : Function.Surjective (algebraMap (R ⧸ nilradical R) C) := by
    intro z
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral z.2
    exact ⟨r, Subtype.ext hr⟩
  have : IsLocalRing C :=
    IsLocalRing.of_surjective' (algebraMap (R ⧸ nilradical R) C) hCsurj
  let f : R →+* C := (algebraMap (R ⧸ nilradical R) C).comp q
  let : Algebra R C := f.toAlgebra
  have : IsLocalHom f := RingHom.isLocalHom_comp _ _
  unfold IsGeometricallyUnibranchRing
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hAlgSurj : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField C)) := by
    intro y
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, rfl⟩ := hCsurj.comp Ideal.Quotient.mk_surjective z
    exact ⟨IsLocalRing.residue R r, IsLocalRing.ResidueField.algebraMap_residue r⟩
  refine ⟨Algebra.isIntegral_def.mpr ?_, ?_⟩
  · intro z
    obtain ⟨r, rfl⟩ := hAlgSurj z
    exact isIntegral_algebraMap
  · intro z _
    obtain ⟨r, hr⟩ := hAlgSurj z
    exact ⟨r, hr⟩

/-- A normal scheme is geometrically unibranch. -/
@[stacks 0BQ3,
  ega "III 4.3.6" "normal ⇒ unibranch",
  ega "IV 6.15.6" "k' = k",
  sga "4 IX 2.14.1",
  sga "4 XVII 6.2.6" "more general"]
public theorem isGeometricallyUnibranch_of_isNormal {X : Scheme.{u}}
    [IsNormal X] : IsGeometricallyUnibranch X :=
  fun x => isGeometricallyUnibranchRing_of_normal (IsNormal.stalk_normal x)

end AlgebraicGeometry

end
