module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.SetTheory.Cardinal.Subfield
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.Extend
public import StacksFrontier.RingTheory.DividedPowers.Ring
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.RingTheory.Flat.TorCriterion
public import StacksFrontier.RingTheory.Tor.Vanishing

/-!
# Divided power envelopes: the construction

This file defines morphisms of ring--ideal pairs (`Crystalline.IdealPair.Hom`) and morphisms of
pairs over a fixed source pair (`Crystalline.IdealPair.HomOver`), the structure
`Crystalline.DividedPowerEnvelope` recording a divided power envelope with its universal Hom
equivalence, and the construction of an envelope when the base and the algebra lie in the same
universe: the functor of compatible maps preserves limits and has a solution set of bounded
cardinality, so Brown representability for divided power rings corepresents it.
-/

@[expose] public section

namespace Crystalline

section Envelope

universe u v w x

/-- Morphisms of ring--ideal pairs: ring homomorphisms which carry the source ideal into the
target ideal. -/
public structure IdealPair.Hom {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) extends R →+* S where
  /-- The distinguished ideal of the source maps into the distinguished ideal of the target. -/
  ideal_comp : I.map toRingHom ≤ J

namespace IdealPair.Hom

variable {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]
  {I : Ideal R} {J : Ideal S} {K : Ideal T}

/-- Regard a ring homomorphism preserving the distinguished ideals as a morphism of
ring--ideal pairs. -/
public def ofRingHom (f : R →+* S) (hf : I.map f ≤ J) : IdealPair.Hom I J where
  toRingHom := f
  ideal_comp := hf

/-- The composite of two morphisms of ring--ideal pairs. -/
public def comp (g : IdealPair.Hom J K) (f : IdealPair.Hom I J) : IdealPair.Hom I K where
  toRingHom := g.toRingHom.comp f.toRingHom
  ideal_comp := by
    rw [← Ideal.map_map f.toRingHom g.toRingHom]
    exact (Ideal.map_mono f.ideal_comp).trans g.ideal_comp

/-- A divided power morphism is, after forgetting divided powers, a morphism of the underlying
ring--ideal pairs. -/
public def ofDPMorphism {hI : DividedPowers I} {hJ : DividedPowers J}
    (f : DividedPowers.DPMorphism hI hJ) : IdealPair.Hom I J where
  toRingHom := f.toRingHom
  ideal_comp := f.ideal_comp

end IdealPair.Hom

namespace IdealPair.Hom

/-- A morphism of ring--ideal pairs is determined by its underlying ring homomorphism. -/
public theorem ext_toRingHom {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {I : Ideal R} {J : Ideal S} (f g : IdealPair.Hom I J)
    (h : f.toRingHom = g.toRingHom) : f = g := by
  cases f
  cases g
  congr

private theorem comp_toRingHom {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T]
    {I : Ideal R} {J : Ideal S} {K : Ideal T}
    (g : IdealPair.Hom J K) (f : IdealPair.Hom I J) :
    (comp g f).toRingHom = g.toRingHom.comp f.toRingHom := rfl

private theorem ofDPMorphism_comp {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T]
    {I : Ideal R} {J : Ideal S} {K : Ideal T}
    {hI : DividedPowers I} {hJ : DividedPowers J} {hK : DividedPowers K}
    (g : DividedPowers.DPMorphism hJ hK)
    (f : DividedPowers.DPMorphism hI hJ) :
    ofDPMorphism (g.comp f) = comp (ofDPMorphism g) (ofDPMorphism f) := by
  apply ext_toRingHom
  rfl

private theorem comp_assoc {R : Type u} {S : Type v} {T : Type w} {U : Type x}
    [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    {I : Ideal R} {J : Ideal S} {K : Ideal T} {L : Ideal U}
    (h : IdealPair.Hom K L) (g : IdealPair.Hom J K) (f : IdealPair.Hom I J) :
    comp (comp h g) f = comp h (comp g f) := by
  apply ext_toRingHom
  rfl

/-- A morphism of ring--ideal pairs sends elements of the source ideal into the target ideal. -/
private theorem apply_mem {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {I : Ideal R} {J : Ideal S} (f : IdealPair.Hom I J) {x : R} (hx : x ∈ I) :
    f.toRingHom x ∈ J :=
  f.ideal_comp (Ideal.mem_map_of_mem _ hx)

end IdealPair.Hom

/-- Morphisms of ring--ideal pairs over a fixed source pair. -/
public def IdealPair.HomOver {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    {I : Ideal A} {J : Ideal B} {K : Ideal C}
    (f : IdealPair.Hom I J) (a : IdealPair.Hom I K) :=
  {g : IdealPair.Hom J K // IdealPair.Hom.comp g f = a}

open CategoryTheory CategoryTheory.Limits

/-- Compatible maps into one divided power ring. -/
private def envelopeData (A : DividedPowerRing) {B : Type u} [CommRing B]
    (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J)
    (C : DividedPowerRing) :=
  {p : (A ⟶ C) × IdealPair.Hom J C.ideal //
    IdealPair.Hom.comp p.2 (IdealPair.Hom.ofRingHom f hJ) =
      IdealPair.Hom.ofDPMorphism p.1}

/-- Two compatible maps are equal when their components agree. -/
private theorem envelopeData_ext {A : DividedPowerRing} {B : Type u} [CommRing B]
    {f : A →+* B} {J : Ideal B} {hJ : A.ideal.map f ≤ J} {C : DividedPowerRing}
    {p q : envelopeData A f J hJ C} (h₁ : p.1.1 = q.1.1)
    (h₂ : p.1.2.toRingHom = q.1.2.toRingHom) : p = q :=
  Subtype.ext (Prod.ext h₁ (IdealPair.Hom.ext_toRingHom _ _ h₂))

/-- The functor of compatible maps from the base divided power ring and the ring--ideal pair.
This is the functor to which the divided-power Brown criterion applies. -/
private def envelopeFunctor (A : DividedPowerRing) {B : Type u} [CommRing B]
    (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J) :
    DividedPowerRing.{u} ⥤ Type u where
  obj C := envelopeData A f J hJ C
  map {C D} g := ↾ fun (p : envelopeData A f J hJ C) ↦
    ⟨(g.comp p.1.1, IdealPair.Hom.comp
    (IdealPair.Hom.ofDPMorphism g) p.1.2), by
      dsimp only [envelopeData] at p
      change IdealPair.Hom.comp
        (IdealPair.Hom.comp (IdealPair.Hom.ofDPMorphism g) p.1.2)
        (IdealPair.Hom.ofRingHom f hJ) =
        IdealPair.Hom.ofDPMorphism (g.comp p.1.1)
      rw [IdealPair.Hom.comp_assoc, p.2]
      exact (IdealPair.Hom.ofDPMorphism_comp g p.1.1).symm⟩
  map_id := by
    intro C
    ext p
    exact envelopeData_ext rfl rfl
  map_comp := by
    intro C D E g h
    ext p
    exact envelopeData_ext rfl rfl

/-- Evaluation of a corepresentation at a map is composition with its universal element. -/
private theorem corepresentation_apply (A : DividedPowerRing) {B : Type u} [CommRing B]
    (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J)
    (E : DividedPowerRing) (R : (envelopeFunctor A f J hJ).CorepresentableBy E)
    (C : DividedPowerRing) (q : E ⟶ C) :
    R.homEquiv q = (envelopeFunctor A f J hJ).map q (R.homEquiv (𝟙 E)) := by
  simpa only [Category.id_comp] using R.homEquiv_comp q (𝟙 E)

/-- Data satisfying the universal property of the divided power envelope of `J` relative to
the divided powers on `A.ideal`.

For every divided power ring `C` over `A`, restriction along `algebraMap` identifies divided
power morphisms from the envelope to `C` over `A` with morphisms `(B, J) → (C, C.ideal)` over
`(A, A.ideal)`. -/
public structure DividedPowerEnvelope (A : DividedPowerRing.{u}) {B : Type v} [CommRing B]
    (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J) where
  /-- The divided power ring underlying the envelope. -/
  object : DividedPowerRing.{max u v}
  /-- The homomorphism of divided power rings from the base to the envelope. -/
  structureMap : DividedPowers.DPMorphism A.dividedPowers object.dividedPowers
  /-- The canonical morphism from `(B, J)` to the underlying ring--ideal pair of the envelope. -/
  algebraMap : IdealPair.Hom J object.ideal
  /-- The canonical map from `B` agrees with the structural divided power morphism on `A`. -/
  algebraMap_comp :
    algebraMap.toRingHom.comp f = structureMap.toRingHom
  /-- The universal Hom equivalence defining the divided power envelope. -/
  homEquiv (C : DividedPowerRing.{max u v})
      (a : DividedPowers.DPMorphism A.dividedPowers C.dividedPowers) :
    {q : DividedPowers.DPMorphism object.dividedPowers C.dividedPowers //
        q.comp structureMap = a} ≃
      IdealPair.HomOver (IdealPair.Hom.ofRingHom f hJ)
        (IdealPair.Hom.ofDPMorphism a)
  /-- The universal Hom equivalence is the canonical one induced by restriction along the map
  from `(B, J)`. -/
  homEquiv_apply (C : DividedPowerRing.{max u v})
      (a : DividedPowers.DPMorphism A.dividedPowers C.dividedPowers)
      (q : {q : DividedPowers.DPMorphism object.dividedPowers C.dividedPowers //
        q.comp structureMap = a}) :
    (homEquiv C a q).1 =
      IdealPair.Hom.comp (IdealPair.Hom.ofDPMorphism q.1) algebraMap

/-- A corepresentation of the compatible-map functor supplies the desired envelope. -/
private noncomputable def envelopeOfCorepresentation (A : DividedPowerRing)
    {B : Type u} [CommRing B] (f : A →+* B) (J : Ideal B)
    (hJ : A.ideal.map f ≤ J) (E : DividedPowerRing)
    (R : (envelopeFunctor A f J hJ).CorepresentableBy E) :
    DividedPowerEnvelope A f J hJ := by
  let U := R.homEquiv (𝟙 E)
  have hmap (C : DividedPowerRing) (q : E ⟶ C) :
      (R.homEquiv q).1.1 = q.comp U.1.1 :=
    congrArg (fun x : envelopeData A f J hJ C => x.1.1)
      (corepresentation_apply A f J hJ E R C q)
  refine {
    object := E
    structureMap := U.1.1
    algebraMap := U.1.2
    algebraMap_comp := ?_
    homEquiv := ?_
    homEquiv_apply := ?_ }
  · exact congrArg IdealPair.Hom.toRingHom U.2
  · intro C a
    refine {
      toFun := fun q => ⟨(R.homEquiv q.1).1.2, ?_⟩
      invFun := fun t => ⟨R.homEquiv.symm ⟨(a, t.1), t.2⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
    · exact (R.homEquiv q.1).2.trans (by
        rw [hmap C q.1, q.2])
    · exact (hmap C (R.homEquiv.symm ⟨(a, t.1), t.2⟩)).symm.trans (congrArg
        (fun x : envelopeData A f J hJ C => x.1.1)
        (R.homEquiv.apply_symm_apply ⟨(a, t.1), t.2⟩))
    · intro q
      apply Subtype.ext
      apply R.homEquiv.injective
      exact (R.homEquiv.apply_symm_apply _).trans (by
        apply Subtype.ext
        apply Prod.ext
        · exact ((hmap C q.1).trans q.2).symm
        · rfl)
    · exact fun t => Subtype.ext (congrArg (fun x : envelopeData A f J hJ C => x.1.2)
        (R.homEquiv.apply_symm_apply ⟨(a, t.1), t.2⟩))
  · intro C a q
    exact congrArg (fun x : envelopeData A f J hJ C => x.1.2)
      (corepresentation_apply A f J hJ E R C q.1)

/-- The two hypotheses needed to apply the divided-power Brown criterion. -/
private noncomputable def envelopeOfBrown (A : DividedPowerRing)
    {B : Type u} [CommRing B] (f : A →+* B) (J : Ideal B)
    (hJ : A.ideal.map f ≤ J)
    (hLimits : CategoryTheory.Limits.PreservesLimitsOfSize.{u, u}
      (envelopeFunctor A f J hJ))
    (hSmall : ∃ κ : Cardinal.{u},
      ∀ (C : DividedPowerRing) (x : (envelopeFunctor A f J hJ).obj C),
        ∃ (C' : DividedPowerRing) (x' : (envelopeFunctor A f J hJ).obj C')
          (g : C' ⟶ C),
          (envelopeFunctor A f J hJ).map g x' = x ∧ Cardinal.mk C' ≤ κ) :
    DividedPowerEnvelope A f J hJ := by
  let F := envelopeFunctor A f J hJ
  let : CategoryTheory.Limits.PreservesLimitsOfSize.{u, u} F := hLimits
  let : F.IsCorepresentable :=
    DividedPowerRing.isCorepresentable_of_cardinal_solutionSet F hSmall
  exact envelopeOfCorepresentation A f J hJ F.coreprX F.corepresentableBy

/-- The powers of elements of `J` in a target divided power ring. -/
private def powerGenerators {B : Type u} [CommRing B] (J : Ideal B)
    (C : DividedPowerRing) (b : IdealPair.Hom J C.ideal) : Set C :=
  {x | ∃ (n : ℕ) (_ : n ≠ 0) (j : B) (_ : j ∈ J),
    x = C.dividedPowers.dpow n (b.toRingHom j)}

/-- A small candidate subring containing both structural images and the needed divided powers. -/
private def candidateSubring (A : DividedPowerRing) {B : Type u} [CommRing B]
    (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal) : Subring C :=
  Subring.closure (Set.range a.toRingHom ∪ Set.range b.toRingHom ∪
    powerGenerators J C b)

private theorem powerGenerators_subset_ideal {B : Type u} [CommRing B]
    (J : Ideal B) (C : DividedPowerRing) (b : IdealPair.Hom J C.ideal) :
    powerGenerators J C b ⊆ C.ideal := by
  rintro x ⟨n, hn, j, hj, rfl⟩
  exact C.dividedPowers.dpow_mem hn (b.apply_mem hj)

private theorem baseRange_le_candidate (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal) :
    a.toRingHom.range ≤ candidateSubring A J C a b :=
  fun _ hx => Subring.subset_closure (Or.inl (Or.inl hx))

private theorem ringRange_le_candidate (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal) :
    b.toRingHom.range ≤ candidateSubring A J C a b :=
  fun _ hx => Subring.subset_closure (Or.inl (Or.inr hx))

private theorem powers_mem_candidate (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal)
    (n : ℕ) (hn : n ≠ 0) (j : B) (hj : j ∈ J) :
    C.dividedPowers.dpow n (b.toRingHom j) ∈ candidateSubring A J C a b :=
  Subring.subset_closure (Or.inr ⟨n, hn, j, hj, rfl⟩)

/-- Generators for the divided power ideal inside the candidate subring. -/
private def candidateIdealGenerators (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal) :
    Set (candidateSubring A J C a b) :=
  {x | (∃ i : A, i ∈ A.ideal ∧ (x : C) = a.toRingHom i) ∨
    (x : C) ∈ powerGenerators J C b}

private def candidateIdeal (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal) :
    Ideal (candidateSubring A J C a b) :=
  Ideal.span (candidateIdealGenerators A J C a b)

private theorem candidateIdeal_le_ambient (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal) :
    candidateIdeal A J C a b ≤ C.ideal.comap
      (SubringClass.subtype (candidateSubring A J C a b)) := by
  rw [candidateIdeal, Ideal.span_le]
  intro x hx
  rcases hx with ⟨i, hi, hx⟩ | hx
  · show (x : C) ∈ C.ideal
    rw [hx]
    exact a.ideal_comp (Ideal.mem_map_of_mem _ hi)
  · exact powerGenerators_subset_ideal J C b hx

private def candidateBaseHom (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal) :
    A →+* candidateSubring A J C a b :=
  a.toRingHom.codRestrict _ fun i =>
    baseRange_le_candidate A J C a b (a.toRingHom.mem_range_self i)

private def candidateRingHom (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal) :
    B →+* candidateSubring A J C a b :=
  b.toRingHom.codRestrict _ fun j =>
    ringRange_le_candidate A J C a b (b.toRingHom.mem_range_self j)

private theorem baseIdeal_le_candidate (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal) :
    A.ideal.map (candidateBaseHom A J C a b) ≤ candidateIdeal A J C a b := by
  rw [Ideal.map_le_iff_le_comap]
  intro i hi
  exact Ideal.subset_span (Or.inl ⟨i, hi, rfl⟩)

private theorem ringIdeal_le_candidate (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal) :
    J.map (candidateRingHom A J C a b) ≤ candidateIdeal A J C a b := by
  rw [Ideal.map_le_iff_le_comap]
  intro j hj
  apply Ideal.subset_span
  right
  refine ⟨1, one_ne_zero, j, hj, ?_⟩
  exact (C.dividedPowers.dpow_one
    (b.apply_mem hj)).symm

/-- Divided powers of the chosen ideal generators already lie in the candidate ideal. -/
private theorem candidateGenerator_dpow (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal)
    (x : candidateSubring A J C a b)
    (hx : x ∈ candidateIdealGenerators A J C a b)
    (n : ℕ) (hn : n ≠ 0) :
    ∃ y : candidateSubring A J C a b,
      y ∈ candidateIdeal A J C a b ∧
        (y : C) = C.dividedPowers.dpow n (x : C) := by
  rcases hx with ⟨i, hi, hxi⟩ | ⟨m, hm, j, hj, hxj⟩
  · refine ⟨candidateBaseHom A J C a b (A.dividedPowers.dpow n i), ?_, ?_⟩
    · exact baseIdeal_le_candidate A J C a b
        (Ideal.mem_map_of_mem _ (A.dividedPowers.dpow_mem hn hi))
    · show a.toRingHom (A.dividedPowers.dpow n i) =
        C.dividedPowers.dpow n (x : C)
      rw [hxi]
      exact (a.dpow_comp i hi).symm
  · let z : candidateSubring A J C a b :=
      ⟨C.dividedPowers.dpow (n * m) (b.toRingHom j),
        powers_mem_candidate A J C a b (n * m) (mul_ne_zero hn hm) j hj⟩
    have hz : z ∈ candidateIdeal A J C a b := by
      apply Ideal.subset_span
      right
      exact ⟨n * m, mul_ne_zero hn hm, j, hj, rfl⟩
    refine ⟨(Nat.uniformBell n m : candidateSubring A J C a b) * z,
      (candidateIdeal A J C a b).mul_mem_left _ hz, ?_⟩
    show (Nat.uniformBell n m : C) *
      C.dividedPowers.dpow (n * m) (b.toRingHom j) =
        C.dividedPowers.dpow n (x : C)
    rw [hxj]
    exact (C.dividedPowers.dpow_comp hm
      (b.apply_mem hj)).symm

/-- The candidate ideal is closed under the divided powers of the ambient ring. -/
private theorem candidateIdeal_dpow (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal)
    (x : candidateSubring A J C a b)
    (hx : x ∈ candidateIdeal A J C a b)
    (n : ℕ) (hn : n ≠ 0) :
    ∃ y : candidateSubring A J C a b,
      y ∈ candidateIdeal A J C a b ∧
        (y : C) = C.dividedPowers.dpow n (x : C) := by
  let S := candidateSubring A J C a b
  let K := candidateIdeal A J C a b
  have hK : ∀ z : S, z ∈ K → (z : C) ∈ C.ideal := by
    intro z hz
    exact candidateIdeal_le_ambient A J C a b hz
  have liftPower (z : S) (hz : z ∈ K)
      (hp : ∀ m : ℕ, m ≠ 0 → ∃ w : S, w ∈ K ∧
        (w : C) = C.dividedPowers.dpow m (z : C)) (m : ℕ) :
      ∃ w : S, (w : C) = C.dividedPowers.dpow m (z : C) ∧
        (m ≠ 0 → w ∈ K) := by
    by_cases hm : m = 0
    · refine ⟨1, ?_, ?_⟩
      · simp [hm, C.dividedPowers.dpow_zero (hK z hz)]
      · exact fun h => (h hm).elim
    · obtain ⟨w, hw, heq⟩ := hp m hm
      exact ⟨w, heq, fun _ => hw⟩
  have haux : ∀ z : S, z ∈ K → ∀ m : ℕ, m ≠ 0 →
      ∃ w : S, w ∈ K ∧ (w : C) = C.dividedPowers.dpow m (z : C) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        exact candidateGenerator_dpow A J C a b z hz
    | zero =>
        intro m hm
        refine ⟨0, K.zero_mem, ?_⟩
        simpa using (C.dividedPowers.dpow_eval_zero hm).symm
    | add x y hx hy hpx hpy =>
        intro m hm
        classical
        let px (k : ℕ) := Classical.choose (liftPower x hx hpx k)
        let py (k : ℕ) := Classical.choose (liftPower y hy hpy k)
        let w : S := (Finset.antidiagonal m).sum fun k => px k.1 * py k.2
        refine ⟨w, ?_, ?_⟩
        · apply Submodule.sum_mem K
          intro k hk
          have hk' : k.1 + k.2 = m := Finset.mem_antidiagonal.mp hk
          by_cases h0 : k.1 = 0
          · have h2 : k.2 ≠ 0 := by omega
            exact K.mul_mem_left _ ((Classical.choose_spec
              (liftPower y hy hpy k.2)).2 h2)
          · exact K.mul_mem_right _ ((Classical.choose_spec
              (liftPower x hx hpx k.1)).2 h0)
        · show ((w : S) : C) = C.dividedPowers.dpow m ((x : C) + (y : C))
          rw [C.dividedPowers.dpow_add (hK x hx) (hK y hy)]
          show (SubringClass.subtype S) w = _
          simp only [w, map_sum, map_mul]
          apply Finset.sum_congr rfl
          intro k hk
          show ((px k.1 : S) : C) * ((py k.2 : S) : C) = _
          rw [(Classical.choose_spec (liftPower x hx hpx k.1)).1,
            (Classical.choose_spec (liftPower y hy hpy k.2)).1]
    | smul r x hx hpx =>
        intro m hm
        obtain ⟨w, hw, heq⟩ := hpx m hm
        refine ⟨r ^ m * w, K.mul_mem_left _ hw, ?_⟩
        show (r : C) ^ m * (w : C) =
          C.dividedPowers.dpow m ((r : C) * (x : C))
        rw [heq]
        exact (C.dividedPowers.dpow_mul (hK x hx)).symm
  exact haux x hx n hn

/-- Restrict ambient divided powers to an ideal of a stable subring. -/
private noncomputable def restrictDividedPowers (C : DividedPowerRing)
    (S : Subring C) (L : Ideal S)
    (hL : ∀ x : S, x ∈ L → (x : C) ∈ C.ideal)
    (hPow : ∀ (x : S), x ∈ L → ∀ n : ℕ, n ≠ 0 →
      ∃ y : S, y ∈ L ∧ (y : C) = C.dividedPowers.dpow n (x : C)) :
    DividedPowers L := by
  classical
  let lift (n : ℕ) (x : S) (hx : x ∈ L) : S :=
    if hn : n = 0 then 1 else Classical.choose (hPow x hx n hn)
  have lift_mem (n : ℕ) (x : S) (hx : x ∈ L) (hn : n ≠ 0) :
      lift n x hx ∈ L := by
    simp only [lift, dite_eq_right hn]
    exact (Classical.choose_spec (hPow x hx n hn)).1
  have lift_val (n : ℕ) (x : S) (hx : x ∈ L) :
      ((lift n x hx : S) : C) = C.dividedPowers.dpow n (x : C) := by
    by_cases hn : n = 0
    · simp only [lift, dite_eq_left hn]
      simpa [hn] using (C.dividedPowers.dpow_zero (hL x hx)).symm
    · simp only [lift, dite_eq_right hn]
      exact (Classical.choose_spec (hPow x hx n hn)).2
  refine
    { dpow := fun n x => if hx : x ∈ L then lift n x hx else 0
      dpow_null := fun hx => by simp [dite_eq_right hx]
      dpow_zero := fun {x} hx => by
        apply Subtype.ext
        simp only [dite_eq_left hx, lift_val]
        exact C.dividedPowers.dpow_zero (hL x hx)
      dpow_one := fun {x} hx => by
        apply Subtype.ext
        simp only [dite_eq_left hx, lift_val]
        exact C.dividedPowers.dpow_one (hL x hx)
      dpow_mem := fun {n x} hn hx => by
        simpa only [dite_eq_left hx] using lift_mem n x hx hn
      dpow_add := fun {n x y} hx hy => by
        have hxy := L.add_mem hx hy
        simp only [dite_eq_left hx, dite_eq_left hy]
        split
        next h =>
          apply Subtype.ext
          rw [lift_val n (x + y) h]
          change C.dividedPowers.dpow n ((x : C) + (y : C)) =
            (SubringClass.subtype S) _
          rw [map_sum]
          apply (C.dividedPowers.dpow_add (hL x hx) (hL y hy)).trans
          apply Finset.sum_congr rfl
          intro k hk
          rw [map_mul]
          exact congrArg₂ (fun a b : C => a * b) (lift_val k.1 x hx).symm
            (lift_val k.2 y hy).symm
        next h => exact (h hxy).elim
      dpow_mul := fun {n r x} hx => by
        have hrx := L.mul_mem_left r hx
        simp only [dite_eq_left hx]
        split
        next h =>
          apply Subtype.ext
          rw [lift_val n (r * x) h]
          change C.dividedPowers.dpow n ((r : C) * (x : C)) =
            (SubringClass.subtype S) (r ^ n * lift n x hx)
          rw [map_mul, map_pow]
          exact (C.dividedPowers.dpow_mul (a := (r : C)) (hL x hx)).trans
            (congrArg ((SubringClass.subtype S) r ^ n * ·)
              (lift_val n x hx).symm)
        next h => exact (h hrx).elim
      mul_dpow := fun {m n x} hx => by
        simp only [dite_eq_left hx]
        apply Subtype.ext
        change (lift m x hx : C) * (lift n x hx : C) =
          ((Nat.choose (m + n) m : S) : C) * (lift (m + n) x hx : C)
        simp only [lift_val]
        exact C.dividedPowers.mul_dpow (hL x hx)
      dpow_comp := fun {n m x} hm hx => by
        simp only [dite_eq_left hx, dite_eq_left (lift_mem m x hx hm)]
        apply Subtype.ext
        change (lift n (lift m x hx) (lift_mem m x hx hm) : C) =
          ((Nat.uniformBell n m : S) : C) * (lift (n * m) x hx : C)
        simp only [lift_val]
        exact C.dividedPowers.dpow_comp hm (hL x hx) }

private noncomputable def candidateDividedPowers (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal) :
    DividedPowers (candidateIdeal A J C a b) :=
  restrictDividedPowers C (candidateSubring A J C a b)
    (candidateIdeal A J C a b)
    (fun _x hx => candidateIdeal_le_ambient A J C a b hx)
    (candidateIdeal_dpow A J C a b)

private theorem restrictDividedPowers_dpow (C : DividedPowerRing)
    (S : Subring C) (L : Ideal S)
    (hL : ∀ x : S, x ∈ L → (x : C) ∈ C.ideal)
    (hPow : ∀ (x : S), x ∈ L → ∀ n : ℕ, n ≠ 0 →
      ∃ y : S, y ∈ L ∧ (y : C) = C.dividedPowers.dpow n (x : C))
    (n : ℕ) (x : S) (hx : x ∈ L) :
    (((restrictDividedPowers C S L hL hPow).dpow n x : S) : C) =
      C.dividedPowers.dpow n (x : C) := by
  classical
  by_cases hn : n = 0
  · simp only [restrictDividedPowers, hx, dite_true, hn]
    exact (C.dividedPowers.dpow_zero (hL x hx)).symm
  · simp only [restrictDividedPowers, hx, dite_true, hn, dite_false]
    exact (Classical.choose_spec (hPow x hx n hn)).2

private theorem candidateDividedPowers_dpow (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal)
    (n : ℕ) (x : candidateSubring A J C a b)
    (hx : x ∈ candidateIdeal A J C a b) :
    (((candidateDividedPowers A J C a b).dpow n x :
      candidateSubring A J C a b) : C) =
      C.dividedPowers.dpow n (x : C) :=
  restrictDividedPowers_dpow C _ _ _ _ n x hx

private noncomputable def candidateObject (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal) : DividedPowerRing :=
  .of (candidateSubring A J C a b) (candidateIdeal A J C a b)
    (candidateDividedPowers A J C a b)

private noncomputable def candidateBaseMorphism (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal) :
    A ⟶ candidateObject A J C a b := by
  refine DividedPowers.DPMorphism.mk'
    (f := candidateBaseHom A J C a b) ⟨baseIdeal_le_candidate A J C a b, ?_⟩
  intro n i hi
  have hmem : candidateBaseHom A J C a b i ∈ candidateIdeal A J C a b :=
    baseIdeal_le_candidate A J C a b (Ideal.mem_map_of_mem _ hi)
  apply Subtype.ext
  change (((candidateDividedPowers A J C a b).dpow n
    (candidateBaseHom A J C a b i) : candidateSubring A J C a b) : C) = _
  rw [candidateDividedPowers_dpow A J C a b n _ hmem]
  exact a.dpow_comp i hi

private noncomputable def candidateRingMorphism (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal) :
    IdealPair.Hom J (candidateObject A J C a b).ideal :=
  IdealPair.Hom.ofRingHom (candidateRingHom A J C a b)
    (ringIdeal_le_candidate A J C a b)

private noncomputable def candidateInclusion (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal) :
    candidateObject A J C a b ⟶ C := by
  refine DividedPowers.DPMorphism.mk'
    (f := SubringClass.subtype (candidateSubring A J C a b)) ⟨?_, ?_⟩
  · change (candidateIdeal A J C a b).map
      (SubringClass.subtype (candidateSubring A J C a b)) ≤ C.ideal
    rw [Ideal.map_le_iff_le_comap]
    exact candidateIdeal_le_ambient A J C a b
  · intro n x hx
    change candidateSubring A J C a b at x
    change x ∈ candidateIdeal A J C a b at hx
    change C.dividedPowers.dpow n
      ((x : candidateSubring A J C a b) : C) =
      (((candidateDividedPowers A J C a b).dpow n x :
        candidateSubring A J C a b) : C)
    exact (candidateDividedPowers_dpow A J C a b n x hx).symm

private noncomputable def candidateData (A : DividedPowerRing)
    {B : Type u} [CommRing B] (f : A →+* B) (J : Ideal B)
    (hJ : A.ideal.map f ≤ J) (C : DividedPowerRing)
    (p : (envelopeFunctor A f J hJ).obj C) :
    (envelopeFunctor A f J hJ).obj
      (candidateObject A J C p.1.1 p.1.2) := by
  refine ⟨(candidateBaseMorphism A J C p.1.1 p.1.2,
    candidateRingMorphism A J C p.1.1 p.1.2), ?_⟩
  apply IdealPair.Hom.ext_toRingHom
  apply RingHom.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun h : IdealPair.Hom A.ideal C.ideal => h.toRingHom x) p.2

private theorem candidateData_map (A : DividedPowerRing)
    {B : Type u} [CommRing B] (f : A →+* B) (J : Ideal B)
    (hJ : A.ideal.map f ≤ J) (C : DividedPowerRing)
    (p : (envelopeFunctor A f J hJ).obj C) :
    (envelopeFunctor A f J hJ).map
      (candidateInclusion A J C p.1.1 p.1.2)
      (candidateData A f J hJ C p) = p := by
  exact envelopeData_ext rfl rfl

private abbrev ringClosureOperands {R : Type u} (s : Set R) : Fin 5 ⊕ s → Type
  | .inl 0 => Bool
  | .inl 1 => Bool
  | .inl 2 => Unit
  | .inl 3 => Empty
  | .inl 4 => Empty
  | .inr _ => Empty

private def ringClosureOperate {R : Type u} [CommRing R] (s : Set R) :
    (Σ n, ringClosureOperands s n → Subring.closure s) → Subring.closure s
  | ⟨.inl 0, f⟩ => f false + f true
  | ⟨.inl 1, f⟩ => f false * f true
  | ⟨.inl 2, f⟩ => -f ()
  | ⟨.inl 3, _⟩ => 0
  | ⟨.inl 4, _⟩ => 1
  | ⟨.inr a, _⟩ => ⟨a, Subring.subset_closure a.prop⟩

private def ringClosureRange {R : Type u} [CommRing R] (s : Set R) :
    Subring (Subring.closure s) where
  carrier := Set.range (WType.elim _ (ringClosureOperate s))
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨WType.mk (.inl 0) (Bool.rec x y), rfl⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨WType.mk (.inl 1) (Bool.rec x y), rfl⟩
  neg_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨WType.mk (.inl 2) fun _ => x, rfl⟩
  zero_mem' := ⟨WType.mk (.inl 3) Empty.rec, rfl⟩
  one_mem' := ⟨WType.mk (.inl 4) Empty.rec, rfl⟩

private theorem ringClosureRange_eq_top {R : Type u} [CommRing R] (s : Set R) :
    ringClosureRange s = ⊤ := by
  apply top_le_iff.mp
  intro x hx
  rw [← SetLike.mem_coe, ← Subtype.val_injective.mem_set_image]
  show (x : R) ∈ Subring.map (Subring.closure s).subtype (ringClosureRange s)
  refine Subring.closure_le.mpr (fun a ha => ?_) x.prop
  exact ⟨⟨a, Subring.subset_closure ha⟩,
    ⟨WType.mk (.inr ⟨a, ha⟩) Empty.rec, rfl⟩, rfl⟩

private theorem cardinalMk_ringClosure_le_max {R : Type u} [CommRing R] (s : Set R) :
    Cardinal.mk (Subring.closure s) ≤ max (Cardinal.mk s) Cardinal.aleph0 := by
  have hs : Function.Surjective (WType.elim _ (ringClosureOperate s)) := by
    rw [← Set.range_eq_univ]
    exact SetLike.coe_set_eq.mpr (ringClosureRange_eq_top s)
  apply (Cardinal.mk_le_of_surjective hs).trans
  convert! WType.cardinalMk_le_max_aleph0_of_finite' using 1
  · rw [Cardinal.lift_uzero, Cardinal.mk_sum, Cardinal.lift_uzero]
    have hfin : Cardinal.lift.{u, 0} (Cardinal.mk (Fin 5)) < Cardinal.aleph0 :=
      Cardinal.lift_lt_aleph0.mpr (Cardinal.lt_aleph0_of_finite _)
    obtain h | h := lt_or_ge (Cardinal.mk s) Cardinal.aleph0
    · rw [max_eq_right h.le, max_eq_right]
      exact (Cardinal.add_lt_aleph0 hfin h).le
    · rw [max_eq_left h, Cardinal.add_eq_right h (hfin.le.trans h), max_eq_left h]
  · rintro (n | _)
    · fin_cases n <;> (dsimp only [ringClosureOperands, id_eq]; infer_instance)
    infer_instance

private theorem cardinalMk_powerGenerators_le
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (b : IdealPair.Hom J C.ideal) :
    Cardinal.mk (powerGenerators J C b) ≤
      max (Cardinal.mk B) Cardinal.aleph0 := by
  let g : {n : ℕ // n ≠ 0} × J → powerGenerators J C b :=
    fun p => ⟨C.dividedPowers.dpow p.1.1 (b.toRingHom p.2.1),
      ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩⟩
  have hg : Function.Surjective g := by
    rintro ⟨x, n, hn, j, hj, rfl⟩
    exact ⟨(⟨n, hn⟩, ⟨j, hj⟩), rfl⟩
  have hi : Function.Injective
      (fun p : {n : ℕ // n ≠ 0} × J => ((p.1.1, p.2.1) : ℕ × B)) := by
    intro p q h
    cases p with
    | mk n j =>
      cases q with
      | mk n' j' =>
        cases n
        cases n'
        cases j
        cases j'
        cases h
        rfl
  calc
    Cardinal.mk (powerGenerators J C b) ≤ Cardinal.mk ({n : ℕ // n ≠ 0} × J) :=
      Cardinal.mk_le_of_surjective hg
    _ ≤ Cardinal.mk (ℕ × B) := Cardinal.mk_le_of_injective hi
    _ ≤ max (Cardinal.mk B) Cardinal.aleph0 := by
      simpa only [Cardinal.mk_prod, Cardinal.lift_uzero, Cardinal.lift_aleph0, Cardinal.mk_nat,
        max_comm] using Cardinal.mul_le_max_of_aleph0_le_left
          (le_refl Cardinal.aleph0) (b := Cardinal.mk B)

private theorem candidateCardinal_le (A : DividedPowerRing)
    {B : Type u} [CommRing B] (J : Ideal B) (C : DividedPowerRing)
    (a : A ⟶ C) (b : IdealPair.Hom J C.ideal) :
    Cardinal.mk (candidateObject A J C a b) ≤
      max (max (Cardinal.mk A) (Cardinal.mk B)) Cardinal.aleph0 := by
  let κ := max (max (Cardinal.mk A) (Cardinal.mk B)) Cardinal.aleph0
  have hκ : Cardinal.aleph0 ≤ κ := le_max_right _ _
  have ha : Cardinal.mk (Set.range a.toRingHom) ≤ κ :=
    Cardinal.mk_range_le.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hb : Cardinal.mk (Set.range b.toRingHom) ≤ κ :=
    Cardinal.mk_range_le.trans ((le_max_right _ _).trans (le_max_left _ _))
  have hp : Cardinal.mk (powerGenerators J C b) ≤ κ :=
    (cardinalMk_powerGenerators_le J C b).trans
      (max_le ((le_max_right _ _).trans (le_max_left _ _)) hκ)
  have hgen : Cardinal.mk ((Set.range a.toRingHom ∪
      Set.range b.toRingHom ∪ powerGenerators J C b) : Set C) ≤ κ := by
    calc
      _ ≤ Cardinal.mk ((Set.range a.toRingHom ∪ Set.range b.toRingHom) : Set C) +
          Cardinal.mk (powerGenerators J C b) := Cardinal.mk_union_le _ _
      _ ≤ (Cardinal.mk (Set.range a.toRingHom) +
          Cardinal.mk (Set.range b.toRingHom)) +
          Cardinal.mk (powerGenerators J C b) :=
            add_le_add (Cardinal.mk_union_le _ _) le_rfl
      _ ≤ κ := Cardinal.add_le_of_le hκ (Cardinal.add_le_of_le hκ ha hb) hp
  show Cardinal.mk (candidateSubring A J C a b) ≤ κ
  exact (cardinalMk_ringClosure_le_max _).trans (max_le hgen hκ)

private theorem envelopeSolutionSet (A : DividedPowerRing)
    {B : Type u} [CommRing B] (f : A →+* B) (J : Ideal B)
    (hJ : A.ideal.map f ≤ J) :
    ∃ κ : Cardinal.{u},
      ∀ (C : DividedPowerRing) (x : (envelopeFunctor A f J hJ).obj C),
        ∃ (C' : DividedPowerRing) (x' : (envelopeFunctor A f J hJ).obj C')
          (g : C' ⟶ C),
          (envelopeFunctor A f J hJ).map g x' = x ∧ Cardinal.mk C' ≤ κ :=
  ⟨max (max (Cardinal.mk A) (Cardinal.mk B)) Cardinal.aleph0, fun C x =>
    ⟨candidateObject A J C x.1.1 x.1.2, candidateData A f J hJ C x,
      candidateInclusion A J C x.1.1 x.1.2, candidateData_map A f J hJ C x,
      candidateCardinal_le A J C x.1.1 x.1.2⟩⟩

private noncomputable def envelopeLimitLift (A : DividedPowerRing)
    {B : Type u} [CommRing B] (f : A →+* B) (J : Ideal B)
    (hJ : A.ideal.map f ≤ J) {ι : Type u} [Category.{u} ι]
    (D : ι ⥤ DividedPowerRing)
    (c : Cone (D ⋙ envelopeFunctor A f J hJ)) :
    c.pt ⟶ (envelopeFunctor A f J hJ).obj (DividedPowerRing.limitObject D) := by
  refine ↾ fun x => ?_
  have hcompat (i j : ι) (g : i ⟶ j) :
      (D.map g).comp (c.π.app i x).1.1 = (c.π.app j x).1.1 ∧
        IdealPair.Hom.comp (IdealPair.Hom.ofDPMorphism (D.map g))
          (c.π.app i x).1.2 = (c.π.app j x).1.2 := by
    have h := congrArg (fun q => q x) (c.w g)
    change (envelopeFunctor A f J hJ).map (D.map g) (c.π.app i x) =
      c.π.app j x at h
    exact ⟨congrArg (fun q : envelopeData A f J hJ (D.obj j) => q.1.1) h,
      congrArg (fun q : envelopeData A f J hJ (D.obj j) => q.1.2) h⟩
  let ac : Cone D :=
    { pt := A
      π :=
        { app := fun i => (c.π.app i x).1.1
          naturality := by
            intro i j g
            change (c.π.app j x).1.1 =
              (D.map g).comp (c.π.app i x).1.1
            exact (hcompat i j g).1.symm } }
  let a : A ⟶ DividedPowerRing.limitObject D := DividedPowerRing.limitLift D ac
  let b : B →+* DividedPowerRing.limitObject D :=
    { toFun := fun z =>
        ⟨fun i => (c.π.app i x).1.2.toRingHom z, by
          intro i j g
          exact congrArg
            (fun q : IdealPair.Hom J (D.obj j).ideal => q.toRingHom z)
            (hcompat i j g).2⟩
      map_one' := Subtype.ext <| funext fun i => (c.π.app i x).1.2.toRingHom.map_one
      map_mul' z w := Subtype.ext <| funext fun i => (c.π.app i x).1.2.toRingHom.map_mul z w
      map_zero' := Subtype.ext <| funext fun i => (c.π.app i x).1.2.toRingHom.map_zero
      map_add' z w := Subtype.ext <| funext fun i => (c.π.app i x).1.2.toRingHom.map_add z w }
  let bp : IdealPair.Hom J (DividedPowerRing.limitObject D).ideal :=
    IdealPair.Hom.ofRingHom b (by
      apply Ideal.map_le_iff_le_comap.mpr
      intro z hz i
      exact (c.π.app i x).1.2.apply_mem hz)
  exact ⟨(a, bp), IdealPair.Hom.ext_toRingHom _ _ <| RingHom.ext fun z => Subtype.ext <|
    funext fun i => congrArg
      (fun q : IdealPair.Hom A.ideal (D.obj i).ideal => q.toRingHom z) (c.π.app i x).2⟩

private noncomputable def envelopeLimitIsLimit (A : DividedPowerRing)
    {B : Type u} [CommRing B] (f : A →+* B) (J : Ideal B)
    (hJ : A.ideal.map f ≤ J) {ι : Type u} [Category.{u} ι]
    (D : ι ⥤ DividedPowerRing) :
    IsLimit ((envelopeFunctor A f J hJ).mapCone (DividedPowerRing.limitCone D)) where
  lift c := envelopeLimitLift A f J hJ D c
  fac c i := by
    ext x
    exact envelopeData_ext rfl rfl
  uniq c m hm := by
    ext x
    refine envelopeData_ext (DividedPowers.DPMorphism.ext (funext fun z => ?_))
      (RingHom.ext fun z => ?_) <;> refine Subtype.ext (funext fun i => ?_)
    · exact congrArg
        (fun q : envelopeData A f J hJ (D.obj i) => q.1.1.toRingHom z)
        (congrArg (fun q => q x) (hm i))
    · exact congrArg
        (fun q : envelopeData A f J hJ (D.obj i) => q.1.2.toRingHom z)
        (congrArg (fun q => q x) (hm i))

private theorem envelopePreservesLimits (A : DividedPowerRing)
    {B : Type u} [CommRing B] (f : A →+* B) (J : Ideal B)
    (hJ : A.ideal.map f ≤ J) :
    PreservesLimitsOfSize.{u, u} (envelopeFunctor A f J hJ) :=
  { preservesLimitsOfShape :=
    { preservesLimit := fun {D} =>
        preservesLimit_of_preserves_limit_cone (DividedPowerRing.limitConeIsLimit D)
          (envelopeLimitIsLimit A f J hJ D) } }

private noncomputable def envelopeConstruction (A : DividedPowerRing)
    {B : Type u} [CommRing B] (f : A →+* B) (J : Ideal B)
    (hJ : A.ideal.map f ≤ J) : DividedPowerEnvelope A f J hJ :=
  envelopeOfBrown A f J hJ (envelopePreservesLimits A f J hJ)
    (envelopeSolutionSet A f J hJ)

end Envelope

end Crystalline

end
