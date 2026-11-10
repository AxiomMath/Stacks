module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.UniformSpace.Cauchy
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleLimit
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.IdealOfDefinition
public import StacksFrontier.Topology.Algebra.RingLimits
public import StacksFrontier.AlgebraicGeometry.FormalScheme.LocallyTopologicallyRingedSpace
public import StacksFrontier.AlgebraicGeometry.FormalScheme.PseudoDiscrete
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Formal spectra and formal schemes à la EGA

The *formal spectrum* `Spf A` of an admissible topological ring `A` is the space of open prime
ideals of `A`, topologised as a subspace of `Spec A`, carrying the structure presheaf
`𝒪_{Spf A} = lim 𝒪_λ`, the limit over the ideals of definition `I_λ` of `A` of the
pseudo-discrete sheaves of topological rings attached to the structure sheaves of the
`Spec (A/I_λ)`. An object of the category `LTRS` of locally topologically ringed spaces is a
*formal scheme* in the sense of EGA when every point has an open neighbourhood isomorphic to a
formal spectrum (Stacks 0AHY).

## Main definitions

* `AlgebraicGeometry.openPrimes` and `AlgebraicGeometry.spfSpace`: the open primes of a
  topological ring and the underlying space of its formal spectrum.
* `AlgebraicGeometry.spfDiagram` and `AlgebraicGeometry.spfPresheaf`: the inverse system of the
  structure sheaves of the `Spec (A/I_λ)`, viewed on `Spf A`, and its limit.
* `AlgebraicGeometry.Spf`: the formal spectrum `(Spf A, 𝒪_{Spf A})`.
* `AlgebraicGeometry.IsFormalScheme` and `AlgebraicGeometry.FormalScheme`: EGA formal schemes,
  the full subcategory of `LTRS` on the objects locally isomorphic to a formal spectrum.

## Main results

* `AlgebraicGeometry.mem_openPrimes_iff_le_of_isWeakIdealOfDefinition`: a prime is open exactly
  when it contains an ideal of definition, which is the source's identification of `Spf A` with
  each `Spec (A/I_λ)`.
* `AlgebraicGeometry.isAdmissible_discrete`: a discrete topological ring is admissible.
* `AlgebraicGeometry.discreteSpecSpfIsoOn`: for a discrete ring `R` the formal spectrum `Spf R` is
  the pseudo-discretisation of `Spec R`, the source's example that `Spf A = Spec A` for `A`
  discrete.

## Implementation notes

The limit defining `𝒪_{Spf A}` is taken in presheaves of topological rings, so objectwise it is
the limit in `TopCommRingCat` of Stacks 0B23. The diagram needs no transport: the triangle
`Spec (A/J) → Spec (A/I) → Spf A` commutes definitionally, because `A/I → A/J` precomposed with
`A → A/I` reduces to `A → A/J`, so the comparison maps of the `Spec` morphisms whisker directly
into morphisms of sheaves on `Spf A`.

`Spf A` is recorded as a presheafed space of topological rings: the source itself defers the
checks that it is a sheaf and that its stalks are local ("At this point one should check several
things"). Correspondingly `AlgebraicGeometry.IsFormalScheme` asks for an isomorphism of
presheafed spaces, which for objects of `LTRS` is the same as an isomorphism in `LTRS`.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open scoped Topology

universe u

/-- Factoring a quotient through itself is the identity. -/
theorem Ideal.Quotient.factor_self {A : Type u} [CommRing A] (I : Ideal A) :
    Ideal.Quotient.factor (le_refl I) = RingHom.id (A ⧸ I) := by
  ext _; rfl

namespace AlgebraicGeometry

open TopologicalRing

/-! ### The formal spectrum -/

section Spf

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The open prime ideals of a topological ring: the points of its formal spectrum. -/
def openPrimes : Set (PrimeSpectrum A) := {p | IsOpen (p.asIdeal : Set A)}

/-- The formal spectrum of `A` as a topological space: its open prime ideals, endowed with the
topology coming from `Spec A`. -/
@[ega "I 10.1.2", sga "3 VIIB 0.1.2" "partial"]
def spfSpace : TopCat.{u} := TopCat.of (openPrimes A)

/-- A family `P` of ideals of a topological ring `A` is a *weak ideal system* when every member
of it is a weak ideal of definition — an open ideal all of whose elements are topologically
nilpotent (Stacks 0AMV) — and the family is closed under intersection with an arbitrary open
ideal.

This is all that the construction of the formal spectrum along `P` needs of the family, and it
is the whole interface the source's arguments about a formal spectrum consume. Membership gives
the identification of each of the schemes `Spec (A/I)`, for `I` in the family, with the space of
open primes of `A`: an open prime contains every element of `I` because the powers of such an
element converge to zero, and a prime containing the open ideal `I` is itself open. Closure
under intersection makes the index of the limit a directed system, so that any two of its terms
are dominated by a third; closure under intersection with an arbitrary open ideal, which is the
stronger statement both families satisfy, additionally puts a member of the family inside every
open ideal, which is what the arguments that choose one term of the system for a given open
kernel consume.

Both the ideals of definition of an admissible topological ring and the weak ideals of
definition of a weakly admissible one form such a family. -/
class IsWeakIdealSystem (P : Ideal A → Prop) : Prop where
  /-- Every ideal of the family is a weak ideal of definition. -/
  isWeakIdealOfDefinition : ∀ I : Ideal A, P I → IsWeakIdealOfDefinition I
  /-- The family is closed under intersection with an arbitrary open ideal. -/
  inf_mem_of_isOpen : ∀ {I J : Ideal A}, P I → IsOpen (J : Set A) → P (I ⊓ J)

omit [IsTopologicalRing A] in
/-- A weak ideal system is closed under intersection: a member of the family is in particular an
open ideal. -/
theorem IsWeakIdealSystem.inf_mem {P : Ideal A → Prop} [IsWeakIdealSystem A P] {I J : Ideal A}
    (hI : P I) (hJ : P J) : P (I ⊓ J) :=
  IsWeakIdealSystem.inf_mem_of_isOpen hI (IsWeakIdealSystem.isWeakIdealOfDefinition J hJ).1

/-- The ideals of `A` belonging to a family `P`, ordered by inclusion: the index of the limit
defining the formal spectrum taken along `P`. -/
abbrev SpfIndex (P : Ideal A → Prop) : Type u := {I : Ideal A // P I}

/-- The ideals of definition of `A`, ordered by inclusion. In any admissible topological ring
the family of all ideals of definition is a fundamental system, so this is the index of the
source's limit over a fundamental system of ideals of definition. -/
abbrev IdealsOfDefinition : Type u := SpfIndex A IsIdealOfDefinition

/-- The weak ideals of definition of `A`, ordered by inclusion. In a weakly admissible
topological ring they form a fundamental system of open neighbourhoods of zero, so this is the
index of McQuillan's limit over a fundamental system of weak ideals of definition. -/
abbrev WeakIdealsOfDefinition : Type u := SpfIndex A IsWeakIdealOfDefinition

/-- A chosen ideal of definition of a pre-admissible topological ring, as a term of the index of
the formal spectrum taken along the ideals of definition. The constructions below need one term
of the inverse system and nothing about which, so they are fed this. -/
noncomputable abbrev preAdmissibleSpfIndex (hA : IsPreAdmissible A) : IdealsOfDefinition A :=
  ⟨hA.choose, hA.choose_spec⟩

/-- A chosen weak ideal of definition of a weakly pre-admissible topological ring, as a term of
the index of McQuillan's formal spectrum. -/
noncomputable abbrev weaklyPreAdmissibleSpfIndex (hA : IsWeaklyPreAdmissible A) :
    WeakIdealsOfDefinition A :=
  ⟨hA.choose, hA.choose_spec⟩

/-- The ideals of definition form a weak ideal system: an ideal of definition is a weak ideal
of definition, and the intersection of an ideal of definition with an open ideal is again an
ideal of definition. -/
instance isWeakIdealSystem_isIdealOfDefinition :
    IsWeakIdealSystem A IsIdealOfDefinition where
  isWeakIdealOfDefinition _ hI := isWeakIdealOfDefinition_of_isIdealOfDefinition hI
  inf_mem_of_isOpen hI hJ := hI.inf_of_isOpen hJ

/-- The weak ideals of definition form a weak ideal system: membership is the condition itself,
and the intersection of a weak ideal of definition with an open ideal — in particular with
another weak ideal of definition — is again one. -/
instance isWeakIdealSystem_isWeakIdealOfDefinition :
    IsWeakIdealSystem A IsWeakIdealOfDefinition where
  isWeakIdealOfDefinition _ hI := hI
  inf_mem_of_isOpen hI hJ := isWeakIdealOfDefinition_inf_of_isOpen_right hI hJ

variable {P : Ideal A → Prop}

/-- The quotient `A ⧸ I` by a member of the family, as an object of `CommRingCat`. -/
abbrev spfQuotientOn (I : SpfIndex A P) : CommRingCat.{u} := CommRingCat.of (A ⧸ I.1)

/-- The quotient `A ⧸ I` by an ideal of definition, as an object of `CommRingCat`.

The ideals-of-definition case of `spfQuotientOn`. -/
@[ega "I 10.10.4" "partial"]
abbrev spfQuotient (I : IdealsOfDefinition A) : CommRingCat.{u} :=
  spfQuotientOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- A prime of `A` is open exactly when it contains a given weak ideal of definition `I`: a
prime containing an open ideal is open, and an open prime contains every element of `I`, the
powers of such an element converging to zero and the prime being a neighbourhood of zero. -/
@[ega "0 7.1.5" "more general"]
theorem mem_openPrimes_iff_le_of_isWeakIdealOfDefinition {I : Ideal A}
    (hI : IsWeakIdealOfDefinition I) (p : PrimeSpectrum A) : p ∈ openPrimes A ↔ I ≤ p.asIdeal := by
  refine ⟨fun hp a ha => ?_, fun h => ?_⟩
  · obtain ⟨n, hn⟩ :=
      (hI.2 a ha).exists_pow_mem_of_mem_nhds (hp.mem_nhds p.asIdeal.zero_mem)
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance n hn
  · exact AddSubgroup.isOpen_mono (H₁ := I.toAddSubgroup) (H₂ := p.asIdeal.toAddSubgroup) h hI.1

/-- A prime of `A` is open exactly when it contains an ideal of definition: a prime containing
an open ideal is open, and an open prime contains a power of any ideal of definition, hence,
being prime, contains the ideal itself.

The ideals-of-definition case of `mem_openPrimes_iff_le_of_isWeakIdealOfDefinition`. -/
@[ega "0 7.1.5" "more general"]
theorem mem_openPrimes_iff_le {I : Ideal A} (hI : IsIdealOfDefinition I) (p : PrimeSpectrum A) :
    p ∈ openPrimes A ↔ I ≤ p.asIdeal :=
  mem_openPrimes_iff_le_of_isWeakIdealOfDefinition A
    (isWeakIdealOfDefinition_of_isIdealOfDefinition hI) p

variable [IsWeakIdealSystem A P]

omit [IsTopologicalRing A] in
/-- The weak ideal of definition underlying a member of a weak ideal system. -/
theorem SpfIndex.isWeakIdealOfDefinition (I : SpfIndex A P) :
    IsWeakIdealOfDefinition I.1 :=
  IsWeakIdealSystem.isWeakIdealOfDefinition I.1 I.2

omit [IsTopologicalRing A] in
/-- A ring carrying a nonempty weak ideal system is weakly pre-admissible: a member of the
system is a weak ideal of definition. -/
theorem isWeaklyPreAdmissible_of_spfIndex (I : SpfIndex A P) : IsWeaklyPreAdmissible A :=
  ⟨I.1, I.isWeakIdealOfDefinition⟩

/-- The intersection of two members of a weak ideal system, as a member of the index: the term
of the inverse system dominating two given ones. -/
def spfIndexMeet (I J : SpfIndex A P) : SpfIndex A P :=
  ⟨I.1 ⊓ J.1, IsWeakIdealSystem.inf_mem A I.2 J.2⟩

/-- The intersection of a member of a weak ideal system with an open ideal, as a member of the
index: the term of the inverse system sitting inside a given open ideal. -/
def spfIndexMeetOpen (I : SpfIndex A P) {J : Ideal A} (hJ : IsOpen (J : Set A)) :
    SpfIndex A P :=
  ⟨I.1 ⊓ J, IsWeakIdealSystem.inf_mem_of_isOpen I.2 hJ⟩

omit [IsTopologicalRing A] in
/-- A member of a weak ideal system sits inside any given open ideal, once the system has a
member at all: intersect that member with the open ideal. -/
theorem exists_spfIndex_le_of_isOpen (I : SpfIndex A P) {J : Ideal A}
    (hJ : IsOpen (J : Set A)) : ∃ K : SpfIndex A P, K.1 ≤ J :=
  ⟨spfIndexMeetOpen A I hJ, inf_le_right⟩

omit [IsTopologicalRing A] in
/-- **One member of a weak ideal system below a whole finite family of open ideals.** A finite
intersection of open ideals is open, so intersecting a member of the system with it gives a
member below every one of them.

This is the uniformity statement behind every argument that chooses an open ideal separately for
each member of a finite family — one quasi-compact open of a formal spectrum at a time, say —
and then needs a single choice serving them all. -/
theorem exists_spfIndex_forall_le (I : SpfIndex A P) {ι : Sort*} [Finite ι] (K : ι → Ideal A)
    (hK : ∀ i, IsOpen (K i : Set A)) : ∃ L : SpfIndex A P, ∀ i, L.1 ≤ K i := by
  have hopen : IsOpen ((⨅ i, K i : Ideal A) : Set A) := by
    rw [Submodule.coe_iInf]
    exact isOpen_iInter_of_finite hK
  exact ⟨spfIndexMeetOpen A I hopen, fun i => inf_le_right.trans (iInf_le _ i)⟩

/-- Every prime of `A ⧸ I`, for `I` in the family, pulls back to an open prime of `A`. -/
theorem spfOfQuotientOn_mem (I : SpfIndex A P) (q : PrimeSpectrum (A ⧸ I.1)) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.1))).base q ∈ openPrimes A := by
  refine (mem_openPrimes_iff_le_of_isWeakIdealOfDefinition A I.isWeakIdealOfDefinition _).2
    fun a ha => ?_
  have h : Ideal.Quotient.mk I.1 a ∈ q.asIdeal := by
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact q.asIdeal.zero_mem
  exact h

/-- Every prime of `A ⧸ I`, for `I` an ideal of definition, pulls back to an open prime of
`A`.

The ideals-of-definition case of `spfOfQuotientOn_mem`. -/
@[ega "I 10.1.1" "partial"]
theorem spfOfQuotient_mem (I : IdealsOfDefinition A) (q : PrimeSpectrum (A ⧸ I.1)) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.1))).base q ∈ openPrimes A :=
  spfOfQuotientOn_mem (A := A) (P := IsIdealOfDefinition) (I := I) (q := q)

/-- For `I` in the family, the closed immersion `Spec (A/I) → Spec A` lands in the open primes,
giving the identification of `Spec (A/I)` with the space of open primes used by the source. -/
noncomputable def spfOfQuotientOn (I : SpfIndex A P) :
    (Spec (spfQuotientOn A I)).toPresheafedSpace.carrier ⟶ spfSpace A :=
  TopCat.ofHom ⟨fun q => ⟨(Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.1))).base q,
      spfOfQuotientOn_mem A I q⟩,
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.1))).base.hom.continuous.subtype_mk _⟩

/-- For an ideal of definition `I`, the closed immersion `Spec (A/I) → Spec A` lands in the open
primes, giving the identification of `Spec (A/I)` with `Spf A` used by the source.

The ideals-of-definition case of `spfOfQuotientOn`. -/
@[reducible, ega "I 10.1.1"] noncomputable def spfOfQuotient (I : IdealsOfDefinition A) :
    (Spec (spfQuotient A I)).toPresheafedSpace.carrier ⟶ spfSpace A :=
  spfOfQuotientOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- The structure sheaf of `Spec (A/I)`, viewed as a sheaf of rings on the space of open primes
of `A`. -/
noncomputable def spfComponentOn (I : SpfIndex A P) :
    (spfSpace A).Presheaf CommRingCat.{u} :=
  (spfOfQuotientOn A I) _* (Spec (spfQuotientOn A I)).presheaf

/-- The structure sheaf of `Spec (A/I)`, viewed as a sheaf of rings on `Spf A`.

The ideals-of-definition case of `spfComponentOn`. -/
@[reducible, ega "I 10.1.1"] noncomputable def spfComponent (I : IdealsOfDefinition A) :
    (spfSpace A).Presheaf CommRingCat.{u} :=
  spfComponentOn (A := A) (P := IsIdealOfDefinition) (I := I)

omit [TopologicalSpace A] [IsTopologicalRing A] [IsWeakIdealSystem A P] in
/-- The identification of `Spec (A/I)` with itself induced by factoring `A/I` through itself is
the identity. -/
theorem spec_map_factor_self_spfQuotientOn (I : SpfIndex A P) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (le_refl I.1)))
      = 𝟙 (Spec (spfQuotientOn A I)) := by
  have h : CommRingCat.ofHom (Ideal.Quotient.factor (le_refl I.1)) = 𝟙 (spfQuotientOn A I) := by
    rw [Ideal.Quotient.factor_self]
    exact CommRingCat.ofHom_id
  rw [h]
  exact Spec.map_id _

omit [IsTopologicalRing A] in
/-- The identification of `Spec (A/I)` with itself induced by factoring `A/I` through itself is
the identity.

The ideals-of-definition case of `spec_map_factor_self_spfQuotientOn`. -/
theorem spec_map_factor_self (I : IdealsOfDefinition A) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (le_refl I.1)))
      = 𝟙 (Spec (spfQuotient A I)) :=
  spec_map_factor_self_spfQuotientOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- For members `I ⊆ J` of the family the surjection `A/I → A/J` induces a map of the structure
sheaves of `Spec (A/I)` and `Spec (A/J)` viewed on the space of open primes. No transport is
needed: the triangle of spectra over that space commutes definitionally, because `A/I → A/J`
composed with `A → A/I` is `A → A/J` on the nose. -/
noncomputable def spfTransitionOn {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    spfComponentOn A I ⟶ spfComponentOn A J :=
  Functor.whiskerLeft _ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))).c

/-- For ideals of definition `I ⊆ J` the surjection `A/I → A/J` induces a map of the structure
sheaves of `Spec (A/I)` and `Spec (A/J)` viewed on `Spf A`. No transport is needed: the triangle
of spectra over `Spf A` commutes definitionally, because `A/I → A/J` composed with `A → A/I` is
`A → A/J` on the nose.

The ideals-of-definition case of `spfTransitionOn`. -/
@[reducible] noncomputable def spfTransition {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1) :
    spfComponent A I ⟶ spfComponent A J :=
  spfTransitionOn (A := A) (P := IsIdealOfDefinition) (I := I) (J := J) (h := h)

variable (P) in
/-- The inverse system of the source, taken along the family `P`: the structure sheaves of the
`Spec (A/I)`, for `I` running through `P`, all viewed as sheaves of rings on the space of open
primes of `A`. -/
noncomputable def spfDiagramOn : SpfIndex A P ⥤ (spfSpace A).Presheaf CommRingCat.{u} where
  obj I := spfComponentOn A I
  map h := spfTransitionOn A (leOfHom h)
  map_id I := by
    refine NatTrans.ext (funext fun V => ?_)
    change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (le_refl I.1)))).c.app _ = _
    rw [PresheafedSpace.congr_app
      (congrArg (fun k => k.toHom) (spec_map_factor_self_spfQuotientOn A I))]
    change _ ≫ (Spec (spfQuotientOn A I)).presheaf.map (𝟙 _) = _
    rw [(Spec (spfQuotientOn A I)).presheaf.map_id]
    exact Category.comp_id _
  map_comp {I _ K} h h' := by
    have hm : Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factor ((leOfHom h).trans (leOfHom h'))))
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom h')))
          ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom h))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp]
    refine NatTrans.ext (funext fun V => ?_)
    change (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor ((leOfHom h).trans (leOfHom h'))))).c.app _ = _
    rw [PresheafedSpace.congr_app (congrArg (fun k => k.toHom) hm)]
    change _ ≫ (Spec (spfQuotientOn A K)).presheaf.map (𝟙 _) = _
    rw [(Spec (spfQuotientOn A K)).presheaf.map_id]
    exact Category.comp_id _

variable (P) in
/-- The structure presheaf of topological rings of the formal spectrum taken along `P`:
`lim 𝒪_λ`, the limit over the members of `P` of the pseudo-discrete sheaves of topological
rings attached to the structure sheaves of the `Spec (A/I_λ)`. The limit is taken in sheaves of
topological rings, so objectwise it is the limit of Stacks 0B23. -/
noncomputable def spfPresheafOn : (spfSpace A).Presheaf TopCommRingCat.{u} :=
  limit (spfDiagramOn A P ⋙ pseudoDiscreteFunctor)

variable (P) in
/-- The formal spectrum of `A` taken along the family `P`: the space of open primes of `A`
carrying the limit over `P` of the pseudo-discretised structure sheaves of the `Spec (A/I_λ)`.
The source defers to a later point the verifications that its stalks are local rings and that it
is a sheaf, so it is recorded here as a presheafed space of topological rings. -/
@[ega "I 10.1.1", ega "I 10.1.2" "more general"]
noncomputable def SpfOn : PresheafedSpace TopCommRingCat.{u} where
  carrier := spfSpace A
  presheaf := spfPresheafOn A P

/-- The inverse system of the source: the structure sheaves of the `Spec (A/I)`, for `I` running
through the ideals of definition of `A`, all viewed as sheaves of rings on `Spf A`. -/
@[reducible] noncomputable def spfDiagram :
    IdealsOfDefinition A ⥤ (spfSpace A).Presheaf CommRingCat.{u} :=
  spfDiagramOn A IsIdealOfDefinition

/-- The structure presheaf of topological rings of the formal spectrum:
`𝒪_{Spf A} = lim 𝒪_λ`, the limit over the ideals of definition of the pseudo-discrete sheaves of
topological rings attached to the structure sheaves of the `Spec (A/I_λ)`. The limit is taken in
sheaves of topological rings, so objectwise it is the limit of Stacks 0B23. -/
@[reducible] noncomputable def spfPresheaf : (spfSpace A).Presheaf TopCommRingCat.{u} :=
  spfPresheafOn A IsIdealOfDefinition

/-- The *formal spectrum* `(Spf A, 𝒪_{Spf A})` of an admissible topological ring. The source
defers to a later point the verifications that its stalks are local rings and that it is a
sheaf, so it is recorded here as a presheafed space of topological rings. -/
@[reducible, ega "I 10.1.2"] noncomputable def Spf : PresheafedSpace TopCommRingCat.{u} :=
  SpfOn A IsIdealOfDefinition

/-- The underlying space of the formal spectrum is the space of open primes. -/
@[simp]
theorem Spf_carrier : (Spf A).carrier = spfSpace A := rfl

/-- The structure presheaf of the formal spectrum is the limit over the ideals of
definition. -/
@[simp]
theorem Spf_presheaf : (Spf A).presheaf = spfPresheaf A := rfl

/-- The underlying space of the formal spectrum taken along `P` is the space of open primes. -/
@[simp]
theorem SpfOn_carrier : (SpfOn A P).carrier = spfSpace A := rfl

/-- The structure presheaf of the formal spectrum taken along `P` is the limit over `P`. -/
@[simp]
theorem SpfOn_presheaf : (SpfOn A P).presheaf = spfPresheafOn A P := rfl

end Spf

/-! ### Formal schemes -/

/-- An object of `LTRS` is a *formal scheme* in the sense of EGA when every point has an open
neighbourhood isomorphic to the formal spectrum of an admissible topological ring. As the source
takes the isomorphism in `LTRS` and the two objects are already locally topologically ringed, it
is equivalent — and is what is recorded here — to ask for an isomorphism of presheafed spaces of
topological rings. -/
def IsFormalScheme : ObjectProperty LTRS.{u} := fun X =>
  ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (A : TopCommRingCat.{u}),
    ∃ (hlinear : IsLinearTopology A.α A.α),
    letI := hlinear
    TopologicalRing.IsAdmissible A.α ∧
      Nonempty (X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ Spf A.α)

/-- The category of *formal schemes*: the full subcategory of `LTRS` on the objects that are
locally isomorphic to a formal spectrum. A morphism of formal schemes is a morphism of
`LTRS`. -/
abbrev FormalScheme := IsFormalScheme.FullSubcategory

/-! ### The formal spectrum of a discrete ring -/

section Discrete

variable (R : Type u) [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

/-- In a discrete topological ring the zero ideal is an ideal of definition. -/
theorem isIdealOfDefinition_bot_discrete : IsIdealOfDefinition (⊥ : Ideal R) := by
  refine ⟨isOpen_discrete _, fun neighbourhood hneighbourhood => ⟨1, ?_⟩⟩
  simpa using (show ({0} : Set R) ⊆ neighbourhood from
    Set.singleton_subset_iff.2 (mem_of_mem_nhds hneighbourhood))

/-- A discrete topological ring is admissible: the zero ideal is an ideal of definition, and the
discrete uniformity is complete and Hausdorff. -/
theorem isAdmissible_discrete : IsAdmissible R := by
  refine ⟨⟨⊥, isIdealOfDefinition_bot_discrete R⟩, inferInstance, ?_⟩
  let _ : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  have : DiscreteUniformity R := by
    apply discreteUniformity_iff_setRelId_mem_uniformity.2
    change SetRel.id ∈ Filter.comap (fun pair : R × R => pair.2 + -pair.1) (nhds 0)
    rw [Filter.mem_comap]
    refine ⟨{0}, by simp, ?_⟩
    intro pair hpair
    exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hpair : pair.2 - pair.1 = 0)).symm
  infer_instance

/-- In a discrete topological ring the zero ideal is a weak ideal of definition: it is open and
its only element is zero, whose powers are eventually zero. -/
theorem isWeakIdealOfDefinition_bot_discrete : IsWeakIdealOfDefinition (⊥ : Ideal R) :=
  isWeakIdealOfDefinition_of_isIdealOfDefinition (isIdealOfDefinition_bot_discrete R)

variable {P : Ideal R → Prop} [IsWeakIdealSystem R P]

/-- For a discrete ring the zero ideal is initial among the members of any family containing it,
so the limit defining the structure presheaf of the formal spectrum taken along that family is
its component there. -/
noncomputable def spfDiscreteComponentIsoOn (hbot : P (⊥ : Ideal R)) :
    spfPresheafOn R P ≅ pseudoDiscrete (spfComponentOn R ⟨⊥, hbot⟩) := by
  have initial : IsInitial (⟨⊥, hbot⟩ : SpfIndex R P) :=
    IsInitial.ofUniqueHom (fun ideal => homOfLE (show (⊥ : Ideal R) ≤ ideal.1 from bot_le))
      (fun _ _ => Subsingleton.elim _ _)
  exact (limit.isLimit _).conePointUniqueUpToIso
    (limitOfDiagramInitial initial (spfDiagramOn R P ⋙ pseudoDiscreteFunctor))

/-- For a discrete ring the zero ideal is initial among the ideals of definition, so the limit
defining `𝒪_{Spf R}` is its component there.

The ideals-of-definition case of `spfDiscreteComponentIsoOn`. -/
@[reducible] noncomputable def spfDiscreteComponentIso :
    spfPresheaf R ≅ pseudoDiscrete (spfComponent R ⟨⊥, isIdealOfDefinition_bot_discrete R⟩) :=
  spfDiscreteComponentIsoOn R (isIdealOfDefinition_bot_discrete R)

/-- **Stacks 0AHY**, the source's example that `Spf A = Spec A` for a discrete ring `A`: the
formal spectrum of a discrete ring, taken along any family of ideals containing the zero ideal,
is the pseudo-discretisation of its spectrum. -/
noncomputable def discreteSpecSpfIsoOn (hbot : P (⊥ : Ideal R)) :
    pseudoDiscreteSpace (Spec (CommRingCat.of R)).toPresheafedSpace ≅ SpfOn R P := by
  let bottom : SpfIndex R P := ⟨⊥, hbot⟩
  let fullSpace : spfSpace R ≅ (Spec (CommRingCat.of R)).toPresheafedSpace.carrier :=
    TopCat.isoOfHomeo ((Homeomorph.setCongr (Set.eq_univ_of_forall fun _ => by
      simp only [openPrimes, isOpen_discrete, Set.mem_ofPred_eq])).trans
        (Homeomorph.Set.univ (PrimeSpectrum R)))
  let quotientSpaceIso := (LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace).mapIso (Spec.toLocallyRingedSpace.mapIso
      (RingEquiv.quotientBot R).toCommRingCatIso.symm.op)
  have hbase : spfOfQuotientOn R bottom =
      ((PresheafedSpace.forget CommRingCat).mapIso quotientSpaceIso).hom ≫ fullSpace.inv := by
    ext prime
    rfl
  have : IsIso (spfOfQuotientOn R bottom) := by
    rw [hbase]
    exact ((PresheafedSpace.forget CommRingCat).mapIso quotientSpaceIso ≪≫
      fullSpace.symm).isIso_hom
  let componentSpace : PresheafedSpace CommRingCat.{u} :=
    ⟨spfSpace R, spfComponentOn R bottom⟩
  let componentIso : (Spec (spfQuotientOn R bottom)).toPresheafedSpace ≅ componentSpace :=
    PresheafedSpace.isoOfComponents (asIso (spfOfQuotientOn R bottom)) (Iso.refl _)
  let ringIso : (Spec (CommRingCat.of R)).toPresheafedSpace ≅ componentSpace :=
    quotientSpaceIso.symm ≪≫ componentIso
  exact pseudoDiscreteSpaceIso ringIso ≪≫
    PresheafedSpace.isoOfComponents (Iso.refl _) (spfDiscreteComponentIsoOn R hbot).symm

/-- **Stacks 0AHY**, the source's example that `Spf A = Spec A` for a discrete ring `A`: the
formal spectrum of a discrete ring is the pseudo-discretisation of its spectrum.

The ideals-of-definition case of `discreteSpecSpfIsoOn`. -/
@[reducible] noncomputable def discreteSpecSpfIso :
    pseudoDiscreteSpace (Spec (CommRingCat.of R)).toPresheafedSpace ≅ Spf R :=
  discreteSpecSpfIsoOn R (isIdealOfDefinition_bot_discrete R)

end Discrete

end AlgebraicGeometry
