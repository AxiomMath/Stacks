module

public import Mathlib
public import Mathlib.FieldTheory.PerfectClosure
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Topology.Algebra.Ring.Compact
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.Etale.NonfiniteGenerators
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.QuotPow
public import StacksFrontier.RingTheory.AdicCompletion.Quotient
public import StacksFrontier.RingTheory.CompleteLocalRing.PowerSeriesFormallySmooth
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.RingTheory.Smoothing.StandardElementAtSmoothPrime
public import StacksFrontier.RingTheory.CompleteLocalRing.PowerSeriesMaps
public import StacksFrontier.RingTheory.Flat.AdicFiltration
public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.FormallySmooth.LocalRings
public import StacksFrontier.RingTheory.FormallySmooth.SpecialFibre
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.RingTheory.FormallySmooth.TopologicalRings
public import StacksFrontier.RingTheory.GeometricallyRegular.FieldExtension
public import StacksFrontier.RingTheory.GeometricallyRegular.PurelyInseparableCriterion
public import StacksFrontier.RingTheory.Kaehler.JacobiZariski
public import StacksFrontier.RingTheory.NaiveCotangent.H1
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension
public import StacksFrontier.Topology.Algebra.AdicTopology.Continuous
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterion
public import StacksFrontier.RingTheory.Flat.TowerLTensor
import StacksFrontier.Topology.Algebra.AdicTopology.QuotientAdic

@[expose] public section

/-!
# Geometric regularity and formal smoothness

Stacks Project, Chapter 15 "More on Algebra". The tags treated here are

07NP, 0DYH, 07EL, 07EM, 07NQ, 07NR, 07NS.

## Tag 07NP — Adically formally smooth local homomorphisms are flat

A local homomorphism between Noetherian local rings that is formally smooth for the
maximal-ideal-adic topologies is flat.

### Main definitions

No new definitions are introduced.

### Main results

* `flat_of_isFormallySmooth_maximalIdeal_adic`: an adically formally smooth local
  homomorphism of Noetherian local rings is flat.

### Implementation notes

Formal smoothness in the maximal-ideal-adic topology is expressed using
`RingHom.FormallySmoothNAdic`, which equips the source with the discrete topology. Flatness is
expressed as a property of the algebra structure induced by the given ring homomorphism.

### References

* [Stacks Project, Tag 07NP](https://stacks.math.columbia.edu/tag/07NP)

## Tag 0DYH — Jacobi–Zariski sequence for an adically formally smooth local map

For a local homomorphism `A → B` of Noetherian local rings which is formally smooth for the
maximal-ideal-adic topology on `B`, the Jacobi–Zariski sequence ending at the residue field of
`B` is exact, including at its leftmost nonzero term.

### Main definitions

There are no new definitions.

### Main results

* `exact_jacobiZariski_residueField_of_formallySmoothNAdic` gives the exact sequence
  from the first cotangent homology over `A`, through the cotangent space of `B` and relative
  Kähler differentials, to the Kähler differentials of the residue field over `A`.

### Implementation notes

The cotangent space `𝔪_B / 𝔪_B²` is `IsLocalRing.CotangentSpace B`.  The canonical comparison
with `Algebra.H1Cotangent B (IsLocalRing.ResidueField B)` is the equivalence of Stacks Project,
Tag 07BP, transported along the equality between the kernel of the residue map and the maximal
ideal.  Exactness of the five-term sequence is expressed by injectivity at the left end, two
`Function.Exact` assertions at the middle terms, and surjectivity at the right end.

### References

* [Stacks Project, Tag 0DYH](https://stacks.math.columbia.edu/tag/0DYH)

## Tag 07EL — Geometric regularity and adic formal smoothness

For a Noetherian local algebra over a field, regularity in characteristic zero and geometric
regularity in positive characteristic are characterized by formal smoothness for the topology
defined by the maximal ideal. In positive characteristic this joins the equivalent criteria in
terms of finite purely inseparable base change, the cotangent complex, and Kähler differentials.

### Main definitions

No new definitions are introduced.

### Main results

* `formalSmoothness_maximalIdeal_characterizations`: the characteristic-zero
  equivalence and the five positive-characteristic characterizations.

### Implementation notes

The two characteristic cases are expressed in one declaration by quantifying over a
characteristic-zero instance and over prime positive characteristics. The maximal-ideal adic
topology and the four geometric-regularity conditions use the same canonical models as Tags
07EB and 07E5.

### References

* [Stacks Project, Tag 07EL](https://stacks.math.columbia.edu/tag/07EL)

## Tag 07EM — Formally smooth local algebras with inseparable residue fields

In positive characteristic, a geometrically regular local algebra can have a purely
inseparable residue field. There is also a formally smooth map from the rational function
field `𝔽ₚ(s)` to the power series ring over the perfect closure of `𝔽ₚ(t)` which sends `s` to
`t + x`.

### Main definitions

* `IsAdicallyFormallySmooth`: formal smoothness from a discrete source to a target
  equipped with an ideal-adic topology.

### Main results

* `formallySmooth_adic_examples_with_inseparable_residueField`: the localized
  polynomial example and the power series example, including their differential bases.

### Implementation notes

The first algebra is represented literally as the stated quotient of a localization of a
two-variable polynomial ring. The variables are indexed by `Fin 2`. In the second example,
`𝔽ₚ(s)` is `RatFunc (ZMod p)`, its perfect closure is `PerfectClosure _ p`, and `K[[x]]` is
`PowerSeries K`. The one-element differential bases are indexed by `Unit`.

Geometric regularity of the first example is checked after field base change and localization.
For the second example, a finite decomposition by exponents modulo `p` computes the differentials,
and extending derivations across square-zero ideals gives the required lifts.

### References

* [Stacks Project, Tag 07EM](https://stacks.math.columbia.edu/tag/07EM)

## Tag 07NQ — Formal smoothness of local homomorphisms

For a local homomorphism of Noetherian local rings, formal smoothness for the
maximal-ideal-adic topology is equivalent to flatness together with geometric
regularity of the special fibre. Equivalently, the map is flat and its special
fibre is formally smooth over the residue field.

### Main definitions

No new definitions are introduced.

### Main results

* `flat_geometricallyRegular_specialFiber_formallySmooth_tfae`:
  the three equivalent characterizations of an adically formally smooth local
  homomorphism of Noetherian local rings.

### Implementation notes

The special fibre is represented by the canonical Mathlib model
`IsLocalRing.ResidueField A ⊗[A] B`, with the residue field as the left tensor
factor. The equivalence
`Algebra.TensorProduct.comm A B (IsLocalRing.ResidueField A)` canonically
identifies the source's `B ⊗[A] k` with `k ⊗[A] B`.

### References

* [Stacks Project, Tag 07NQ](https://stacks.math.columbia.edu/tag/07NQ)

## Tag 07NR — Lifting formally smooth complete local algebras

A formally smooth complete local algebra over the residue field of a Noetherian complete local
ring lifts to an adically formally smooth complete local algebra over that ring.

### Main definitions

No new definitions are introduced.

### Main results

* `exists_completeLocal_formallySmooth_lift`: a formally smooth complete local
  residue-field algebra lifts across a Noetherian complete local ring.

### Implementation notes

The special fibre is represented by the canonical Mathlib model
`IsLocalRing.ResidueField A ⊗[A] C`. Tensor-product commutativity canonically identifies this
with the source's `C ⊗[A] IsLocalRing.ResidueField A`.

### References

* [Stacks Project, Tag 07NR](https://stacks.math.columbia.edu/tag/07NR)

## Tag 07NS — Formally smooth lifts and completed base change

A formally smooth special fibre in a diagram of Noetherian complete local rings lifts to an
adically formally smooth complete local algebra. Its map to the original algebra has a
surjective completed base change, with stronger conclusions under surjectivity, finiteness, or
flatness hypotheses.

### Main definitions

No new definitions are introduced.

### Main results

* `exists_completeLocal_formallySmooth_lift_with_baseChange`: constructs the lift and
  records the properties of its completed base change.

### Implementation notes

Special fibres use the canonical Mathlib models with the residue field as the left tensor
factor. The isomorphism between them is required to agree with the induced residue-field map and
the constructed map on the two tensor factors. The completed tensor product is represented by
`AdicCompletion` at the extension of the maximal ideal of the second base ring.

### References

* [Stacks Project, Tag 07NS](https://stacks.math.columbia.edu/tag/07NS)

-/

/-! ### Stacks Tag 07NP -/

section

section

set_option maxRecDepth 4096

@[expose] public section

open IsLocalRing
open UniformSpace
open TensorProduct
open Stacks.Flatness.NilpotentFibreCriterion
open AlgebraTensorModule

private theorem flat_of_flat_tensorProduct_of_faithfullyFlat
    {A C D P : Type*} [CommRing A] [CommRing C] [Algebra A C]
    [AddCommGroup D] [Module A D] [Module C D] [IsScalarTower A C D]
    [AddCommGroup P] [Module A P] [Module C P] [IsScalarTower A C P]
    [Module.FaithfullyFlat C D] [Module.Flat A (D ⊗[C] P)] :
    Module.Flat A P := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro X Y _ _ _ _ u hu
  rw [← coe_lTensor (A := C),
    ← Module.FaithfullyFlat.lTensor_injective_iff_injective (M := D) (f := lTensor C P u),
    ← lTensor_baseChange_injective_iff]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hu

private lemma flat_of_comp_of_faithfullyFlat
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hg : g.FaithfullyFlat) (hgf : (g.comp f).Flat) : f.Flat := by
  let : Algebra A B := f.toAlgebra
  let : Algebra B C := g.toAlgebra
  let : Algebra A C := (g.comp f).toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Module.Flat A C := hgf
  have : Module.FaithfullyFlat B C := hg
  exact flat_of_flat_of_faithfullyFlat C

private lemma flat_of_split_surjection
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Module.Flat A C]
    (s : B →ₐ[A] C) (p : C →ₐ[A] B)
    (h : p.comp s = AlgHom.id A B) : Module.Flat A B := by
  exact Module.Flat.of_retract s.toLinearMap p.toLinearMap
    (by ext x; exact congrArg (fun q : B →ₐ[A] B => q x) h)

private lemma adic_to_top.{u,v,w} {A : Type v} {B : Type w}
    [CommRing A] [CommRing B] (f : A →+* B) (n : Ideal B)
    (hf : RingHom.FormallySmoothNAdic.{u} f n) :
    letI : TopologicalSpace A := (⊥ : Ideal A).adicTopology
    letI : IsTopologicalRing A := (⊥ : Ideal A).ringFilterBasis.isTopologicalRing
    letI : IsLinearTopology A A := (⊥ : Ideal A).isLinearTopology
    letI : TopologicalSpace B := n.adicTopology
    letI : IsTopologicalRing B := n.ringFilterBasis.isTopologicalRing
    letI : IsLinearTopology B B := n.isLinearTopology
    IsFormallySmooth.{u} f := by
  let : TopologicalSpace A := (⊥ : Ideal A).adicTopology
  let : IsTopologicalRing A := (⊥ : Ideal A).ringFilterBasis.isTopologicalRing
  let : IsLinearTopology A A := (⊥ : Ideal A).isLinearTopology
  let : TopologicalSpace B := n.adicTopology
  let : IsTopologicalRing B := n.ringFilterBasis.isTopologicalRing
  let : IsLinearTopology B B := n.isLinearTopology
  have : DiscreteTopology A := is_bot_adic_iff.mp rfl
  refine ⟨continuous_of_discreteTopology, ?_⟩
  intro T _ _ _ J hJ fA hfA ψ hψ hcomm
  have : DiscreteTopology (T ⧸ J) :=
    QuotientAddGroup.discreteTopology_iff.mpr (isOpen_discrete _)
  have hT : (inferInstance : TopologicalSpace T) = (⊥ : Ideal T).adicTopology :=
    (is_bot_adic_iff.mpr inferInstance)
  have hTJ : (inferInstance : TopologicalSpace (T ⧸ J)) =
      (⊥ : Ideal (T ⧸ J)).adicTopology :=
    (is_bot_adic_iff.mpr inferInstance)
  have hψ' : @Continuous B (T ⧸ J) n.adicTopology
      (⊥ : Ideal (T ⧸ J)).adicTopology ψ := by
    rw [← hTJ]
    exact hψ
  obtain ⟨k, hkpos, hkψ⟩ := (RingHom.continuous_adic_iff ψ n ⊥).mp hψ'
  have hker : n ^ k ≤ RingHom.ker ψ := by
    intro x hx
    simpa only [Ideal.mem_bot, RingHom.mem_ker] using hkψ x hx
  obtain ⟨g, hπ, hφ⟩ := hf T J hJ fA ψ hcomm ⟨k, hkpos, hker⟩
  have hmap : Ideal.map g (n ^ k) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change g x ∈ J
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h := congrArg (fun h : B →+* T ⧸ J => h x) hπ
    simpa only [RingHom.comp_apply] using h.trans (RingHom.mem_ker.mp (hker hx))
  have hmap2 : Ideal.map g (n ^ (k * 2)) ≤ (⊥ : Ideal T) := by
    rw [pow_mul, Ideal.map_pow]
    calc
      Ideal.map g (n ^ k) ^ 2 ≤ J ^ 2 := pow_le_pow_left' hmap 2
      _ = ⊥ := hJ
  have hg' : @Continuous B T n.adicTopology (⊥ : Ideal T).adicTopology g := by
    apply (RingHom.continuous_adic_iff g n ⊥).mpr
    refine ⟨k * 2, by omega, ?_⟩
    intro x hx
    exact hmap2 (Ideal.mem_map_of_mem g hx)
  have hg : Continuous g := by
    convert hg' using 1
  exact ⟨g, hg, hφ, hπ⟩

private lemma adic_to_top_of_continuous.{u, v, w}
    {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (m : Ideal A) (n : Ideal B)
    (hf : RingHom.FormallySmoothNAdic.{u} f n)
    (hcont : @Continuous A B m.adicTopology n.adicTopology f) :
    letI : TopologicalSpace A := m.adicTopology
    letI : IsTopologicalRing A := m.ringFilterBasis.isTopologicalRing
    letI : IsLinearTopology A A := m.isLinearTopology
    letI : TopologicalSpace B := n.adicTopology
    letI : IsTopologicalRing B := n.ringFilterBasis.isTopologicalRing
    letI : IsLinearTopology B B := n.isLinearTopology
    IsFormallySmooth.{u} f := by
  let : TopologicalSpace A := m.adicTopology
  let : IsTopologicalRing A := m.ringFilterBasis.isTopologicalRing
  let : IsLinearTopology A A := m.isLinearTopology
  let : TopologicalSpace B := n.adicTopology
  let : IsTopologicalRing B := n.ringFilterBasis.isTopologicalRing
  let : IsLinearTopology B B := n.isLinearTopology
  refine ⟨hcont, ?_⟩
  intro T _ _ _ J hJ fA hfA ψ hψ hcomm
  let : TopologicalSpace A := (⊥ : Ideal A).adicTopology
  let : IsTopologicalRing A := (⊥ : Ideal A).ringFilterBasis.isTopologicalRing
  let : IsLinearTopology A A := (⊥ : Ideal A).isLinearTopology
  have : DiscreteTopology A := is_bot_adic_iff.mp rfl
  have hs := (adic_to_top f n hf).2
  exact hs T J hJ fA continuous_of_discreteTopology ψ hψ hcomm

private lemma isPrecomplete_of_surjective
    {R M N : Type*} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [IsPrecomplete I M] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    IsPrecomplete I N := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨x, rfl⟩ := AdicCompletion.map_surjective I hf y
  obtain ⟨m, rfl⟩ := AdicCompletion.of_surjective (I := I) (M := M) x
  exact ⟨f m, (AdicCompletion.map_of I f m).symm⟩

private lemma isAdicComplete_of_surjective
    {R S : Type*} [CommRing R] [IsLocalRing R]
    [IsPrecomplete (maximalIdeal R) R]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (f : R →+* S) (hf : Function.Surjective f) :
    IsAdicComplete (maximalIdeal S) S := by
  let := f.toAlgebra
  have h : IsPrecomplete (maximalIdeal S) S := by
    rw [← map_maximalIdeal_of_surjective f hf]
    change IsPrecomplete ((maximalIdeal R).map (algebraMap R S)) S
    rw [IsPrecomplete.map_algebraMap_iff]
    exact isPrecomplete_of_surjective (maximalIdeal R) (Algebra.linearMap R S) hf
  exact ⟨⟩

private lemma continuous_of_isLocalHom
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] :
    @Continuous R S (maximalIdeal R).adicTopology (maximalIdeal S).adicTopology f := by
  apply (RingHom.continuous_adic_iff _ _ _).mpr
  refine ⟨1, le_rfl, ?_⟩
  simpa only [pow_one] using (show ∀ x ∈ maximalIdeal R, f x ∈ maximalIdeal S from
    fun x hx => map_maximalIdeal_le f (Ideal.mem_map_of_mem f hx))

private lemma exists_section_of_surjective_of_formallySmooth.{u, v, w}
    {A : Type v} {B : Type w} {C : Type u} [CommRing A] [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [CommRing C] [IsLocalRing C]
    [IsAdicComplete (maximalIdeal C) C]
    (f : A →+* B) (g : A →+* C) (p : C →+* B)
    (hp : Function.Surjective p) (hcomm : p.comp g = f)
    (hf : RingHom.FormallySmoothNAdic.{u} f (maximalIdeal B)) :
    ∃ s : B →+* C, s.comp f = g ∧ p.comp s = RingHom.id B := by
  let : TopologicalSpace A := (⊥ : Ideal A).adicTopology
  let : IsTopologicalRing A := (⊥ : Ideal A).ringFilterBasis.isTopologicalRing
  let : IsLinearTopology A A := (⊥ : Ideal A).isLinearTopology
  let : TopologicalSpace B := (maximalIdeal B).adicTopology
  let : IsTopologicalRing B := (maximalIdeal B).ringFilterBasis.isTopologicalRing
  let : IsLinearTopology B B := (maximalIdeal B).isLinearTopology
  let : TopologicalSpace C := (maximalIdeal C).adicTopology
  let : IsTopologicalRing C := (maximalIdeal C).ringFilterBasis.isTopologicalRing
  have : DiscreteTopology A := is_bot_adic_iff.mp rfl
  have : IsLocalHom p := IsLocalHom.of_surjective p hp
  have : T2Space B := (IsAdic.isHausdorff_iff (I := maximalIdeal B) rfl).mp inferInstance
  let J := RingHom.ker p
  let e : C ⧸ J ≃+* B := RingHom.quotientKerEquivOfSurjective hp
  have hpcont : Continuous p := continuous_of_isLocalHom p
  have hJ : IsClosed (J : Set C) := isClosed_singleton.preimage hpcont
  have hJne : J ≠ ⊤ := RingHom.ker_ne_top p
  have : Nontrivial (C ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJne
  have : IsLocalRing (C ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have htop : (inferInstance : TopologicalSpace (C ⧸ J)) =
      (maximalIdeal (C ⧸ J)).adicTopology := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective]
    exact isAdic_map_quotient_mk (maximalIdeal C) J rfl
  have : IsLocalHom e.symm.toRingHom := isLocalHom_toRingHom e.symm
  have hecont : Continuous e.symm := by
    exact (congrArg (fun t => @Continuous B (C ⧸ J)
      (maximalIdeal B).adicTopology t e.symm) htop).mpr
        (continuous_of_isLocalHom e.symm.toRingHom)
  obtain ⟨s, _, hsg, hs⟩ :=
    exists_continuous_lift_of_isFormallySmooth_of_isAdic
      f (maximalIdeal B) rfl (adic_to_top f (maximalIdeal B) hf)
      (maximalIdeal C) rfl J hJ 1 le_rfl
      (by simpa using le_maximalIdeal hJne)
      g continuous_of_discreteTopology e.symm.toRingHom hecont (by
        rw [← hcomm, ← RingHom.comp_assoc]
        exact congrArg (fun q : C →+* C ⧸ J => q.comp g)
          (RingHom.quotientKerEquivOfSurjective_symm_comp hp))
  refine ⟨s, hsg, ?_⟩
  ext b
  have h := congrArg (fun q : B →+* C ⧸ J => e (q b)) hs
  change (RingHom.quotientKerEquivOfSurjective hp)
    ((Ideal.Quotient.mk (RingHom.ker p)) (s b)) = e (e.symm b) at h
  rw [RingHom.quotientKerEquivOfSurjective_apply_mk] at h
  exact h.trans (e.apply_symm_apply b)

lemma flat_of_surjective_of_formallySmooth.{u, v, w}
    {A : Type v} {B : Type w} {C : Type u}
    [CommRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [CommRing C] [IsLocalRing C] [IsAdicComplete (maximalIdeal C) C]
    [Algebra A B] [Algebra A C] [Module.Flat A C]
    (p : C →ₐ[A] B) (hp : Function.Surjective p)
    (hf : RingHom.FormallySmoothNAdic.{u} (algebraMap A B) (maximalIdeal B)) :
    Module.Flat A B := by
  obtain ⟨s, hsg, hs⟩ := exists_section_of_surjective_of_formallySmooth
    (algebraMap A B) (algebraMap A C) p.toRingHom hp
    (by ext a; exact p.commutes a) hf
  let s' : B →ₐ[A] C := { s with
    commutes' := fun a => congrArg (fun q : A →+* C => q a) hsg }
  apply flat_of_split_surjection s' p
  ext b
  exact congrArg (fun q : B →+* B => q b) hs

private theorem formallySmoothNAdic_of_isFormallySmooth.{u, v, w}
    {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (m : Ideal A) (n : Ideal B) :
    letI : TopologicalSpace A := m.adicTopology
    letI : IsTopologicalRing A := m.ringFilterBasis.isTopologicalRing
    letI : IsLinearTopology A A := m.isLinearTopology
    letI : TopologicalSpace B := n.adicTopology
    letI : IsTopologicalRing B := n.ringFilterBasis.isTopologicalRing
    letI : IsLinearTopology B B := n.isLinearTopology
    IsFormallySmooth.{u} f → RingHom.FormallySmoothNAdic.{u} f n := by
  let : TopologicalSpace A := m.adicTopology
  let : IsTopologicalRing A := m.ringFilterBasis.isTopologicalRing
  let : IsLinearTopology A A := m.isLinearTopology
  let : TopologicalSpace B := n.adicTopology
  let : IsTopologicalRing B := n.ringFilterBasis.isTopologicalRing
  let : IsLinearTopology B B := n.isLinearTopology
  intro hf T _ J hJ fA ψ hcomm hk
  let : TopologicalSpace T := (⊥ : Ideal T).adicTopology
  let : IsTopologicalRing T := (⊥ : Ideal T).ringFilterBasis.isTopologicalRing
  have : DiscreteTopology T := is_bot_adic_iff.mp rfl
  have : DiscreteTopology (T ⧸ J) :=
    QuotientAddGroup.discreteTopology_iff.mpr (isOpen_discrete _)
  have hTJ : (inferInstance : TopologicalSpace (T ⧸ J)) =
      (⊥ : Ideal (T ⧸ J)).adicTopology := is_bot_adic_iff.mpr inferInstance
  have hψ : Continuous ψ := by
    apply (congrArg (fun t => @Continuous B (T ⧸ J) n.adicTopology t ψ) hTJ).mpr
    apply (RingHom.continuous_adic_iff ψ n ⊥).mpr
    obtain ⟨k, hk, hker⟩ := hk
    exact ⟨k, hk, fun x hx => hker hx⟩
  have hcomp : @Continuous A (T ⧸ J) m.adicTopology
      (⊥ : Ideal (T ⧸ J)).adicTopology (ψ.comp f) := by
    rw [← hTJ]
    exact hψ.comp hf.1
  obtain ⟨k, hk, hbound⟩ := (RingHom.continuous_adic_iff (ψ.comp f) m ⊥).mp hcomp
  have hmap : Ideal.map fA (m ^ k) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change fA x ∈ J
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h := congrArg (fun h : A →+* T ⧸ J => h x) hcomm
    exact h.symm.trans (hbound x hx)
  have hmap2 : Ideal.map fA (m ^ (k * 2)) ≤ (⊥ : Ideal T) := by
    rw [pow_mul, Ideal.map_pow]
    calc
      Ideal.map fA (m ^ k) ^ 2 ≤ J ^ 2 := pow_le_pow_left' hmap 2
      _ = ⊥ := hJ
  have hfA : Continuous fA := by
    apply (RingHom.continuous_adic_iff fA m ⊥).mpr
    exact ⟨k * 2, by omega, fun x hx => hmap2 (Ideal.mem_map_of_mem fA hx)⟩
  obtain ⟨g, _, hgf, hπ⟩ := hf.2 T J hJ fA hfA ψ hψ hcomm
  exact ⟨g, hπ, hgf⟩

private theorem flat_of_isFormallySmooth_of_isAdicComplete.{v, w}
    {A : Type v} {B : Type w}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [IsAdicComplete (maximalIdeal A) A]
    [IsAdicComplete (maximalIdeal B) B]
    (f : A →+* B) [IsLocalHom f]
    (hf : RingHom.FormallySmoothNAdic.{max v w} f (maximalIdeal B)) : f.Flat := by
  obtain ⟨R, S, _, _, _, _, _, _, g, qA, qB, hqA, hqB, hg, hqAloc, hqBloc,
    hcomm, _, hflat⟩ := exists_powerSeries_presentation_of_isLocalHom f
  let : Algebra R S := g.toAlgebra
  have : Module.Flat R S := hflat.1
  let I := RingHom.ker qA
  let J := I.map g
  have hJ : J ≤ RingHom.ker qB := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change qB (g r) = 0
    rw [← RingHom.comp_apply, ← hcomm, RingHom.comp_apply]
    exact (congrArg f hr).trans (map_zero f)
  let C := S ⧸ J
  let p : C →+* B := Ideal.Quotient.lift J qB hJ
  have hp : Function.Surjective p := by
    intro b
    obtain ⟨s, rfl⟩ := hqB b
    exact ⟨Ideal.Quotient.mk J s, rfl⟩
  have : Nontrivial C :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (RingHom.ker_ne_top qB) hJ)
  have : IsLocalRing C :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have : IsAdicComplete (maximalIdeal C) C :=
    isAdicComplete_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let : Algebra (R ⧸ I) C :=
    show Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) from inferInstance
  let e : R ⧸ I ≃+* A := RingHom.quotientKerEquivOfSurjective hqA
  let a : A →+* C := (algebraMap (R ⧸ I) C).comp e.symm.toRingHom
  have ha : a.Flat := by
    apply RingHom.Flat.comp (RingHom.Flat.of_bijective (f := e.symm.toRingHom) e.symm.bijective)
    exact RingHom.flat_algebraMap_iff.mpr (flat_quotient_map I)
  have hpa : p.comp a = f := by
    apply RingHom.ext
    intro x
    obtain ⟨r, rfl⟩ := hqA x
    have he : e.symm (qA r) = Ideal.Quotient.mk I r := by
      apply e.injective
      simp [e, I]
    change p (algebraMap (R ⧸ I) C (e.symm (qA r))) = f (qA r)
    rw [he]
    exact (congrArg (fun h : R →+* B => h r) hcomm).symm
  let : Algebra A B := f.toAlgebra
  let : Algebra A C := a.toAlgebra
  have : Module.Flat A C := ha
  let p' : C →ₐ[A] B := { p with
    commutes' := fun x => congrArg (fun h : A →+* B => h x) hpa }
  exact flat_of_surjective_of_formallySmooth p' hp hf

/-- **Stacks 07NP.** A formally smooth local homomorphism of Noetherian local rings, for the
maximal-ideal-adic topologies on source and target, is flat. -/
@[stacks 07NP, sga "1 III 1.7" "only if, flatness"]
public theorem flat_of_isFormallySmooth_maximalIdeal_adic.{v, w}
    {A : Type v} {B : Type w}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hf : RingHom.FormallySmoothNAdic.{max v w} f (maximalIdeal B)) :
    letI : Algebra A B := f.toAlgebra
    Module.Flat A B := by
  let : Algebra A B := f.toAlgebra
  let : WithIdeal A := ⟨maximalIdeal A⟩
  let : WithIdeal B := ⟨maximalIdeal B⟩
  have hm : (maximalIdeal A).FG := Ideal.fg_of_isNoetherianRing _
  have hn : (maximalIdeal B).FG := Ideal.fg_of_isNoetherianRing _
  have hcont := continuous_of_isLocalHom f
  let fhat : Completion A →+* Completion B := Completion.mapRingHom f hcont
  have hiff := isFormallySmooth_iff_adicCompletion.{max v w}
    (maximalIdeal A) (maximalIdeal B) hm hn f hcont
  have hsmooth := hiff.2.mp (hiff.1.mp
    (adic_to_top_of_continuous f (maximalIdeal A) (maximalIdeal B) hf hcont))
  have hadic := formallySmoothNAdic_of_isFormallySmooth fhat
    ((maximalIdeal A).map Completion.coeRingHom)
    ((maximalIdeal B).map Completion.coeRingHom) hsmooth
  have := isNoetherianRing_uniformCompletion (maximalIdeal A)
  have := isNoetherianRing_uniformCompletion (maximalIdeal B)
  have := isLocalRing_uniformCompletion hm
  have := isLocalRing_uniformCompletion hn
  have := isAdicComplete_maximalIdeal_uniformCompletion hm
  have := isAdicComplete_maximalIdeal_uniformCompletion hn
  have : IsLocalHom fhat := isLocalHom_mapRingHom hm hn f hcont
  rw [← maximalIdeal_uniformCompletion_eq_map hn] at hadic
  have hflat : fhat.Flat := flat_of_isFormallySmooth_of_isAdicComplete fhat hadic
  have hA := faithfullyFlat_coeRingHom (maximalIdeal A)
    (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal])
  have hB := faithfullyFlat_coeRingHom (maximalIdeal B)
    (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal])
  have hcomp : fhat.comp Completion.coeRingHom = Completion.coeRingHom.comp f := by
    ext a
    exact Completion.mapRingHom_coe hcont a
  have hflat' : (Completion.coeRingHom.comp f).Flat := by
    rw [← hcomp]
    exact hA.flat.comp hflat
  exact flat_of_comp_of_faithfullyFlat f Completion.coeRingHom hB hflat'

end

end

end

/-! ### Stacks Tag 0DYH -/

section

section

open scoped TensorProduct

open Algebra IsLocalRing

universe u v w

/-- Lifting the base map to the universal square-zero extension detects first cotangent
homology injectively.

If the structure map `B → S` factors through the universal square-zero extension of the
tautological presentation of `S` over `A`, then `H₁(L_{S/B}) → H₁(L_{S/A})` is injective. -/
public theorem h1Cotangent_map_injective_of_infinitesimal_lift
    {A B S : Type*} [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra A S] [Algebra B S] [IsScalarTower A B S]
    (g : B →ₐ[A] (Generators.self A S).toExtension.infinitesimal.Ring)
    (hg : (IsScalarTower.toAlgHom A
        (Generators.self A S).toExtension.infinitesimal.Ring S).comp g =
      IsScalarTower.toAlgHom A B S) :
    Function.Injective (H1Cotangent.map A B S S) := by
  let P := (Generators.self A S).toExtension
  let Q := P.infinitesimal
  let E : Extension B S :=
    { Ring := Q.Ring
      algebra₁ := g.toAlgebra
      isScalarTower := by
        let : Algebra B Q.Ring := g.toAlgebra
        exact IsScalarTower.of_algebraMap_eq' (congrArg AlgHom.toRingHom hg).symm
      σ := Q.σ
      algebraMap_σ := Q.algebraMap_σ }
  let q : P.Hom E :=
    { toRingHom := P.toInfinitesimal.toRingHom
      toRingHom_algebraMap := fun x ↦ by
        exact (g.commutes x).symm
      algebraMap_toRingHom := P.toInfinitesimal.algebraMap_toRingHom }
  have hi : Function.Injective (Extension.Cotangent.map q) := by
    have he : Extension.Cotangent.map q = Extension.Cotangent.map P.toInfinitesimal := by
      ext x
      obtain ⟨x, rfl⟩ := Extension.Cotangent.mk_surjective x
      rfl
    rw [he]
    exact (Extension.Cotangent.map_toInfinitesimal_bijective P).1
  have hq : Function.Injective (Extension.H1Cotangent.map q) := by
    intro x y h
    apply Extension.h1Cotangentι_ext
    exact hi (congrArg Subtype.val h)
  let d := (Generators.defaultHom (Generators.self A S) (Generators.self B S)).toExtensionHom
  let t := E.defaultHom
  intro x y h
  change Extension.H1Cotangent.map d x = Extension.H1Cotangent.map d y at h
  apply hq
  rw [Extension.H1Cotangent.map_eq q (t.comp d)]
  simpa only [Extension.H1Cotangent.map_comp_apply] using
    congrArg (Extension.H1Cotangent.map t) h

/-- Adic formal smoothness makes the change-of-base map on first cotangent homology
injective whenever the target kills a power of the adic ideal.

If `A → B` is formally smooth for the `n`-adic topology and some power of `n` dies in `S`,
then `H₁(L_{S/B}) → H₁(L_{S/A})` is injective. -/
public theorem h1Cotangent_map_injective_of_formallySmoothNAdic
    {A : Type u} {B : Type v} {S : Type w}
    [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra A S] [Algebra B S] [IsScalarTower A B S]
    (n : Ideal B)
    (hf : RingHom.FormallySmoothNAdic.{max u w} (algebraMap A B) n)
    (hn : ∃ k : ℕ, 1 ≤ k ∧ n ^ k ≤ RingHom.ker (algebraMap B S)) :
    Function.Injective (H1Cotangent.map A B S S) := by
  let P := (Generators.self A S).toExtension
  let Q := P.infinitesimal
  let e : (Q.Ring ⧸ Q.ker) ≃ₐ[A] S :=
    Ideal.quotientKerAlgEquivOfSurjective (f := IsScalarTower.toAlgHom A Q.Ring S)
      Q.algebraMap_surjective
  let ψ : B →ₐ[A] Q.Ring ⧸ Q.ker :=
    e.symm.toAlgHom.comp (IsScalarTower.toAlgHom A B S)
  have hψ : ψ.toRingHom.comp (algebraMap A B) =
      (Ideal.Quotient.mk Q.ker).comp (algebraMap A Q.Ring) := by
    ext a
    exact ψ.commutes a
  have hnψ : ∃ k : ℕ, 1 ≤ k ∧ n ^ k ≤ RingHom.ker ψ.toRingHom := by
    obtain ⟨k, hk, hn⟩ := hn
    refine ⟨k, hk, ?_⟩
    intro x hx
    change e.symm (algebraMap B S x) = 0
    rw [show algebraMap B S x = 0 from hn hx, map_zero]
  obtain ⟨g, hg, hgA⟩ := hf Q.Ring Q.ker
    (by rw [Extension.ker_infinitesimal]; exact Ideal.cotangentIdeal_square _)
    (algebraMap A Q.Ring) ψ.toRingHom hψ hnψ
  let gA : B →ₐ[A] Q.Ring :=
    { __ := g
      commutes' := fun a ↦ RingHom.congr_fun hgA a }
  apply h1Cotangent_map_injective_of_infinitesimal_lift gA
  ext x
  apply e.symm.injective
  exact (Ideal.quotientKerAlgEquivOfSurjective_symm_apply
    (f := IsScalarTower.toAlgHom A Q.Ring S) Q.algebraMap_surjective (g x)).trans
      (RingHom.congr_fun hg x)

/-- Let `A → B` be a local homomorphism of Noetherian local rings which is formally smooth for
the maximal-ideal-adic topology on `B`, and let `K` be the residue field of `B`.  Then the
canonical Jacobi–Zariski sequence

`0 → H₁(L_{K/A}) → 𝔪_B/𝔪_B² → Ω[B⁄A] ⊗[B] K → Ω[K⁄A] → 0`

is exact. -/
@[stacks 0DYH, ega "0 20.6.23" "residue field, m-adic"]
public theorem exact_jacobiZariski_residueField_of_formallySmoothNAdic
    {A : Type u} {B : Type v}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hf : RingHom.FormallySmoothNAdic.{max u v} f (maximalIdeal B)) :
    let K := ResidueField B
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A K := ((residue B).comp f).toAlgebra
    letI : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq' rfl
    let e : Algebra.H1Cotangent B K ≃ₗ[B] CotangentSpace B :=
      (h1Cotangent_equiv_cotangent_of_surjective B K residue_surjective).trans
        (Ideal.Cotangent.equivOfEq _ _ (ker_residue (R := B)))
    let i : Algebra.H1Cotangent A K → CotangentSpace B :=
      fun x ↦ e (Algebra.H1Cotangent.map A B K K x)
    let d : CotangentSpace B → K ⊗[B] Ω[B⁄A] :=
      fun x ↦ Algebra.H1Cotangent.δ A B K (e.symm x)
    Function.Injective i ∧
      Function.Exact i d ∧
      Function.Exact d (KaehlerDifferential.mapBaseChange A B K) ∧
      Function.Surjective (KaehlerDifferential.mapBaseChange A B K) := by
  let K := ResidueField B
  let _ : Algebra A B := f.toAlgebra
  let _ : Algebra A K := ((residue B).comp f).toAlgebra
  let _ : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq' rfl
  dsimp only
  let e : Algebra.H1Cotangent B K ≃ₗ[B] CotangentSpace B :=
    (h1Cotangent_equiv_cotangent_of_surjective B K residue_surjective).trans
      (Ideal.Cotangent.equivOfEq _ _ (ker_residue (R := B)))
  have hi : Function.Injective (Algebra.H1Cotangent.map A B K K) :=
    h1Cotangent_map_injective_of_formallySmoothNAdic (maximalIdeal B) hf
      ⟨1, le_rfl, by
        change maximalIdeal B ^ 1 ≤ RingHom.ker (residue B)
        rw [pow_one, ker_residue]⟩
  refine ⟨e.injective.comp hi, ?_, ?_,
    KaehlerDifferential.mapBaseChange_surjective A B K residue_surjective⟩
  · intro y
    change Algebra.H1Cotangent.δ A B K (e.symm y) = 0 ↔
      y ∈ Set.range (fun x ↦ e (Algebra.H1Cotangent.map A B K K x))
    rw [Algebra.H1Cotangent.exact_map_δ A B K]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by simp only [hx, LinearEquiv.apply_symm_apply]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, (e.symm_apply_apply _).symm⟩
  · intro y
    change KaehlerDifferential.mapBaseChange A B K y = 0 ↔
      y ∈ Set.range (fun x ↦ Algebra.H1Cotangent.δ A B K (e.symm x))
    rw [Algebra.H1Cotangent.exact_δ_mapBaseChange A B K]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e x, by simp only [LinearEquiv.symm_apply_apply]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e.symm x, rfl⟩

end

end

/-! ### Stacks Tag 07EL -/

section

section

set_option maxRecDepth 4096

open scoped TensorProduct
open IsLocalRing

universe t u v

private lemma exists_derivation_extension_of_injective
    (R k A K M : Type*) [CommRing R] [CommRing k] [CommRing A] [Field K]
    [Algebra R k] [Algebra k A] [Algebra R A] [IsScalarTower R k A]
    [Algebra A K] [Algebra k K] [IsScalarTower k A K]
    [AddCommGroup M] [Module K M] [Module A M] [Module k M] [Module R M]
    [IsScalarTower A K M] [IsScalarTower k A M] [IsScalarTower R k M] [IsScalarTower R A M]
    (hinj : Function.Injective ((KaehlerDifferential.mapBaseChange R k A).baseChange K))
    (d : Derivation R k M) :
    ∃ D : Derivation R A M, ∀ x, D (algebraMap k A x) = d x := by
  let f := (KaehlerDifferential.mapBaseChange R k A).baseChange K
  let g := f.leftInverse
  have hg : g.comp f = LinearMap.id :=
    LinearMap.leftInverse_comp_of_inj (LinearMap.ker_eq_bot.mpr hinj)
  let l := (d.liftKaehlerDifferential.liftBaseChange A).liftBaseChange K
  let t : Ω[A⁄R] →ₗ[A] K ⊗[A] Ω[A⁄R] := TensorProduct.mk A K Ω[A⁄R] 1
  let D := ((l.comp g).restrictScalars A |>.comp t).compDer (KaehlerDifferential.D R A)
  refine ⟨D, fun x => ?_⟩
  have hgx := LinearMap.congr_fun hg (1 ⊗ₜ[A] (1 ⊗ₜ[k] KaehlerDifferential.D R k x))
  dsimp [f] at hgx
  simp only [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D,
    one_smul] at hgx
  change l (g (1 ⊗ₜ[A] KaehlerDifferential.D R A (algebraMap k A x))) = d x
  rw [hgx]
  simp [l]

private lemma exists_lift_of_injective_kaehlerDifferential
    (p : ℕ) (k A : Type*)
    [CommRing k] [CommRing A] [IsLocalRing A]
    [Algebra (ZMod p) k] [Algebra k A] [Algebra (ZMod p) A]
    [IsScalarTower (ZMod p) k A]
    (hinj : Function.Injective
      ((KaehlerDifferential.mapBaseChange (ZMod p) k A).baseChange (ResidueField A)))
    {B : Type*} [CommRing B] (J : Ideal B) (hJ : J ^ 2 = ⊥)
    (φ : k →+* B) (ψ : A →+* B)
    (hcomm : (Ideal.Quotient.mk J).comp φ =
      ((Ideal.Quotient.mk J).comp ψ).comp (algebraMap k A))
    (hkill : ∀ a ∈ maximalIdeal A, ∀ b ∈ J, ψ a * b = 0) :
    ∃ ψ' : A →+* B, ψ'.comp (algebraMap k A) = φ ∧
      (Ideal.Quotient.mk J).comp ψ' = (Ideal.Quotient.mk J).comp ψ := by
  let : Algebra A B := ψ.toAlgebra
  let : Algebra k B := (ψ.comp (algebraMap k A)).toAlgebra
  let : Algebra (ZMod p) B := (ψ.comp (algebraMap (ZMod p) A)).toAlgebra
  let : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (ZMod p) A B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (ZMod p) k B := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact congrArg ψ (IsScalarTower.algebraMap_apply (ZMod p) k A x))
  have htor : Module.IsTorsionBySet A J (maximalIdeal A) := by
    intro b a
    apply Subtype.ext
    exact hkill a a.property b b.property
  let : Module (ResidueField A) J := htor.module
  have : IsScalarTower A (ResidueField A) J := htor.isScalarTower
  let φₐ : k →ₐ[ZMod p] B :=
    { φ with
      commutes' := by
        intro x
        exact congrArg (fun f : ZMod p →+* B => f x)
          (Subsingleton.elim (φ.comp (algebraMap (ZMod p) k)) (algebraMap (ZMod p) B)) }
  have he : (Ideal.Quotient.mkₐ (ZMod p) J).comp φₐ =
      IsScalarTower.toAlgHom (ZMod p) k (B ⧸ J) := by
    ext x
    exact RingHom.congr_fun hcomm x
  let d := derivationToSquareZeroOfLift J hJ φₐ he
  obtain ⟨D, hD⟩ := exists_derivation_extension_of_injective
    (ZMod p) k A (ResidueField A) J hinj d
  let ψ' := liftOfDerivationToSquareZero J hJ D
  refine ⟨ψ'.toRingHom, ?_, ?_⟩
  · ext x
    change (D (algebraMap k A x) : B) + ψ (algebraMap k A x) = φ x
    rw [hD]
    exact sub_add_cancel _ _
  · ext x
    exact liftOfDerivationToSquareZero_mk_apply J hJ D x
private lemma formallySmoothNAdic_of_injective_kaehlerDifferential
    (p : ℕ) [Fact p.Prime] (k : Type u) (A : Type v)
    [Field k] [CharP k p] [CommRing A] [Algebra k A] [IsRegularLocalRing A]
    [Algebra (ZMod p) k] [Algebra (ZMod p) A] [IsScalarTower (ZMod p) k A]
    (hinj : Function.Injective
      ((KaehlerDifferential.mapBaseChange (ZMod p) k A).baseChange (ResidueField A))) :
    RingHom.FormallySmoothNAdic.{t} (algebraMap k A) (maximalIdeal A) := by
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := ⟨rfl⟩
  let : TopologicalSpace A := (maximalIdeal A).adicTopology
  let : IsTopologicalRing A := (maximalIdeal A).ringFilterBasis.isTopologicalRing
  let : IsLinearTopology A A := (maximalIdeal A).isLinearTopology
  apply (isFormallySmooth_iff_formallySmoothNAdic _ _ rfl).mp
  have htop : (maximalIdeal k).adicTopology = (⊥ : TopologicalSpace k) := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact (is_bot_adic_iff.mpr (inferInstance : DiscreteTopology k)).symm
  have hfs := (formallySmooth_adic_iff_lifts_local_squareZero.{t}
    (algebraMap k A)).2 (inferInstance : IsNoetherianRing A)
  suffices H :
      @IsFormallySmooth.{t} k A _ (maximalIdeal k).adicTopology
        (maximalIdeal k).ringFilterBasis.isTopologicalRing
        (maximalIdeal k).isLinearTopology _ (maximalIdeal A).adicTopology
        (maximalIdeal A).ringFilterBasis.isTopologicalRing
        (maximalIdeal A).isLinearTopology (algebraMap k A) by
    convert H using 1
    exact htop.symm
  apply hfs.mpr
  intro B _ _ J _ hJ hn hsmall φ _ gbar _ hcomm _
  obtain ⟨n, hn, hnil⟩ := hn
  have hnilq : maximalIdeal (B ⧸ J) ^ n = ⊥ := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective,
      ← Ideal.map_pow, hnil, Ideal.map_bot]
  have hker : maximalIdeal A ^ n ≤ RingHom.ker gbar := by
    apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_pow]
    exact (pow_le_pow_left' (map_maximalIdeal_le gbar) n).trans_eq hnilq
  let : TopologicalSpace (ZMod p) := ⊥
  let : DiscreteTopology (ZMod p) := ⟨rfl⟩
  have hFp := isFormallySmooth_maximalIdeal_of_isRegularLocalRing.{t}
    (k := ZMod p) (A := A) (Algebra.isSeparableExtension_of_perfectField _ _)
  have hFpN := (isFormallySmooth_iff_formallySmoothNAdic
    (algebraMap (ZMod p) A) (maximalIdeal A) rfl).mp hFp
  obtain ⟨ψ, hψ, _⟩ := hFpN B J hJ (φ.comp (algebraMap (ZMod p) k)) gbar
    (by rw [IsScalarTower.algebraMap_eq (ZMod p) k A, ← RingHom.comp_assoc, hcomm,
      RingHom.comp_assoc]) ⟨n, hn, hker⟩
  have : IsLocalHom ((Ideal.Quotient.mk J).comp ψ) := hψ.symm ▸ inferInstance
  have : IsLocalHom ψ := isLocalHom_of_comp ψ (Ideal.Quotient.mk J)
  have hs : IsSimpleModule B J := by
    apply Module.length_eq_one_iff.mp
    have hh : Module.length B (RingHom.ker (Ideal.Quotient.mk J)) = 1 :=
      hsmall.2.2.2.2.2
    exact (LinearEquiv.ofEq (RingHom.ker (Ideal.Quotient.mk J)) J
      (Ideal.mk_ker (I := J))).length_eq.symm.trans hh
  have hann : Module.annihilator B J = maximalIdeal B :=
    eq_maximalIdeal (IsSimpleModule.annihilator_isMaximal (R := B) (M := J))
  obtain ⟨ψ', hψ'k, hψ'q⟩ := exists_lift_of_injective_kaehlerDifferential p k A hinj
    J hJ φ ψ (by rw [hψ]; exact hcomm.symm) (by
      intro a ha b hb
      have hmem : ψ a ∈ Module.annihilator B J := by
        rw [hann]
        exact map_nonunit ψ a ha
      exact congrArg Subtype.val ((Module.mem_annihilator.mp hmem) ⟨b, hb⟩))
  have hq : (Ideal.Quotient.mk J).comp ψ' = gbar := hψ'q.trans hψ
  have : IsLocalHom ((Ideal.Quotient.mk J).comp ψ') := hq.symm ▸ inferInstance
  exact ⟨ψ', isLocalHom_of_comp ψ' (Ideal.Quotient.mk J), hψ'k, hq⟩

private lemma RingHom.FormallySmoothNAdic.exists_lift_of_surjective
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (n : Ideal S)
    (h : RingHom.FormallySmoothNAdic.{t} φ n)
    {B : Type t} {C : Type*} [CommRing B] [CommRing C]
    (π : B →+* C) (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = ⊥)
    (f : R →+* B) (g : S →+* C) (hcomm : g.comp φ = π.comp f)
    (hker : ∃ n' : ℕ, 1 ≤ n' ∧ n ^ n' ≤ RingHom.ker g) :
    ∃ g' : S →+* B, π.comp g' = g ∧ g'.comp φ = f := by
  let e := π.quotientKerEquivOfSurjective hπ
  obtain ⟨m, hm, hmk⟩ := hker
  obtain ⟨g', hq, hf⟩ := h B (RingHom.ker π) hsq f (e.symm.toRingHom.comp g)
    (by rw [RingHom.comp_assoc, hcomm, ← RingHom.comp_assoc]
        exact congrArg (fun q => q.comp f) (RingHom.quotientKerEquivOfSurjective_symm_comp hπ))
    ⟨m, hm, fun x hx => by change e.symm (g x) = 0; rw [hmk hx, map_zero]⟩
  refine ⟨g', ?_, hf⟩
  ext x
  have hx := congrArg e (RingHom.congr_fun hq x)
  simpa [e] using hx

private lemma exists_derivation_extension_of_formallySmoothNAdic
    (p : ℕ) (k : Type u) (A : Type v) [CommRing k]
    [CommRing A] [IsLocalRing A] [Algebra (ZMod p) k] [Algebra k A]
    [Algebra (ZMod p) A] [IsScalarTower (ZMod p) k A]
    (M : Type t) [AddCommGroup M] [Module (ResidueField A) M]
    [Module A M] [Module k M] [Module (ZMod p) M]
    [IsScalarTower A (ResidueField A) M] [IsScalarTower k A M]
    [IsScalarTower (ZMod p) A M] [IsScalarTower (ZMod p) k M]
    (h : RingHom.FormallySmoothNAdic.{max v t} (algebraMap k A) (maximalIdeal A))
    (d : Derivation (ZMod p) k M) :
    ∃ D : Derivation (ZMod p) A M, ∀ x, D (algebraMap k A x) = d x := by
  let K := ResidueField A
  let : Module Kᵐᵒᵖ M := Module.compHom M (RingEquiv.toOpposite K).symm.toRingHom
  let : IsCentralScalar K M := ⟨fun _ _ => rfl⟩
  let B := TrivSqZeroExt K M
  let π : B →+* K := (TrivSqZeroExt.fstHom K K M).toRingHom
  let f : k →+* B :=
    { toFun := fun x => ⟨algebraMap k K x, d x⟩
      map_one' := by
        apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk]
      map_zero' := by
        apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk]
      map_add' := by
        intro x y
        apply TrivSqZeroExt.ext
        · exact map_add (algebraMap k K) x y
        · exact map_add d x y
      map_mul' := by
        intro x y
        apply TrivSqZeroExt.ext
        · exact map_mul (algebraMap k K) x y
        · change d (x * y) = algebraMap k K x • d y + algebraMap k K y • d x
          simpa only [IsScalarTower.algebraMap_apply k A K, IsScalarTower.algebraMap_smul]
            using d.leibniz x y }
  have hπ : Function.Surjective π := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  obtain ⟨g, hg, hgf⟩ := RingHom.FormallySmoothNAdic.exists_lift_of_surjective
    (algebraMap k A) (maximalIdeal A) h π hπ (TrivSqZeroExt.kerIdeal_sq K M)
    f (algebraMap A K) (by ext; rfl) ⟨1, le_rfl, by
      change maximalIdeal A ^ 1 ≤ RingHom.ker (residue A)
      rw [pow_one, IsLocalRing.ker_residue]⟩
  let gₐ : A →ₐ[ZMod p] B :=
    { g with
      commutes' := by
        intro x
        exact congrArg (fun f : ZMod p →+* B => f x)
          (Subsingleton.elim (g.comp (algebraMap (ZMod p) A)) (algebraMap (ZMod p) B)) }
  have hgfst (a : A) : (g a).fst = algebraMap A K a := RingHom.congr_fun hg a
  let D : Derivation (ZMod p) A M :=
    { (TrivSqZeroExt.sndHom K M).restrictScalars (ZMod p) |>.comp gₐ.toLinearMap with
      map_one_eq_zero' := by change (g 1).snd = 0; simp
      leibniz' := by
        intro a b
        change (g (a * b)).snd = a • (g b).snd + b • (g a).snd
        rw [map_mul, TrivSqZeroExt.snd_mul, hgfst, hgfst]
        simp }
  refine ⟨D, fun x => ?_⟩
  exact congrArg TrivSqZeroExt.snd (RingHom.congr_fun hgf x)
private lemma injective_kaehlerDifferential_of_formallySmoothNAdic
    (p : ℕ) (k : Type u) (A : Type v)
    [CommRing k] [CommRing A] [IsLocalRing A] [Algebra k A]
    [Algebra (ZMod p) k] [Algebra (ZMod p) A] [IsScalarTower (ZMod p) k A]
    (h : RingHom.FormallySmoothNAdic.{max u v} (algebraMap k A) (maximalIdeal A)) :
    Function.Injective
      ((KaehlerDifferential.mapBaseChange (ZMod p) k A).baseChange (ResidueField A)) := by
  let K := ResidueField A
  let M := K ⊗[A] (A ⊗[k] Ω[k⁄ZMod p])
  let t₁ : Ω[k⁄ZMod p] →ₗ[k] A ⊗[k] Ω[k⁄ZMod p] :=
    TensorProduct.mk k A Ω[k⁄ZMod p] 1
  let t₂ : A ⊗[k] Ω[k⁄ZMod p] →ₗ[A] M :=
    TensorProduct.mk A K (A ⊗[k] Ω[k⁄ZMod p]) 1
  let d := ((t₂.restrictScalars k).comp t₁).compDer (KaehlerDifferential.D (ZMod p) k)
  obtain ⟨D, hD⟩ := exists_derivation_extension_of_formallySmoothNAdic p k A M h d
  let l := D.liftKaehlerDifferential.liftBaseChange K
  let f := (KaehlerDifferential.mapBaseChange (ZMod p) k A).baseChange K
  have hl : l.comp f = LinearMap.id := by
    ext x
    simp [f, l, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D,
      hD, d, t₁, t₂]
    rfl
  exact Function.LeftInverse.injective (fun x => LinearMap.congr_fun hl x)

/-- Let `A` be a Noetherian local algebra over a field `k`. In characteristic zero, `A` is a
regular local ring if and only if `k → A` is formally smooth for the maximal-ideal adic
topology. In prime characteristic `p`, the following are equivalent:

1. `A` is geometrically regular over `k`;
2. `k → A` is formally smooth for the maximal-ideal adic topology;
3. every finite intermediate extension in `k¹ᵖ` gives a regular base change;
4. `A` is regular and the canonical cotangent-complex map is injective;
5. `A` is regular and the canonical map on Kähler differentials is injective. -/
@[stacks 07EL,
  ega "0 19.6.6" "a) <=> c)",
  ega "0 19.6.4" "char 0: a) ⇔ c)",
  ega "0 19.6.5" "form. smooth ⟹ geom reg",
  ega "0 22.1.2" "base a field, Noetherian",
  ega "0 22.2.2" "(i)&(ii), char p",
  ega "0 22.2.3" "a) (char p)",
  ega "0 22.7.2" "a) <=> c) char 0",
  ega "0 22.5.8",
  ega "0 22.6.7" "(i) b) ⇔ d)",
  ega "0 19.0.2" "special case",
  ega "0 19.6.7" "19.6.7(ii), special case"]
public theorem formalSmoothness_maximalIdeal_characterizations
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsNoetherianRing A] [IsLocalRing A] :
    (let m := IsLocalRing.maximalIdeal A
     letI : TopologicalSpace k := ⊥
     letI : DiscreteTopology k := ⟨rfl⟩
     letI : TopologicalSpace A := m.adicTopology
     letI : IsTopologicalRing A := m.ringFilterBasis.isTopologicalRing
     letI : IsLinearTopology A A := m.isLinearTopology
     ∀ [CharZero k],
       IsRegularLocalRing A ↔
         IsFormallySmooth.{max u v} (algebraMap k A)) ∧
    (∀ (p : ℕ) [Fact p.Prime] [CharP k p],
      letI : Algebra (ZMod p) k := ZMod.algebra k p
      letI : Algebra (ZMod p) A :=
        ((algebraMap k A).comp (algebraMap (ZMod p) k)).toAlgebra
      letI : IsScalarTower (ZMod p) k A := IsScalarTower.of_algebraMap_eq' rfl
      letI : Algebra k (PerfectClosure k p) := (PerfectClosure.of k p).toAlgebra
      let m := IsLocalRing.maximalIdeal A
      letI : TopologicalSpace k := ⊥
      letI : DiscreteTopology k := ⟨rfl⟩
      letI : TopologicalSpace A := m.adicTopology
      letI : IsTopologicalRing A := m.ringFilterBasis.isTopologicalRing
      letI : IsLinearTopology A A := m.isLinearTopology
      List.TFAE [
        Algebra.IsGeometricallyRegular k A,
        IsFormallySmooth.{max u v} (algebraMap k A),
        (∀ (k' : IntermediateField k (PerfectClosure k p)),
          FiniteDimensional k k' →
          (∀ x : k', (x : PerfectClosure k p) ^ p ∈
            Set.range (algebraMap k (PerfectClosure k p))) →
          IsRegularRing (A ⊗[k] k')),
        IsRegularLocalRing A ∧
          Function.Injective
            (Algebra.H1Cotangent.map k A (IsLocalRing.ResidueField A)
              (IsLocalRing.ResidueField A)),
        IsRegularLocalRing A ∧
          Function.Injective
            ((KaehlerDifferential.mapBaseChange (ZMod p) k A).baseChange
              (IsLocalRing.ResidueField A))]) := by
  constructor
  · dsimp only
    intro _
    constructor
    · intro h
      let := h
      exact isFormallySmooth_maximalIdeal_of_isRegularLocalRing
        (Algebra.isSeparableExtension_of_perfectField k (ResidueField A))
    · exact isRegularLocalRing_of_isFormallySmooth_maximalIdeal
  · intro p _ _
    dsimp only
    let : Algebra (ZMod p) k := ZMod.algebra k p
    let : Algebra (ZMod p) A :=
      ((algebraMap k A).comp (algebraMap (ZMod p) k)).toAlgebra
    let : IsScalarTower (ZMod p) k A := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra k (PerfectClosure k p) := (PerfectClosure.of k p).toAlgebra
    let : TopologicalSpace k := ⊥
    let : DiscreteTopology k := ⟨rfl⟩
    let : TopologicalSpace A := (maximalIdeal A).adicTopology
    let : IsTopologicalRing A := (maximalIdeal A).ringFilterBasis.isTopologicalRing
    let : IsLinearTopology A A := (maximalIdeal A).isLinearTopology
    have hfour := geometricallyRegular_tfae p k A
    tfae_have 1 ↔ 3 := hfour.out 1 2
    tfae_have 1 ↔ 4 := hfour.out 1 3
    tfae_have 1 ↔ 5 := hfour.out 1 4
    tfae_have 2 → 5 := by
      intro h
      refine ⟨isRegularLocalRing_of_isFormallySmooth_maximalIdeal h, ?_⟩
      exact injective_kaehlerDifferential_of_formallySmoothNAdic p k A
        ((isFormallySmooth_iff_formallySmoothNAdic _ _ rfl).mp h)
    tfae_have 5 → 2 := by
      rintro ⟨hreg, hinj⟩
      let := hreg
      exact (isFormallySmooth_iff_formallySmoothNAdic _ _ rfl).mpr
        (formallySmoothNAdic_of_injective_kaehlerDifferential p k A hinj)
    tfae_finish

end

end

/-! ### Stacks Tag 07EM -/

section

universe u v w

/-- `IsAdicallyFormallySmooth I f` means that `f` is formally smooth in the sense of
`IsFormallySmooth` when its source has the discrete topology and its target has the
`I`-adic topology. -/
public def IsAdicallyFormallySmooth {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    (I : Ideal S) (f : R →+* S) : Prop :=
  letI : TopologicalSpace R := ⊥
  letI : DiscreteTopology R := ⟨rfl⟩
  letI : TopologicalSpace S := I.adicTopology
  letI : IsTopologicalRing S := I.ringFilterBasis.isTopologicalRing
  letI : IsLinearTopology S S := I.isLinearTopology
  IsFormallySmooth.{max v w, v, w} f

private theorem irreducible_X_pow_sub_C_of_not_isPow
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] (a : k)
    (ha : a ∉ Set.range (fun b : k => b ^ p)) :
    Irreducible (Polynomial.X ^ p - Polynomial.C a) := by
  apply X_pow_sub_C_irreducible_of_prime Fact.out
  intro b hb
  exact ha ⟨b, hb⟩

private theorem kaehler_D_map_perfect {R : Type*} {K : Type*} {A : Type*}
    [CommRing R] [CommSemiring K] [CommRing A] [Algebra R A] [Algebra K A]
    (p : ℕ) [CharP A p] [PerfectRing K p] (a : K) :
    KaehlerDifferential.D R A (algebraMap K A a) = 0 := by
  obtain ⟨b, hb⟩ := (PerfectRing.bijective_frobenius (R := K) (p := p)).2 a
  rw [← hb, map_pow, Stacks.Derivations.derivation_pow_char]

open scoped BigOperators
open PowerSeries

private theorem exists_sum_pow_mul_X_pow
    {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (hroot : Function.Surjective (fun x : R => x ^ p)) (f : PowerSeries R) :
    ∃ g : Fin p → PowerSeries R, f = ∑ i, g i ^ p * X ^ (i : ℕ) := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  choose root hroot using hroot
  dsimp only at hroot
  let g : Fin p → PowerSeries R := fun i => mk fun n => root (coeff (p * n + i) f)
  refine ⟨g, ?_⟩
  ext n
  rw [map_sum]
  symm
  rw [Finset.sum_eq_single (⟨n % p, Nat.mod_lt _ hp⟩ : Fin p)]
  · rw [coeff_mul_X_pow', ite_eq_left (Nat.mod_le _ _)]
    rw [← map_frobenius_expand p hp.ne', coeff_map, coeff_expand]
    rw [ite_eq_left (Nat.dvd_sub_mod n)]
    dsimp [g]
    rw [coeff_mk, frobenius_def, hroot]
    rw [Nat.mul_div_cancel' (Nat.dvd_sub_mod n), Nat.sub_add_cancel (Nat.mod_le n p)]
  · intro i _ hi
    rw [coeff_mul_X_pow']
    split_ifs with hin
    · rw [← map_frobenius_expand p hp.ne', coeff_map, coeff_expand]
      have hn : ¬ p ∣ n - i := by
        intro hd
        have heq : n % p = i := by
          have : n = (n - i) + i := by omega
          rw [this, Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, zero_add,
            Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt i.isLt]
        exact hi (Fin.ext heq.symm)
      simp [hn]
    · rfl
  · simp

private theorem exists_kaehler_basis_powerSeries
    {R K : Type*} [CommRing R] [CommRing K] [Algebra R K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hroot : Function.Surjective (fun x : K => x ^ p)) :
    ∃ b : Module.Basis Unit (PowerSeries K) (KaehlerDifferential R (PowerSeries K)),
      b () = KaehlerDifferential.D R (PowerSeries K) X := by
  classical
  have : CharP (PowerSeries K) p :=
    charP_of_injective_algebraMap PowerSeries.C_injective p
  let D := KaehlerDifferential.D R (PowerSeries K)
  let v := D X
  let l := LinearMap.toSpanSingleton (PowerSeries K) _ v
  let d := (PowerSeries.derivative (R := K)).restrictScalars R
  have hd : d.liftKaehlerDifferential v = 1 := by simp [v, D, d]
  have hinj : Function.Injective l := by
    intro a b h
    have h' := congrArg d.liftKaehlerDifferential h
    simpa [l, LinearMap.toSpanSingleton_apply, hd] using h'
  have hsurj : Function.Surjective l := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← KaehlerDifferential.span_range_derivation,
      Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    obtain ⟨g, rfl⟩ := exists_sum_pow_mul_X_pow p hroot f
    rw [map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [Derivation.leibniz, Stacks.Derivations.derivation_pow_char p D, smul_zero, add_zero,
      Derivation.leibniz_pow]
    exact ⟨g i ^ p * ((i : ℕ) • X ^ ((i : ℕ) - 1)), by
      simp only [l, v, D, LinearMap.toSpanSingleton_apply,
        ← Nat.cast_smul_eq_nsmul (PowerSeries K), smul_smul, smul_eq_mul]⟩
  let e := LinearEquiv.ofBijective l ⟨hinj, hsurj⟩
  refine ⟨(Module.Basis.singleton Unit (PowerSeries K)).map e, ?_⟩
  change l ((Module.Basis.singleton Unit (PowerSeries K)) ()) = D X
  simp [l, v, LinearMap.toSpanSingleton_apply]

open scoped nonZeroDivisors

private theorem exists_ratFunc_to_powerSeries
    {F K : Type*} [Field F] [Field K] (i : RatFunc F →+* K) :
    ∃ f : RatFunc F →+* PowerSeries K,
      f RatFunc.X = PowerSeries.C (i RatFunc.X) + PowerSeries.X := by
  let h : Polynomial F →+* PowerSeries K :=
    Polynomial.eval₂RingHom (PowerSeries.C.comp (i.comp RatFunc.C))
      (PowerSeries.C (i RatFunc.X) + PowerSeries.X)
  have hc : PowerSeries.constantCoeff.comp h = i.comp (algebraMap (Polynomial F) (RatFunc F)) := by
    ext <;> simp [h, RatFunc.algebraMap_X]
  have hu : ∀ a : (Polynomial F)⁰, IsUnit (h a) := by
    intro a
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    change (PowerSeries.constantCoeff.comp h) a ≠ 0
    rw [hc]
    apply (map_ne_zero i).2
    simpa only [map_zero] using (IsFractionRing.injective (Polynomial F) (RatFunc F)).ne
      (mem_nonZeroDivisors_iff_ne_zero.mp a.property)
  let f : RatFunc F →+* PowerSeries K := IsLocalization.lift hu
  refine ⟨f, ?_⟩
  change f (algebraMap (Polynomial F) (RatFunc F) Polynomial.X) = _
  rw [IsLocalization.lift_eq]
  simp [h]

private theorem exists_kaehler_basis_ratFunc
    (F : Type*) [Field F] :
    ∃ b : Module.Basis Unit (RatFunc F) (KaehlerDifferential F (RatFunc F)),
      b () = KaehlerDifferential.D F (RatFunc F) RatFunc.X := by
  let b := (Module.Basis.singleton Unit (Polynomial F)).map
    (KaehlerDifferential.polynomialEquiv F).symm
  let f := KaehlerDifferential.map F F (Polynomial F) (RatFunc F)
  refine ⟨b.ofIsLocalizedModule (RatFunc F) (Polynomial F)⁰ f, ?_⟩
  simp [b, f, Module.Basis.ofIsLocalizedModule_apply, KaehlerDifferential.polynomialEquiv_symm,
    KaehlerDifferential.map_D, RatFunc.algebraMap_X]

private theorem injective_baseChange_kaehler_mapBaseChange_of_basis
    {R A B S : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing S]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra B S] {ι : Type*}
    (a : Module.Basis ι A (KaehlerDifferential R A))
    (b : Module.Basis ι B (KaehlerDifferential R B))
    (h : ∀ i, KaehlerDifferential.map R R A B (a i) = b i) :
    Function.Injective ((KaehlerDifferential.mapBaseChange R A B).baseChange S) := by
  let e := (a.baseChange B).equiv b (Equiv.refl ι)
  have he : KaehlerDifferential.mapBaseChange R A B = e.toLinearMap := by
    apply (a.baseChange B).ext
    intro i
    change _ = ((a.baseChange B).equiv b (Equiv.refl ι)) ((a.baseChange B) i)
    rw [Module.Basis.equiv_apply]
    simp [Module.Basis.baseChange_apply, KaehlerDifferential.mapBaseChange_tmul, h]
  rw [he]
  exact (LinearEquiv.baseChange B S _ _ e).injective

private theorem exists_kaehler_basis_powerSeries_zmod
    {K : Type*} [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [a : Algebra (ZMod p) (PowerSeries K)]
    (hroot : Function.Surjective (fun x : K => x ^ p)) :
    ∃ b : Module.Basis Unit (PowerSeries K) (KaehlerDifferential (ZMod p) (PowerSeries K)),
      b () = KaehlerDifferential.D (ZMod p) (PowerSeries K) X := by
  let : Algebra (ZMod p) K := ZMod.algebra K p
  have heq : a = MvPowerSeries.instAlgebra := Subsingleton.elim _ _
  cases heq
  exact exists_kaehler_basis_powerSeries p hroot

private theorem exists_ratFunc_to_powerSeries_with_differential_bases (p : ℕ) [Fact p.Prime] :
    let k := RatFunc (ZMod p)
    let K := PerfectClosure k p
    let : Algebra k K := (PerfectClosure.of k p).toAlgebra
    let A := PowerSeries K
    ∃ f : k →+* A,
      f RatFunc.X =
         PowerSeries.C (algebraMap k K RatFunc.X) + PowerSeries.X ∧
      let : Algebra k A := f.toAlgebra
      let : Algebra (ZMod p) A :=
        (f.comp (algebraMap (ZMod p) k)).toAlgebra
      let : IsScalarTower (ZMod p) k A :=
        IsScalarTower.of_algebraMap_eq' rfl
      (∃ b : Module.Basis Unit k (KaehlerDifferential (ZMod p) k),
         b () = KaehlerDifferential.D (ZMod p) k RatFunc.X) ∧
      (∃ b : Module.Basis Unit A (KaehlerDifferential (ZMod p) A),
         b () = KaehlerDifferential.D (ZMod p) A PowerSeries.X) ∧
      KaehlerDifferential.map (ZMod p) (ZMod p) k A
          (KaehlerDifferential.D (ZMod p) k RatFunc.X) =
        KaehlerDifferential.D (ZMod p) A PowerSeries.X := by
  classical
  let k := RatFunc (ZMod p)
  let K := PerfectClosure k p
  let : Algebra k K := (PerfectClosure.of k p).toAlgebra
  let A := PowerSeries K
  obtain ⟨f, hf⟩ := exists_ratFunc_to_powerSeries (PerfectClosure.of k p)
  refine ⟨f, hf, ?_⟩
  let : Algebra k A := f.toAlgebra
  let : Algebra (ZMod p) A := (f.comp (algebraMap (ZMod p) k)).toAlgebra
  let : IsScalarTower (ZMod p) k A := IsScalarTower.of_algebraMap_eq' rfl
  have hchar : CharP A p := charP_of_injective_algebraMap PowerSeries.C_injective p
  obtain ⟨bk, hbk⟩ := exists_kaehler_basis_ratFunc (ZMod p)
  obtain ⟨ba, hba⟩ := exists_kaehler_basis_powerSeries_zmod (K := K) p
    (surjective_frobenius K p)
  have hd : KaehlerDifferential.map (ZMod p) (ZMod p) k A
      (KaehlerDifferential.D (ZMod p) k RatFunc.X) =
        KaehlerDifferential.D (ZMod p) A X := by
    rw [KaehlerDifferential.map_D]
    change KaehlerDifferential.D (ZMod p) A (f RatFunc.X) = _
    rw [hf, map_add]
    have hz := kaehler_D_map_perfect (R := ZMod p) (A := A) p
      (algebraMap k K RatFunc.X)
    change KaehlerDifferential.D (ZMod p) A (C _) = 0 at hz
    simpa only [RingHom.algebraMap_toAlgebra, zero_add] using congrArg
      (fun z => z + KaehlerDifferential.D (ZMod p) A X) hz
  exact ⟨⟨bk, hbk⟩, ⟨ba, hba⟩, hd⟩

section

set_option maxRecDepth 4096

open scoped TensorProduct
open IsLocalRing

universe t



end

private theorem isAdicallyFormallySmooth_of_injective_kaehler_mapBaseChange
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    [IsRegularLocalRing A] (p : ℕ) [Fact p.Prime] [CharP k p]
    [a₀ : Algebra (ZMod p) k] [a₁ : Algebra (ZMod p) A]
    [IsScalarTower (ZMod p) k A]
    (hinj : Function.Injective
      ((KaehlerDifferential.mapBaseChange (ZMod p) k A).baseChange (IsLocalRing.ResidueField A))) :
    IsAdicallyFormallySmooth (IsLocalRing.maximalIdeal A) (algebraMap k A) := by
  have hk : a₀ = ZMod.algebra k p := Subsingleton.elim _ _
  cases hk
  let : Algebra (ZMod p) k := ZMod.algebra k p
  have ha : a₁ = ((algebraMap k A).comp (algebraMap (ZMod p) k)).toAlgebra :=
    Subsingleton.elim _ _
  cases ha
  let : Algebra (ZMod p) A := ((algebraMap k A).comp (algebraMap (ZMod p) k)).toAlgebra
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := ⟨rfl⟩
  let : TopologicalSpace A := (IsLocalRing.maximalIdeal A).adicTopology
  let : IsTopologicalRing A := (IsLocalRing.maximalIdeal A).ringFilterBasis.isTopologicalRing
  let : IsLinearTopology A A := (IsLocalRing.maximalIdeal A).isLinearTopology
  exact (isFormallySmooth_iff_formallySmoothNAdic _ _ rfl).mpr
    (formallySmoothNAdic_of_injective_kaehlerDifferential p k A hinj)

private theorem exists_adicallyFormallySmooth_ratFunc_to_powerSeries (p : ℕ) [Fact p.Prime] :
    let k := RatFunc (ZMod p)
    let K := PerfectClosure k p
    let : Algebra k K := (PerfectClosure.of k p).toAlgebra
    let A := PowerSeries K
    ∃ f : k →+* A,
      f RatFunc.X =
         PowerSeries.C (algebraMap k K RatFunc.X) + PowerSeries.X ∧
      let : Algebra k A := f.toAlgebra
      let : Algebra (ZMod p) A :=
        (f.comp (algebraMap (ZMod p) k)).toAlgebra
      let : IsScalarTower (ZMod p) k A :=
        IsScalarTower.of_algebraMap_eq' rfl
      (∃ b : Module.Basis Unit k (KaehlerDifferential (ZMod p) k),
         b () = KaehlerDifferential.D (ZMod p) k RatFunc.X) ∧
      (∃ b : Module.Basis Unit A (KaehlerDifferential (ZMod p) A),
         b () = KaehlerDifferential.D (ZMod p) A PowerSeries.X) ∧
      KaehlerDifferential.map (ZMod p) (ZMod p) k A
          (KaehlerDifferential.D (ZMod p) k RatFunc.X) =
        KaehlerDifferential.D (ZMod p) A PowerSeries.X ∧
      IsAdicallyFormallySmooth (Ideal.span {PowerSeries.X}) f := by
  classical
  let k := RatFunc (ZMod p)
  let K := PerfectClosure k p
  let : Algebra k K := (PerfectClosure.of k p).toAlgebra
  let A := PowerSeries K
  obtain ⟨f, hf, hb, hc, hd⟩ := exists_ratFunc_to_powerSeries_with_differential_bases p
  refine ⟨f, hf, hb, hc, hd, ?_⟩
  let : Algebra k A := f.toAlgebra
  let : Algebra (ZMod p) A := (f.comp (algebraMap (ZMod p) k)).toAlgebra
  let : IsScalarTower (ZMod p) k A := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨bk, hbk⟩ := hb
  obtain ⟨ba, hba⟩ := hc
  have hinj := injective_baseChange_kaehler_mapBaseChange_of_basis
    (S := IsLocalRing.ResidueField A) bk ba (fun i => by
      cases i
      rw [hbk, hba]
      exact hd)
  rw [← PowerSeries.maximalIdeal_eq_span_X]
  exact isAdicallyFormallySmooth_of_injective_kaehler_mapBaseChange p hinj

set_option backward.isDefEq.respectTransparency false in
private theorem isAdicallyFormallySmooth_of_formallySmooth
    {R : Type u} {A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FormallySmooth R A] (I : Ideal A) :
    IsAdicallyFormallySmooth I (algebraMap R A) := by
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  let : TopologicalSpace A := I.adicTopology
  let : IsTopologicalRing A := I.ringFilterBasis.isTopologicalRing
  let : IsLinearTopology A A := I.isLinearTopology
  apply (isFormallySmooth_iff_formallySmoothNAdic _ I rfl).mpr
  intro B _ J hJ f ψ hcomm _
  let : Algebra R B := f.toAlgebra
  let ψₐ : A →ₐ[R] B ⧸ J := ⟨ψ, fun r => RingHom.congr_fun hcomm r⟩
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_lift J ⟨2, hJ⟩ ψₐ
  exact ⟨g.toRingHom, congrArg AlgHom.toRingHom hg, g.comp_algebraMap⟩

open scoped TensorProduct in
private theorem geometricallyRegular_of_formallySmooth_essFiniteType
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [Algebra.EssFiniteType k A] [Algebra.FormallySmooth k A] :
    Algebra.IsGeometricallyRegular k A := by
  constructor
  intro K _ _ _
  have : IsNoetherianRing (K ⊗[k] A) := Algebra.EssFiniteType.isNoetherianRing K _
  rw [isRegularRing_iff]
  intro q _
  have : Algebra.FormallySmooth (K ⊗[k] A) (Localization.AtPrime q) :=
    Algebra.FormallySmooth.of_isLocalization q.primeCompl
  have : Algebra.FormallySmooth K (Localization.AtPrime q) :=
    Algebra.FormallySmooth.comp K (K ⊗[k] A) _
  exact isRegularLocalRing_of_isFormallySmooth_maximalIdeal (k := K)
    (isAdicallyFormallySmooth_of_formallySmooth (R := K)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)))

set_option synthInstance.maxHeartbeats 200000 in
-- instance synthesis for the algebra structures on quotients of `MvPolynomial (Fin 2) R` is heavy
set_option backward.isDefEq.respectTransparency false in
private theorem formallySmooth_quotient_X_pow_sub_C_sub_X
    {R : Type*} [CommRing R] (n : ℕ) (a : R) :
    Algebra.FormallySmooth R
      (MvPolynomial (Fin 2) R ⧸ Ideal.span
        {MvPolynomial.X 1 ^ n - MvPolynomial.C a - MvPolynomial.X 0}) := by
  let P := MvPolynomial (Fin 2) R
  let g : P := MvPolynomial.X 1 ^ n - MvPolynomial.C a - MvPolynomial.X 0
  let I : Ideal P := Ideal.span {g}
  let q := Ideal.Quotient.mkₐ R I
  let t : P →ₐ[R] P := MvPolynomial.aeval
    ![MvPolynomial.X 1 ^ n - MvPolynomial.C a, MvPolynomial.X 1]
  have ht : I ≤ RingHom.ker t := by
    rw [Ideal.span_le]
    rintro _ rfl
    simp [P, t, g]
  let s := Ideal.Quotient.liftₐ I t ht
  apply Stacks.Smoothing.formallySmooth_of_retraction q s
  apply Ideal.Quotient.algHom_ext
  have hg : q g = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hg' : q (MvPolynomial.X 1) ^ n - algebraMap R (P ⧸ I) a =
      q (MvPolynomial.X 0) := by
    simpa only [g, map_sub, map_pow,
      show q (MvPolynomial.C a) = algebraMap R (P ⧸ I) a from q.commutes a,
      sub_eq_zero] using hg
  ext i
  fin_cases i <;> simp [P, q, s, t, ← hg']
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_span_X_and_X_pow_sub_C_equiv_adjoinRoot
    {R : Type*} [CommRing R] (n : ℕ) (a : R) :
    Nonempty ((MvPolynomial (Fin 2) R ⧸ Ideal.span
      {(MvPolynomial.X 0 : MvPolynomial (Fin 2) R), MvPolynomial.X 1 ^ n - MvPolynomial.C a}) ≃ₐ[R]
      AdjoinRoot (Polynomial.X ^ n - Polynomial.C a)) := by
  let P := MvPolynomial (Fin 2) R
  let m : Ideal P := Ideal.span
    {MvPolynomial.X 0, MvPolynomial.X 1 ^ n - MvPolynomial.C a}
  let q := Ideal.Quotient.mkₐ R m
  let f := Polynomial.X ^ n - Polynomial.C a
  have hx : q (MvPolynomial.X 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hy : q (MvPolynomial.X 1) ^ n - algebraMap R (P ⧸ m) a = 0 := by
    have hq : q (MvPolynomial.X 1 ^ n - MvPolynomial.C a) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simpa only [map_sub, map_pow,
      show q (MvPolynomial.C a) = algebraMap R (P ⧸ m) a from q.commutes a] using hq
  let l := AdjoinRoot.liftAlgHom f (Algebra.ofId R (P ⧸ m)) (q (MvPolynomial.X 1))
    (by simpa [f] using hy)
  let t : P →ₐ[R] AdjoinRoot f := MvPolynomial.aeval ![0, AdjoinRoot.root f]
  have hroot : AdjoinRoot.root f ^ n - algebraMap R (AdjoinRoot f) a = 0 := by
    simpa [f] using AdjoinRoot.eval₂_root f
  have ht : m ≤ RingHom.ker t := by
    rw [Ideal.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · simp [P, t]
    · simpa [P, t] using hroot
  let r := Ideal.Quotient.liftₐ m t ht
  have hlroot : l (AdjoinRoot.root f) = q (MvPolynomial.X 1) :=
    AdjoinRoot.liftAlgHom_root _ _ _ _
  have hrq (z : P) : r (q z) = t z := rfl
  have htX (i : Fin 2) : t (MvPolynomial.X i) = ![0, AdjoinRoot.root f] i :=
    MvPolynomial.aeval_X _ _
  refine ⟨AlgEquiv.ofAlgHom r l ?_ ?_⟩
  · apply AdjoinRoot.algHom_ext
    change r (l (AdjoinRoot.root f)) = AdjoinRoot.root f
    rw [hlroot, hrq, htX]
    rfl
  · apply Ideal.Quotient.algHom_ext
    ext i
    change l (r (q (MvPolynomial.X i))) = q (MvPolynomial.X i)
    rw [hrq, htX]
    fin_cases i
    · simpa using hx.symm
    · exact hlroot

private theorem isPurelyInseparable_of_adjoin_eq_top_of_pow_mem
    {k E : Type*} [Field k] [CommRing E] [IsDomain E] [Algebra k E]
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP E p] {x : E}
    (hx : Algebra.adjoin k {x} = ⊤) (hp : x ^ p ∈ (algebraMap k E).range) :
    IsPurelyInseparable k E := by
  let S : Subalgebra k E :=
    { (algebraMap k E).range.comap (frobenius E p) with
      algebraMap_mem' := fun r => ⟨r ^ p, map_pow _ _ _⟩ }
  have hS : S = ⊤ := top_unique (hx ▸ Algebra.adjoin_le (by
    intro y hy
    rcases hy with rfl
    exact hp))
  apply (isPurelyInseparable_iff_pow_mem k p).mpr
  intro y
  have hy : y ∈ S := hS ▸ Algebra.mem_top
  change y ^ p ∈ (algebraMap k E).range at hy
  exact ⟨1, by simpa only [pow_one] using hy⟩

set_option backward.isDefEq.respectTransparency false in
private theorem exists_quotient_equiv_residueField_of_localization_surjective
    {R P A : Type*} [CommRing R] [CommRing P] [CommRing A]
    [Algebra R P] (m : Ideal P) [m.IsMaximal]
    [Algebra P A] [Algebra R A] [IsScalarTower R P A]
    [Algebra (Localization.AtPrime m) A] [IsScalarTower P (Localization.AtPrime m) A]
    [IsLocalRing A]
    (hsurj : Function.Surjective (algebraMap (Localization.AtPrime m) A)) :
    Nonempty ((P ⧸ m) ≃ₐ[R] IsLocalRing.ResidueField A) := by
  let B := Localization.AtPrime m
  have : IsLocalHom (algebraMap B A) := IsLocalHom.of_surjective _ hsurj
  have hPB : Function.Surjective (algebraMap P (IsLocalRing.ResidueField B)) := by
    have hm : (Ideal.under P (IsLocalRing.maximalIdeal B)).IsMaximal := by
      change (Ideal.under P (IsLocalRing.maximalIdeal (Localization.AtPrime m))).IsMaximal
      rw [Localization.AtPrime.under_maximalIdeal]
      infer_instance
    have hle : m ≤ Ideal.under P (IsLocalRing.maximalIdeal B) := by
      rw [Localization.AtPrime.under_maximalIdeal]
    have hs := IsLocalization.surjective_quotientMap_of_maximal_of_localization
      m.primeCompl B (J := m) (H := hle) hm
    intro b
    obtain ⟨z, hz⟩ := hs b
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨z, hz⟩
  have hPA : Function.Surjective (algebraMap P (IsLocalRing.ResidueField A)) := by
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨b, rfl⟩ := hsurj a
    obtain ⟨c, hc⟩ := hPB (IsLocalRing.residue B b)
    refine ⟨c, ?_⟩
    have hh := congrArg (IsLocalRing.ResidueField.map (algebraMap B A)) hc
    simpa only [IsScalarTower.algebraMap_apply P B (IsLocalRing.ResidueField B),
      show algebraMap B (IsLocalRing.ResidueField B) = IsLocalRing.residue B from rfl,
      IsLocalRing.ResidueField.map_residue,
      ← IsScalarTower.algebraMap_apply P B A,
      IsScalarTower.algebraMap_apply P A (IsLocalRing.ResidueField A),
      show algebraMap A (IsLocalRing.ResidueField A) = IsLocalRing.residue A from rfl] using hh
  have hker : m ≤ RingHom.ker (algebraMap P (IsLocalRing.ResidueField A)) := by
    intro c hc
    change IsLocalRing.residue A (algebraMap P A c) = 0
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    rw [IsScalarTower.algebraMap_apply P B A]
    apply IsLocalRing.map_maximalIdeal_le (algebraMap B A)
    apply Ideal.mem_map_of_mem
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hc
  let g := Ideal.Quotient.liftₐ m (IsScalarTower.toAlgHom R P (IsLocalRing.ResidueField A)) hker
  let : Field (P ⧸ m) := Ideal.Quotient.field m
  refine ⟨AlgEquiv.ofBijective g ⟨g.toRingHom.injective, ?_⟩⟩
  intro z
  obtain ⟨c, rfl⟩ := hPA z
  exact ⟨Ideal.Quotient.mk m c, rfl⟩

private theorem formallySmooth_quotient_map_of_isLocalization
    {R P : Type*} [CommRing R] [CommRing P] [Algebra R P]
    (M : Submonoid P) (B : Type*) [CommRing B] [Algebra P B]
    [Algebra R B] [IsScalarTower R P B] [IsLocalization M B]
    (I : Ideal P) [Algebra.FormallySmooth R (P ⧸ I)] :
    Algebra.FormallySmooth R (B ⧸ I.map (algebraMap P B)) := by
  have : Algebra.FormallySmooth (P ⧸ I) (B ⧸ I.map (algebraMap P B)) :=
    Algebra.FormallySmooth.of_isLocalization (Algebra.algebraMapSubmonoid (P ⧸ I) M)
  have : IsScalarTower R (P ⧸ I) (B ⧸ I.map (algebraMap P B)) :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := P ⧸ I)
      (A := B ⧸ I.map (algebraMap P B)) (by
        ext r
        change Ideal.Quotient.mk _ (algebraMap R B r) =
          Ideal.Quotient.mk _ (algebraMap P B (algebraMap R P r))
        rw [IsScalarTower.algebraMap_apply R P B])
  exact Algebra.FormallySmooth.comp R (P ⧸ I) _

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
-- Elaborating the compatible scalar actions on this localization and quotient is expensive.
private theorem formallySmooth_localized_polynomial_example
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (a : k)
    (ha : a ∉ Set.range (fun b : k => b ^ p)) :
    let P := MvPolynomial (Fin 2) k
    let m : Ideal P := Ideal.span
      {MvPolynomial.X 0, MvPolynomial.X 1 ^ p - MvPolynomial.C a}
    let g : P := MvPolynomial.X 1 ^ p - MvPolynomial.C a - MvPolynomial.X 0
    ∃ hm : m.IsPrime,
      letI : m.IsPrime := hm
      let B := Localization.AtPrime m
      let A := B ⧸ Ideal.span {algebraMap P B g}
      ∃ hlocal : IsLocalRing A,
        letI : IsLocalRing A := hlocal
        IsNoetherianRing A ∧
        Algebra.IsGeometricallyRegular k A ∧
        IsPurelyInseparable k (IsLocalRing.ResidueField A) ∧
        Algebra.FormallySmooth k A ∧
        @IsAdicallyFormallySmooth k A _ _ (IsLocalRing.maximalIdeal A) (algebraMap k A) := by
  let P := MvPolynomial (Fin 2) k
  let m : Ideal P := Ideal.span
    {MvPolynomial.X 0, MvPolynomial.X 1 ^ p - MvPolynomial.C a}
  let g : P := MvPolynomial.X 1 ^ p - MvPolynomial.C a - MvPolynomial.X 0
  let f := Polynomial.X ^ p - Polynomial.C a
  have : Fact (Irreducible f) := ⟨irreducible_X_pow_sub_C_of_not_isPow p a ha⟩
  obtain ⟨e⟩ := quotient_span_X_and_X_pow_sub_C_equiv_adjoinRoot p a
  have hm : m.IsMaximal := Ideal.Quotient.maximal_of_isField m
    (e.toRingEquiv.toMulEquiv.isField (Field.toIsField (AdjoinRoot f)))
  let : m.IsMaximal := hm
  refine ⟨hm.isPrime, ?_⟩
  let B := Localization.AtPrime m
  let I : Ideal P := Ideal.span {g}
  have hmap : I.map (algebraMap P B) = Ideal.span {algebraMap P B g} := by
    simp only [I, Ideal.map_span, Set.image_singleton]
  change ∃ hlocal : IsLocalRing (B ⧸ Ideal.span {algebraMap P B g}), _
  rw [← hmap]
  let A := B ⧸ I.map (algebraMap P B)
  have hg : g ∈ m := m.sub_mem
    (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  have hI : I.map (algebraMap P B) ≤ IsLocalRing.maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hg))
  have hne : I.map (algebraMap P B) ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal B).ne_top hI
  let : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr hne
  let : IsLocalRing A :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : Algebra.FormallySmooth k (P ⧸ I) := formallySmooth_quotient_X_pow_sub_C_sub_X p a
  have : Algebra.FormallySmooth k A :=
    formallySmooth_quotient_map_of_isLocalization (R := k) m.primeCompl B I
  have hadic := isAdicallyFormallySmooth_of_formallySmooth
    (R := k) (A := A) (IsLocalRing.maximalIdeal A)
  have hgeo : Algebra.IsGeometricallyRegular k A :=
    geometricallyRegular_of_formallySmooth_essFiniteType
  have : IsPurelyInseparable k (AdjoinRoot f) := by
    have : CharP (AdjoinRoot f) p :=
      charP_of_injective_algebraMap (algebraMap k (AdjoinRoot f)).injective p
    apply isPurelyInseparable_of_adjoin_eq_top_of_pow_mem
      (k := k) (E := AdjoinRoot f) (x := AdjoinRoot.root f) p AdjoinRoot.adjoinRoot_eq_top
    refine ⟨a, ?_⟩
    have hr := AdjoinRoot.eval₂_root f
    have hr' : AdjoinRoot.root f ^ p - algebraMap k (AdjoinRoot f) a = 0 := by
      simpa [f] using hr
    exact (sub_eq_zero.mp hr').symm
  have : IsPurelyInseparable k (P ⧸ m) := e.symm.isPurelyInseparable
  obtain ⟨er⟩ := exists_quotient_equiv_residueField_of_localization_surjective
    (R := k) (A := A) m (Ideal.Quotient.mk_surjective)
  exact ⟨inferInstance, inferInstance, hgeo, er.isPurelyInseparable, inferInstance, hadic⟩

/-- In characteristic `p`, the local ring
`k[x, y]_(x, y ^ p - a) / (y ^ p - a - x)` is geometrically regular over `k`, formally
smooth both algebraically and for its maximal-ideal-adic topology, and has purely inseparable
residue field. Closely relatedly, if `K` is the perfect closure of `𝔽ₚ(t)`, there is a map
`𝔽ₚ(s) → K[[x]]` sending `s` to `t + x` which is formally smooth for the `(x)`-adic topology.
For the latter map, `ds` and `dx` are the indicated bases of the Kähler differentials and the
map on differentials sends `ds` to `dx`. -/
@[stacks 07EM, ega "0 19.6.5.2" "existence of examples"]
public theorem formallySmooth_adic_examples_with_inseparable_residueField
    (p : ℕ) [Fact p.Prime] :
    (∀ (k : Type u) [Field k] [CharP k p] (a : k),
      a ∉ Set.range (fun b : k => b ^ p) →
      let P := MvPolynomial (Fin 2) k
      let m : Ideal P := Ideal.span
        {MvPolynomial.X 0, MvPolynomial.X 1 ^ p - MvPolynomial.C a}
      let g : P := MvPolynomial.X 1 ^ p - MvPolynomial.C a - MvPolynomial.X 0
      ∃ hm : m.IsPrime,
        letI : m.IsPrime := hm
        let B := Localization.AtPrime m
        let A := B ⧸ Ideal.span {algebraMap P B g}
        ∃ hlocal : IsLocalRing A,
          letI : IsLocalRing A := hlocal
          IsNoetherianRing A ∧
          Algebra.IsGeometricallyRegular k A ∧
          IsPurelyInseparable k (IsLocalRing.ResidueField A) ∧
          Algebra.FormallySmooth k A ∧
          let n := IsLocalRing.maximalIdeal A
          @IsAdicallyFormallySmooth k A _ _ n (algebraMap k A)) ∧
    (let k := RatFunc (ZMod p)
     let K := PerfectClosure k p
     letI : Algebra k K := (PerfectClosure.of k p).toAlgebra
     let A := PowerSeries K
     ∃ f : k →+* A,
       f RatFunc.X =
          PowerSeries.C (algebraMap k K RatFunc.X) + PowerSeries.X ∧
       letI : Algebra k A := f.toAlgebra
       letI : Algebra (ZMod p) A :=
         (f.comp (algebraMap (ZMod p) k)).toAlgebra
       letI : IsScalarTower (ZMod p) k A :=
         IsScalarTower.of_algebraMap_eq' rfl
       (∃ b : Module.Basis Unit k (KaehlerDifferential (ZMod p) k),
          b () = KaehlerDifferential.D (ZMod p) k RatFunc.X) ∧
       (∃ b : Module.Basis Unit A (KaehlerDifferential (ZMod p) A),
          b () = KaehlerDifferential.D (ZMod p) A PowerSeries.X) ∧
       KaehlerDifferential.map (ZMod p) (ZMod p) k A
           (KaehlerDifferential.D (ZMod p) k RatFunc.X) =
         KaehlerDifferential.D (ZMod p) A PowerSeries.X ∧
       let x : Ideal A := Ideal.span {PowerSeries.X}
       @IsAdicallyFormallySmooth k A _ _ x f) := by
  constructor
  · intro k _ _ a ha
    exact formallySmooth_localized_polynomial_example p k a ha
  · exact exists_adicallyFormallySmooth_ratFunc_to_powerSeries p

end

/-! ### Stacks Tag 07NQ -/

section

section

set_option maxRecDepth 4096

open scoped TensorProduct

open IsLocalRing
universe u v

private theorem geometricallyRegular_iff_formallySmoothNAdic_of_charP
    (k : Type u) (C : Type v) [Field k] [CommRing C] [Algebra k C]
    [IsNoetherianRing C] [IsLocalRing C] (p : ℕ) [Fact p.Prime] [CharP k p] :
    Algebra.IsGeometricallyRegular k C ↔
      RingHom.FormallySmoothNAdic.{max u v} (algebraMap k C) (maximalIdeal C) := by
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := ⟨rfl⟩
  let : TopologicalSpace C := (maximalIdeal C).adicTopology
  let : IsTopologicalRing C := (maximalIdeal C).ringFilterBasis.isTopologicalRing
  let : IsLinearTopology C C := (maximalIdeal C).isLinearTopology
  change Algebra.IsGeometricallyRegular k C ↔
    RingHom.FormallySmoothNAdic.{max u v} (algebraMap k C) (maximalIdeal C)
  rw [← isFormallySmooth_iff_formallySmoothNAdic
    (algebraMap k C) (maximalIdeal C) (by rfl)]
  exact ((formalSmoothness_maximalIdeal_characterizations k C).2 p).out 1 2

public theorem isGeometricallyRegular_of_isRegularRing_of_charZero (k : Type u) (C : Type v)
    [Field k] [CommRing C] [Algebra k C]
    [CharZero k] [IsRegularRing C] : Algebra.IsGeometricallyRegular k C := by
  refine ⟨fun K _ _ _ => ?_⟩
  revert K
  refine (Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
    k C).mpr ?_
  intro K _ _ _ _
  have hbij : Function.Bijective (algebraMap k K) :=
    ⟨(algebraMap k K).injective, IsPurelyInseparable.surjective_algebraMap_of_isSeparable k K⟩
  let e : K ≃ₐ[k] k := (AlgEquiv.ofBijective (Algebra.ofId k K) hbij).symm
  let e' : K ⊗[k] C ≃+* C :=
    ((Algebra.TensorProduct.congr e AlgEquiv.refl).trans
      (Algebra.TensorProduct.lid k C)).toRingEquiv
  exact IsRegularRing.of_ringEquiv e'.symm

private theorem geometricallyRegular_iff_formallySmoothNAdic_of_charZero
    (k : Type u) (C : Type v) [Field k] [CommRing C] [Algebra k C]
    [IsNoetherianRing C] [IsLocalRing C] [CharZero k] :
    Algebra.IsGeometricallyRegular k C ↔
      RingHom.FormallySmoothNAdic.{max u v} (algebraMap k C) (maximalIdeal C) := by
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := ⟨rfl⟩
  let : TopologicalSpace C := (maximalIdeal C).adicTopology
  let : IsTopologicalRing C := (maximalIdeal C).ringFilterBasis.isTopologicalRing
  let : IsLinearTopology C C := (maximalIdeal C).isLinearTopology
  change Algebra.IsGeometricallyRegular k C ↔
    RingHom.FormallySmoothNAdic.{max u v} (algebraMap k C) (maximalIdeal C)
  rw [← isFormallySmooth_iff_formallySmoothNAdic
    (algebraMap k C) (maximalIdeal C) (by rfl)]
  rw [← (formalSmoothness_maximalIdeal_characterizations k C).1]
  constructor
  · intro h
    have : IsRegularRing (k ⊗[k] C) := h.isRegularRing_tensorProduct k
    have : IsRegularRing C := IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.lid k C).toRingEquiv
    exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing C
  · intro h
    let : IsRegularLocalRing C := h
    have : IsRegularRing C := ((IsLocalRing.isRegularRing_tfae (R := C)).out 1 3).mp h
    exact isGeometricallyRegular_of_isRegularRing_of_charZero k C

private theorem formallySmoothNAdic_of_algEquiv.{t}
    {K C D : Type*} [CommRing K] [CommRing C] [CommRing D]
    [Algebra K C] [Algebra K D] [IsLocalRing C] [IsLocalRing D]
    (e : C ≃ₐ[K] D)
    (h : RingHom.FormallySmoothNAdic.{t}
      (algebraMap K C) (maximalIdeal C)) :
    RingHom.FormallySmoothNAdic.{t} (algebraMap K D) (maximalIdeal D) := by
  intro E _ J hJ a psi hcomm hk
  have hcomm' : (psi.comp e.toRingHom).comp (algebraMap K C) =
      (Ideal.Quotient.mk J).comp a := by
    ext r
    simpa using DFunLike.congr_fun hcomm r
  obtain ⟨n, hn, hk⟩ := hk
  have hk' : maximalIdeal C ^ n ≤ RingHom.ker (psi.comp e.toRingHom) := by
    intro x hx
    apply hk
    rw [← map_maximalIdeal_of_surjective e.toRingHom e.surjective, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨d, hd, hda⟩ := h E J hJ a (psi.comp e.toRingHom) hcomm' ⟨n, hn, hk'⟩
  refine ⟨d.comp e.symm.toRingHom, ?_, ?_⟩
  · ext x
    simpa using DFunLike.congr_fun hd (e.symm x)
  · ext r
    simpa using DFunLike.congr_fun hda r

private theorem lift_of_annihilated {R : Type*} {S : Type v} {E : Type (max u v)}
    [CommRing R] [CommRing S] [CommRing E] [IsNoetherianRing S]
    (f : R →+* S) (hflat : letI := f.toAlgebra; Module.Flat R S)
    (I : Ideal R) (n : Ideal S)
    (H : ∀ (T : Type (max u v)) [CommRing T] (K : Ideal T), K ^ 2 = ⊥ →
      ∀ (α : R →+* T), I ≤ RingHom.ker α → ∀ (β : S →+* T ⧸ K),
        β.comp f = (Ideal.Quotient.mk K).comp α →
        (∃ j : ℕ, 1 ≤ j ∧ n ^ j ≤ RingHom.ker β) →
        ∃ γ : S →+* T, (Ideal.Quotient.mk K).comp γ = β ∧ γ.comp f = α)
    (L : Ideal E) (hL : L ^ 2 = ⊥) (a : R →+* E) (haL : I.map a * L = ⊥)
    (φ : S →+* E ⧸ L) (hcomm : φ.comp f = (Ideal.Quotient.mk L).comp a)
    (m : ℕ) (hm : 1 ≤ m) (hφ : n ^ m ≤ RingHom.ker φ) :
    ∃ g : S →+* E, (Ideal.Quotient.mk L).comp g = φ ∧ g.comp f = a := by
  classical
  let D : Subring (E × S) :=
    RingHom.eqLocus ((Ideal.Quotient.mk L).comp (RingHom.fst E S)) (φ.comp (RingHom.snd E S))
  have memD : ∀ x : E × S, x ∈ D ↔ Ideal.Quotient.mk L x.1 = φ x.2 := fun x => Iff.rfl
  let π : D →+* S := (RingHom.snd E S).comp D.subtype
  let π₁ : D →+* E := (RingHom.fst E S).comp D.subtype
  let ρ : R →+* D := RingHom.codRestrict (a.prod f) D
    (fun r => (DFunLike.congr_fun hcomm r).symm)
  have hπρ : π.comp ρ = f := rfl
  have hπ : Function.Surjective π := by
    intro s
    obtain ⟨e, he⟩ := Ideal.Quotient.mk_surjective (φ s)
    exact ⟨⟨(e, s), he⟩, rfl⟩
  have hzeroD : ∀ t : S, t ∈ n ^ m → (((0 : E), t) ∈ D) := by
    intro t ht
    rw [memD, map_zero]
    exact (RingHom.mem_ker.mp (hφ ht)).symm
  have hkerL : ∀ x : D, x ∈ RingHom.ker π → x.1.1 ∈ L := by
    intro x hx
    have h2 : x.1.2 = 0 := hx
    have := (memD x.1).mp x.2
    rw [h2, map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  have hflatD : RingHom.ker π ⊓ I.map ρ = ⊥ := by
    let : Algebra R S := f.toAlgebra
    let : Algebra R D := ρ.toAlgebra
    have : Module.Flat R S := hflat
    let πₗ : D →ₗ[R] S :=
      { toFun := π
        map_add' := π.map_add
        map_smul' := fun r x => by
          change π (ρ r * x) = f r * π x
          rw [map_mul]; rfl }
    have key := LinearMap.ker_inf_smul_top_eq_smul_of_flat I πₗ hπ
    have hzero : I • LinearMap.ker πₗ = ⊥ := by
      rw [eq_bot_iff]
      apply Submodule.smul_le.mpr
      intro i hi x hx
      have hx1 : x.1.1 ∈ L := hkerL x hx
      have hx2 : x.1.2 = 0 := hx
      change ρ i * x ∈ (⊥ : Submodule R D)
      rw [Submodule.mem_bot]
      apply Subtype.ext
      apply Prod.ext
      · change a i * x.1.1 = 0
        have : a i * x.1.1 ∈ I.map a * L :=
          Ideal.mul_mem_mul (Ideal.mem_map_of_mem a hi) hx1
        rw [haL] at this
        exact this
      · change f i * x.1.2 = 0
        rw [hx2, mul_zero]
    rw [hzero, Ideal.smul_top_eq_map] at key
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ LinearMap.ker πₗ ⊓ (I.map (algebraMap R D)).restrictScalars R := ⟨hx.1, hx.2⟩
    rw [key] at this
    exact this
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul n (I.map f : Submodule S S)
  set j := m + c with hj
  have hAR : n ^ j ⊓ I.map f ≤ n ^ m * I.map f := by
    have h := hc j (by omega)
    have hjc : j - c = m := by omega
    rw [hjc] at h
    intro x hx
    have hx' : x ∈ n ^ j • (⊤ : Submodule S S) ⊓ (I.map f : Submodule S S) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact hx
    rw [h] at hx'
    exact Submodule.smul_mono le_rfl inf_le_right hx'
  have hgen : n ^ m * I.map f ≤ (I.map ρ ⊓ RingHom.ker π₁).map π := by
    rw [Ideal.mul_le]
    intro t ht w hw
    have hw' : w ∈ (I.map ρ).map π := by rwa [Ideal.map_map, hπρ]
    obtain ⟨y₀, hy₀, rfl⟩ := (Ideal.mem_map_iff_of_surjective π hπ).mp hw'
    let t' : D := ⟨(0, t), hzeroD t ht⟩
    have : π (t' * y₀) = t * π y₀ := by rw [map_mul]; rfl
    rw [← this]
    refine Ideal.mem_map_of_mem π ⟨Ideal.mul_mem_left _ _ hy₀, ?_⟩
    change (0 : E) * y₀.1.1 = 0
    rw [zero_mul]
  let N : Ideal D := RingHom.ker π₁ ⊓ (n ^ j).comap π
  let M : Ideal D := I.map ρ ⊔ N
  have hdisj : RingHom.ker π ⊓ M = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hxM⟩
    obtain ⟨y, hy, u, hu, rfl⟩ := Submodule.mem_sup.mp hxM
    have hπy : π y ∈ n ^ j ⊓ I.map f := by
      constructor
      · have h0 : π y + π u = 0 := by rw [← map_add]; exact hx
        rw [eq_neg_of_add_eq_zero_left h0]
        exact neg_mem hu.2
      · have := Ideal.mem_map_of_mem π hy
        rwa [Ideal.map_map, hπρ] at this
    obtain ⟨y', ⟨hy'I, hy'1⟩, hy'π⟩ :=
      (Ideal.mem_map_iff_of_surjective π hπ).mp (hgen (hAR hπy))
    have hyy' : y = y' := by
      have hmem : y - y' ∈ RingHom.ker π ⊓ I.map ρ :=
        ⟨by change π (y - y') = 0; rw [map_sub, hy'π, sub_self], sub_mem hy hy'I⟩
      rw [hflatD] at hmem
      exact sub_eq_zero.mp hmem
    subst hyy'
    rw [Submodule.mem_bot]
    apply Subtype.ext
    apply Prod.ext
    · change y.1.1 + u.1.1 = 0
      have h1 : y.1.1 = 0 := hy'1
      have h2 : u.1.1 = 0 := hu.1
      rw [h1, h2, add_zero]
    · exact hx
  let K : Ideal (D ⧸ M) := (RingHom.ker π).map (Ideal.Quotient.mk M)
  have hK : K ^ 2 = ⊥ := by
    have hker : RingHom.ker π ^ 2 = ⊥ := by
      rw [eq_bot_iff, pow_two, Ideal.mul_le]
      intro x hx y hy
      rw [Submodule.mem_bot]
      apply Subtype.ext
      apply Prod.ext
      · change x.1.1 * y.1.1 = 0
        have : x.1.1 * y.1.1 ∈ L ^ 2 := by
          rw [pow_two]; exact Ideal.mul_mem_mul (hkerL x hx) (hkerL y hy)
        rw [hL] at this
        exact this
      · change x.1.2 * y.1.2 = 0
        have : x.1.2 = 0 := hx
        rw [this, zero_mul]
    change ((RingHom.ker π).map (Ideal.Quotient.mk M)) ^ 2 = ⊥
    rw [← Ideal.map_pow, hker, Ideal.map_bot]
  let α : R →+* D ⧸ M := (Ideal.Quotient.mk M).comp ρ
  have hαI : I ≤ RingHom.ker α := by
    intro i hi
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem ρ hi))
  let β : S →+* (D ⧸ M) ⧸ K := π.liftOfSurjective hπ
    ⟨(Ideal.Quotient.mk K).comp (Ideal.Quotient.mk M), fun x hx => by
      rw [RingHom.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx)⟩
  have hβ : ∀ x : D, β (π x) = Ideal.Quotient.mk K (Ideal.Quotient.mk M x) := fun x =>
    RingHom.liftOfSurjective_comp_apply π hπ _ x
  have hβf : β.comp f = (Ideal.Quotient.mk K).comp α := by
    ext r
    exact hβ (ρ r)
  have hβn : n ^ j ≤ RingHom.ker β := by
    intro t ht
    have htm : t ∈ n ^ m := Ideal.pow_le_pow_right (by omega) ht
    let t' : D := ⟨(0, t), hzeroD t htm⟩
    have ht'M : t' ∈ M := Ideal.mem_sup_right ⟨rfl, ht⟩
    rw [RingHom.mem_ker]
    change β (π t') = 0
    rw [hβ, Ideal.Quotient.eq_zero_iff_mem.mpr ht'M, map_zero]
  obtain ⟨γ, hγK, hγf⟩ := H (D ⧸ M) K hK α hαI β hβf ⟨j, by omega, hβn⟩
  obtain ⟨s, hsπ, hsM⟩ := RingHom.section_of_disjoint π hπ M hdisj γ (fun e => by
    rw [← hβ e, ← hγK]; rfl)
  have hsf : ∀ r, s (f r) = ρ r := by
    intro r
    have hmem : s (f r) - ρ r ∈ RingHom.ker π ⊓ M := by
      constructor
      · change π (s (f r) - ρ r) = 0
        rw [map_sub, hsπ]
        exact sub_self _
      · apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub, hsM, ← RingHom.comp_apply γ f, hγf]
        exact sub_self _
    rw [hdisj] at hmem
    exact sub_eq_zero.mp hmem
  refine ⟨π₁.comp s, ?_, ?_⟩
  · ext t
    change Ideal.Quotient.mk L (s t).1.1 = φ t
    rw [(memD (s t).1).mp (s t).2]
    exact congrArg φ (hsπ t)
  · ext r
    change (s (f r)).1.1 = a r
    rw [hsf r]
    rfl

private theorem lift_through_specialFiber
    {A : Type u} {B : Type v}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hbar : letI : Algebra A B := f.toAlgebra
      RingHom.FormallySmoothNAdic.{max u v}
        (algebraMap (ResidueField A) (ResidueField A ⊗[A] B))
        (maximalIdeal (ResidueField A ⊗[A] B)))
    (T : Type (max u v)) [CommRing T] (K : Ideal T) (hK : K ^ 2 = ⊥)
    (α : A →+* T) (hα : maximalIdeal A ≤ RingHom.ker α) (β : B →+* T ⧸ K)
    (hβf : β.comp f = (Ideal.Quotient.mk K).comp α)
    (hβn : ∃ j : ℕ, 1 ≤ j ∧ maximalIdeal B ^ j ≤ RingHom.ker β) :
    ∃ γ : B →+* T, (Ideal.Quotient.mk K).comp γ = β ∧ γ.comp f = α := by
  let : Algebra A B := f.toAlgebra
  let k := ResidueField A
  let Bbar := k ⊗[A] B
  let incl : B →+* Bbar := Algebra.TensorProduct.includeRight.toRingHom
  have hincl : Function.Surjective incl :=
    TensorProduct.mk_surjective A B k residue_surjective
  have hker : RingHom.ker incl ≤ RingHom.ker β := by
    intro b hb
    have hb' : b ∈ (maximalIdeal A).map (algebraMap A B) := by
      let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A)
      have h0 : e (Ideal.Quotient.mk _ b) = 0 := by
        rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
        exact hb
      exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h0)
    have hle : (maximalIdeal A).map f ≤ RingHom.ker β := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      change β (f x) = 0
      rw [← RingHom.comp_apply, hβf, RingHom.comp_apply, RingHom.mem_ker.mp (hα hx), map_zero]
    exact hle hb'
  let βbar : Bbar →+* T ⧸ K := incl.liftOfSurjective hincl ⟨β, hker⟩
  have hβbar : ∀ b, βbar (incl b) = β b := fun b =>
    RingHom.liftOfSurjective_comp_apply incl hincl ⟨β, hker⟩ b
  let αbar : k →+* T := Ideal.Quotient.lift (maximalIdeal A) α hα
  have halg : ∀ x : A, algebraMap k Bbar (residue A x) = incl (f x) := by
    intro x
    change (residue A x) ⊗ₜ[A] (1 : B) = (1 : k) ⊗ₜ[A] (algebraMap A B x)
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  have hcomm : βbar.comp (algebraMap k Bbar) = (Ideal.Quotient.mk K).comp αbar := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    change βbar (algebraMap k Bbar (residue A x)) = Ideal.Quotient.mk K (α x)
    rw [halg, hβbar, ← RingHom.comp_apply, hβf, RingHom.comp_apply]
  obtain ⟨j, hj, hjle⟩ := hβn
  have hpow : maximalIdeal Bbar ^ j ≤ RingHom.ker βbar := by
    rw [← map_maximalIdeal_of_surjective incl hincl, ← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro b hb
    change βbar (incl b) = 0
    rw [hβbar]
    exact hjle hb
  obtain ⟨γbar, hγK, hγk⟩ := hbar T K hK αbar βbar hcomm ⟨j, hj, hpow⟩
  refine ⟨γbar.comp incl, ?_, ?_⟩
  · ext b
    change Ideal.Quotient.mk K (γbar (incl b)) = β b
    rw [← hβbar, ← hγK]
    rfl
  · ext x
    change γbar (incl (f x)) = α x
    rw [← halg, ← RingHom.comp_apply γbar, hγk]
    rfl

private theorem formallySmoothNAdic_of_flat_of_specialFiber
    {A : Type u} {B : Type v}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hflat : letI : Algebra A B := f.toAlgebra; Module.Flat A B)
    (hbar : letI : Algebra A B := f.toAlgebra
      RingHom.FormallySmoothNAdic.{max u v}
        (algebraMap (ResidueField A) (ResidueField A ⊗[A] B))
        (maximalIdeal (ResidueField A ⊗[A] B))) :
    RingHom.FormallySmoothNAdic.{max u v} f (maximalIdeal B) := by
  let I := maximalIdeal A
  let n := maximalIdeal B
  have H : ∀ (T : Type (max u v)) [CommRing T] (K : Ideal T), K ^ 2 = ⊥ →
      ∀ (α : A →+* T), I ≤ RingHom.ker α → ∀ (β : B →+* T ⧸ K),
        β.comp f = (Ideal.Quotient.mk K).comp α →
        (∃ j : ℕ, 1 ≤ j ∧ n ^ j ≤ RingHom.ker β) →
        ∃ γ : B →+* T, (Ideal.Quotient.mk K).comp γ = β ∧ γ.comp f = α :=
    fun T _ K hK α hα β hβf hβn => lift_through_specialFiber f hbar T K hK α hα β hβf hβn
  have step : ∀ t : ℕ, ∀ (E : Type (max u v)) [CommRing E] (L : Ideal E), L ^ 2 = ⊥ →
      ∀ (a : A →+* E) (φ : B →+* E ⧸ L), φ.comp f = (Ideal.Quotient.mk L).comp a →
        (∃ m : ℕ, 1 ≤ m ∧ n ^ m ≤ RingHom.ker φ) → (I.map a) ^ (t + 1) * L = ⊥ →
        ∃ g : B →+* E, (Ideal.Quotient.mk L).comp g = φ ∧ g.comp f = a := by
    intro t
    induction t with
    | zero =>
      intro E _ L hL a φ hcomm ⟨m, hm, hφ⟩ hann
      rw [zero_add, pow_one] at hann
      exact lift_of_annihilated.{u} f hflat I n H L hL a hann φ hcomm m hm hφ
    | succ t ih =>
      intro E _ L hL a φ hcomm ⟨m, hm, hφ⟩ hann
      let L' : Ideal E := (I.map a) ^ (t + 1) * L
      have hL'L : L' ≤ L := Ideal.mul_le_right
      have hL'2 : L' ^ 2 = ⊥ := eq_bot_iff.mpr (hL ▸ Ideal.pow_right_mono hL'L 2)
      have hIL' : I.map a * L' = ⊥ := by
        rw [← hann, ← mul_assoc, ← pow_succ']
      let L₁ : Ideal (E ⧸ L') := L.map (Ideal.Quotient.mk L')
      let eq := DoubleQuot.quotQuotEquivQuotOfLE hL'L
      have heq : ∀ x : E, eq (Ideal.Quotient.mk L₁ (Ideal.Quotient.mk L' x)) =
          Ideal.Quotient.mk L x := fun x => DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk x hL'L
      let a' : A →+* E ⧸ L' := (Ideal.Quotient.mk L').comp a
      let φ' : B →+* (E ⧸ L') ⧸ L₁ := eq.symm.toRingHom.comp φ
      have hL₁ : L₁ ^ 2 = ⊥ := by
        change (L.map (Ideal.Quotient.mk L')) ^ 2 = ⊥
        rw [← Ideal.map_pow, hL, Ideal.map_bot]
      have hcomm' : φ'.comp f = (Ideal.Quotient.mk L₁).comp a' := by
        ext r
        change eq.symm (φ (f r)) = Ideal.Quotient.mk L₁ (Ideal.Quotient.mk L' (a r))
        rw [eq.symm_apply_eq, heq, ← RingHom.comp_apply, hcomm, RingHom.comp_apply]
      have hφ' : n ^ m ≤ RingHom.ker φ' := by
        intro x hx
        change eq.symm (φ x) = 0
        rw [RingHom.mem_ker.mp (hφ hx), map_zero]
      have hann' : (I.map a') ^ (t + 1) * L₁ = ⊥ := by
        change (I.map ((Ideal.Quotient.mk L').comp a)) ^ (t + 1) *
          L.map (Ideal.Quotient.mk L') = ⊥
        rw [← Ideal.map_map, ← Ideal.map_pow, ← Ideal.map_mul]
        exact Ideal.map_quotient_self L'
      obtain ⟨g', hg'K, hg'f⟩ := ih (E ⧸ L') L₁ hL₁ a' φ' hcomm' ⟨m, hm, hφ'⟩ hann'
      have hg'n : n ^ (m + m) ≤ RingHom.ker g' := by
        have h1 : n ^ m ≤ L₁.comap g' := by
          intro x hx
          rw [Ideal.mem_comap]
          apply Ideal.Quotient.eq_zero_iff_mem.mp
          change ((Ideal.Quotient.mk L₁).comp g') x = 0
          rw [hg'K]
          exact hφ' hx
        rw [pow_add, Ideal.mul_le]
        intro x hx y hy
        rw [RingHom.mem_ker, map_mul]
        have : g' x * g' y ∈ L₁ ^ 2 := by
          rw [pow_two]; exact Ideal.mul_mem_mul (h1 hx) (h1 hy)
        rw [hL₁] at this
        exact this
      obtain ⟨g, hgK, hgf⟩ := lift_of_annihilated.{u} f hflat I n H L' hL'2 a hIL' g' hg'f
        (m + m) (by omega) hg'n
      refine ⟨g, ?_, hgf⟩
      ext x
      change Ideal.Quotient.mk L (g x) = φ x
      rw [← heq, ← RingHom.comp_apply (Ideal.Quotient.mk L'), hgK]
      change eq ((Ideal.Quotient.mk L₁).comp g' x) = φ x
      rw [hg'K]
      exact eq.apply_symm_apply (φ x)
  intro E _ J hJ a ψ hcomm ⟨m, hm, hk⟩
  have hIm : (I ^ m).map a ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change ((Ideal.Quotient.mk J).comp a) x = 0
    rw [← hcomm]
    apply hk
    have : (I ^ m).map f ≤ n ^ m := by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono (map_maximalIdeal_le f) m
    exact this (Ideal.mem_map_of_mem f hx)
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  apply step t E J hJ a ψ hcomm ⟨t + 1, hm, hk⟩
  rw [eq_bot_iff, ← hJ, pow_two, ← Ideal.map_pow]
  exact Ideal.mul_mono_left hIm

/-- Let `f : A → B` be a local homomorphism of Noetherian local rings, let
`k` be the residue field of `A`, and let `B̄ = k ⊗[A] B` be the special
fibre. The following are equivalent:

1. `f` is flat and `B̄` is geometrically regular over `k`;
2. `f` is flat and `k → B̄` is formally smooth for the maximal-ideal-adic
   topology;
3. `f` is formally smooth for the maximal-ideal-adic topology on `B`. -/
@[stacks 07NQ,
  ega "0 19.0.2" "I",
  ega "0 19.7.1" "more general",
  sga "1 III 1.7" "Noetherian local rings", sga "1 III 1.3" "more general"]
public theorem flat_geometricallyRegular_specialFiber_formallySmooth_tfae
    {A : Type u} {B : Type v}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] :
    letI : Algebra A B := f.toAlgebra
    let k := ResidueField A
    let Bbar := k ⊗[A] B
    List.TFAE [
      Module.Flat A B ∧ Algebra.IsGeometricallyRegular k Bbar,
      Module.Flat A B ∧
        RingHom.FormallySmoothNAdic.{max u v}
          (algebraMap k Bbar) (maximalIdeal Bbar),
      RingHom.FormallySmoothNAdic.{max u v} f (maximalIdeal B)] := by
  let : Algebra A B := f.toAlgebra
  let k := ResidueField A
  let Bbar := k ⊗[A] B
  let : IsNoetherianRing Bbar := isNoetherianRing_of_surjective B Bbar
    Algebra.TensorProduct.includeRight.toRingHom
    (TensorProduct.mk_surjective A B k residue_surjective)
  tfae_have 1 ↔ 2 := by
    obtain hk | ⟨p, hp, hkp⟩ := CharP.exists' k
    · let : CharZero k := hk
      exact and_congr_right fun _ ↦
        geometricallyRegular_iff_formallySmoothNAdic_of_charZero k Bbar
    · let := hp
      let := hkp
      exact and_congr_right fun _ =>
        geometricallyRegular_iff_formallySmoothNAdic_of_charP k Bbar p
  tfae_have 2 → 3 := fun h => formallySmoothNAdic_of_flat_of_specialFiber f h.1 h.2
  tfae_have 3 → 2 := by
    intro h
    refine ⟨flat_of_isFormallySmooth_maximalIdeal_adic f h, ?_⟩
    have hb := RingHom.FormallySmoothNAdic.baseChange
      (R' := k) (maximalIdeal B) h
    let : Algebra k (B ⊗[A] k) := Algebra.TensorProduct.rightAlgebra
    let e : (B ⊗[A] k) ≃ₐ[k] Bbar :=
      { (Algebra.TensorProduct.comm A B k).toRingEquiv with
        commutes' := by intro r; rfl }
    let : Nontrivial (B ⊗[A] k) := Function.Injective.nontrivial e.symm.injective
    let : IsLocalRing (B ⊗[A] k) :=
      IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
    apply formallySmoothNAdic_of_algEquiv e
    rw [← map_maximalIdeal_of_surjective
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] k)
      (by
        intro x
        obtain ⟨b, hb⟩ := (TensorProduct.mk_surjective A B k residue_surjective) (e x)
        refine ⟨b, e.injective ?_⟩
        exact hb)]
    exact hb
  tfae_finish

end

end

/-! ### Stacks Tag 07NR -/

section

section

set_option maxRecDepth 4096

open IsLocalRing
open scoped TensorProduct

universe u v w

/-- The dimension of a quotient by an initial part of a parameter system. -/
private theorem spanFinrank_quotient_add_length {S : Type*} [CommRing S]
    [IsRegularLocalRing S] (xs zs : List S)
    (hgen : Ideal.ofList (xs ++ zs) = maximalIdeal S)
    (hlen : (xs ++ zs).length = (maximalIdeal S).spanFinrank) :
    ∃ (_ : IsRegularLocalRing (S ⧸ Ideal.ofList xs)),
      (maximalIdeal (S ⧸ Ideal.ofList xs)).spanFinrank + xs.length =
        (maximalIdeal S).spanFinrank := by
  have h :=
    ((IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      S).1 (xs ++ zs) hgen hlen).2 xs.length (by simp)
  rw [List.take_left] at h
  have := h.1
  refine ⟨h.1, ?_⟩
  have hd := h.2
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal,
    ← IsRegularLocalRing.spanFinrank_maximalIdeal] at hd
  exact_mod_cast hd

/-- Lifting a minimal parameter system from a quotient complements the parameters killed
by the quotient. -/
@[ega "IV 19.7.3" "J + R = m"]
private theorem ofList_append_lift_eq_maximalIdeal {S : Type*} [CommRing S]
    [IsLocalRing S] (xs us : List S) [IsLocalRing (S ⧸ Ideal.ofList xs)]
    (hgen : Ideal.ofList (us.map (Ideal.Quotient.mk (Ideal.ofList xs))) =
      maximalIdeal (S ⧸ Ideal.ofList xs)) :
    Ideal.ofList (xs ++ us) = maximalIdeal S := by
  have : IsLocalHom (Ideal.Quotient.mk (Ideal.ofList xs)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have h := congrArg (Ideal.comap (Ideal.Quotient.mk (Ideal.ofList xs))) hgen
  rw [← Ideal.map_ofList, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, IsLocalRing.maximalIdeal_comap] at h
  simpa [Ideal.ofList_append, sup_comm] using h

/-- A regular presentation can be quotiented so that its closed fibre is a specified
regular quotient, while retaining flatness over the parameter ring. -/
private theorem exists_flat_quotient {R S B : Type*}
    [CommRing R] [IsRegularLocalRing R] [CommRing S] [IsRegularLocalRing S]
    [CommRing B] [IsRegularLocalRing B]
    (g : R →+* S) [IsLocalHom g] (q : S →+* B) (hq : Function.Surjective q)
    (xs : List R) (zs : List S)
    (hxs : Ideal.ofList xs = maximalIdeal R)
    (hxlen : xs.length = (maximalIdeal R).spanFinrank)
    (hgen : Ideal.ofList (xs.map g ++ zs) = maximalIdeal S)
    (hlen : (xs.map g ++ zs).length = (maximalIdeal S).spanFinrank)
    (hkill : (maximalIdeal R).map g ≤ RingHom.ker q) :
    ∃ J : Ideal S, J ≤ RingHom.ker q ∧ IsRegularLocalRing (S ⧸ J) ∧
      ((Ideal.Quotient.mk J).comp g).Flat ∧
      J ⊔ (maximalIdeal R).map g = RingHom.ker q := by
  classical
  let ts := xs.map g
  let I := Ideal.ofList ts
  have hI : I = (maximalIdeal R).map g := by rw [← hxs, Ideal.map_ofList]
  obtain ⟨hF, hdim⟩ := spanFinrank_quotient_add_length ts zs hgen hlen
  let π := Ideal.Quotient.mk I
  let qF : (S ⧸ I) →+* B := Ideal.Quotient.lift I q (hI ▸ hkill)
  have hqF : Function.Surjective qF := by
    intro b
    obtain ⟨s, rfl⟩ := hq b
    exact ⟨π s, rfl⟩
  have hreg : IsRegularLocalRing ((S ⧸ I) ⧸ RingHom.ker qF) :=
    IsRegularLocalRing.of_ringEquiv (RingHom.quotientKerEquivOfSurjective hqF).symm
  obtain ⟨ws, hwgen, hwlen, n, hn, hwn, _⟩ :=
    IsRegularLocalRing.exists_ofList_eq_maximalIdeal_length_eq_spanFinrank_and_ofList_take_eq
      (RingHom.ker qF) hreg
  let us := ws.map (Function.surjInv (Ideal.Quotient.mk_surjective (I := I)))
  have hus : us.map π = ws := by
    simp only [us, List.map_map]
    exact List.map_id'' (Function.surjInv_eq Ideal.Quotient.mk_surjective) ws
  have huser : Ideal.ofList (ts ++ us) = maximalIdeal S :=
    ofList_append_lift_eq_maximalIdeal ts us (by rw [hus]; exact hwgen)
  have huslen : (ts ++ us).length = (maximalIdeal S).spanFinrank := by
    simpa [us, List.length_append, hwlen, add_comm] using hdim
  let vs := us.take n
  let rest := ts ++ us.drop n
  have hperm : (vs ++ rest).Perm (ts ++ us) := by
    dsimp only [vs, rest]
    rw [← List.append_assoc]
    simpa [List.append_assoc] using
      (show (us.take n ++ ts).Perm (ts ++ us.take n) from List.perm_append_comm).append_right
        (us.drop n)
  have hvgen : Ideal.ofList (vs ++ rest) = maximalIdeal S := by
    rw [← huser]
    exact congrArg Ideal.span (Set.ext fun x => hperm.mem_iff)
  have hvlen : (vs ++ rest).length = (maximalIdeal S).spanFinrank :=
    hperm.length_eq.trans huslen
  let J := Ideal.ofList vs
  obtain ⟨hT, hTdim⟩ := spanFinrank_quotient_add_length vs rest hvgen hvlen
  have hJI : J ⊔ I = RingHom.ker q := by
    have hm : J.map π = RingHom.ker qF := by
      rw [Ideal.map_ofList, show vs.map π = ws.take n by rw [List.map_take, hus], hwn]
    have hh := congrArg (Ideal.comap π) hm
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hh
    exact hh
  have hJq : J ≤ RingHom.ker q := hJI ▸ le_sup_left
  let πJ := Ideal.Quotient.mk J
  have : IsLocalHom πJ := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let g' := πJ.comp g
  let : Algebra R (S ⧸ J) := g'.toAlgebra
  have : IsLocalHom (algebraMap R (S ⧸ J)) := RingHom.isLocalHom_comp πJ g
  have hrest : Ideal.ofList (rest.map πJ) = maximalIdeal (S ⧸ J) := by
    rw [← map_maximalIdeal_of_surjective πJ Ideal.Quotient.mk_surjective, ← hvgen,
      Ideal.ofList_append, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq,
      Ideal.map_ofList]
  have hrestlen : (rest.map πJ).length = (maximalIdeal (S ⧸ J)).spanFinrank := by
    simp only [List.length_append] at hvlen
    simp only [List.length_map]
    change (maximalIdeal (S ⧸ J)).spanFinrank + vs.length =
      (maximalIdeal S).spanFinrank at hTdim
    omega
  have hr :=
    ((IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      (S ⧸ J)).1 _ hrest hrestlen).1.toIsWeaklyRegular
  have hflat : Module.Flat R (S ⧸ J) := by
    apply Module.Flat.of_ofList_eq_maximalIdeal_of_isWeaklyRegular_map (S ⧸ J) (S ⧸ J)
      xs hxs hxlen
    have hh := (RingTheory.Sequence.isWeaklyRegular_append_iff (S ⧸ J)
      (ts.map πJ) ((us.drop n).map πJ)).mp (by simpa [rest] using hr)
    simpa only [ts, List.map_map, RingHom.algebraMap_toAlgebra, g', RingHom.coe_comp]
      using hh.1
  exact ⟨J, hJq, hT, hflat, by rwa [hI] at hJI⟩

/-- A quotient with the kernel prescribed by base change represents the tensor product. -/
private theorem nonempty_tensorProduct_equiv_of_ker
    {R K T B : Type*} [CommRing R] [CommRing K] [CommRing T] [CommRing B]
    [Algebra R K] [Algebra R T] [Algebra R B] [Algebra K B] [IsScalarTower R K B]
    (hr : Function.Surjective (algebraMap R K))
    (q : T →ₐ[R] B) (hq : Function.Surjective q)
    (hker : RingHom.ker q = (RingHom.ker (algebraMap R K)).map (algebraMap R T)) :
    Nonempty ((K ⊗[R] T) ≃ₐ[K] B) := by
  let φ : (K ⊗[R] T) →ₐ[K] B := AlgHom.liftEquiv R K T B q
  let i : T →ₐ[R] K ⊗[R] T := Algebra.TensorProduct.includeRight
  have hi : Function.Surjective i := Algebra.TensorProduct.includeRight_surjective T hr
  have hqi : RingHom.ker q ≤ RingHom.ker i := by
    rw [hker, Ideal.map_le_iff_le_comap]
    intro r hr
    change i (algebraMap R T r) = 0
    rw [i.commutes, IsScalarTower.algebraMap_apply R K (K ⊗[R] T), hr, map_zero]
  let ψ : B →+* K ⊗[R] T := q.toRingHom.liftOfSurjective hq ⟨i.toRingHom, hqi⟩
  have hψ : ∀ t, ψ (q t) = i t :=
    q.toRingHom.liftOfSurjective_comp_apply hq ⟨i.toRingHom, hqi⟩
  have hφ : ∀ t, φ (i t) = q t := fun t => by
    change (AlgHom.liftEquiv R K T B q) (1 ⊗ₜ[R] t) = q t
    simp
  refine ⟨AlgEquiv.ofBijective φ ⟨?_, ?_⟩⟩
  · have hleft : Function.LeftInverse ψ φ := by
      intro z
      obtain ⟨t, rfl⟩ := hi z
      rw [hφ, hψ]
    exact hleft.injective
  · intro b
    obtain ⟨t, rfl⟩ := hq b
    exact ⟨i t, hφ t⟩

/-- Flatness and formal smoothness of the special fibre imply formal smoothness of a
local algebra. -/
private theorem formallySmoothNAdic_of_flat_specialFiber
    {A : Type u} {C : Type v} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing C] [IsNoetherianRing C] [IsLocalRing C] [Algebra A C]
    [IsLocalHom (algebraMap A C)] [Module.Flat A C]
    (h : RingHom.FormallySmoothNAdic.{max u v}
      (algebraMap (ResidueField A) (ResidueField A ⊗[A] C))
      (maximalIdeal (ResidueField A ⊗[A] C))) :
    RingHom.FormallySmoothNAdic.{max u v} (algebraMap A C) (maximalIdeal C) := by
  let P (a : Algebra A C) : Prop :=
    let := a
    ∀ (_ : IsLocalHom (algebraMap A C)), Module.Flat A C →
      RingHom.FormallySmoothNAdic.{max u v}
        (algebraMap (ResidueField A) (ResidueField A ⊗[A] C))
        (maximalIdeal (ResidueField A ⊗[A] C)) →
      RingHom.FormallySmoothNAdic.{max u v} (algebraMap A C) (maximalIdeal C)
  have hP : P (algebraMap A C).toAlgebra := by
    intro hl hf hs
    exact ((flat_geometricallyRegular_specialFiber_formallySmooth_tfae
      (algebraMap A C)).out 2 3).mp (And.intro hf hs)
  have hP' : P (inferInstance : Algebra A C) := by
    rw [← toAlgebra_algebraMap (R := A) (S := C)]
    exact hP
  exact hP' inferInstance inferInstance h

/-- **Stacks 07NR.** Let `A` be a Noetherian complete local ring and let `B` be a
Noetherian complete local algebra over the residue field of `A`. If `B` is formally smooth for
its maximal-ideal-adic topology, then it is the special fibre of a Noetherian complete local
ring `C` that is adically formally smooth over `A` via a local homomorphism. -/
@[stacks 07NR,
  ega "0 19.7.2" "existence, J = 𝔪",
  ega "0 19.0.2" "III existence",
  ega "0 19.7.1.3" "A complete, B geom reg", ega "0 19.8.2" "(ii) existence", ega "0 22.2.7" "(i)"]
public theorem exists_completeLocal_formallySmooth_lift
    {A : Type u} {B : Type v}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [IsAdicComplete (maximalIdeal B) B]
    [Algebra (ResidueField A) B]
    (hB : RingHom.FormallySmoothNAdic.{max u v}
      (algebraMap (ResidueField A) B) (maximalIdeal B)) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : IsNoetherianRing C)
      (_ : IsLocalRing C) (_ : IsAdicComplete (maximalIdeal C) C)
      (f : A →+* C) (_ : IsLocalHom f),
      RingHom.FormallySmoothNAdic.{max u v} f (maximalIdeal C) ∧
        letI : Algebra A C := f.toAlgebra
        Nonempty ((ResidueField A ⊗[A] C) ≃ₐ[ResidueField A] B) := by
  have hregB : IsRegularLocalRing B := by
    apply isRegularLocalRing_of_isFormallySmooth_maximalIdeal (k := ResidueField A)
    let : TopologicalSpace (ResidueField A) := ⊥
    let : DiscreteTopology (ResidueField A) := ⟨rfl⟩
    let : TopologicalSpace B := (maximalIdeal B).adicTopology
    let : IsTopologicalRing B := (maximalIdeal B).ringFilterBasis.isTopologicalRing
    let : IsLinearTopology B B := (maximalIdeal B).isLinearTopology
    exact (isFormallySmooth_iff_formallySmoothNAdic
      (algebraMap (ResidueField A) B) (maximalIdeal B) rfl).mpr hB
  let f : A →+* B := (algebraMap (ResidueField A) B).comp (residue A)
  have : IsLocalHom f := RingHom.isLocalHom_comp _ _
  obtain ⟨R, S, hR, hregR, hcR, hS, hregS, hcS, g, qA, qB,
    hqA, hqB, hg, hqAl, hqBl, hcomm, hparams, _⟩ :=
    exists_powerSeries_presentation_of_isLocalHom f
  obtain ⟨xs, ys, zs, hxs, hxlen, hys, hylen, rfl, _, _⟩ := hparams
  let : Algebra R A := qA.toAlgebra
  let : Algebra A B := f.toAlgebra
  let : Algebra R (ResidueField A) := ((residue A).comp qA).toAlgebra
  let : Algebra R B := (f.comp qA).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R A (ResidueField A) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R (ResidueField A) B := IsScalarTower.of_algebraMap_eq' rfl
  have hres : Function.Surjective (algebraMap R (ResidueField A)) :=
    residue_surjective.comp hqA
  have hresker : RingHom.ker (algebraMap R (ResidueField A)) = maximalIdeal R :=
    ker_eq_maximalIdeal _ hres
  have hkill : (maximalIdeal R).map g ≤ RingHom.ker qB := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change qB (g r) = 0
    rw [← RingHom.comp_apply, ← hcomm]
    change algebraMap (ResidueField A) B (algebraMap R (ResidueField A) r) = 0
    have hr' : r ∈ RingHom.ker (algebraMap R (ResidueField A)) := by rwa [hresker]
    rw [show algebraMap R (ResidueField A) r = 0 from hr', map_zero]
  obtain ⟨J, hJq, hregT, hflat, hker⟩ :=
    exists_flat_quotient g qB hqB xs zs hxs hxlen hys hylen hkill
  let T := S ⧸ J
  let π := Ideal.Quotient.mk J
  let gT : R →+* T := π.comp g
  let : Algebra R T := gT.toAlgebra
  have : Module.Flat R T := hflat
  have : IsAdicComplete (maximalIdeal T) T := isAdicComplete_of_surjective π
    Ideal.Quotient.mk_surjective
  let qT : T →ₐ[R] B :=
    { Ideal.Quotient.lift J qB hJq with
      commutes' := fun r => (DFunLike.congr_fun hcomm r).symm }
  have hqT : Function.Surjective qT := by
    intro b
    obtain ⟨s, rfl⟩ := hqB b
    exact ⟨π s, rfl⟩
  have hqTker : RingHom.ker qT =
      (RingHom.ker (algebraMap R (ResidueField A))).map (algebraMap R T) := by
    rw [hresker]
    calc
      RingHom.ker qT = (RingHom.ker qB).map π :=
        (Ideal.map_comap_of_surjective π Ideal.Quotient.mk_surjective _).symm
      _ = (J ⊔ (maximalIdeal R).map g).map π := by rw [hker]
      _ = (maximalIdeal R).map (algebraMap R T) := by
        rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_map]
        rfl
  obtain ⟨eT⟩ := nonempty_tensorProduct_equiv_of_ker hres qT hqT hqTker
  let C := A ⊗[R] T
  let c : C →ₐ[A] B := AlgHom.liftEquiv R A T B qT
  have : Nontrivial C := c.toRingHom.domain_nontrivial
  let i : T →+* C := Algebra.TensorProduct.includeRight.toRingHom
  have hi : Function.Surjective i := Algebra.TensorProduct.includeRight_surjective T hqA
  have : IsLocalRing C := IsLocalRing.of_surjective' i hi
  have : IsNoetherianRing C := isNoetherianRing_of_surjective T C i hi
  have : IsAdicComplete (maximalIdeal C) C := isAdicComplete_of_surjective i hi
  have : IsLocalHom (algebraMap A C) := by
    have hcomp : IsLocalHom (c.toRingHom.comp (algebraMap A C)) := by
      change IsLocalHom ((c : C →+* B).comp (algebraMap A C))
      rw [c.comp_algebraMap]
      exact inferInstanceAs (IsLocalHom f)
    exact isLocalHom_of_comp (algebraMap A C) c.toRingHom
  let e : (ResidueField A ⊗[A] C) ≃ₐ[ResidueField A] B :=
    (Algebra.TensorProduct.cancelBaseChange R A (ResidueField A) (ResidueField A) T).trans eT
  have hfsB : RingHom.FormallySmoothNAdic.{max u v}
      (algebraMap (ResidueField A) (ResidueField A ⊗[A] C))
      (maximalIdeal (ResidueField A ⊗[A] C)) :=
    formallySmoothNAdic_of_algEquiv e.symm hB
  have hfs : RingHom.FormallySmoothNAdic.{max u v}
      (algebraMap A C) (maximalIdeal C) :=
    formallySmoothNAdic_of_flat_specialFiber hfsB
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance,
    algebraMap A C, inferInstance, hfs, ?_⟩
  rw [toAlgebra_algebraMap]
  exact ⟨e⟩

end

end

/-! ### Stacks Tag 07NS -/

section

section

set_option maxRecDepth 4096

open IsLocalRing
open scoped TensorProduct
open scoped Topology

universe u v w x

/-- Formal smoothness for an adic topology is invariant under an isomorphism of
the source ring. -/
private theorem formallySmoothNAdic_comp_of_bijective
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (hf : Function.Bijective f) (g : S →+* T)
    (n : Ideal T) (hg : RingHom.FormallySmoothNAdic.{x} g n) :
    RingHom.FormallySmoothNAdic.{x} (g.comp f) n := by
  let e : R ≃+* S := RingEquiv.ofBijective f hf
  intro A _ J hJ α ψ hcomm hk
  let β : S →+* A := α.comp e.symm.toRingHom
  have hcomm' : ψ.comp g = (Ideal.Quotient.mk J).comp β := by
    ext s
    have hs : f (e.symm s) = s := e.apply_symm_apply s
    have hh := congrArg (fun h : R →+* A ⧸ J => h (e.symm s)) hcomm
    change ψ (g s) = (Ideal.Quotient.mk J) (α (e.symm s))
    simpa only [RingHom.comp_apply, hs] using hh
  obtain ⟨γ, hγ, hγg⟩ := hg A J hJ β ψ hcomm' hk
  refine ⟨γ, hγ, ?_⟩
  ext r
  have hr := congrArg (fun h : S →+* A => h (f r)) hγg
  change γ (g (f r)) = α r
  change γ (g (f r)) = α (e.symm (f r)) at hr
  rw [show f r = e r from rfl, e.symm_apply_apply] at hr
  exact hr

/-- A surjective image of a Noetherian complete local ring is complete for its
maximal ideal. -/
private theorem isAdicComplete_of_surjective_07ns
    {R S : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    [CommRing S] [IsLocalRing S]
    (f : R →+* S) (hf : Function.Surjective f) :
    IsAdicComplete (maximalIdeal S) S :=
  have := isNoetherianRing_of_surjective R S f hf
  isAdicComplete_of_surjective f hf

/-- The special fibre of a Noetherian complete local algebra is again
Noetherian and complete local. -/
private theorem specialFiber_noetherian_complete
    {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [IsAdicComplete (maximalIdeal B) B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] :
    IsNoetherianRing (ResidueField A ⊗[A] B) ∧
      IsAdicComplete (maximalIdeal (ResidueField A ⊗[A] B))
        (ResidueField A ⊗[A] B) := by
  let F := ResidueField A ⊗[A] B
  have hloc : IsLocalRing F := inferInstance
  let b : B →+* F :=
    (Algebra.TensorProduct.includeRight (R := A) (A := ResidueField A) (B := B)).toRingHom
  have hb : Function.Surjective b :=
    Algebra.TensorProduct.includeRight_surjective B residue_surjective
  exact ⟨isNoetherianRing_of_surjective B F b hb,
    isAdicComplete_of_surjective_07ns b hb⟩

private theorem isAdicComplete_of_le_maximalIdeal
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (hM : IsAdicComplete (maximalIdeal R) M)
    {I : Ideal R} (hI : I ≤ maximalIdeal R) : IsAdicComplete I M :=
  isAdicComplete_of_le_of_fg_of_isAdicComplete hI hM I.fg_of_isNoetherianRing

/-- Every ideal of a Noetherian local ring is closed in the maximal-ideal-adic
topology. -/
private theorem ideal_isClosed_maximal_adic
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (K : Ideal R) :
    letI : TopologicalSpace R := (maximalIdeal R).adicTopology
    IsClosed (K : Set R) := by
  let : TopologicalSpace R := (maximalIdeal R).adicTopology
  have hhaus : IsHausdorff (maximalIdeal R) (R ⧸ K) := inferInstance
  apply isClosed_of_closure_subset
  intro x hx
  have hxq : ∀ n, (K.mkQ x) ≡ 0
      [SMOD (maximalIdeal R) ^ n • (⊤ : Submodule R (R ⧸ K))] := by
    intro n
    obtain ⟨y, hy, z, hz, rfl⟩ :=
      (mem_closure_iff_nhds_basis
        ((maximalIdeal R).hasBasis_nhds_adic x)).mp hx n trivial
    rw [SModEq.zero]
    have hz' : z ∈ (maximalIdeal R) ^ n • (⊤ : Submodule R R) := by
      simpa [Ideal.smul_top_eq_map] using hz
    have hzq : K.mkQ z ∈ Submodule.map K.mkQ
        ((maximalIdeal R) ^ n • (⊤ : Submodule R R)) :=
      Submodule.mem_map_of_mem hz'
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at hzq
    have hsum : K.mkQ x + K.mkQ z = 0 := by
      change K.mkQ (x + z) = 0
      exact (Submodule.Quotient.mk_eq_zero K).mpr hy
    have hxneg : K.mkQ x = -(K.mkQ z) := eq_neg_of_add_eq_zero_left hsum
    rw [hxneg]
    exact Submodule.neg_mem _ hzq
  exact (Submodule.Quotient.mk_eq_zero K).mp (hhaus.haus' (K.mkQ x) hxq)


/-- The quotient topology of an adic ring is adic for the image ideal. -/
private theorem quotient_isAdic_map
    {R : Type*} [CommRing R] (I K : Ideal R) :
    letI : TopologicalSpace R := I.adicTopology
    IsAdic (I.map (Ideal.Quotient.mk K)) := by
  let : TopologicalSpace R := I.adicTopology
  have : IsTopologicalRing R := I.ringFilterBasis.isTopologicalRing
  have : IsTopologicalRing (R ⧸ K) := inferInstance
  apply isAdic_iff.mpr
  constructor
  · intro n
    rw [← Ideal.map_pow]
    rw [Ideal.map_eq_image_of_surjective (Ideal.Quotient.mk K)
      Ideal.Quotient.mk_surjective]
    exact QuotientRing.isOpenMap_coe K ((I ^ n : Ideal R) : Set R)
      (I.openAddSubgroup n).isOpen'
  · intro U hU
    change U ∈ 𝓝 (Ideal.Quotient.mk K (0 : R)) at hU
    have hpre : (Ideal.Quotient.mk K) ⁻¹' U ∈ 𝓝 (0 : R) :=
      continuous_quot_mk.continuousAt.tendsto hU
    obtain ⟨n, _, hn⟩ := I.hasBasis_nhds_zero_adic.mem_iff.mp hpre
    refine ⟨n, ?_⟩
    intro y hy
    rw [← Ideal.map_pow] at hy
    obtain ⟨x, hx, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk K)
        Ideal.Quotient.mk_surjective).mp hy
    exact hn hx

/-- A local map to a quotient is continuous for the quotient of the maximal-ideal-adic
topology. -/
private theorem continuous_quotient_maximal_adic_of_localHom
    {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S]
    (K : Ideal S) (hK : K ≤ maximalIdeal S)
    (f : R →+* S ⧸ K) [IsLocalHom f] :
    letI : TopologicalSpace S := (maximalIdeal S).adicTopology
    @Continuous R (S ⧸ K) (maximalIdeal R).adicTopology
      (inferInstance : TopologicalSpace (S ⧸ K)) f := by
  have hproper : K ≠ ⊤ := (hK.trans_lt (maximalIdeal.isMaximal S).lt_top).ne
  have : Nontrivial (S ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hproper
  have : IsLocalRing (S ⧸ K) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  let : TopologicalSpace S := (maximalIdeal S).adicTopology
  have htop := quotient_isAdic_map (maximalIdeal S) K
  have hmax : (maximalIdeal S).map (Ideal.Quotient.mk K) =
      maximalIdeal (S ⧸ K) :=
    IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk K)
      Ideal.Quotient.mk_surjective
  rw [hmax] at htop
  change (inferInstance : TopologicalSpace (S ⧸ K)) =
    (maximalIdeal (S ⧸ K)).adicTopology at htop
  rw [htop]
  exact continuous_of_isLocalHom f

/-- The special fibre over `A'` is formally smooth over `A` when the two
residue fields agree. -/
private theorem formallySmoothNAdic_specialFiber_of_residueField_map_bijective
    {A : Type u} {A' : Type v} {B : Type w}
    [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
    [CommRing B] [IsLocalRing B]
    (f : A →+* A') [IsLocalHom f] (g : A' →+* B) [IsLocalHom g]
    (hf : Function.Bijective (ResidueField.map f))
    (hB : letI : Algebra A' B := g.toAlgebra
      RingHom.FormallySmoothNAdic.{max u v w}
        (algebraMap (ResidueField A') (ResidueField A' ⊗[A'] B))
        (maximalIdeal (ResidueField A' ⊗[A'] B))) :
    letI : Algebra A' B := g.toAlgebra
    let F := ResidueField A' ⊗[A'] B
    letI : Algebra (ResidueField A) F :=
      ((algebraMap (ResidueField A') F).comp (ResidueField.map f)).toAlgebra
    RingHom.FormallySmoothNAdic.{max u v w}
      (algebraMap (ResidueField A) F) (maximalIdeal F) := by
  let : Algebra A' B := g.toAlgebra
  let F := ResidueField A' ⊗[A'] B
  let : Algebra (ResidueField A) F :=
    ((algebraMap (ResidueField A') F).comp (ResidueField.map f)).toAlgebra
  dsimp only
  exact formallySmoothNAdic_comp_of_bijective
    (ResidueField.map f) hf
    (algebraMap (ResidueField A') (ResidueField A' ⊗[A'] B))
    (maximalIdeal (ResidueField A' ⊗[A'] B)) hB

/-- Apply the complete local lifting theorem to the special fibre after
identifying the two residue fields. -/
private theorem exists_completeLocal_lift_for_specialFiber
    {A : Type u} {A' : Type v} {B : Type w}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing A'] [IsLocalRing A']
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [IsAdicComplete (maximalIdeal B) B]
    (f : A →+* A') [IsLocalHom f] (g : A' →+* B) [IsLocalHom g]
    (hf : Function.Bijective (ResidueField.map f))
    (hB : letI : Algebra A' B := g.toAlgebra
      RingHom.FormallySmoothNAdic.{max u v w}
        (algebraMap (ResidueField A') (ResidueField A' ⊗[A'] B))
        (maximalIdeal (ResidueField A' ⊗[A'] B))) :
    letI : Algebra A' B := g.toAlgebra
    let F := ResidueField A' ⊗[A'] B
    letI : Algebra (ResidueField A) F :=
      ((algebraMap (ResidueField A') F).comp (ResidueField.map f)).toAlgebra
    ∃ (C : Type (max u v w)) (_ : CommRing C) (_ : IsNoetherianRing C)
      (_ : IsLocalRing C) (_ : IsAdicComplete (maximalIdeal C) C)
      (a : A →+* C) (_ : IsLocalHom a),
      RingHom.FormallySmoothNAdic.{max u v w} a (maximalIdeal C) ∧
        letI : Algebra A C := a.toAlgebra
        Nonempty ((ResidueField A ⊗[A] C) ≃ₐ[ResidueField A] F) := by
  let : Algebra A' B := g.toAlgebra
  let F := ResidueField A' ⊗[A'] B
  let : Algebra (ResidueField A) F :=
    ((algebraMap (ResidueField A') F).comp (ResidueField.map f)).toAlgebra
  have : IsLocalRing F := inferInstance
  obtain ⟨hnoeth, hcomplete⟩ := specialFiber_noetherian_complete (A := A') (B := B)
  let : IsNoetherianRing F := hnoeth
  let : IsAdicComplete (maximalIdeal F) F := hcomplete
  exact exists_completeLocal_formallySmooth_lift
    (formallySmoothNAdic_specialFiber_of_residueField_map_bijective f g hf hB)

/-- The isomorphism of special fibres determines a surjective map to the
closed-fibre quotient. -/
private theorem exists_quotient_map_of_specialFiber_equiv
    {A : Type u} {A' : Type v} {B : Type w} {C : Type x}
    [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
    [CommRing B] [CommRing C]
    (f : A →+* A') [IsLocalHom f] (g : A' →+* B) (a : A →+* C)
    (e : letI : Algebra A' B := g.toAlgebra
      letI : Algebra A C := a.toAlgebra
      letI : Algebra (ResidueField A) (ResidueField A' ⊗[A'] B) :=
        ((algebraMap (ResidueField A') (ResidueField A' ⊗[A'] B)).comp
          (ResidueField.map f)).toAlgebra
      (ResidueField A ⊗[A] C) ≃ₐ[ResidueField A]
        (ResidueField A' ⊗[A'] B)) :
    letI : Algebra A' B := g.toAlgebra
    letI : Algebra A C := a.toAlgebra
    let J : Ideal B := (maximalIdeal A').map g
    ∃ ψ : C →+* B ⧸ J,
      Function.Surjective ψ ∧
      ψ.comp a = (Ideal.Quotient.mk J).comp (g.comp f) ∧
      ∀ y : C,
        Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A') (ψ y) =
          e (Algebra.TensorProduct.includeRight (R := A)
            (A := ResidueField A) (B := C) y) := by
  let : Algebra A' B := g.toAlgebra
  let : Algebra A C := a.toAlgebra
  let : Algebra (ResidueField A) (ResidueField A' ⊗[A'] B) :=
    ((algebraMap (ResidueField A') (ResidueField A' ⊗[A'] B)).comp
      (ResidueField.map f)).toAlgebra
  let J : Ideal B := (maximalIdeal A').map g
  let eB := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A')
  let ι : C →+* ResidueField A ⊗[A] C :=
    (Algebra.TensorProduct.includeRight (R := A)
      (A := ResidueField A) (B := C)).toRingHom
  let ψ : C →+* B ⧸ J := eB.symm.toRingHom.comp (e.toRingHom.comp ι)
  refine ⟨ψ, ?_, ?_, ?_⟩
  · exact eB.symm.surjective.comp
      (e.surjective.comp (Algebra.TensorProduct.includeRight_surjective C residue_surjective))
  · ext r
    apply eB.injective
    change eB (eB.symm (e (ι (a r)))) = eB (Ideal.Quotient.mk J (g (f r)))
    erw [eB.apply_symm_apply]
    have hι : ι (a r) = algebraMap (ResidueField A)
        (ResidueField A ⊗[A] C) (residue A r) := by
      exact (Algebra.TensorProduct.includeRight (R := A)
        (A := ResidueField A) (B := C)).commutes r
    rw [hι, e.commutes]
    change algebraMap (ResidueField A') (ResidueField A' ⊗[A'] B)
      (ResidueField.map f (residue A r)) = eB (Ideal.Quotient.mk J (g (f r)))
    rw [ResidueField.map_residue]
    symm
    exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B
      (maximalIdeal A')).commutes (f r)
  · intro y
    exact eB.apply_symm_apply _

namespace Stacks.GeometricallyRegular.AdicLifting

/-- Algebraic adic lifting gives continuous lifting when the source is discrete. -/
theorem isFormallySmooth_of_formallySmoothNAdic {A : Type u} {B : Type v}
    [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [DiscreteTopology A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (f : A →+* B) (m : Ideal B) (hm : IsAdic m)
    (hfs : RingHom.FormallySmoothNAdic.{w, u, v} f m) :
    IsFormallySmooth.{w} f := by
  constructor
  · exact continuous_of_discreteTopology
  · intro C _ _ _ J hJ g hg ψ hψ hcomm
    have : DiscreteTopology (C ⧸ J) :=
      QuotientAddGroup.discreteTopology (N := J.toAddSubgroup) (isOpen_discrete _)
    have hbot : IsAdic (⊥ : Ideal (C ⧸ J)) := is_bot_adic_iff.mpr inferInstance
    have hk : ∃ k : ℕ, 1 ≤ k ∧ m ^ k ≤ RingHom.ker ψ := by
      have hψadic : @Continuous B (C ⧸ J) m.adicTopology
          (⊥ : Ideal (C ⧸ J)).adicTopology ψ := by
        change (inferInstance : TopologicalSpace B) = m.adicTopology at hm
        change (inferInstance : TopologicalSpace (C ⧸ J)) =
          (⊥ : Ideal (C ⧸ J)).adicTopology at hbot
        rw [← hm, ← hbot]
        exact hψ
      obtain ⟨k, hk, hle⟩ :=
        (RingHom.continuous_adic_iff ψ m (⊥ : Ideal (C ⧸ J))).mp hψadic
      exact ⟨k, hk, fun x hx => hle x hx⟩
    obtain ⟨k, hk1, hkle⟩ := hk
    obtain ⟨g', hq, hf⟩ := hfs C J hJ g ψ hcomm ⟨k, hk1, hkle⟩
    have hJg : m ^ k ≤ J.comap g' := by
      intro x hx
      have hψx : ψ x = 0 := hkle hx
      have hq' : Ideal.Quotient.mk J (g' x) = ψ x := congrArg (fun h : B →+* C ⧸ J => h x) hq
      exact (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp (hq'.trans hψx)
    have hmapJ : (m ^ k).map g' ≤ J := (Ideal.map_le_iff_le_comap).mpr hJg
    have hzero : (m ^ (k * 2)).map g' ≤ (⊥ : Ideal C) := by
      rw [pow_mul, Ideal.map_pow]
      calc
        (Ideal.map g' (m ^ k)) ^ 2 ≤ J ^ 2 := pow_le_pow_left' hmapJ 2
        _ = ⊥ := hJ
    have hcont' : @Continuous B C m.adicTopology (⊥ : Ideal C).adicTopology g' :=
      (RingHom.continuous_adic_iff g' m ⊥).mpr ⟨k * 2, by omega, by
        intro x hx
        exact hzero (Ideal.mem_map_of_mem g' hx)⟩
    have hc : IsAdic (⊥ : Ideal C) := is_bot_adic_iff.mpr inferInstance
    refine ⟨g', ?_, hf, hq⟩
    change (inferInstance : TopologicalSpace C) = (⊥ : Ideal C).adicTopology at hc
    change (inferInstance : TopologicalSpace B) = m.adicTopology at hm
    rw [← hm, ← hc] at hcont'
    exact hcont'

end Stacks.GeometricallyRegular.AdicLifting

/-- Adic formal smoothness can be tested in any smaller universe. -/
private theorem formallySmoothNAdic_universe_down
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal S)
    (h : RingHom.FormallySmoothNAdic.{max w x} f I) :
    RingHom.FormallySmoothNAdic.{w} f I := by
  intro T _ J hJ a ψ hcomm hk
  let e : T ≃+* ULift.{x} T := ULift.ringEquiv.symm
  let K := J.map e.toRingHom
  let eqv : T ⧸ J ≃+* ULift.{x} T ⧸ K := Ideal.quotientEquiv J K e rfl
  have hK : K ^ 2 = 0 := by
    rw [← Ideal.map_pow, hJ]
    exact Ideal.map_bot
  have hc : (eqv.toRingHom.comp ψ).comp f =
      (Ideal.Quotient.mk K).comp (e.toRingHom.comp a) := by
    ext r
    change eqv (ψ (f r)) = Ideal.Quotient.mk K (e (a r))
    rw [show ψ (f r) = Ideal.Quotient.mk J (a r) from DFunLike.congr_fun hcomm r]
    exact Ideal.quotientEquiv_mk J K e rfl _
  obtain ⟨b, hb, hba⟩ := h _ K hK (e.toRingHom.comp a)
    (eqv.toRingHom.comp ψ) hc (by
      obtain ⟨n, hn, hk⟩ := hk
      exact ⟨n, hn, fun z hz => by change eqv (ψ z) = 0; rw [hk hz, map_zero]⟩)
  refine ⟨e.symm.toRingHom.comp b, ?_, ?_⟩
  · ext z
    apply eqv.injective
    change eqv (Ideal.Quotient.mk J (e.symm (b z))) = eqv (ψ z)
    rw [show eqv (Ideal.Quotient.mk J (e.symm (b z))) =
      Ideal.Quotient.mk K (e (e.symm (b z))) from Ideal.quotientEquiv_mk J K e rfl _,
      e.apply_symm_apply]
    exact DFunLike.congr_fun hb z
  · ext r
    change e.symm (b (f r)) = a r
    rw [show b (f r) = e (a r) from DFunLike.congr_fun hba r]
    exact e.symm_apply_apply _

/-- A surjective map onto a closed local quotient lifts along an adically
formally smooth map, and the lift is local. -/
private theorem exists_local_lift_of_formallySmoothNAdic
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [IsLocalRing S]
    [CommRing T] [IsNoetherianRing T] [IsLocalRing T]
    [IsAdicComplete (maximalIdeal T) T]
    (f : R →+* S) (h : RingHom.FormallySmoothNAdic.{w} f (maximalIdeal S))
    (a : R →+* T) (J : Ideal T) (hJ : J ≤ maximalIdeal T)
    (ψ : S →+* T ⧸ J) (hψ : Function.Surjective ψ)
    (hc : ψ.comp f = (Ideal.Quotient.mk J).comp a) :
    ∃ b : S →+* T, IsLocalHom b ∧ b.comp f = a ∧
      (Ideal.Quotient.mk J).comp b = ψ := by
  have hproper : J ≠ ⊤ := (hJ.trans_lt (maximalIdeal.isMaximal T).lt_top).ne
  have : Nontrivial (T ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hproper
  have : IsLocalRing (T ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have : IsLocalHom ψ := hψ.isLocalHom
  let : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  let : TopologicalSpace S := (maximalIdeal S).adicTopology
  have : IsTopologicalRing S := (maximalIdeal S).ringFilterBasis.isTopologicalRing
  have : IsLinearTopology S S := (maximalIdeal S).isLinearTopology
  let : TopologicalSpace T := (maximalIdeal T).adicTopology
  have : IsTopologicalRing T := (maximalIdeal T).ringFilterBasis.isTopologicalRing
  obtain ⟨b, _, hb, hbψ⟩ :=
    exists_continuous_lift_of_isFormallySmooth_of_isAdic
      f (maximalIdeal S) rfl
      (Stacks.GeometricallyRegular.AdicLifting.isFormallySmooth_of_formallySmoothNAdic f _ rfl h)
      (maximalIdeal T) rfl J (ideal_isClosed_maximal_adic J)
      1 (le_refl 1) (by simpa only [pow_one] using hJ)
      a continuous_of_discreteTopology ψ
      (continuous_quotient_maximal_adic_of_localHom J hJ ψ) hc
  have : IsLocalHom ((Ideal.Quotient.mk J).comp b) := hbψ.symm ▸ inferInstance
  exact ⟨b, isLocalHom_of_comp b (Ideal.Quotient.mk J), hb, hbψ⟩

/-- A homomorphism to a complete adic ring extends to the completion when it
maps the ideal of definition into the target ideal. -/
private theorem exists_extension_to_adicCompletion
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) [IsAdicComplete J S]
    (f : R →+* S) (hf : I ≤ J.comap f) :
    ∃ q : AdicCompletion I R →+* S,
      q.comp (algebraMap R (AdicCompletion I R)) = f := by
  let fs (n : ℕ) : R ⧸ I ^ n →+* S ⧸ J ^ n :=
    Ideal.quotientMap (J ^ n) f (by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
      exact pow_le_pow_left' (Ideal.map_le_iff_le_comap.mpr hf) n)
  let qs (n : ℕ) : AdicCompletion I R →+* S ⧸ J ^ n :=
    (fs n).comp (AdicCompletion.evalₐ I n).toRingHom
  have hqs : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow J hmn).comp (qs n) = qs m := by
    intro m n hmn
    ext z
    change (Ideal.Quotient.factorPow J hmn) (fs n (AdicCompletion.evalₐ I n z)) =
      fs m (AdicCompletion.evalₐ I m z)
    have hz : (Ideal.Quotient.factorPow I hmn) (AdicCompletion.evalₐ I n z) =
        AdicCompletion.evalₐ I m z := by
      rw [← AdicCompletion.factor_eval_eq_evalₐ I _ (le_of_eq (Ideal.mul_top _)),
        ← AdicCompletion.factor_eval_eq_evalₐ I _ (le_of_eq (Ideal.mul_top _))]
      change (Ideal.Quotient.factorPow I hmn)
        (Submodule.factor _ (z.val n)) = Submodule.factor _ (z.val m)
      calc
        _ = Submodule.factor (le_of_eq (Ideal.mul_top (I ^ m)))
            (AdicCompletion.transitionMap I R hmn (z.val n)) := by
          generalize (z.val n) = y
          obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ y
          rfl
        _ = _ := congrArg (Submodule.factor (le_of_eq (Ideal.mul_top (I ^ m)))) (z.2 hmn)
    rw [← hz]
    generalize AdicCompletion.evalₐ I n z = y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    rfl
  refine ⟨IsAdicComplete.liftRingHom J qs hqs, ?_⟩
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' J
  intro n r
  change Ideal.Quotient.mk (J ^ n)
    (IsAdicComplete.liftRingHom J qs hqs (algebraMap R (AdicCompletion I R) r)) = _
  rw [IsAdicComplete.mk_liftRingHom]
  change fs n (AdicCompletion.evalₐ I n (AdicCompletion.of I R r)) = _
  rw [AdicCompletion.evalₐ_of]
  rfl

/-- Surjectivity modulo an ideal implies surjectivity of the induced map
from the completion. -/
private theorem exists_surjective_extension_to_adicCompletion
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (hI : I.FG) (f : R →+* S)
    [IsAdicComplete (I.map f) S]
    (hf : Function.Surjective ((Ideal.Quotient.mk (I.map f)).comp f)) :
    ∃ q : AdicCompletion I R →+* S,
      q.comp (algebraMap R (AdicCompletion I R)) = f ∧ Function.Surjective q := by
  obtain ⟨q, hq⟩ := exists_extension_to_adicCompletion I (I.map f) f Ideal.le_comap_map
  let K := I.map (algebraMap R (AdicCompletion I R))
  have hK : K.map q = I.map f := by
    rw [Ideal.map_map, hq]
  have : IsAdicComplete K (AdicCompletion I R) := AdicCompletion.isAdicComplete_self I hI
  have : IsHausdorff (K.map q) S := hK.symm ▸ inferInstance
  refine ⟨q, hq, surjective_of_mk_map_comp_surjective (I := K) q ?_⟩
  rw [hK]
  intro y
  obtain ⟨r, hr⟩ := hf y
  refine ⟨algebraMap R (AdicCompletion I R) r, ?_⟩
  change Ideal.Quotient.mk (I.map f) (q (algebraMap R (AdicCompletion I R) r)) = y
  rw [show q (algebraMap R (AdicCompletion I R) r) = f r from DFunLike.congr_fun hq r]
  exact hr

/-- Completion is Noetherian and complete local when its reduction is
Noetherian and complete local and the ideal of definition is finitely generated. -/
private theorem adicCompletion_noetherian_completeLocal
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] [IsLocalRing (R ⧸ I)]
    [IsAdicComplete (maximalIdeal (R ⧸ I)) (R ⧸ I)] :
    ∃ (_ : IsNoetherianRing (AdicCompletion I R))
      (_ : IsLocalRing (AdicCompletion I R)),
      IsAdicComplete (maximalIdeal (AdicCompletion I R)) (AdicCompletion I R) := by
  let D := AdicCompletion I R
  let K := I.map (algebraMap R D)
  have : IsNoetherianRing D := (completion_noetherian R I inferInstance hI).1
  have : IsAdicComplete K D := AdicCompletion.isAdicComplete_self I hI
  let e : D ⧸ K ≃+* R ⧸ I :=
    (Ideal.quotEquivOfEq (AdicCompletion.ker_evalOneₐ_eq_map I hI).symm).trans
      (RingHom.quotientKerEquivOfSurjective (AdicCompletion.evalOneₐ_surjective I))
  have : Nontrivial (D ⧸ K) := e.toRingHom.domain_nontrivial
  have : IsLocalRing (D ⧸ K) := IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  have : Nontrivial D := (Ideal.Quotient.mk K).domain_nontrivial
  have : IsLocalHom (Ideal.Quotient.mk K) :=
    isLocalHom_of_le_jacobson_bot K (IsAdicComplete.le_jacobson_bot K)
  have : IsLocalRing D := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun r => by
    have h := IsLocalRing.isUnit_or_isUnit_one_sub_self (Ideal.Quotient.mk K r)
    rcases h with h | h
    · exact Or.inl (IsUnit.of_map (Ideal.Quotient.mk K) r h)
    · exact Or.inr (IsUnit.of_map (Ideal.Quotient.mk K) (1 - r) (by simpa using h))
  have hcomplete : IsAdicComplete (maximalIdeal (D ⧸ K)) (D ⧸ K) := by
    have he := (IsAdicComplete.congr_ringEquiv (maximalIdeal (R ⧸ I)) e.symm).mpr
      (inferInstance : IsAdicComplete (maximalIdeal (R ⧸ I)) (R ⧸ I))
    change IsAdicComplete ((maximalIdeal (R ⧸ I)).map e.symm.toRingHom) (D ⧸ K) at he
    rwa [IsLocalRing.map_maximalIdeal_of_surjective e.symm.toRingHom e.symm.surjective] at he
  refine ⟨inferInstance, inferInstance, IsAdicComplete.of_quotient K (maximalIdeal D) ?_⟩
  apply (IsAdicComplete.map_algebraMap_iff (S := D ⧸ K) (maximalIdeal D) (D ⧸ K)).mp
  rw [Ideal.Quotient.algebraMap_eq,
    IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective]
  exact hcomplete

/-- A commutative square of rings induces the compatible map from its tensor
product, and it carries extended ideals to the corresponding extended ideals. -/
private theorem exists_tensorProduct_map
    {A A' B C : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing C]
    (f : A →+* A') (g : A' →+* B) (a : A →+* C) (c : C →+* B)
    (hc : c.comp a = g.comp f) :
    letI : Algebra A A' := f.toAlgebra
    letI : Algebra A C := a.toAlgebra
    ∃ t : C ⊗[A] A' →+* B,
      t.comp (Algebra.TensorProduct.includeLeft (R := A) (S := A)
        (A := C) (B := A')).toRingHom = c ∧
      t.comp (Algebra.TensorProduct.includeRight (R := A)
        (A := C) (B := A')).toRingHom = g ∧
      ∀ I : Ideal A',
        (I.map (Algebra.TensorProduct.includeRight (R := A)
          (A := C) (B := A')).toRingHom).map t = I.map g := by
  let : Algebra A A' := f.toAlgebra
  let : Algebra A C := a.toAlgebra
  let : Algebra A B := (g.comp f).toAlgebra
  let ca : C →ₐ[A] B := { __ := c, commutes' := fun r => DFunLike.congr_fun hc r }
  let ga : A' →ₐ[A] B := { __ := g, commutes' := fun _ => rfl }
  let t : C ⊗[A] A' →ₐ[A] B := Algebra.TensorProduct.lift ca ga (fun _ _ => Commute.all _ _)
  have hl : t.toRingHom.comp (Algebra.TensorProduct.includeLeft (R := A) (S := A)
      (A := C) (B := A')).toRingHom = c := by
    ext x
    simp [t, ca]
  have hr : t.toRingHom.comp (Algebra.TensorProduct.includeRight (R := A)
      (A := C) (B := A')).toRingHom = g := by
    ext x
    simp [t, ga]
  refine ⟨t.toRingHom, hl, hr, fun I => ?_⟩
  rw [Ideal.map_map, hr]

/-- For a square of local homomorphisms, surjectivity on the special fibre
and on the base implies surjectivity on complete local algebras. -/
private theorem surjective_of_surjective_base_of_surjective_specialFiber
    {A A' B C : Type*}
    [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [CommRing C] [IsNoetherianRing C] [IsLocalRing C]
    [IsAdicComplete (maximalIdeal C) C]
    (f : A →+* A') (g : A' →+* B) [IsLocalHom g]
    (a : A →+* C) [IsLocalHom a] (c : C →+* B)
    (hc : c.comp a = g.comp f) (hf : Function.Surjective f)
    (hψ : Function.Surjective
      ((Ideal.Quotient.mk ((maximalIdeal A').map g)).comp c)) :
    Function.Surjective c := by
  let I := (maximalIdeal A).map a
  have hI : I ≤ maximalIdeal C := map_maximalIdeal_le a
  have : IsAdicComplete I C := isAdicComplete_of_le_maximalIdeal inferInstance hI
  have hmap : I.map c = (maximalIdeal A').map g := by
    dsimp only [I]
    rw [Ideal.map_map, hc, ← Ideal.map_map,
      IsLocalRing.map_maximalIdeal_of_surjective f hf]
  have : IsHausdorff (I.map c) B := by
    rw [hmap]
    exact IsHausdorff.of_isLocalRing _ B (map_maximalIdeal_lt_top g).ne
  apply surjective_of_mk_map_comp_surjective (I := I) c
  rwa [hmap]

/-- A formally smooth special fibre admits a complete local lift with a
compatible local map to the original algebra. -/
private theorem exists_completeLocal_lift_with_local_map
    {A : Type u} {A' : Type v} {B : Type w}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing A'] [IsNoetherianRing A'] [IsLocalRing A']
    [IsAdicComplete (maximalIdeal A') A']
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [IsAdicComplete (maximalIdeal B) B]
    (f : A →+* A') [IsLocalHom f]
    (g : A' →+* B) [IsLocalHom g]
    (hf : Function.Bijective (ResidueField.map f))
    (hB : letI : Algebra A' B := g.toAlgebra
      RingHom.FormallySmoothNAdic.{max u v w}
        (algebraMap (ResidueField A') (ResidueField A' ⊗[A'] B))
        (maximalIdeal (ResidueField A' ⊗[A'] B))) :
    ∃ (C : Type (max u v w)) (_ : CommRing C) (_ : IsNoetherianRing C)
      (_ : IsLocalRing C) (_ : IsAdicComplete (maximalIdeal C) C)
      (a : A →+* C) (_ : IsLocalHom a)
      (c : C →+* B) (_ : IsLocalHom c),
      c.comp a = g.comp f ∧
      RingHom.FormallySmoothNAdic.{max u v w} a (maximalIdeal C) ∧
      (letI : Algebra A A' := f.toAlgebra
       letI : Algebra A' B := g.toAlgebra
       letI : Algebra A C := a.toAlgebra
       letI : Algebra (ResidueField A) (ResidueField A') := (ResidueField.map f).toAlgebra
       ∃ e : (ResidueField A ⊗[A] C) ≃ₐ[ResidueField A]
           (ResidueField A' ⊗[A'] B),
         (∀ x : ResidueField A,
           e (Algebra.TensorProduct.includeLeft (R := A) (S := ResidueField A)
             (A := ResidueField A) (B := C) x) =
             Algebra.TensorProduct.includeLeft (R := A') (S := ResidueField A')
               (A := ResidueField A') (B := B) (ResidueField.map f x)) ∧
         (∀ y : C,
           e (Algebra.TensorProduct.includeRight (R := A)
             (A := ResidueField A) (B := C) y) =
           Algebra.TensorProduct.includeRight (R := A')
             (A := ResidueField A') (B := B) (c y))) := by
  let : Algebra A' B := g.toAlgebra
  let F := ResidueField A' ⊗[A'] B
  let : Algebra (ResidueField A) F :=
    ((algebraMap (ResidueField A') F).comp (ResidueField.map f)).toAlgebra
  obtain ⟨C, hC, hnC, hlC, hcC, a, hla, ha, ⟨e⟩⟩ :=
    exists_completeLocal_lift_for_specialFiber f g hf hB
  let : CommRing C := hC
  let : IsNoetherianRing C := hnC
  let : IsLocalRing C := hlC
  let : IsAdicComplete (maximalIdeal C) C := hcC
  let : IsLocalHom a := hla
  let : Algebra A C := a.toAlgebra
  obtain ⟨ψ, hψ, hψa, hψe⟩ := exists_quotient_map_of_specialFiber_equiv f g a e
  obtain ⟨c, hlc, hca, hcψ⟩ := exists_local_lift_of_formallySmoothNAdic a
    (formallySmoothNAdic_universe_down.{u, max u v w, w, max u v} a _ ha)
    (g.comp f) ((maximalIdeal A').map g) (map_maximalIdeal_le g) ψ hψ hψa
  let er : (ResidueField A ⊗[A] C) ≃+* F := e.toRingEquiv
  have he (x : ResidueField A) :
      er (algebraMap (ResidueField A) (ResidueField A ⊗[A] C) x) =
        (ResidueField.map f x) ⊗ₜ[A'] (1 : B) := e.commutes x
  refine ⟨C, hC, hnC, hlC, hcC, a, hla, c, hlc, hca, ha, ?_⟩
  let : Algebra A A' := f.toAlgebra
  let : Algebra (ResidueField A) (ResidueField A') := (ResidueField.map f).toAlgebra
  let : Algebra (ResidueField A) F :=
    Algebra.TensorProduct.leftAlgebra (R := A') (S := ResidueField A)
      (A := ResidueField A') (B := B)
  refine ⟨{ __ := er, commutes' := ?_ }, ?_, ?_⟩
  · intro x
    change er (algebraMap (ResidueField A) (ResidueField A ⊗[A] C) x) =
      (ResidueField.map f x) ⊗ₜ[A'] (1 : B)
    exact he x
  · intro x
    exact he x
  · intro y
    have hh := hψe y
    rw [← DFunLike.congr_fun hcψ y] at hh
    exact hh.symm

/-- Base change along a local map inducing an isomorphism on residue fields
preserves the special fibre, compatibly with the map from the original algebra. -/
private theorem exists_tensorProduct_quotient_equiv
    {A A' C : Type*} [CommRing A] [IsLocalRing A]
    [CommRing A'] [IsLocalRing A'] [CommRing C]
    (f : A →+* A') [IsLocalHom f] (hf : Function.Bijective (ResidueField.map f))
    [Algebra A C] :
    letI : Algebra A A' := f.toAlgebra
    let T := C ⊗[A] A'
    let J := (maximalIdeal A').map
      (Algebra.TensorProduct.includeRight (R := A) (A := C) (B := A')).toRingHom
    ∃ e : T ⧸ J ≃+* ResidueField A ⊗[A] C,
      ∀ y : C, e (Ideal.Quotient.mk J (y ⊗ₜ[A] (1 : A'))) = 1 ⊗ₜ[A] y := by
  let : Algebra A A' := f.toAlgebra
  let : Algebra A (ResidueField A') := ((residue A').comp f).toAlgebra
  let ek : ResidueField A ≃ₐ[A] ResidueField A' :=
    { __ := RingEquiv.ofBijective (ResidueField.map f) hf
      commutes' := ResidueField.map_residue f }
  let e₁ := Algebra.TensorProduct.tensorQuotientEquiv (R := A) A A' C (maximalIdeal A')
  let e₂ := Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[A] C) ek.symm
  let e₃ := Algebra.TensorProduct.comm A C (ResidueField A)
  refine ⟨e₁.symm.toRingEquiv.trans (e₂.toRingEquiv.trans e₃.toRingEquiv), ?_⟩
  intro y
  change e₃ (e₂ (e₁.symm (Ideal.Quotient.mk _ (y ⊗ₜ[A] (1 : A'))))) = _
  rw [Algebra.TensorProduct.tensorQuotientEquiv_symm_apply_tmul]
  change ek.symm 1 ⊗ₜ[A] y = (1 : ResidueField A) ⊗ₜ[A] y
  rw [map_one]

/-- Quotients of a completed algebra by powers of an extended ideal agree
with the corresponding quotients before completion. -/
private theorem exists_quotient_completion_linearEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) (n : ℕ) :
    let D := AdicCompletion (I.map (algebraMap R S)) S
    Nonempty ((D ⧸ (I ^ n • (⊤ : Submodule R D))) ≃ₗ[R ⧸ I ^ n]
      (S ⧸ (I ^ n • (⊤ : Submodule R S)))) := by
  let J := I.map (algebraMap R S)
  let D := AdicCompletion J S
  have hD : ((J ^ n • (⊤ : Submodule S D)).restrictScalars R) =
      I ^ n • (⊤ : Submodule R D) := by
    rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq,
      Submodule.restrictScalars_top]
  have hS : ((J ^ n • (⊤ : Submodule S S)).restrictScalars R) =
      I ^ n • (⊤ : Submodule R S) := by
    rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq,
      Submodule.restrictScalars_top]
  let eD := (Submodule.quotEquivOfEq _ _ hD.symm).trans
    (Submodule.Quotient.restrictScalarsEquiv R (J ^ n • (⊤ : Submodule S D)))
  let eS := (Submodule.quotEquivOfEq _ _ hS.symm).trans
    (Submodule.Quotient.restrictScalarsEquiv R (J ^ n • (⊤ : Submodule S S)))
  let e := eD.trans (((AdicCompletion.quotPowSMulTopEquiv (hI.map _) S n).restrictScalars R).trans
    eS.symm)
  exact ⟨e.extendScalarsOfSurjective Ideal.Quotient.mk_surjective⟩

/-- A Noetherian local completion of a flat algebra is flat over the
Noetherian base if the ideal of completion is extended from the base. -/
@[ega "0 7.6.13" "special case"]
private theorem flat_adicCompletion_of_isNoetherian_local
    {R S : Type*} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S]
    (I : Ideal R)
    [IsNoetherianRing (AdicCompletion (I.map (algebraMap R S)) S)]
    [IsLocalRing (AdicCompletion (I.map (algebraMap R S)) S)] :
    Module.Flat R (AdicCompletion (I.map (algebraMap R S)) S) := by
  let D := AdicCompletion (I.map (algebraMap R S)) S
  have hflat (n : ℕ) : Module.Flat (R ⧸ I ^ (n + 1))
      (D ⧸ (I ^ (n + 1) • (⊤ : Submodule R D))) := by
    obtain ⟨e⟩ := exists_quotient_completion_linearEquiv (S := S) I
      I.fg_of_isNoetherianRing (n + 1)
    have : Module.Flat (R ⧸ I ^ (n + 1))
        (S ⧸ (I ^ (n + 1) • (⊤ : Submodule R S))) :=
      Module.Flat.of_linearEquiv
        ((TensorProduct.quotTensorEquivQuotSMul S (I ^ (n + 1))).symm.extendScalarsOfSurjective
          Ideal.Quotient.mk_surjective)
    exact Module.Flat.of_linearEquiv e
  have hK : I.map (algebraMap R D) ≤ maximalIdeal D := by
    have hcomp : IsAdicComplete (I.map (algebraMap R D)) D := by
      rw [show algebraMap R D = (algebraMap S D).comp (algebraMap R S) from
        (IsScalarTower.algebraMap_eq R S D), ← Ideal.map_map]
      exact AdicCompletion.isAdicComplete_self _ (I.fg_of_isNoetherianRing.map _)
    exact (IsAdicComplete.le_jacobson_bot _).trans (by
      exact (IsLocalRing.jacobson_eq_maximalIdeal (R := D) (I := ⊥) bot_ne_top).le)
  have : IsLocalization.AtPrime D (maximalIdeal D) :=
    IsLocalization.of_le_isUnit fun x hx => by
      exact not_not.mp hx
  have : IsLocalizedModule.AtPrime (maximalIdeal D) (LinearMap.id : D →ₗ[D] D) :=
    isLocalizedModule_id _ D D
  exact Module.Flat.of_flat_quotient_pow I D hflat (maximalIdeal D) hK D LinearMap.id

/-- Completeness for a positive power of an ideal implies completeness for
the ideal itself. -/
private theorem isAdicComplete_of_pow
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (k : ℕ) (hk : 1 ≤ k) [IsAdicComplete (I ^ k) M] :
    IsAdicComplete I M where
  haus' x hx := IsHausdorff.haus' (I := I ^ k) x (fun n => by
    simpa only [pow_mul] using hx (k * n))
  prec' f hf := by
    obtain ⟨l, hl⟩ := IsPrecomplete.prec' (I := I ^ k) (fun n => f (k * n))
      (fun {m n} hmn => by simpa only [pow_mul] using hf (Nat.mul_le_mul_left k hmn))
    refine ⟨l, fun n => ?_⟩
    have hn : n ≤ k * n := by simpa using Nat.mul_le_mul_right n hk
    have hln : f (k * n) ≡ l [SMOD I ^ (k * n) • (⊤ : Submodule R M)] := by
      simpa only [pow_mul] using hl n
    exact (hf hn).trans (hln.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hn)))

/-- A finite algebra over a complete local ring is complete along an ideal
whose power lies in the extended maximal ideal. -/
private theorem isAdicComplete_of_finite_of_pow_le
    {R S : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [CommRing S] [Algebra R S] [Module.Finite R S]
    (J : Ideal S) {k : ℕ} (hk : J ^ k ≤ (maximalIdeal R).map (algebraMap R S)) :
    IsAdicComplete J S := by
  have : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  have : IsAdicComplete (maximalIdeal R) S :=
    isAdicComplete_of_iInf_smul_eq_bot (maximalIdeal R)
      (IsHausdorff.iInf_pow_smul (inferInstance : IsHausdorff (maximalIdeal R) S))
  have hc : IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S :=
    (IsAdicComplete.map_algebraMap_iff (S := S) (maximalIdeal R) S).mpr inferInstance
  have : IsAdicComplete (J ^ (k + 1)) S :=
    isAdicComplete_of_le_of_fg_of_isAdicComplete
      ((Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk) hc
      (J ^ (k + 1)).fg_of_isNoetherianRing
  exact isAdicComplete_of_pow J (k + 1) (by omega)

/-- In a square with finite base map, a map surjective on the special fibre
is finite when the upper left ring is complete local. -/
private theorem finite_of_finite_base_of_surjective_specialFiber
    {A A' B C : Type*}
    [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [CommRing C] [IsNoetherianRing C] [IsLocalRing C]
    [IsAdicComplete (maximalIdeal C) C]
    (f : A →+* A') (g : A' →+* B) [IsLocalHom g]
    (a : A →+* C) [IsLocalHom a] (c : C →+* B)
    (hc : c.comp a = g.comp f) (hf : f.Finite)
    (hψ : Function.Surjective
      ((Ideal.Quotient.mk ((maximalIdeal A').map g)).comp c)) :
    c.Finite := by
  let : Algebra A A' := f.toAlgebra
  let : Algebra A C := a.toAlgebra
  have : Module.Finite A A' := hf
  let T := C ⊗[A] A'
  let i : A' →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let J := (maximalIdeal A').map i
  have hArt : IsArtinianRing (ResidueField A ⊗[A] A') :=
    IsArtinianRing.of_finite (ResidueField A) _
  let ek := Algebra.TensorProduct.quotIdealMapEquivQuotTensor A' (maximalIdeal A)
  have : IsArtinianRing (A' ⧸ (maximalIdeal A).map f) :=
    ek.symm.surjective.isArtinianRing (H := hArt)
  obtain ⟨k, hk⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient
    ((maximalIdeal A).map f)
  have hbase : i.comp f = (algebraMap C T).comp a := by
    ext r
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul r).symm
  have hpow : J ^ k ≤ (maximalIdeal C).map (algebraMap C T) := by
    calc
      J ^ k = ((maximalIdeal A') ^ k).map i := (Ideal.map_pow _ _ _).symm
      _ ≤ ((maximalIdeal A).map f).map i := Ideal.map_mono hk
      _ = ((maximalIdeal A).map a).map (algebraMap C T) := by
        rw [Ideal.map_map, hbase, ← Ideal.map_map]
      _ ≤ (maximalIdeal C).map (algebraMap C T) := Ideal.map_mono (map_maximalIdeal_le a)
  have : IsAdicComplete J T := isAdicComplete_of_finite_of_pow_le J hpow
  obtain ⟨t, htC, htA', hmap⟩ := exists_tensorProduct_map f g a c hc
  have hJ : J.map t = (maximalIdeal A').map g := hmap _
  have : IsHausdorff (J.map t) B := by
    rw [hJ]
    exact IsHausdorff.of_isLocalRing _ B (map_maximalIdeal_lt_top g).ne
  have ht : Function.Surjective t := by
    apply surjective_of_mk_map_comp_surjective (I := J) t
    rw [hJ]
    intro z
    obtain ⟨y, hy⟩ := hψ z
    refine ⟨algebraMap C T y, ?_⟩
    change Ideal.Quotient.mk _ (t (algebraMap C T y)) = z
    rw [show t (algebraMap C T y) = c y from DFunLike.congr_fun htC y]
    exact hy
  rw [← htC]
  exact (RingHom.Finite.of_surjective t ht).comp
    ((RingHom.finite_algebraMap).mpr (inferInstance : Module.Finite C T))

/-- Injectivity on the reduction before completion identifies the inverse
image of the ideal under any extension to the completion. -/
private theorem mem_map_of_quotient_extension
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (hI : I.FG) (f : R →+* S)
    (q : AdicCompletion I R →+* S)
    (hq : q.comp (algebraMap R (AdicCompletion I R)) = f)
    (hf : Function.Injective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map))
    (d : AdicCompletion I R) (hd : q d ∈ I.map f) :
    d ∈ I.map (algebraMap R (AdicCompletion I R)) := by
  let D := AdicCompletion I R
  let K := I.map (algebraMap R D)
  have hmap : K.map q = I.map f := by rw [Ideal.map_map, hq]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I d)
  have hz : d - algebraMap R D r ∈ K := by
    dsimp only [K, D]
    rw [← AdicCompletion.ker_evalOneₐ_eq_map I hI, RingHom.mem_ker, map_sub]
    change AdicCompletion.evalOneₐ I d - Ideal.Quotient.mk I r = 0
    exact sub_eq_zero.mpr hr.symm
  have hzq : q d - f r ∈ I.map f := by
    have hh := Ideal.mem_map_of_mem q hz
    rw [hmap, map_sub, show q (algebraMap R D r) = f r from DFunLike.congr_fun hq r] at hh
    exact hh
  have hfr : f r ∈ I.map f := by
    simpa only [sub_sub_cancel] using (I.map f).sub_mem hd hzq
  have hrI : r ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hf
    change Ideal.Quotient.mk (I.map f) (f r) =
      (Ideal.quotientMap (I.map f) f Ideal.le_comap_map) 0
    rw [map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hfr
  have hdr := K.add_mem hz (Ideal.mem_map_of_mem (algebraMap R D) hrI)
  simpa only [sub_add_cancel] using hdr

open Module.Flat in
/-- The local flatness criterion makes a map into a flat module injective
when its reduction modulo the maximal ideal is injective. -/
private theorem injective_of_flat_of_comap_maximalIdeal_le
    {R S B : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [CommRing B] [Algebra R B] [Module.Flat R B]
    (q : S →ₐ[R] B)
    (hq : ∀ s, q s ∈ (maximalIdeal R).map (algebraMap R B) →
      s ∈ (maximalIdeal R).map (algebraMap R S)) :
    Function.Injective q := by
  refine
    (injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing
      (S := S) q.toLinearMap ?_).1
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective _ z
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have hs : q s ∈ maximalIdeal R • (⊤ : Submodule R B) :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  have hqs : q s ∈ (maximalIdeal R).map (algebraMap R B) := by
    rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map]
    exact hs
  have hh := hq s hqs
  rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map] at hh
  exact hh

/-- **Stacks 07NS.** Consider local homomorphisms `A → A' → B` of Noetherian complete local
rings such that `A → A'` induces an isomorphism on residue fields. If the special fibre of `B`
over `A'` is formally smooth, then it is induced by an adically formally smooth Noetherian
complete local `A`-algebra `C` mapping locally to `B`.

The completed base change of `C` to `A'` is again Noetherian, complete, local, and flat over
`A'`, and its induced map to `B` is surjective. Moreover, `C → B` is surjective when `A → A'`
is, finite when `A → A'` is finite, and the completed base-change map is an isomorphism when
`A' → B` is flat. -/
@[stacks 07NS, ega "0 22.2.7" "(i)"]
public theorem exists_completeLocal_formallySmooth_lift_with_baseChange
    {A : Type u} {A' : Type v} {B : Type w}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing A'] [IsNoetherianRing A'] [IsLocalRing A']
    [IsAdicComplete (maximalIdeal A') A']
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [IsAdicComplete (maximalIdeal B) B]
    (f : A →+* A') [IsLocalHom f]
    (g : A' →+* B) [IsLocalHom g]
    (hf : Function.Bijective (ResidueField.map f))
    (hB : letI : Algebra A' B := g.toAlgebra
      RingHom.FormallySmoothNAdic.{max u v w}
        (algebraMap (ResidueField A') (ResidueField A' ⊗[A'] B))
        (maximalIdeal (ResidueField A' ⊗[A'] B))) :
    ∃ (C : Type (max u v w)) (_ : CommRing C) (_ : IsNoetherianRing C)
      (_ : IsLocalRing C) (_ : IsAdicComplete (maximalIdeal C) C)
      (a : A →+* C) (_ : IsLocalHom a)
      (c : C →+* B) (_ : IsLocalHom c),
      c.comp a = g.comp f ∧
      RingHom.FormallySmoothNAdic.{max u v w} a (maximalIdeal C) ∧
      (letI : Algebra A A' := f.toAlgebra
       letI : Algebra A' B := g.toAlgebra
       letI : Algebra A C := a.toAlgebra
       letI : Algebra (ResidueField A) (ResidueField A') := (ResidueField.map f).toAlgebra
       ∃ e : (ResidueField A ⊗[A] C) ≃ₐ[ResidueField A]
           (ResidueField A' ⊗[A'] B),
         (∀ x : ResidueField A,
           e (Algebra.TensorProduct.includeLeft (R := A) (S := ResidueField A)
             (A := ResidueField A) (B := C) x) =
             Algebra.TensorProduct.includeLeft (R := A') (S := ResidueField A')
               (A := ResidueField A') (B := B) (ResidueField.map f x)) ∧
         (∀ y : C,
           e (Algebra.TensorProduct.includeRight (R := A)
             (A := ResidueField A) (B := C) y) =
           Algebra.TensorProduct.includeRight (R := A')
             (A := ResidueField A') (B := B) (c y))) ∧
      (letI : Algebra A A' := f.toAlgebra
       letI : Algebra A C := a.toAlgebra
       let T := C ⊗[A] A'
       let iA' : A' →+* T :=
         (Algebra.TensorProduct.includeRight (R := A) (A := C) (B := A')).toRingHom
       let J : Ideal T := (maximalIdeal A').map iA'
       let D := AdicCompletion J T
       ∃ (t : T →+* B) (q : D →+* B)
         (_ : IsNoetherianRing D) (_ : IsLocalRing D),
         t.comp (Algebra.TensorProduct.includeLeft (R := A) (S := A)
           (A := C) (B := A')).toRingHom = c ∧
         t.comp iA' = g ∧
         q.comp (algebraMap T D) = t ∧
         IsAdicComplete (maximalIdeal D) D ∧
         ((algebraMap T D).comp iA').Flat ∧
         Function.Surjective q ∧
         (Function.Surjective f → Function.Surjective c) ∧
         (f.Finite → c.Finite) ∧
         (g.Flat → Function.Bijective q)) :=
  by
  obtain ⟨C, hC, hnC, hlC, hcomplC, a, hla, c, hlc, hca, ha, hF⟩ :=
    exists_completeLocal_lift_with_local_map f g hf hB
  let : CommRing C := hC
  have : IsNoetherianRing C := hnC
  have : IsLocalRing C := hlC
  have : IsAdicComplete (maximalIdeal C) C := hcomplC
  have : IsLocalHom a := hla
  have : IsLocalHom c := hlc
  refine ⟨C, hC, hnC, hlC, hcomplC, a, hla, c, hlc, hca, ha, hF, ?_⟩
  let : Algebra A A' := f.toAlgebra
  let : Algebra A C := a.toAlgebra
  let : Algebra A' B := g.toAlgebra
  let : Algebra (ResidueField A) (ResidueField A') := (ResidueField.map f).toAlgebra
  obtain ⟨e, _, heC⟩ := hF
  let T := C ⊗[A] A'
  let i : A' →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let J := (maximalIdeal A').map i
  let L := (maximalIdeal A').map g
  obtain ⟨t, htC, htA', htmap⟩ := exists_tensorProduct_map f g a c hca
  have hJL : J.map t = L := htmap _
  obtain ⟨eT, heT⟩ := exists_tensorProduct_quotient_equiv (C := C) f hf
  let eB := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A')
  let e₀ : T ⧸ J ≃+* B ⧸ L := (eT.trans e.toRingEquiv).trans eB.symm.toRingEquiv
  have hCT : Function.Surjective ((Ideal.Quotient.mk J).comp (algebraMap C T)) := by
    intro z
    obtain ⟨y, hy⟩ := Algebra.TensorProduct.includeRight_surjective C
      (residue_surjective (R := A)) (eT z)
    refine ⟨y, eT.injective ?_⟩
    exact (heT y).trans hy
  have he₀ (y : C) : e₀ (Ideal.Quotient.mk J (algebraMap C T y)) =
      Ideal.Quotient.mk L (c y) := by
    change eB.symm (e (eT (Ideal.Quotient.mk J (y ⊗ₜ[A] (1 : A'))))) = _
    rw [heT]
    change eB.symm (e (Algebra.TensorProduct.includeRight y)) = _
    rw [heC]
    exact eB.symm_apply_apply (Ideal.Quotient.mk L (c y))
  have hψ : Function.Surjective ((Ideal.Quotient.mk L).comp c) := by
    intro z
    obtain ⟨x, rfl⟩ := e₀.surjective z
    obtain ⟨y, rfl⟩ := hCT x
    exact ⟨y, (he₀ y).symm⟩
  let t₀ : T ⧸ J →+* B ⧸ L := Ideal.quotientMap L t
    (Ideal.map_le_iff_le_comap.mp hJL.le)
  have ht₀ : t₀ = e₀.toRingHom := by
    apply RingHom.ext
    intro z
    obtain ⟨y, rfl⟩ := hCT z
    change Ideal.Quotient.mk L (t (algebraMap C T y)) =
      e₀ (Ideal.Quotient.mk J (algebraMap C T y))
    rw [show t (algebraMap C T y) = c y from DFunLike.congr_fun htC y, he₀]
  have hnoethF : IsNoetherianRing (B ⧸ L) := inferInstance
  have hproperL : L ≠ ⊤ := (map_maximalIdeal_lt_top g).ne
  have : Nontrivial (B ⧸ L) := Ideal.Quotient.nontrivial_iff.mpr hproperL
  have : IsLocalRing (B ⧸ L) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk L) Ideal.Quotient.mk_surjective
  have : IsNoetherianRing (T ⧸ J) :=
    isNoetherianRing_of_ringEquiv (B ⧸ L) e₀.symm
  have : Nontrivial (T ⧸ J) := e₀.toRingHom.domain_nontrivial
  have : IsLocalRing (T ⧸ J) :=
    IsLocalRing.of_surjective' e₀.symm.toRingHom e₀.symm.surjective
  have : IsAdicComplete (maximalIdeal (B ⧸ L)) (B ⧸ L) :=
    isAdicComplete_of_surjective_07ns (Ideal.Quotient.mk L) Ideal.Quotient.mk_surjective
  have : IsAdicComplete (maximalIdeal (T ⧸ J)) (T ⧸ J) :=
    isAdicComplete_of_surjective_07ns e₀.symm.toRingHom e₀.symm.surjective
  have hJfg : J.FG := (maximalIdeal A').fg_of_isNoetherianRing.map i
  obtain ⟨hnD, hlD, hcD⟩ := adicCompletion_noetherian_completeLocal J hJfg
  let D := AdicCompletion J T
  have : IsNoetherianRing D := hnD
  have : IsLocalRing D := hlD
  have : IsAdicComplete L B :=
    isAdicComplete_of_le_maximalIdeal inferInstance (map_maximalIdeal_le g)
  have : IsAdicComplete (J.map t) B := hJL.symm ▸ inferInstance
  obtain ⟨q, hqt, hqsurj⟩ := exists_surjective_extension_to_adicCompletion J hJfg t (by
    rw [hJL]
    intro z
    obtain ⟨y, hy⟩ := hψ z
    refine ⟨algebraMap C T y, ?_⟩
    change Ideal.Quotient.mk L (t (algebraMap C T y)) = z
    rw [show t (algebraMap C T y) = c y from DFunLike.congr_fun htC y]
    exact hy)
  have : Module.Flat A C := flat_of_isFormallySmooth_maximalIdeal_adic a ha
  let : Algebra A' T := Algebra.TensorProduct.rightAlgebra
  let ec : T ≃ₐ[A'] A' ⊗[A] C :=
    { __ := (Algebra.TensorProduct.comm A C A').toRingEquiv
      commutes' := fun _ => rfl }
  have : Module.Flat A' T := Module.Flat.of_linearEquiv ec.toLinearEquiv
  have hflatD : Module.Flat A' D :=
    flat_adicCompletion_of_isNoetherian_local (S := T) (maximalIdeal A')
  have hA'D : algebraMap A' D = (algebraMap T D).comp i :=
    IsScalarTower.algebraMap_eq A' T D
  have hqg : q.comp (algebraMap A' D) = g := by
    rw [hA'D, ← RingHom.comp_assoc, hqt, htA']
  have : IsLocalHom (q.comp (algebraMap A' D)) := hqg.symm ▸ inferInstance
  have : IsLocalHom (algebraMap A' D) := isLocalHom_of_comp _ q
  refine ⟨t, q, hnD, hlD, htC, htA', hqt, hcD, ?_, hqsurj, ?_, ?_, ?_⟩
  · rw [← hA'D, RingHom.flat_algebraMap_iff]
    exact hflatD
  · exact fun h => surjective_of_surjective_base_of_surjective_specialFiber
      f g a c hca h hψ
  · exact fun h => finite_of_finite_base_of_surjective_specialFiber f g a c hca h hψ
  · intro hg
    have : Module.Flat A' B := hg
    let qa : D →ₐ[A'] B := { __ := q, commutes' := DFunLike.congr_fun hqg }
    refine ⟨injective_of_flat_of_comap_maximalIdeal_le qa ?_, hqsurj⟩
    intro d hd
    have hmod : Function.Injective (Ideal.quotientMap (J.map t) t Ideal.le_comap_map) := by
      have htinj (K : Ideal B) (hK : K = L) (h : J ≤ K.comap t) :
          Function.Injective (Ideal.quotientMap K t h) := by
        subst K
        change Function.Injective t₀
        rw [ht₀]
        exact e₀.injective
      exact htinj (J.map t) hJL Ideal.le_comap_map
    have hmem := mem_map_of_quotient_extension J hJfg t q hqt hmod d
      (by rwa [hJL])
    rw [hA'D, ← Ideal.map_map]
    exact hmem

end

end

end
