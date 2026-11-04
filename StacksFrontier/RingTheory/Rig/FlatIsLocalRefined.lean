module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FiniteTypeComposition
public import StacksFrontier.RingTheory.Rig.AdicCompletionMap
public import StacksFrontier.RingTheory.Rig.FiniteType
public import StacksFrontier.RingTheory.Rig.FlatDescent
public import StacksFrontier.RingTheory.Rig.FlatEtaleLocalization
public import StacksFrontier.RingTheory.Rig.FlatIsLocal
public import StacksFrontier.RingTheory.Rig.FlatJacobson
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicFiniteTypeIsLocalRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeIsLocalRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.FlatLocalPropertyRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianAdic
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMapRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined

/-!
# Rig-flatness is a local property of morphisms of Noetherian adic rings: the refined forms

We show that rig-flatness is independent of the topological-ring presentations of the source
and target, and that it is a local property of arrows of `WAdm^Noeth`.

## Main results

* `rigFlat_isomorphismInvariant`: Rig-flatness is invariant under isomorphisms of the source
  and target.
* `rigFlat_isLocalNoetherian'`: Rig-flatness is a local property of arrows of `WAdm^Noeth`.
-/

@[expose] public section

open TopologicalRing

universe u

namespace Rig

section EtaleQuotient

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsNoetherianRing B] [CommRing A] (f : B →+* A)
  {I : Ideal B} (hI : TopologicalRing.IsIdealOfDefinition I) (hIadic : _root_.IsAdic I)

end EtaleQuotient


section CanonicalMap

end CanonicalMap

section Local

section Pi

/-! ### Finite products -/

namespace RingHom

end RingHom

end Pi

/-! ### Presentation independence -/

/-- A surjective ring homomorphism is topologically of finite type. -/
theorem isTopologicallyOfFiniteType_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace S] (φ : R →+* S) (hφ : Function.Surjective φ) :
    TopologicalRing.IsTopologicallyOfFiniteType φ := by
  refine ⟨0, MvPolynomial.eval₂Hom φ (fun i : Fin 0 ↦ Fin.elim0 i), ?_, ?_⟩
  · ext x
    simp
  · refine Function.Surjective.denseRange fun y ↦ ?_
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨MvPolynomial.C x, by simp⟩

/-- The reduction of a ring isomorphism modulo an ideal and its image is bijective. -/
private theorem bijective_quotientMap_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) :
    Function.Bijective
      (Ideal.quotientMap (I.map e.toRingHom) e.toRingHom Ideal.le_comap_map) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective] at hx
    obtain ⟨b, hb, hba⟩ := hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (e.injective hba ▸ hb)
  · intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk I (e.symm b), by rw [Ideal.quotientMap_mk]; simp⟩

/-- Given a commutative square of Noetherian adic rings whose horizontal maps are isomorphisms
of topological rings, if the left vertical map is rig-flat then so is the right one. -/
private theorem isRigFlat_of_ringEquiv_square {B A B' A' : Type u}
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B'] [TopologicalSpace B'] [IsTopologicalRing B'] [IsLinearTopology B' B']
    [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
    (eB : B ≃+* B') (eA : A ≃+* A')
    (heB : Continuous eB) (heBs : Continuous eB.symm)
    (heA : Continuous eA) (heAs : Continuous eA.symm)
    (f : B →+* A) (g : B' →+* A') (hf : Continuous f)
    (hsq : eA.toRingHom.comp f = g.comp eB.toRingHom)
    (hB : TopologicalRing.IsNoetherianAdic B) (hA : TopologicalRing.IsNoetherianAdic A)
    (hB' : TopologicalRing.IsNoetherianAdic B') (hA' : TopologicalRing.IsNoetherianAdic A')
    (h : RingHom.IsRigFlat f) : RingHom.IsRigFlat g := by
  have : IsNoetherianRing B := hB.2
  have : IsNoetherianRing A := hA.2
  have : IsNoetherianRing B' := hB'.2
  have : IsNoetherianRing A' := hA'.2
  have hg : g = (eA.toRingHom.comp f).comp eB.symm.toRingHom := by
    rw [hsq]
    ext x
    simp
  have hgcont : Continuous g := by
    rw [hg]
    exact (heA.comp hf).comp heBs
  have hgadic : _root_.RingHom.IsAdic g := by
    rw [hg]
    exact (RingHom.isAdic_comp_ringEquiv_iff eB eA heB heBs heA heAs f).mp h.1
  have hgft : TopologicalRing.IsTopologicallyOfFiniteType g := by
    rw [hg]
    exact (TopologicalRing.isTopologicallyOfFiniteType_isomorphismInvariant
      (fun _ ↦ True) eB eA heB heBs heA heAs f hf trivial trivial trivial trivial).mp h.2.1
  obtain ⟨I, hIdef, hIadic⟩ := hB.1.1
  obtain ⟨J, -, hJadic⟩ := hA.1.1
  exact isRigFlat_of_flat_etale_square
    (weaklyAdmissible_of_isAdicRing hB.1) (weaklyAdmissible_of_isAdicRing hB'.1)
    (weaklyAdmissible_of_isAdicRing hA.1) (weaklyAdmissible_of_isAdicRing hA'.1)
    f g eB.toRingHom eA.toRingHom hsq.symm hf hgcont heB heA
    h.1 hgadic ⟨I, hIadic, RingHom.isAdic_ideal_map_of_ringEquiv eB heB heBs I hIadic⟩
    ⟨J, hJadic, RingHom.isAdic_ideal_map_of_ringEquiv eA heA heAs J hJadic⟩
    h.2.1 hgft (isTopologicallyOfFiniteType_of_surjective _ eB.surjective)
    (isTopologicallyOfFiniteType_of_surjective _ eA.surjective)
    (_root_.RingHom.Flat.of_bijective eB.bijective)
    (_root_.RingHom.Flat.of_bijective eA.bijective)
    I hIdef h (RingHom.Etale.of_bijective (bijective_quotientMap_of_ringEquiv eB I))

/-- **Rig-flatness is independent of the topological-ring presentations of its source and its
target.** -/
theorem rigFlat_isomorphismInvariant :
    TopologicalRing.IsomorphismInvariant.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigFlat φ)
      (fun R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] ↦
        TopologicalRing.IsNoetherianAdic R) := by
  intro B A B' A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  intro eB eA heB heBs heA heAs f hf hB hA hB' hA'
  exact ⟨isRigFlat_of_ringEquiv_square eB eA heB heBs heA heAs f _ hf (by ext; simp)
      hB hA hB' hA',
    isRigFlat_of_ringEquiv_square eB.symm eA.symm heBs (by simpa using heB) heAs
      (by simpa using heA) _ f ((heA.comp hf).comp heBs) (by ext; simp) hB' hA' hB hA⟩

/-- **Rig-flatness is a local property of arrows of `WAdm^Noeth`**: it is
independent of the presentations of its source and target, ascends along completed étale
localization diagrams, descends along faithfully flat ones, and is preserved by finite products
of targets. -/
@[stacks 0GGU]
theorem rigFlat_isLocalNoetherian' :
    TopologicalRing.PropertyIsLocalNoetherian'
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigFlat φ) where
  isomorphismInvariant := rigFlat_isomorphismInvariant
  localizationPreserves := rigFlat_localizationPreserves
  faithfullyFlatDescent := rigFlat_faithfullyFlatDescent
  finiteProduct := rigFlat_finiteProductPreserves

end Local

end Rig

end
