module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.RigEtaleLocality
public import StacksFrontier.RingTheory.Rig.RigSmoothLocalityRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicFiniteTypeIsLocalRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined

/-!
# Rig-étaleness is a local property of arrows of `WAdm^Noeth`

## Main results

* `Rig.rigEtale_isomorphismInvariant`: rig-étaleness of an arrow of Noetherian adic rings is
  invariant under isomorphisms of its source and of its target.
* `Rig.rigEtale_isLocalNoetherian'`: rig-étaleness is a local property of arrows of
  `WAdm^Noeth`, provided the annihilation condition `Rig.RigEtaleCondition` ascends along completed
  étale localizations, descends along faithfully flat ones and is preserved by finite products.
-/

@[expose] public noncomputable section

open CategoryTheory Filter
open scoped Topology

namespace Rig

attribute [local instance] HasDerivedCategory.standard

universe u v

/-- **Rig-étaleness is independent of the topological-ring presentations of its source and its
target.** Rig-étaleness of a continuous ring map of Noetherian adic rings is invariant under
isomorphisms of topological rings of its source and of its target. -/
public theorem rigEtale_isomorphismInvariant :
    TopologicalRing.IsomorphismInvariant.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigEtaleArrow φ)
      (fun R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] ↦
        TopologicalRing.IsNoetherianAdic R) := by
  refine TopologicalRing.IsomorphismInvariant.of_comp_of_ringEquiv ?_ ?_
  · intro X Y Z _ _ _ _ _ _ _ _ _ _ _ _ hX hY hZ f g hf hg hPf hPg _ _ _ _
    have : IsNoetherianRing Y := hY.2
    exact ⟨hf.comp hg, rigEtale_comp hX.1 hY.1 hZ.1 f g hf hg hPf.2 hPg.2⟩
  · intro X Y _ _ _ _ _ _ _ _ e hX hY he hes
    exact isRigEtaleArrow_of_ringEquiv e hX hY he hes

/-- For a continuous arrow of Noetherian adic rings, "adic finite-type algebra for every ideal of
definition" is equivalent to being adic and topologically of finite type. -/
private theorem finiteTypeAdicAlgebra_iff_isAdic_and_ft {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B) (hA : TopologicalRing.IsNoetherianAdic A)
    (hB : TopologicalRing.IsNoetherianAdic B) :
    Rig.FiniteTypeAdicAlgebraForEveryIdeal φ ↔
      RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ :=
  (Rig.adicFiniteType_tfae φ hA.1 hB.1 (exists_idealOfDefinition_fg hA.1 hA.2)
    (exists_idealOfDefinition_fg hB.1 hB.2)).out 6 1

/-- A continuous rig-étale arrow of adic rings satisfies the annihilation condition. -/
private theorem rigEtaleCondition_of_isRigEtale {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing B]
    (φ : A →+* B) (hφ : Continuous φ) (hA : TopologicalRing.IsAdic A)
    (hB : TopologicalRing.IsAdic B) (h : RingHom.IsRigEtale φ) : Rig.RigEtaleCondition φ := by
  intro _ _ _ _ _ J hJ
  exact (RingHom.IsRigEtale.forall_idealOfDefinition h hφ hA hB J hJ).2.2

/-- **Stacks 0AQL.** Rig-étaleness is a local property of arrows of `WAdm^Noeth`: it is
independent of the presentations of its source and target, ascends along a completed étale
localization diagram, descends along one whose target-side horizontal map is faithfully flat,
and is preserved by finite products of targets, provided the annihilation condition
`Rig.RigEtaleCondition` has the last three of these properties. -/
public theorem rigEtale_isLocalNoetherian'
    (hcond : TopologicalRing.PropertyIsLocalNoetherian'.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        Rig.RigEtaleCondition φ)) :
    TopologicalRing.PropertyIsLocalNoetherian'.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigEtaleArrow φ) := by
  refine ⟨rigEtale_isomorphismInvariant, ?_, ?_, ?_⟩
  · intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hP _ _ _ _
    have : IsNoetherianRing A := hA.2
    have : IsNoetherianRing B := hB.2
    obtain ⟨-, hft, hex⟩ : Continuous D.map ∧ RingHom.IsRigEtale D.map := hP
    have hone := (finiteTypeAdicAlgebra_iff_isAdic_and_ft D.map hB hA).mp hft
    have hcomp := TopologicalRing.adicTopologicallyFiniteType_isLocal'.localizationPreserves
      D (exists_fg_isAdic hA.1 hA.2) (exists_fg_isAdic hB.1 hB.2)
      (exists_fg_isAdic hA'.1 hA'.2) (exists_fg_isAdic hB'.1 hB'.2) hone
    have hft' := (finiteTypeAdicAlgebra_iff_isAdic_and_ft D.completedMap hB' hA').mpr hcomp
    have hPc := rigEtaleCondition_of_isRigEtale D.map D.continuousMap hB.1 hA.1 ⟨hft, hex⟩
    obtain ⟨I', hI', -⟩ := hB'.1.1
    exact ⟨D.continuousCompletedMap, hft', I', hI',
      isRigEtaleOver_of_isRigEtale D.completedMap hft' I' hI'
        (hcond.localizationPreserves D hA hB hA' hB' hPc hft' I' hI')⟩
  · intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hFF hP _ _ _ _
    have : IsNoetherianRing (TopologicalRing.CompletionOver D.toA') := hA'.2
    have : IsNoetherianRing (TopologicalRing.CompletionOver D.toB') := hB'.2
    obtain ⟨-, hft', hex'⟩ : Continuous D.completedMap ∧ RingHom.IsRigEtale D.completedMap := hP
    have hone' := (finiteTypeAdicAlgebra_iff_isAdic_and_ft D.completedMap hB' hA').mp hft'
    have hcomp := TopologicalRing.adicTopologicallyFiniteType_isLocal'.faithfullyFlatDescent
      D (exists_fg_isAdic hA.1 hA.2) (exists_fg_isAdic hB.1 hB.2)
      (exists_fg_isAdic hA'.1 hA'.2) (exists_fg_isAdic hB'.1 hB'.2) hFF hone'
    have hft := (finiteTypeAdicAlgebra_iff_isAdic_and_ft D.map hB hA).mpr hcomp
    have hPc := rigEtaleCondition_of_isRigEtale D.completedMap D.continuousCompletedMap
      hB'.1 hA'.1 ⟨hft', hex'⟩
    obtain ⟨I, hI, -⟩ := hB.1.1
    exact ⟨D.continuousMap, hft, I, hI,
      isRigEtaleOver_of_isRigEtale D.map hft I hI
        (hcond.faithfullyFlatDescent D hA hB hA' hB' hFF hPc hft I hI)⟩
  · intro B _ _ _ _ hBweak hBcount ι _ A _ _ _ _ hAweak hAcount f hf hCB hCA hPi _ _ _ _
    have : IsNoetherianRing B := hCB.2
    have : ∀ i, IsNoetherianRing (A i) := fun i ↦ (hCA i).2
    have hPi' : ∀ i, Continuous (f i) ∧ RingHom.IsRigEtale (f i) := fun i ↦ hPi i
    have hprodadic : TopologicalRing.IsAdic (∀ i, A i) := isAdic_pi A fun i ↦ (hCA i).1
    have hone := fun i ↦
      (finiteTypeAdicAlgebra_iff_isAdic_and_ft (f i) hCB (hCA i)).mp (hPi' i).2.1
    have hcomp := TopologicalRing.adicTopologicallyFiniteType_isLocal'.finiteProduct
      hBweak hBcount A hAweak hAcount f hf (exists_fg_isAdic hCB.1 hCB.2)
      (fun i ↦ exists_fg_isAdic (hCA i).1 (hCA i).2) hone
    have hft := (finiteTypeAdicAlgebra_iff_isAdic_and_ft (RingHom.pi f) hCB
      ⟨hprodadic, inferInstance⟩).mpr hcomp
    have hPc : ∀ i, Rig.RigEtaleCondition (f i) := fun i ↦
      rigEtaleCondition_of_isRigEtale (f i) (hf i) hCB.1 (hCA i).1 (hPi' i).2
    obtain ⟨I, hI, -⟩ := hCB.1.1
    exact ⟨continuous_pi hf, hft, I, hI,
      isRigEtaleOver_of_isRigEtale (RingHom.pi f) hft I hI
        (hcond.finiteProduct hBweak hBcount A hAweak hAcount f hf hCB hCA hPc hft I hI)⟩

end Rig

end
