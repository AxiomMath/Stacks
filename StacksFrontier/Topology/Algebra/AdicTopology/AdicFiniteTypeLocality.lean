module

public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FiniteTypeComposition
public import StacksFrontier.RingTheory.Rig.RigSmoothStability
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeLocality

/-!
# Locality of adic morphisms of topologically finite type

On weakly admissible adic-star rings, being an adic homomorphism and topologically of finite
type is a local property of morphisms.  Over such rings adicness and tautness agree, so the
property coincides there with tautness together with topological finite type, whose locality is
already available; the only work is to transport the equivalence across the four corners of a
localization diagram and across a finite product of targets.

Locality is what upgrades the bare composition statement for such morphisms into stability of
the local property under composition, which is recorded here as well.

## Main results

* `TopologicalRing.adicAndFiniteType_propertyIsLocal`: adic morphisms of topologically finite
  type form a local property on weakly admissible adic-star rings.
* `TopologicalRing.adicAndFiniteType_propertyIsStableUnderComposition`: that local property is
  stable under composition.

## References

* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0GBS](https://stacks.math.columbia.edu/tag/0GBS)
* [Stacks Project, Tag 0ANH](https://stacks.math.columbia.edu/tag/0ANH)
* [Stacks Project, Tag 0GBZ](https://stacks.math.columbia.edu/tag/0GBZ)
-/

@[expose] public section

namespace TopologicalRing

universe u

open Filter
open scoped Topology

/-- The submodule of a product of rings cut out by requiring the coordinates in a given set to
lie in prescribed submodules. -/
private def piCoordinateSubmodule {ι : Type*} {A : ι → Type*}
    [∀ i, Ring (A i)] (S : Set ι) (J : ∀ i, Submodule (A i) (A i)) :
    Submodule (∀ i, A i) (∀ i, A i) where
  carrier := S.pi fun i => (J i : Set (A i))
  zero_mem' := by simp
  add_mem' hx hy i hi := (J i).add_mem (hx i hi) (hy i hi)
  smul_mem' r _ hx i hi := (J i).smul_mem (r i) (hx i hi)

/-- For a continuous homomorphism from an adic-star ring to a complete separated linearly
topologized ring, being adic and topologically of finite type is the same as being taut and
topologically of finite type. -/
private theorem adicAndFiniteType_iff_tautAndFiniteType
    {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] (φ : B →+* A)
    (hB : ∃ I : Ideal B, I.FG ∧ _root_.IsAdic I)
    (hAcomplete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hAT2 : T2Space A) :
    (RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) ↔
      (RingHom.IsTaut φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) :=
  and_congr (@RingHom.isAdic_iff_isTaut _ _ _ _ _ _ _ _ _ _ φ hB hAcomplete hAT2) Iff.rfl

/-- Adic morphisms of topologically finite type form a local property on weakly admissible
adic-star rings. -/
public theorem adicAndFiniteType_propertyIsLocal :
    TopologicalRing.AdicStarPropertyIsLocal.{u}
      (fun φ => RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hMap
    have hA'w : TopologicalRing.IsCountablyWeaklyAdmissible
        (TopologicalRing.CompletionOver D.toA') :=
      ⟨TopologicalRing.completionOver_isWeaklyAdmissible D.toA' D.weaklyAdmissibleA,
        TopologicalRing.completionOver_isCountablyGenerated_nhds_zero
          D.toA' D.weaklyAdmissibleA D.countableA⟩
    exact (adicAndFiniteType_iff_tautAndFiniteType D.completedMap hB'
      hA'w.1.2.1 hA'w.1.2.2).mpr <| tautAndFiniteType_localizationPreserves D
        ⟨D.weaklyAdmissibleA, D.countableA⟩ ⟨D.weaklyAdmissibleB, D.countableB⟩ hA'w
        ⟨TopologicalRing.completionOver_isWeaklyAdmissible D.toB' D.weaklyAdmissibleB,
          TopologicalRing.completionOver_isCountablyGenerated_nhds_zero
            D.toB' D.weaklyAdmissibleB D.countableB⟩
        ((adicAndFiniteType_iff_tautAndFiniteType D.map hB
          D.weaklyAdmissibleA.2.1 D.weaklyAdmissibleA.2.2).mp hMap)
  · intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hFF hCompleted
    have hA'w : TopologicalRing.IsCountablyWeaklyAdmissible
        (TopologicalRing.CompletionOver D.toA') :=
      ⟨TopologicalRing.completionOver_isWeaklyAdmissible D.toA' D.weaklyAdmissibleA,
        TopologicalRing.completionOver_isCountablyGenerated_nhds_zero
          D.toA' D.weaklyAdmissibleA D.countableA⟩
    exact (adicAndFiniteType_iff_tautAndFiniteType D.map hB
      D.weaklyAdmissibleA.2.1 D.weaklyAdmissibleA.2.2).mpr <|
        tautAndFiniteType_faithfullyFlatDescent D
          ⟨D.weaklyAdmissibleA, D.countableA⟩ ⟨D.weaklyAdmissibleB, D.countableB⟩ hA'w
          ⟨TopologicalRing.completionOver_isWeaklyAdmissible D.toB' D.weaklyAdmissibleB,
            TopologicalRing.completionOver_isCountablyGenerated_nhds_zero
              D.toB' D.weaklyAdmissibleB D.countableB⟩ hFF
          ((adicAndFiniteType_iff_tautAndFiniteType D.completedMap hB'
            hA'w.1.2.1 hA'w.1.2.2).mp hCompleted)
  · intro B _ _ _ _ hB hBcount ι _ A _ _ _ _ hAweak hAcount f hf hBstar _ hfProp
    let : ∀ i, UniformSpace (A i) := fun i => IsTopologicalAddGroup.rightUniformSpace (A i)
    have : ∀ i, CompleteSpace (A i) := fun i => (hAweak i).2.1
    have : ∀ i, T2Space (A i) := fun i => (hAweak i).2.2
    have : ∀ i, IsUniformAddGroup (A i) := fun _ => isUniformAddGroup_of_addCommGroup
    have : IsLinearTopology (∀ i, A i) (∀ i, A i) := pi_isLinearTopology
    have hcomplete :
        @CompleteSpace (∀ i, A i) (IsTopologicalAddGroup.rightUniformSpace (∀ i, A i)) := by
      rw [IsUniformAddGroup.rightUniformSpace_eq]
      infer_instance
    exact (adicAndFiniteType_iff_tautAndFiniteType (RingHom.pi f) hBstar
      hcomplete inferInstance).mpr <| tautAndFiniteType_finiteProductPreserves hB hBcount A hAweak
        hAcount f hf ⟨hB, hBcount⟩ (fun i => ⟨hAweak i, hAcount i⟩) fun i =>
          (adicAndFiniteType_iff_tautAndFiniteType (f i) hBstar (hAweak i).2.1
            (hAweak i).2.2).mp (hfProp i)

/-- A local property of morphisms at the class of rings `TopologicalRing.AdicStarPropertyIsLocal`
tests is a local property of morphisms of `WAdm^{adic*}`.

In an adic topological ring every ideal of definition defines the topology through its powers,
so a finitely generated one witnesses `∃ I : Ideal R, I.FG ∧ _root_.IsAdic I`; the three
locality axioms hypothesise membership of the class, so the implication follows. The converse
also holds, because every ring the axioms test is weakly admissible, and is recorded with this
implication in `TopologicalRing.adicStarPropertyIsLocal_iff_propertyIsLocalAdicStar`. -/
public theorem propertyIsLocalAdicStar_of_adicStarPropertyIsLocal
    {P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop}
    (hP : TopologicalRing.AdicStarPropertyIsLocal.{u} P) :
    TopologicalRing.PropertyIsLocalAdicStar.{u} P := by
  have key : ∀ {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], TopologicalRing.IsAdic R ∧
        (∃ I : Ideal R, TopologicalRing.IsIdealOfDefinition I ∧ I.FG) →
        ∃ I : Ideal R, I.FG ∧ _root_.IsAdic I := by
    rintro R _ _ _ _ ⟨hadic, I, hIdef, hIfg⟩
    exact ⟨I, hIfg, Rig.idealOfDefinition_isAdic_of_isAdicRing hadic I hIdef⟩
  refine ⟨?_, ?_, ?_⟩
  · intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hMap
    exact hP.localizationPreserves D (key hA) (key hB) (key hA') (key hB') hMap
  · intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hFF hCompleted
    exact hP.faithfullyFlatDescent D (key hA) (key hB) (key hA') (key hB') hFF hCompleted
  · intro B _ _ _ _ hB hBcount ι _ A _ _ _ _ hAweak hAcount f hf hBstar hAstar hfProp
    exact hP.finiteProduct hB hBcount A hAweak hAcount f hf (key hBstar)
      (fun i => key (hAstar i)) hfProp

/-- Adic morphisms of topologically finite type form a local property of morphisms of
`WAdm^{adic*}`, the adic topological rings with a finitely generated ideal of definition. This
is `TopologicalRing.adicAndFiniteType_propertyIsLocal` read at the class of rings Stacks 0ANH
names. -/
public theorem adicAndFiniteType_propertyIsLocalAdicStar :
    TopologicalRing.PropertyIsLocalAdicStar.{u}
      (fun φ => RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) :=
  propertyIsLocalAdicStar_of_adicStarPropertyIsLocal adicAndFiniteType_propertyIsLocal

/-- Adic morphisms of topologically finite type form a local property of morphisms of weakly
admissible adic-star rings which is stable under composition. -/
@[ega "I 10.13.5" "(i), special case"]
public theorem adicAndFiniteType_propertyIsStableUnderComposition :
    TopologicalRing.AdicStarPropertyIsStableUnderComposition.{u}
      (fun φ => RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) where
  isLocal := adicAndFiniteType_propertyIsLocal
  comp := fun _ _ _ _ _ _ f g hf _ hPf hPg =>
    TopologicalRing.isAdic_and_isTopologicallyOfFiniteType_comp f g hf hPf hPg

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Stability under base change at the class of rings `AdicStarPropertyIsStableUnderBaseChange`
tests implies stability under base change in the sense of the first half of **Stacks 0GBE**.

An object of `WAdm^{adic*}` is adic, so each of its ideals of definition defines the topology
through its powers, and a finitely generated one witnesses
`∃ I : Ideal R, I.FG ∧ _root_.IsAdic I`. The converse also holds, the rings tested being weakly
admissible; the equivalence is `TopologicalRing.adicStarPropertyIsStableUnderBaseChange_iff`. -/
public theorem isStableUnderBaseChangeAdicStar_of_adicStarProperty
    {P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop}
    (hP : TopologicalRing.AdicStarPropertyIsStableUnderBaseChange.{u} P) :
    TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar.{u} P where
  isLocal := propertyIsLocalAdicStar_of_adicStarPropertyIsLocal hP.isLocal
  baseChange := by
    intro B A C _ _ _ _ _ _ _ _ _ _ _ _ _ _ hBw hBstar hAw hAstar hCw hCstar hcA hcC hp
    obtain ⟨hBadic, IB, hIBdef, hIBfg⟩ := hBstar
    obtain ⟨hAadic, IA, hIAdef, hIAfg⟩ := hAstar
    obtain ⟨hCadic, IC, hICdef, hICfg⟩ := hCstar
    exact hP.baseChange hBw
      ⟨IB, hIBfg, Rig.idealOfDefinition_isAdic_of_isAdicRing hBadic IB hIBdef⟩ hAw
      ⟨IA, hIAfg, Rig.idealOfDefinition_isAdic_of_isAdicRing hAadic IA hIAdef⟩ hCw
      ⟨IC, hICfg, Rig.idealOfDefinition_isAdic_of_isAdicRing hCadic IC hICdef⟩ hcA hcC hp

end

/-- Stability under composition at the class of rings
`AdicStarPropertyIsStableUnderComposition` tests implies stability under composition in the
sense of **Stacks 0GBJ**. The converse also holds; the equivalence is
`TopologicalRing.adicStarPropertyIsStableUnderComposition_iff`. -/
public theorem isStableUnderCompositionAdicStar_of_adicStarProperty
    {P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop}
    (hP : TopologicalRing.AdicStarPropertyIsStableUnderComposition.{u} P) :
    TopologicalRing.PropertyIsStableUnderCompositionAdicStar.{u} P where
  isLocal := propertyIsLocalAdicStar_of_adicStarPropertyIsLocal hP.isLocal
  comp := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hA hB hC hAstar hBstar hCstar f g hf hg hPf hPg
    obtain ⟨hAadic, IA, hIAdef, hIAfg⟩ := hAstar
    obtain ⟨hBadic, IB, hIBdef, hIBfg⟩ := hBstar
    obtain ⟨hCadic, IC, hICdef, hICfg⟩ := hCstar
    exact hP.comp hA hB hC
      ⟨IA, hIAfg, Rig.idealOfDefinition_isAdic_of_isAdicRing hAadic IA hIAdef⟩
      ⟨IB, hIBfg, Rig.idealOfDefinition_isAdic_of_isAdicRing hBadic IB hIBdef⟩
      ⟨IC, hICfg, Rig.idealOfDefinition_isAdic_of_isAdicRing hCadic IC hICdef⟩ f g hf hg hPf hPg

/-- Adic morphisms of topologically finite type form a local property of morphisms of
`WAdm^{adic*}` which is stable under composition in the sense of Stacks 0GBJ. This is
`TopologicalRing.adicAndFiniteType_propertyIsStableUnderComposition` read at the class of
rings the source names. -/
@[ega "I 10.13.5" "(i), special case"]
public theorem adicAndFiniteType_propertyIsStableUnderCompositionAdicStar :
    TopologicalRing.PropertyIsStableUnderCompositionAdicStar.{u}
      (fun φ => RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) :=
  isStableUnderCompositionAdicStar_of_adicStarProperty
    adicAndFiniteType_propertyIsStableUnderComposition

end TopologicalRing

end
