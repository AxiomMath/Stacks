module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.RigEtaleSurjection
public import StacksFrontier.RingTheory.Rig.RigSmooth
public import StacksFrontier.RingTheory.Rig.RigSmoothLocality
public import StacksFrontier.RingTheory.Rig.RigSmoothTower
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicFiniteTypeIsLocalRefined
public import StacksFrontier.RingTheory.Rig.FlatIsLocalRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMapRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined

/-!
# Rig-smoothness is a local property of arrows of `WAdm^Noeth`: the refined forms

Strengthened forms of results of `StacksFrontier.RingTheory.Rig.RigSmoothLocality`, together with
further results on the locality of rig-smoothness. A strengthened form of a declaration of that
module carries the primed name of the original.
-/

@[expose] public noncomputable section

open CategoryTheory Filter TopologicalRing Rig.CompletedPolynomialPresentation
open scoped Topology TensorProduct

namespace Rig

attribute [local instance] HasDerivedCategory.standard

universe u

/-! ### Presentation independence -/

/-- **A bicontinuous ring isomorphism of Noetherian adic topological rings presents its target
as a rig-étale adic algebra of finite type over any ideal of definition of its source.**  Such
an isomorphism is adic and topologically of finite type, hence satisfies condition (6) of
Stacks 0GBW by `Rig.adicFiniteType_tfae`; and it exhibits its target as a surjective quotient
with zero kernel, so the criterion of Stacks 0GD4 is met with exponent zero. -/
public theorem exists_isRigEtale_adicFiniteTypeAlgebra_of_ringEquiv {X Y : Type u}
    [CommRing X] [TopologicalSpace X] [IsTopologicalRing X] [IsLinearTopology X X]
    [IsNoetherianRing X]
    [CommRing Y] [TopologicalSpace Y] [IsTopologicalRing Y] [IsLinearTopology Y Y]
    [IsNoetherianRing Y]
    (e : X ≃+* Y) (hX : TopologicalRing.IsNoetherianAdic X)
    (hY : TopologicalRing.IsNoetherianAdic Y)
    (he : Continuous e) (hes : Continuous e.symm) :
    ∃ (hft : FiniteTypeAdicAlgebraForEveryIdeal e.toRingHom) (I : Ideal X)
      (hI : TopologicalRing.IsIdealOfDefinition I),
      IsRigEtale (adicFiniteTypeAlgebra e.toRingHom hft I hI) := by
  obtain ⟨⟨I, hIdef, hIadic⟩, hT2, hCompl⟩ := hX.1
  have hadic : _root_.RingHom.IsAdic e.toRingHom :=
    ⟨I, hIadic, RingHom.isAdic_ideal_map_of_ringEquiv e he hes I hIadic⟩
  have hone : _root_.RingHom.IsAdic e.toRingHom ∧
      TopologicalRing.IsTopologicallyOfFiniteType e.toRingHom :=
    ⟨hadic, isTopologicallyOfFiniteType_of_surjective e.toRingHom e.surjective⟩
  have hft : FiniteTypeAdicAlgebraForEveryIdeal e.toRingHom :=
    ((adicFiniteType_tfae e.toRingHom he hX.1 hY.1 (exists_idealOfDefinition_fg hX.1 hX.2)
      (exists_idealOfDefinition_fg hY.1 hY.2)).out 1 6).mp hone
  refine ⟨hft, I, hIdef, ?_⟩
  let _ : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  have _ : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  let _ : IsAdicComplete I X := (IsAdic.isAdicComplete_iff hIadic).mpr ⟨hCompl, hT2⟩
  refine (isRigEtale_iff_exists_pow_mul_ker_le_sq
    (adicFiniteTypeAlgebra e.toRingHom hft I hIdef) e.surjective).mpr ⟨0, ?_⟩
  intro a _ y hy
  have h0 : e y = 0 := _root_.RingHom.mem_ker.mp hy
  have hy0 : y = 0 := e.injective (show e y = e 0 by rw [h0, map_zero])
  subst hy0
  simp

/-- **A bicontinuous ring isomorphism of Noetherian adic topological rings is rig-étale**
(Stacks 0GCV): it satisfies condition (6) of Stacks 0GBW and is rig-étale over an ideal of
definition of its source by `Rig.exists_isRigEtale_adicFiniteTypeAlgebra_of_ringEquiv`. -/
public theorem isRigEtaleArrow_of_ringEquiv {X Y : Type u}
    [CommRing X] [TopologicalSpace X] [IsTopologicalRing X] [IsLinearTopology X X]
    [CommRing Y] [TopologicalSpace Y] [IsTopologicalRing Y] [IsLinearTopology Y Y]
    (e : X ≃+* Y) (hX : TopologicalRing.IsNoetherianAdic X)
    (hY : TopologicalRing.IsNoetherianAdic Y)
    (he : Continuous e) (hes : Continuous e.symm) :
    RingHom.IsRigEtaleArrow e.toRingHom := by
  intro _ _ _ _
  obtain ⟨hft, I, hI, h⟩ :=
    exists_isRigEtale_adicFiniteTypeAlgebra_of_ringEquiv e hX hY he hes
  exact ⟨he, RingHom.isRigEtale_of_isRigEtaleOver hft I hI
    (isRigEtaleOver_of_isRigEtale_adicFiniteTypeAlgebra e.toRingHom hft I hI h)⟩

/-- **A bicontinuous ring isomorphism of Noetherian adic topological rings is rig-smooth**
(Stacks 0GCJ): it is rig-étale, and a rig-étale adic algebra of finite type is rig-smooth by
Stacks 0GB1. -/
public theorem isRigSmoothArrow_of_ringEquiv {X Y : Type u}
    [CommRing X] [TopologicalSpace X] [IsTopologicalRing X] [IsLinearTopology X X]
    [CommRing Y] [TopologicalSpace Y] [IsTopologicalRing Y] [IsLinearTopology Y Y]
    (e : X ≃+* Y) (hX : TopologicalRing.IsNoetherianAdic X)
    (hY : TopologicalRing.IsNoetherianAdic Y)
    (he : Continuous e) (hes : Continuous e.symm) :
    RingHom.IsRigSmoothArrow e.toRingHom := by
  intro _ _ _ _
  obtain ⟨hft, I, hI, h⟩ :=
    exists_isRigEtale_adicFiniteTypeAlgebra_of_ringEquiv e hX hY he hes
  exact ⟨he, hft, I, hI, isRigSmooth_of_isRigEtale _ h⟩

/-- **Rig-smoothness is independent of the topological-ring presentations of its source and its
target.**  Both directions of the equivalence are compositions with the isomorphisms and their
inverses, which are rig-smooth by `Rig.isRigSmoothArrow_of_ringEquiv`; rig-smoothness is stable
under composition by Stacks 0GCM. -/
public theorem rigSmooth_isomorphismInvariant :
    TopologicalRing.IsomorphismInvariant.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigSmoothArrow φ)
      (fun R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] ↦
        TopologicalRing.IsNoetherianAdic R) := by
  refine TopologicalRing.IsomorphismInvariant.of_comp_of_ringEquiv ?_ ?_
  · intro X Y Z _ _ _ _ _ _ _ _ _ _ _ _ hX hY hZ f g hf hg hPf hPg
    exact rigSmooth_comp hX hY hZ f g hf hg hPf hPg
  · intro X Y _ _ _ _ _ _ _ _ e hX hY he hes
    exact isRigSmoothArrow_of_ringEquiv e hX hY he hes

/-- **Stacks 0GCK.** Rig-smoothness is a local property of arrows of `WAdm^Noeth`: it is
independent of the presentations of its source and target, ascends along a completed étale
localization diagram, descends along one whose target-side horizontal map is faithfully flat,
and is preserved by finite products of targets. -/
@[stacks 0GCK]
public theorem rigSmooth_isLocalNoetherian' :
    TopologicalRing.PropertyIsLocalNoetherian'.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigSmoothArrow φ) :=
  ⟨rigSmooth_isomorphismInvariant, rigSmooth_localizationPreserves,
    rigSmooth_faithfullyFlatDescent, rigSmooth_finiteProductPreserves⟩

end Rig

end
