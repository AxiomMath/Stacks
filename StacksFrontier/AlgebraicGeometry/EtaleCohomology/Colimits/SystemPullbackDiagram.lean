module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageOfPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackComparison

/-!
# The diagram of inverse images of a system of sheaves along the projections of a cone

Let `(X_i, f_{i'i})` be an inverse system of schemes over a preordered set `I`, let
`(𝓕_i, φ_{i'i})` be a system of abelian sheaves on it (Stacks 0EZL) and let `f_i : X ⟶ X_i` be
the projections of a cone over the system. The inverse images `f_i⁻¹𝓕_i` on the small étale site
of `X`, with the maps `f_{i'}⁻¹ φ_{i'i} : f_i⁻¹𝓕_i = f_{i'}⁻¹ f_{i'i}⁻¹ 𝓕_i ⟶ f_{i'}⁻¹𝓕_{i'}`,
form a diagram of sheaves, and the sheaf `𝓕 = colim f_i⁻¹𝓕_i` of Stacks 09YQ is its colimit.

That these maps form a *functor* needs the identity law `φ_{ii} = id`, which is part of the
notion of a system over a preordered set (Stacks 0020, a directed system has identity transition
maps) but not of the cocycle condition alone; it is recorded here as
`Stacks.EtaleCohomology.EtaleSheafSystem.IsUnital`.

## Main definitions

* `Stacks.EtaleCohomology.EtaleSheafSystem.transition`: the transition map of a system in adjoint
  form `𝓕_j ⟶ f_{a,*}𝓕_i`.
* `Stacks.EtaleCohomology.EtaleSheafSystem.IsUnital`: the identity law of a system.
* `Stacks.EtaleCohomology.EtaleSheafSystem.pullbackDiagram`: the diagram `i ↦ f_i⁻¹𝓕_i`.

## Main results

* `Stacks.EtaleCohomology.EtaleSheafSystem.transition_comp`: the cocycle condition in adjoint
  form.
* `Stacks.EtaleCohomology.EtaleSheafSystem.pullbackDiagramMap_eq`: the maps of the diagram in
  adjoint form.
* `Stacks.EtaleCohomology.directImageSystem_isUnital`: the system of direct images of a sheaf on
  the limit is unital.

## Implementation notes

All compatibilities are checked on the side of direct images, where composites of base changes
are compared by the explicit isomorphisms `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'`,
and then transported to inverse images through the adjunctions; this is how
`Stacks.EtaleCohomology.directImageSystem` is treated as well.

## References

* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}

namespace EtaleSheafSystem

variable {A : Type*} [Category* A]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint] (F : EtaleSheafSystem D A)

/-- The transition map of a system of sheaves in adjoint form,
`𝓕_j ⟶ f_{a,*}𝓕_i` for `a : i ⟶ j`. -/
def transition {i j : Iᵒᵖ} (a : i ⟶ j) :
    F.obj j ⟶ (systemPushforward D A a).obj (F.obj i) :=
  (systemAdjunction D A a).homEquiv _ _ (F.map a)

/-- The map `F.map a : f_a⁻¹𝓕_j ⟶ 𝓕_i` of a system is the adjoint of its transition map
`Stacks.EtaleCohomology.EtaleSheafSystem.transition`. -/
lemma map_eq_transition {i j : Iᵒᵖ} (a : i ⟶ j) :
    F.map a = ((systemAdjunction D A a).homEquiv _ _).symm (F.transition a) :=
  (((systemAdjunction D A a).homEquiv _ _).symm_apply_apply _).symm

/-- **The cocycle condition in adjoint form.** -/
lemma transition_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    F.transition (a ≫ b) =
      F.transition b ≫ (systemPushforward D A b).map (F.transition a) ≫
        (systemPushforwardComp D A a b).hom.app (F.obj i) := by
  have h := leftAdjointCompIso_inv_homEquiv_symm (systemAdjunction D A b)
    (systemAdjunction D A a) (systemAdjunction D A (a ≫ b))
    (systemPushforwardComp D A a b) (F.transition b) (F.transition a)
  rw [← map_eq_transition, ← map_eq_transition] at h
  have h' : F.map (a ≫ b) = ((systemAdjunction D A (a ≫ b)).homEquiv _ _).symm
      (F.transition b ≫ (systemPushforward D A b).map (F.transition a) ≫
        (systemPushforwardComp D A a b).hom.app (F.obj i)) :=
    (F.map_comp a b).symm.trans h
  rw [transition, h', Equiv.apply_symm_apply]

/-- **The identity law** of a system of sheaves: the transition map attached to an
identity index is, in adjoint form, the canonical identification of the direct image along the
identity with the sheaf. -/
def IsUnital : Prop :=
  ∀ i : Iᵒᵖ, F.transition (𝟙 i) = (systemPushforwardId D A i).inv.app (F.obj i)

end EtaleSheafSystem

/-- The system of direct images of a sheaf on the limit is unital. -/
lemma directImageSystem_isUnital (c : Cone D)
    (𝓕 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}) :
    (directImageSystem D Ab.{u + 1} c 𝓕).IsUnital :=
  directImageSystem_map_id D Ab.{u + 1} c 𝓕

namespace EtaleSheafSystem

variable (F : EtaleSheafSystem D Ab.{u + 1}) (c : Cone D)

/-- The map `f_j⁻¹𝓕_j ⟶ f_i⁻¹𝓕_i` of the diagram of inverse images, for `a : i ⟶ j`:
the comparison `f_j⁻¹ ≅ f_i⁻¹ f_a⁻¹` followed by `f_i⁻¹φ_a`. -/
def pullbackDiagramMap {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtalePullbackAb (c.π.app j)).obj (F.obj j) ⟶
      (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) :=
  (conePullbackComp c a).inv.app (F.obj j) ≫ (smallEtalePullbackAb (c.π.app i)).map (F.map a)

/-- The adjoint of a map out of an inverse image, followed by a map of the diagram. -/
private lemma pullbackDiagramMap_comp_homEquiv_symm_aux {i j : Iᵒᵖ} (a : i ⟶ j)
    {G : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
    (κ : F.obj i ⟶ (smallEtalePushforwardAb (c.π.app i)).obj G) :
    F.pullbackDiagramMap c (i := i) (j := j) a ≫
        ((smallEtaleAdjunctionAb (c.π.app i)).homEquiv (F.obj i) G).symm κ =
      ((smallEtaleAdjunctionAb (c.π.app j)).homEquiv (F.obj j) G).symm
        (F.transition a ≫ (systemPushforward D Ab.{u + 1} a).map κ ≫
          (coneDirectImageCompAb c a).hom.app G) := by
  have h := leftAdjointCompIso_inv_homEquiv_symm (systemAdjunction D Ab.{u + 1} a)
    (smallEtaleAdjunctionAb (c.π.app i)) (smallEtaleAdjunctionAb (c.π.app j))
    (coneDirectImageCompAb c a) (F.transition a) κ
  rw [← h, ← map_eq_transition, pullbackDiagramMap, Category.assoc]
  rfl

/-- The maps of the diagram of inverse images in adjoint form. -/
lemma pullbackDiagramMap_eq {i j : Iᵒᵖ} (a : i ⟶ j) :
    F.pullbackDiagramMap c a =
      ((smallEtaleAdjunctionAb (c.π.app j)).homEquiv _ _).symm
        (F.transition a ≫ (systemPushforward D Ab.{u + 1} a).map
          ((smallEtaleAdjunctionAb (c.π.app i)).unit.app (F.obj i)) ≫
            (coneDirectImageCompAb c a).hom.app _) := by
  rw [← pullbackDiagramMap_comp_homEquiv_symm_aux]
  simp [Adjunction.homEquiv_counit]

/-- The adjoint of a map out of an inverse image, followed by a map of the diagram. -/
lemma pullbackDiagramMap_comp_homEquiv_symm {i j : Iᵒᵖ} (a : i ⟶ j)
    {G : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
    (κ : F.obj i ⟶ (smallEtalePushforwardAb (c.π.app i)).obj G) :
    F.pullbackDiagramMap c (i := i) (j := j) a ≫
        ((smallEtaleAdjunctionAb (c.π.app i)).homEquiv (F.obj i) G).symm κ =
      ((smallEtaleAdjunctionAb (c.π.app j)).homEquiv (F.obj j) G).symm
        (F.transition a ≫ (systemPushforward D Ab.{u + 1} a).map κ ≫
          (coneDirectImageCompAb c a).hom.app G) :=
  pullbackDiagramMap_comp_homEquiv_symm_aux F c a κ

end EtaleSheafSystem

end Stacks.EtaleCohomology

end
