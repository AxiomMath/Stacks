module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Topology.LocallyConstant.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Linear.RepresentationsCofibered

/-!
# Continuous representations of a topological group

Let `Γ` be a topological group. A representation of `Γ` on a module is *continuous* when the
associated homomorphism to the general linear group of the module is continuous for the
discrete topology on the latter, equivalently when its kernel is open. The finite projective
representations of `Γ` over Artinian local `Λ`-algebras whose representation is continuous
span a full subcategory of the category of Stacks 0D3J, and the functor remembering only the
coefficient algebra restricts to it. This is the category `ℱ` of Stacks 0D3K.

Continuity is inherited by extension of scalars: a morphism `(B, N, τ) → (A, M, ρ)` presents
`M` as `N ⊗_B A`, so every element of `Γ` acting trivially on `N` acts trivially on `M`. Hence
the restricted projection is again cofibered in groupoids, and localizing it at a continuous
representation on a finite-dimensional vector space over the residue field produces the
deformation category of that representation.

## Main definitions

All names below are in the namespace `Deformation.Examples`.

* `IsContinuousRepresentation`: continuity of a representation, measured against the discrete
  topology on the general linear group.
* `FiniteProjectiveRepresentation.continuousObjects`: the objects of the representation category
  of Stacks 0D3J whose representation is continuous.
* `FiniteProjectiveRepresentation.continuousProjection`: the functor `ℱ ⥤ 𝒞_Λ` on the full
  subcategory they span.
* `FiniteProjectiveRepresentation.continuousSpecialFiber`: the object `(k, V, ρ₀)` attached to a
  continuous representation over the residue field.
* `FiniteProjectiveRepresentation.continuousDeformationCategory`: the category of objects of `ℱ`
  over `(k, V, ρ₀)`.

## Main results

* `FiniteProjectiveRepresentation.isContinuousRepresentation_of_hom`: continuity passes along a
  morphism of the representation category.
* `FiniteProjectiveRepresentation.continuousProjection_isCofiberedInGroupoids`: the category of
  continuous representations is cofibered in groupoids over `𝒞_Λ`.

## Implementation notes

The category `ℱ` is realised as `CategoryTheory.ObjectProperty.FullSubcategory` of the
category of Stacks 0D3J rather than as a parallel structure, so that its morphisms, its
category structure and its base-change condition are the inherited ones. Only a topology on
`Γ` is used; compatibility of the topology with the group structure is not needed.

Continuity along a morphism, and cofiberedness, are deduced from the corresponding statements
for the ambient category: the object property is stable under arbitrary morphisms, which is
exactly what makes a full subcategory of a category cofibered in groupoids again cofibered.

## References

* [Stacks Project, Tag 0D3K](https://stacks.math.columbia.edu/tag/0D3K)
* [Stacks Project, Tag 0D3J](https://stacks.math.columbia.edu/tag/0D3J)
-/

@[expose] public section

open CategoryTheory

namespace Deformation

universe u₁ v₁ u₂ v₂

/-- A full subcategory of a category cofibered in groupoids whose defining property is stable
under arbitrary morphisms is again cofibered in groupoids: pushforwards stay in the
subcategory, and fill-ins are inherited because the inclusion is full and faithful. -/
private theorem isCofiberedInGroupoids_fullSubcategory
    {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C] (p : F ⥤ C)
    (P : ObjectProperty F) (hP : ∀ {X Y : F}, (X ⟶ Y) → P X → P Y)
    (hp : IsCofiberedInGroupoids p) :
    IsCofiberedInGroupoids (P.ι ⋙ p) := by
  constructor
  · intro V U f x hx
    obtain ⟨y, φ, hφ⟩ := hp.exists_lift f (Opposite.op x.unop.obj) hx
    let Y : P.FullSubcategory := ⟨y.unop, hP φ.unop x.unop.property⟩
    refine ⟨Opposite.op Y, (ObjectProperty.homMk (X := x.unop) (Y := Y) φ.unop).op, ?_⟩
    exact IsHomLift.of_fac' _ f _
      (IsHomLift.domain_eq p.op f φ) (IsHomLift.codomain_eq p.op f φ)
      (IsHomLift.fac' p.op f φ)
  · intro x y z φ ψ f hf
    obtain ⟨χ, hχ, huniq⟩ := hp.unique_lift φ.unop.hom.op ψ.unop.hom.op f hf
    refine ⟨(ObjectProperty.homMk (X := y.unop) (Y := z.unop) χ.unop).op, ⟨hχ.1, ?_⟩, ?_⟩
    · exact P.ι.op.map_injective hχ.2
    · exact fun χ' hχ' => P.ι.op.map_injective (huniq _ ⟨hχ'.1, congrArg P.ι.op.map hχ'.2⟩)

end Deformation

namespace Deformation.Examples

universe u v w m

/-- A representation of a topological group is *continuous* when the associated homomorphism
into the general linear group of the module is continuous for the discrete topology on that
group. -/
public def IsContinuousRepresentation {R : Type*} [CommSemiring R] {Γ : Type*} [Group Γ]
    [TopologicalSpace Γ] {M : Type*} [AddCommMonoid M] [Module R M]
    (ρ : Representation R Γ M) : Prop :=
  letI : TopologicalSpace (LinearMap.GeneralLinearGroup R M) := ⊥
  Continuous ρ.asGroupHom

namespace FiniteProjectiveRepresentation

/-- The objects of the category of finite projective representations of Stacks 0D3J whose
representation is continuous. The category `ℱ` of Stacks 0D3K is the full subcategory they
span. -/
@[stacks 0D3K "continuous_representation_category"]
public def continuousObjects (Λ : Type u) (k : Type w) (Γ : Type*) [CommRing Λ] [Field k]
    [Algebra Λ k] [Group Γ] [TopologicalSpace Γ] :
    ObjectProperty (FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ) :=
  fun X => IsContinuousRepresentation X.action

variable {Λ : Type u} {k : Type w} {Γ : Type*}
  [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ] [TopologicalSpace Γ]

/-- Continuity of the representation passes along a morphism of the representation category:
the target module is obtained from the source module by extension of scalars, so the target
representation is locally constant wherever the source one is. -/
public theorem isContinuousRepresentation_of_hom
    {X Y : FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ} (f : X ⟶ Y)
    (hX : IsContinuousRepresentation X.action) : IsContinuousRepresentation Y.action := by
  let : Algebra X.base Y.base := f.base.hom.toAlgebra
  let : Module X.base Y.carrier := Module.compHom Y.carrier f.base.hom.toRingHom
  let : IsScalarTower X.base Y.base Y.carrier :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hl : IsLocallyConstant X.action.asGroupHom := by
    let : TopologicalSpace (LinearMap.GeneralLinearGroup X.base X.carrier) := ⊥
    have := discreteTopology_bot (LinearMap.GeneralLinearGroup X.base X.carrier)
    exact (IsLocallyConstant.iff_continuous _).2 hX
  let : TopologicalSpace (LinearMap.GeneralLinearGroup Y.base Y.carrier) := ⊥
  apply IsLocallyConstant.continuous
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro γ
  filter_upwards [hl.eventually_eq γ] with δ he
  apply Units.ext
  simp only [Representation.asGroupHom_apply]
  apply (f : FiniteProjectiveRepresentation.Hom X Y).isBaseChange.algHom_ext
  intro x
  show Y.action δ (f.map x) = Y.action γ (f.map x)
  rw [← f.equivariant, ← f.equivariant]
  exact congrArg (fun value => f.map (value.val x)) he

/-- The functor remembering only the coefficient algebra of a continuous finite projective
representation. -/
@[stacks 0D3K "continuous_representation_category"]
public def continuousProjection :
    (continuousObjects.{u, v, w, m} Λ k Γ).FullSubcategory ⥤
      ArtinianLocalAlgCat.{u, v, w} Λ k :=
  (continuousObjects.{u, v, w, m} Λ k Γ).ι ⋙ projection

/-- The functor `continuousProjection` sends a continuous representation to its coefficient
algebra. -/
@[simp]
public theorem continuousProjection_obj
    (X : (continuousObjects.{u, v, w, m} Λ k Γ).FullSubcategory) :
    (continuousProjection (Λ := Λ) (k := k) (Γ := Γ)).obj X = X.obj.base := rfl

/-- The functor `continuousProjection` sends a morphism of continuous representations to its
underlying morphism of coefficient algebras. -/
@[simp]
public theorem continuousProjection_map
    {X Y : (continuousObjects.{u, v, w, m} Λ k Γ).FullSubcategory} (f : X ⟶ Y) :
    (continuousProjection (Λ := Λ) (k := k) (Γ := Γ)).map f = f.hom.base := rfl

/-- The category of continuous finite projective representations is cofibered in groupoids
over the category of Artinian local coefficient algebras: the pushforward of a continuous
representation is continuous, and fill-ins are those of the ambient category. -/
@[stacks 0D3K "continuous_representation_category"]
public theorem continuousProjection_isCofiberedInGroupoids
    (hp : IsCofiberedInGroupoids
      (projection (Λ := Λ) (k := k) (Γ := Γ) :
        FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ ⥤
          ArtinianLocalAlgCat.{u, v, w} Λ k)) :
    IsCofiberedInGroupoids (continuousProjection.{u, v, w, m} (Λ := Λ) (k := k) (Γ := Γ)) :=
  isCofiberedInGroupoids_fullSubcategory _ _ isContinuousRepresentation_of_hom hp

/-- The continuous representation `(V, ρ₀)` over the residue field `k`, viewed as the
special-fibre object `(k, V, ρ₀)` of the category of continuous representations. -/
@[stacks 0D3K "continuous_representation_deformation_category"]
public noncomputable def continuousSpecialFiber (V : Type m) [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ₀ : Representation k Γ V)
    (hρ₀ : IsContinuousRepresentation ρ₀) :
    (continuousObjects.{u, w, w, m} Λ k Γ).FullSubcategory where
  obj := specialFiber (Λ := Λ) V ρ₀
  property := hρ₀

/-- The category of deformations of a finite-dimensional continuous representation of `Γ`. -/
@[stacks 0D3K "continuous_representation_deformation_category"]
public abbrev continuousDeformationCategory (V : Type m) [AddCommGroup V]
    [Module k V] [Module.Finite k V] (ρ₀ : Representation k Γ V)
    (hρ₀ : IsContinuousRepresentation ρ₀) :=
  Over (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀)

end FiniteProjectiveRepresentation

end Deformation.Examples
