module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.ClassicalCase
public import StacksFrontier.Deformation.Formal.VersalObject.IsomorphismClassesHull
public import StacksFrontier.Deformation.Representation.TangentSelfExt
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison
public import StacksFrontier.RepresentationTheory.GroupAlgebraExtOne

/-!
# A hull for the deformations of a representation

Let `Λ → k` be a classical base, `Γ` a finitely generated group and `ρ₀` a finite-dimensional
representation of `Γ` on a `k`-vector space `V`. The deformations of `ρ₀` form a deformation
category, and its functor of fibrewise isomorphism classes has a hull: a versal formal object
whose differential is bijective. This is Stacks 0ET1.

The finite-dimensionality of the tangent space, the tangent clause of Stacks 0DVT, is reduced
to that of `Ext¹_{k[Γ]}(V, V)`, which holds for every finitely generated `Γ` with no finiteness
hypothesis on `k[Γ]`.

## Main results

All in the namespace `Deformation`.

* `finite_selfExt_representation`: the first self-extension group of a finite-dimensional
  representation of a finitely generated group is finite dimensional over `k`.
* `finiteDimensional_tangentSpace_representation`: Stacks 0DVT, the tangent clause: the
  tangent space of the deformation category of such a representation is finite dimensional.
* `exists_hull_isomorphismClasses_representation`: Stacks 0ET1: the functor of isomorphism
  classes of deformations of `ρ₀` has a versal formal object with bijective differential.

## References

* [Stacks Project, Tag 0ET1](https://stacks.math.columbia.edu/tag/0ET1)
* [Stacks Project, Tag 0DVT](https://stacks.math.columbia.edu/tag/0DVT)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] HasExt.standard

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

universe u w g m

namespace Deformation

variable {Λ : Type u} {k : Type w} {Γ : Type g} [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]

/-- A finite-dimensional representation, viewed as a module over the group algebra `k[Γ]`, is
finite dimensional over `k`. -/
theorem finite_moduleMonoidAlgebra_of_finite (V : Type m) [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ₀ : Representation k Γ V) :
    Module.Finite k
      (((Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
        (Rep.of ρ₀) : ModuleCat.{m} (MonoidAlgebra k Γ)) : Type m) :=
  Module.Finite.equiv
    ({ ρ₀.asModuleEquiv.symm.toAddEquiv with
        map_smul' := fun a x ↦ ρ₀.asModuleEquiv_symm_map_smul a x } :
      V ≃ₗ[k] (((Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
        (Rep.of ρ₀) : ModuleCat.{m} (MonoidAlgebra k Γ)) : Type m))

/-- The first self-extension group over `k[Γ]` of a finite-dimensional representation of a
finitely generated group `Γ` is finite dimensional over `k`. -/
theorem finite_selfExt_representation (V : Type m) [AddCommGroup V] [Module k V]
    [Module.Finite k V] [Group.FG Γ] (ρ₀ : Representation k Γ V) :
    Module.Finite k (Abelian.Ext
      ((Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj (Rep.of ρ₀))
      ((Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj (Rep.of ρ₀)) 1) := by
  set M₀ := (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj (Rep.of ρ₀)
  by_cases hV : ∃ v : V, v ≠ 0
  · obtain ⟨v, hv⟩ := hV
    have hfin : Module.Finite k (M₀ : Type m) := finite_moduleMonoidAlgebra_of_finite V ρ₀
    exact MonoidAlgebra.finite_extOne M₀ M₀
      (MonoidAlgebra.small_of_ne_zero (Γ := Γ) hv) hfin hfin
  · push Not at hV
    have hsubV : Subsingleton V := ⟨fun x y ↦ (hV x).trans (hV y).symm⟩
    have hsub : Subsingleton (M₀ : Type m) := hsubV
    have hproj : CategoryTheory.Projective M₀ :=
      ModuleCat.projective_of_free
        (Module.Basis.empty (ι := PEmpty.{1}) (R := MonoidAlgebra k Γ) (M₀ : Type m))
    have hzeroext : Subsingleton (Abelian.Ext M₀ M₀ 1) :=
      Abelian.Ext.subsingleton_of_projective _ _ 0
    exact Module.Finite.of_surjective (0 : (Fin 0 → k) →ₗ[k] Abelian.Ext M₀ M₀ 1)
      fun _ ↦ ⟨0, Subsingleton.elim _ _⟩

/-- The tangent space of the deformation category of a finite-dimensional representation of a
finitely generated group is finite dimensional over `k`, for the canonical vector space structure
of Stacks 06IH. -/
@[stacks 0DVT "clause 5: `T Def_{V,ρ₀}` is finite dimensional over `k` when `Γ` is finitely \
generated, for the canonical vector space structure of Stacks 06IH. The hypothesis `Group.FG Γ` \
is what separates this from clause 4, which holds for every `Γ`"]
theorem finiteDimensional_tangentSpace_representation (V : Type m) [AddCommGroup V] [Module k V]
    [Module.Finite k V] [Group.FG Γ] (ρ₀ : Representation k Γ V) :
    let 𝓕 := BasedCategory.ofFunctor (deformationCategoryProjection (Λ := Λ) V ρ₀)
    let ee := tangentSpaceEquivSelfExt (Λ := Λ) V ρ₀
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨ee.1⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 ee.1.cofibered))) := ⟨ee.2.1⟩
    FiniteDimensional k (artinianTangentSpace Λ k (isomorphismClasses 𝓕 ee.1.cofibered)) := by
  intro 𝓕 ee
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨ee.1⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓕 ee.1.cofibered))) := ⟨ee.2.1⟩
  let L := ee.2.2.1
  let : Module.Finite k (Abelian.Ext
    ((Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj (Rep.of ρ₀))
    ((Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj (Rep.of ρ₀)) 1) :=
    finite_selfExt_representation V ρ₀
  exact Module.Finite.of_surjective L.symm.toLinearMap L.symm.surjective

/-- The functor of isomorphism classes of deformations of a finite-dimensional representation of
a finitely generated group over a classical base has a hull: a versal formal object with
bijective differential. -/
@[stacks 0ET1 "representation_hull"]
theorem exists_hull_isomorphismClasses_representation (V : Type m) [AddCommGroup V] [Module k V]
    [Module.Finite k V] [Group.FG Γ] (ρ₀ : Representation k Γ V) (hΛ : IsClassical Λ k) :
    let 𝓕 := BasedCategory.ofFunctor (deformationCategoryProjection (Λ := Λ) V ρ₀)
    let hpre := (tangentSpaceEquivSelfExt (Λ := Λ) V ρ₀).1
    let F := isomorphismClasses 𝓕 hpre.cofibered
    ∃ ξ : FormalObject (CategoryOfElements.π F),
      IsVersal (categoryOfElements_projection_isCofibered F) ξ ∧
        HasBijectiveDifferential (categoryOfElements_projection_isCofibered F) ξ := by
  intro 𝓕 hpre F
  let hDef := isDeformationCategory_deformationCategoryProjection (Λ := Λ) V ρ₀
  let ee := tangentSpaceEquivSelfExt (Λ := Λ) V ρ₀
  let : IsNoetherianRing Λ := hΛ.isNoetherianRing
  let : Module.Finite Λ k := hΛ.moduleFinite
  let : Algebra.IsSeparable (residueImageField Λ k) k := hΛ.isSeparable
  let : Fact (IsPredeformationCategory.{u, w, w} 𝓕.p) := ⟨hpre⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓕 hpre.cofibered))) := ⟨ee.2.1⟩
  let : FiniteDimensional k (tangentSpaceArtinian.{u, w, w} Λ k
      (isomorphismClasses 𝓕 hpre.cofibered)) :=
    finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace 𝓕 hpre ee.2.1
      (finiteDimensional_tangentSpace_representation (Λ := Λ) V ρ₀)
  obtain ⟨ξ, -, hversal, hbijective⟩ :=
    exists_hull_isomorphismClasses.{u, w, w} Λ k 𝓕 hpre
      (schlessingerConditionS1_of_satisfiesRS hDef.satisfiesRS)
      (schlessingerConditionS2_of_satisfiesRS hDef.satisfiesRS) inferInstance
  exact ⟨imageInIsomorphismClasses _ hpre ξ, hversal, hbijective⟩

end Deformation

end
