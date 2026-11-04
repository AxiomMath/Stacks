module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.GlueStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleStalkConservative
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareGeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact

/-!
# Restriction to an étale monomorphism is surjective on morphisms into an injective module

Let `r : X ⟶ Y` be an étale morphism of algebraic spaces which is a monomorphism, for instance
the inclusion of an open subspace or a base change of one.  The counit `r_!(r^*N) ⟶ N` of
extension by zero is then a monomorphism
(`AlgebraicGeometry.Space.mono_etaleModuleLowerShriekAdjunction_counit_app`): on the stalk at a
geometric point of `Y` with a lift to `X` the lift is unique and the counit is invertible, and at
a point with no lift the stalk of `r_!(r^*N)` vanishes.  Consequently restriction along `r` is
surjective on morphisms into an injective `𝒪_Y`-module
(`AlgebraicGeometry.Space.etaleModulePullback_map_surjective_of_injective`), and restriction
along any étale morphism preserves injective modules, its left adjoint being exact
(`AlgebraicGeometry.Space.injective_etaleModulePullback_obj`).

These are the flasqueness inputs of the Zariski gluing of morphisms in the derived category of
an algebraic space.  Nothing here is registered.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A map of `𝒪_Y`-modules whose underlying map of abelian sheaves is a monomorphism on the
stalk at a geometric point is a monomorphism on the module stalk there. -/
theorem mono_geometricModuleStalk_map_of_mono_sheafFiber {Y : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (g : M ⟶ N) (x : GeometricPoint B S hS Y.1)
    (h : Mono ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map g))) :
    Mono ((geometricModuleStalkFunctor B S hS Y.1 Y.2 (etaleRingSheaf B S hS Y) x).map g) := by
  let e := Stacks.sheafModuleFiberCompForget₂ (etaleSitePoint B S hS Y.1 x Y.2)
    (etaleRingSheaf B S hS Y)
  have : IsIso (e.hom.app M) := Iso.isIso_hom (e.app M)
  have : Mono (e.hom.app M ≫ ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)) ⋙
      (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber).map g) := mono_comp' inferInstance h
  rw [← e.hom.naturality g] at this
  exact Functor.mono_of_mono_map (forget₂ _ AddCommGrpCat.{u})
    (mono_of_mono ((Stacks.sheafModuleFiber (etaleSitePoint B S hS Y.1 x Y.2)
      (etaleRingSheaf B S hS Y) ⋙ forget₂ (ModuleCat.{u}
        (((etaleSitePoint B S hS Y.1 x Y.2).presheafFiber (A := RingCat.{u})).obj
          (etaleRingSheaf B S hS Y).obj)) AddCommGrpCat.{u}).map g) (e.hom.app N))

variable {X Y : AlgebraicSpaces B S hS} (r : X ⟶ Y) (hr : IsEtale B S hS r.hom)

/-- **The counit of extension by zero along an étale monomorphism is a monomorphism.** -/
theorem mono_etaleModuleLowerShriekAdjunction_counit_app [Mono r.hom]
    (N : Modules.{u, u} B S hS Y.1 Y.2) :
    Mono ((etaleModuleLowerShriekAdjunction B S hS r hr).counit.app N) := by
  refine mono_of_mono_geometricModuleStalk B S hS Y.1 Y.2 (etaleRingSheaf B S hS Y) _
    fun x => mono_geometricModuleStalk_map_of_mono_sheafFiber B S hS _ x ?_
  have : Subsingleton (GeometricPointLift B S hS r.hom x) :=
    subsingleton_geometricPointLift_of_mono B S hS r.hom inferInstance x
  rcases isEmpty_or_nonempty (GeometricPointLift B S hS r.hom x) with h | h'
  · have hz := isZero_sheafFiber_etaleModuleShriek_of_isEmpty B S hS r hr x
      ((etaleModulePullback.{u, u} B S hS r hr).obj N)
    exact ⟨fun a b _ => hz.eq_of_tgt a b⟩
  · obtain ⟨t⟩ := h'
    have : Unique (GeometricPointLift B S hS r.hom x) := uniqueOfSubsingleton t
    have := isIso_sheafFiber_etaleModuleCounit_of_unique B S hS r hr x N
    infer_instance

/-- **Restriction along an étale monomorphism is surjective on morphisms into an injective
module.**  A morphism `ψ : r^*M ⟶ r^*J` is, by adjunction, a morphism `r_!(r^*M) ⟶ J`, which
extends along the monomorphism `r_!(r^*M) ⟶ M` since `J` is injective; the extension restricts
to `ψ`. -/
theorem etaleModulePullback_map_surjective_of_injective [Mono r.hom]
    (M J : Modules.{u, u} B S hS Y.1 Y.2) [Injective J] :
    Function.Surjective ((etaleModulePullback.{u, u} B S hS r hr).map : (M ⟶ J) → _) := by
  intro ψ
  let adj := etaleModuleLowerShriekAdjunction B S hS r hr
  have := mono_etaleModuleLowerShriekAdjunction_counit_app B S hS r hr M
  refine ⟨Injective.factorThru ((adj.homEquiv _ _).symm ψ) (adj.counit.app M), ?_⟩
  have h := congrArg (adj.homEquiv _ _)
    (Injective.comp_factorThru ((adj.homEquiv _ _).symm ψ) (adj.counit.app M))
  rwa [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, adj.right_triangle_components, Category.id_comp] at h

/-- **Restriction along an étale morphism preserves injective modules**: its left adjoint,
extension by zero, is exact. -/
theorem injective_etaleModulePullback_obj (J : Modules.{u, u} B S hS Y.1 Y.2) [Injective J] :
    Injective ((etaleModulePullback.{u, u} B S hS r hr).obj J) :=
  Injective.injective_of_adjoint (etaleModuleLowerShriekAdjunction B S hS r hr) J

end AlgebraicGeometry.Space

end
