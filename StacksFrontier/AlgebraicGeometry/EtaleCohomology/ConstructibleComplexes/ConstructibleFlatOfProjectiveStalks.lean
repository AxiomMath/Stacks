module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatOfFlatStalks

/-!
# A constructible sheaf with projective stalks is constructible flat, over any ring

Let `Λ` be a ring, not necessarily commutative, and `F` a constructible sheaf of `Λ`-modules on
the small étale site of `X`. If every étale stalk of `F` is a projective `Λ`-module, then `F` is
constructible flat. This is
`AlgebraicGeometry.isConstructibleFlatModuleSheaf_of_flat_etaleModuleStalk` with flatness of the
stalks replaced by projectivity, and with neither commutativity nor a Noetherian hypothesis.

## Main results

* `AlgebraicGeometry.isConstructibleFlatModuleSheaf_of_projective_etaleModuleStalk`: a
  constructible sheaf of modules over any ring with projective étale stalks is constructible flat.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r

namespace AlgebraicGeometry

attribute [local instance] Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]

/-- **A constructible sheaf of `Λ`-modules with projective étale stalks is constructible flat**,
for an arbitrary ring `Λ`, not necessarily commutative. -/
public theorem isConstructibleFlatModuleSheaf_of_projective_etaleModuleStalk
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
    (hF : IsConstructibleModuleSheaf B X Λ F)
    (hproj : ∀ s : GeometricPoint X.obj,
      Module.Projective Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).obj F)) :
    IsConstructibleFlatModuleSheaf B X Λ F := by
  intro U
  obtain ⟨σ, hσ⟩ := hF U
  refine ⟨σ, fun i U' => ?_⟩
  obtain ⟨I, V, f, hcov, hloc⟩ := hσ i U'
  refine ⟨{j // Nonempty ((SmallEtale.toScheme B (σ.piece i).obj (σ.piece i).property).obj
      (V j))}, fun j => V j.1, fun j => f j.1,
    ofArrows_nonempty_mem_topology B (σ.piece i) V f hcov, fun j => ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := hloc j.1
  obtain ⟨v⟩ := j.2
  let Y := σ.piece i
  let t₀ := GeometricPoint.ofPoint ((SmallEtale.toScheme B Y.obj Y.property).obj (V j.1)) v
  let t : GeometricPoint Y.obj := t₀.map (B.inclusion.map (V j.1).obj.hom)
  let q := geometricPointSitePoint B Y.obj Y.property t
  let y : q.fiber.obj (V j.1) := ⟨t₀.hom, rfl⟩
  let s := t.map (B.inclusion.map (σ.inclusion i))
  let eE : E ≅ (etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).obj F :=
    (GrothendieckTopology.Point.constantFiberIso _ _ (q.over y) E).symm ≪≫
      (q.over y).sheafFiber.mapIso e ≪≫
      (GrothendieckTopology.Point.sheafFiberOverIso q y (ModuleCat.{max (u + 1) r} Λ)).app _ ≪≫
      (smallEtalePullbackSheafFiberIso B (σ.inclusion i) t (ModuleCat.{max (u + 1) r} Λ)).app F
  have : Module.Finite Λ E := by rw [ModuleCat.isFG_iff] at hE; exact hE
  have := hproj s
  exact ⟨E, inferInstance, Module.Projective.of_equiv eE.toLinearEquiv.symm, ⟨e⟩⟩

end AlgebraicGeometry

end
