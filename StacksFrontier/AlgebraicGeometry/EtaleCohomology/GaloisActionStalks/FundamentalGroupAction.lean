module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisActionStalks.GeometricPointAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.GeometricPointStalkMapNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusElementDegree

/-!
# The Galois action on the stalk of a pulled-back locally constant sheaf is the `π₁`-action

Let `X` be a connected scheme of a big étale site with base geometric point `x̄`, let
`g : Spec K ⟶ X` be a morphism from the spectrum of a field, `t̄` a geometric point of `Spec K`
and `p` a path from `g(t̄)` to `x̄`. For a finite locally constant sheaf of sets `G` on `X`, the
stalk of `g⁻¹ G` at `t̄` is the stalk of `G` at `g(t̄)` (Stacks 03Q1), which `p` identifies with
the finite `π₁(X, x̄)`-set `M_G` attached to `G` (Stacks 0DV5). Under this identification a
Galois automorphism `σ` of `K^sep/K`, extended to an automorphism `τ` of the algebraically closed
field of `t̄`, acts on the stalk (Stacks 03QT) as the element of `π₁(X, x̄)` that `p` transports
the automorphism `Spec τ` of the geometric point `g(t̄)` to.

This is the comparison that turns the Galois invariants of Stacks 04JM, over `K = K^{sh}` the
fraction field of a strict henselization at a boundary point of a curve, into invariants of the
image of the inertia group in `π₁`.

## Main results

* `Stacks.EtaleCohomology.etaleStalkSmul_pullback_finiteLocallyConstant` — the comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] GeometricPoint.residueFieldAlgebra

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

/-- The identification of the stalk at `t̄` of the inverse image of a finite locally constant
sheaf `G` along `g : Spec K ⟶ X` with the finite `π₁(X, x̄)`-set of `G`, through a path `p` from
`g(t̄)` to `x̄`. -/
def pullbackFiniteLocallyConstantStalkIso (g : B.obj (Spec (.of K)) hK ⟶ X)
    (t : GeometricPoint (Spec (.of K)))
    (p : finiteEtaleFiberFunctor (X := X.1) (t.map (B.inclusion.map g)) ≅ finiteEtaleFiberFunctor x)
    (G : (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory) :
    (etaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK t).obj
        (((smallEtaleBaseChange B g).sheafPullback (Type (u + 1))
          (SmallEtale.topology B X.1 X.2)
          (SmallEtale.topology B (Spec (.of K)) hK)).obj G.obj) ≅
      (((canonicalFiniteLocallyConstantSetsEquivalence B X x).functor.obj G).obj.obj.obj.V) :=
  etaleStalkSmallEtalePullObjIso B g t (Type (u + 1)) G.obj ≪≫
    (finiteLocallyConstantStalkForgetIso B X p).app G

/-- **The Galois action on the stalk of a pulled-back finite locally constant sheaf is the action
of the fundamental group.** If `τ` extends `σ` and `α = Spec τ` is an automorphism of the
geometric point `t̄`, then `σ` acts on the stalk of `g⁻¹ G` at `t̄` as the element of `π₁(X, x̄)`
which the path `p` transports the automorphism `α` of `g(t̄)` to. -/
theorem etaleStalkSmul_pullback_finiteLocallyConstant (g : B.obj (Spec (.of K)) hK ⟶ X)
    (t : GeometricPoint (Spec (.of K)))
    (p : finiteEtaleFiberFunctor (X := X.1) (t.map (B.inclusion.map g)) ≅ finiteEtaleFiberFunctor x)
    (G : (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory)
    (σ : GeometricPoint.absoluteGaloisGroup t)
    (τ : Gal(t.residueField/(Spec (.of K)).residueField (t.hom default)))
    (hτ : ∀ a : GeometricPoint.separableClosure t,
      (σ a : t.residueField) = τ (a : t.residueField))
    (α : t.source ≅ t.source) (hα : α.hom = Spec.map (CommRingCat.ofHom τ.toRingHom))
    (hαt : α.hom ≫ t.hom = t.hom)
    (z : (etaleStalkFunctor.{u, u + 1} B (Spec (.of K)) hK t).obj
        (((smallEtaleBaseChange B g).sheafPullback (Type (u + 1))
          (SmallEtale.topology B X.1 X.2)
          (SmallEtale.topology B (Spec (.of K)) hK)).obj G.obj)) :
    (pullbackFiniteLocallyConstantStalkIso B X x K hK g t p G).hom
        (ConcreteCategory.hom (etaleStalkSmul.{u, u + 1} B K hK t _ σ) z) =
      ((canonicalFiniteLocallyConstantSetsEquivalence B X x).functor.obj G).obj.obj.obj.ρ
        (etaleFundamentalGroupMulEquiv p
          (GeometricPoint.sourceAutElement (S := X.1) (t.map (B.inclusion.map g)) α (by
            change α.hom ≫ t.hom ≫ _ = t.hom ≫ _
            rw [← Category.assoc, hαt])))
        ((pullbackFiniteLocallyConstantStalkIso B X x K hK g t p G).hom z) := by
  let a : GeometricPoint.Hom t t := ⟨α.hom, hαt⟩
  let s := GeometricPoint.sourceAutElement (S := X.1) (t.map (B.inclusion.map g)) α (by
    change α.hom ≫ t.hom ≫ _ = t.hom ≫ _
    rw [← Category.assoc, hαt])
  have h1 := etaleStalkSmul_eq_geometricPointStalkMap.{u, u + 1} B K hK t
    (((smallEtaleBaseChange B g).sheafPullback (Type (u + 1))
      (SmallEtale.topology B X.1 X.2)
      (SmallEtale.topology B (Spec (.of K)) hK)).obj G.obj) σ τ hτ a hα
  have h2 := geometricPointStalkMap_comp_etaleStalkSmallEtalePullObjIso_hom B g t
    (Type (u + 1)) a G.obj
  have h3 := geometricPointStalkMap_finiteLocallyConstantStalkForgetIso B X p
    (a.mapHom (B.inclusion.map g))
    s (by ext; rfl) G
  have E : (geometricPointStalkMap B (Spec (.of K)) hK a (Type (u + 1))).app
        (((smallEtaleBaseChange B g).sheafPullback (Type (u + 1))
          (SmallEtale.topology B X.1 X.2)
          (SmallEtale.topology B (Spec (.of K)) hK)).obj G.obj).obj ≫
        (pullbackFiniteLocallyConstantStalkIso B X x K hK g t p G).hom =
      (pullbackFiniteLocallyConstantStalkIso B X x K hK g t p G).hom ≫
        (((canonicalFiniteLocallyConstantSetsEquivalence B X x).functor.obj G).obj.obj.obj.ρ
          (etaleFundamentalGroupMulEquiv p s)).asHom := by
    change _ ≫ (etaleStalkSmallEtalePullObjIso B g t (Type (u + 1)) G.obj).hom ≫
        (finiteLocallyConstantStalkForgetIso B X p).hom.app G = _
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (finiteLocallyConstantStalkForgetIso B X p).hom.app G) h2).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((etaleStalkSmallEtalePullObjIso B g t (Type (u + 1)) G.obj).hom ≫ ·)
      h3).trans ?_
    exact (Category.assoc _ _ _).symm
  have hz := ConcreteCategory.congr_hom E z
  simp only at hz
  rw [h1]
  exact hz

end Stacks.EtaleCohomology

end
