module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusClosedPoint

/-!
# The geometric Frobenius at a closed point and at a rational point, through a morphism into the
closed point

`Stacks.Frobenius.frobeniusStalkFunctor_comm` compares the geometric Frobenius at a point `x` with
finite residue field and the geometric Frobenius at a rational point `y` over a finite field `k`,
through a morphism of geometric points from the geometric point at `x` (built from an algebraic
closure of `κ(x)`) to the geometric point over `y` (built from an algebraically closed field `K`).
Such a morphism is a `k`-embedding of `K` into the algebraic closure of `κ(x)`, which exists only
when `K` is algebraic over `k`. The morphisms in the other direction, embeddings of the algebraic
closure of `κ(x)` into `K`, exist for every algebraically closed `K`, and this file gives the
comparison through them. It is what identifies the local terms `Tr(π_x | K_x̄)` of the trace
formula of [Tag 03V3] at the geometric points over rational points with the traces of the
geometric Frobenius on the stalks at the closed points, used for the point side of the trace
formula of [Tag 03V2](https://stacks.math.columbia.edu/tag/03V2).

## Main results

* `Stacks.Frobenius.frobeniusStalkFunctor_comm_of_hom_to`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.Frobenius

variable (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u, u} A] (X : Scheme.{u}) (x : X)
  [Finite (X.residueField x)] {k : Type u} [Field k] [Fintype k] (K : Type u) [Field K]
  [IsAlgClosed K] [Algebra k K] (p f : ℕ) [Fact p.Prime] [CharP K p]

/-- At a rational point `y` of a scheme over a finite field `k` whose residue field at `x` has
`#k` elements, a morphism of geometric points from the geometric point over `y` to the geometric
point at `x` intertwines the two geometric Frobenius actions on the stalk functors. -/
public lemma frobeniusStalkFunctor_comm_of_hom_to (hcard : Fintype.card k = p ^ f)
    (y : Spec (.of k) ⟶ X)
    (θ : GeometricPoint.Hom (rationalGeometricPoint K y) (geometricPointAt X x))
    (hres : Nat.card (X.residueField x) = Fintype.card k) :
    GrothendieckTopology.Point.Hom.sheafFiber (A := A) (smallEtalePointHom X θ) ≫
        geometricFrobeniusStalkFunctor A K p f hcard y =
      frobeniusStalkFunctor A X x ≫
        GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom X θ) := by
  obtain ⟨φ, hθ⟩ : ∃ φ : AlgebraicClosure (X.residueField x) →+* K,
      θ.hom = Spec.map (CommRingCat.ofHom φ) :=
    ⟨(Spec.preimage θ.hom).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  have key : ∀ z : AlgebraicClosure (X.residueField x), φ ((residueGeometricFrobenius X x) z) =
      (arithmeticFrobenius k K p f hcard).symm (φ z) := by
    intro z
    refine (arithmeticFrobenius k K p f hcard).injective ?_
    rw [AlgEquiv.apply_symm_apply, arithmeticFrobenius_apply, ← map_pow, ← hres,
      ← residueGeometricFrobenius_symm_apply, AlgEquiv.symm_apply_apply]
  have hring : CommRingCat.ofHom (residueGeometricFrobenius X x).toAlgHom.toRingHom ≫
      CommRingCat.ofHom φ =
    CommRingCat.ofHom φ ≫
      CommRingCat.ofHom (arithmeticFrobenius k K p f hcard).symm.toAlgHom.toRingHom := by
    ext z
    exact key z
  have ha : (galoisPointHom K (arithmeticFrobenius k K p f hcard).symm y).hom ≫ θ.hom =
      θ.hom ≫ (galoisPointHom (AlgebraicClosure (X.residueField x))
        (residueGeometricFrobenius X x) (X.fromSpecResidueField x)).hom := by
    rw [galoisPointHom_hom, galoisPointHom_hom, hθ, ← Spec.map_comp, ← Spec.map_comp, hring]
  let c : GeometricPoint.Hom (rationalGeometricPoint K y) (geometricPointAt X x) :=
    ⟨(galoisPointHom K (arithmeticFrobenius k K p f hcard).symm y).hom ≫ θ.hom, by
      rw [Category.assoc, θ.comm]
      exact (galoisPointHom K (arithmeticFrobenius k K p f hcard).symm y).comm⟩
  simp only [frobeniusStalkFunctor, geometricFrobeniusStalkFunctor, galoisStalkAction]
  rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp,
    ← GrothendieckTopology.Point.Hom.sheafFiber_comp,
    ← smallEtalePointHom_comp _ θ c rfl,
    ← smallEtalePointHom_comp θ _ c ha]

end Stacks.Frobenius
