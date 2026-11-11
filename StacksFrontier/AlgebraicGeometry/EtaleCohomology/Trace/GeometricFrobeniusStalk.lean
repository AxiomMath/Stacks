module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMap
public import StacksFrontier.AlgebraicGeometry.Frobenius

/-!
# The geometric Frobenius at a rational point

Let `k` be a finite field with `q = p ^ f` elements, let `X` be a scheme over `k`, let `x` be a
rational point of `X` and let `x̄` be the geometric point over `x` determined by an
algebraically closed extension `k̄` of `k`. An element `σ` of `Gal(k̄/k)` is an endomorphism of
`x̄`, because `Spec σ` is a morphism over `Spec k` and `x̄` factors through `x`, so it acts on
the étale stalk at `x̄`. The *geometric Frobenius* at `x` is the action of the inverse of the
arithmetic Frobenius.

## Main definitions

* `Stacks.Frobenius.rationalGeometricPoint` is the geometric point over a rational point.
* `Stacks.Frobenius.galoisPointHom` exhibits an automorphism of the extension field as an
  endomorphism of that geometric point.
* `Stacks.Frobenius.galoisStalkAction` is the resulting action on the étale stalk functor.
* `Stacks.Frobenius.geometricFrobeniusStalkFunctor` and
  `Stacks.Frobenius.geometricFrobeniusStalk` are the geometric Frobenius at a rational point,
  as an endomorphism of the stalk functor and of the stalk of a single sheaf.

## Main results

* `Stacks.Frobenius.galoisStalkAction_one` and `Stacks.Frobenius.galoisStalkAction_mul` say
  that the Galois group acts on the left on the stalk functor.
* `Stacks.Frobenius.galoisStalkAction_comp_geometricFrobeniusStalkFunctor` and
  `Stacks.Frobenius.geometricFrobeniusStalkFunctor_comp_galoisStalkAction` say that the
  geometric Frobenius is inverse to the action of the arithmetic Frobenius.
* `Stacks.Frobenius.geometricFrobeniusStalkFunctor_eq` says that the geometric Frobenius is the
  action of the inverse of any automorphism raising to the power the cardinality of `k`.

## Implementation notes

The action is the one attached to a morphism of geometric points: an automorphism `σ` of `k̄`
over `k` gives a morphism of geometric points, which induces a morphism of the associated
points of the small étale site and hence an endomorphism of the fiber functor on sheaves. Both
steps reverse direction, so the resulting action of the Galois group is a left action.

The geometric Frobenius is given both as an endomorphism of the stalk functor and as its
component at a single sheaf; the functor form is what makes it functorial in the coefficients.
The coefficient category is arbitrary subject to the existence of the colimits defining the
stalk, so taking modules over a ring gives the linear endomorphism whose trace enters the
trace formula.

## References

* [Stacks Project, Tag 03SU](https://stacks.math.columbia.edu/tag/03SU)
* [Stacks Project, Tag 03SW](https://stacks.math.columbia.edu/tag/03SW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.Frobenius

section GeometricPoint

variable {k : Type u} [Field k] {X : Scheme.{u}} (K : Type u) [Field K] [IsAlgClosed K]
  [Algebra k K]

/-- The geometric point lying over a rational point `x` of a scheme over `k`, determined by an
algebraically closed extension `K` of `k`. -/
abbrev rationalGeometricPoint (x : Spec (.of k) ⟶ X) : GeometricPoint X where
  residueField := K
  hom := Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ x

/-- The geometric point attached to a rational point lies over it. -/
lemma rationalGeometricPoint_liesOver (x : Spec (.of k) ⟶ X) :
    (rationalGeometricPoint K x).LiesOver (x default) := by
  change x (Spec.map (CommRingCat.ofHom (algebraMap k K)) default) = x default
  exact congrArg _ (Subsingleton.elim _ _)

/-- An automorphism of `K` over `k`, viewed as an endomorphism of the geometric point over a
rational point: `Spec σ` is a morphism over `Spec k`, hence over `X` after composing with the
rational point. -/
def galoisPointHom (σ : K ≃ₐ[k] K) (x : Spec (.of k) ⟶ X) :
    GeometricPoint.Hom (rationalGeometricPoint K x) (rationalGeometricPoint K x) where
  hom := Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)
  comm := by
    have h : CommRingCat.ofHom (algebraMap k K) ≫
        CommRingCat.ofHom σ.toAlgHom.toRingHom = CommRingCat.ofHom (algebraMap k K) := by
      ext y
      exact σ.commutes y
    change Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ x) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ x
    rw [← Category.assoc, ← Spec.map_comp, h]

/-- The underlying morphism of schemes of `galoisPointHom K σ x` is `Spec σ`. -/
@[simp]
lemma galoisPointHom_hom (σ : K ≃ₐ[k] K) (x : Spec (.of k) ⟶ X) :
    (galoisPointHom K σ x).hom = Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) := rfl

end GeometricPoint

section SmallEtalePoint

variable {X : Scheme.{u}}

/-- The morphism of points of the small étale site attached to an identity morphism of
geometric points is the identity. -/
lemma smallEtalePointHom_id {s : GeometricPoint X}
    (a : GeometricPoint.Hom s s) (ha : a.hom = 𝟙 s.source) :
    smallEtalePointHom X a = 𝟙 (Scheme.pointSmallEtale s.hom) := by
  apply GrothendieckTopology.Point.hom_ext
  ext U p
  apply Over.OverMorphism.ext
  change a.hom ≫ _ = _
  rw [ha, Category.id_comp]
  rfl

/-- The morphism of points of the small étale site attached to a composite of morphisms of
geometric points is the composite of the morphisms it attaches to the factors. -/
lemma smallEtalePointHom_comp {s t r : GeometricPoint X} (a : GeometricPoint.Hom s t)
    (b : GeometricPoint.Hom t r) (c : GeometricPoint.Hom s r) (hc : c.hom = a.hom ≫ b.hom) :
    smallEtalePointHom X c = smallEtalePointHom X a ≫ smallEtalePointHom X b := by
  apply GrothendieckTopology.Point.hom_ext
  ext U p
  apply Over.OverMorphism.ext
  change c.hom ≫ _ = a.hom ≫ b.hom ≫ _
  rw [hc, Category.assoc]

end SmallEtalePoint

section StalkAction

variable {k : Type u} [Field k] {X : Scheme.{u}} (A : Type v) [Category.{w} A]
  [HasColimitsOfSize.{u, u} A] (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]

/-- The action of an automorphism of `K` over `k` on the étale stalk functor at the geometric
point over a rational point `x`, induced by the automorphism as an endomorphism of that
geometric point. -/
def galoisStalkAction (σ : K ≃ₐ[k] K) (x : Spec (.of k) ⟶ X) :
    (Scheme.pointSmallEtale (rationalGeometricPoint K x).hom).sheafFiber (A := A) ⟶
      (Scheme.pointSmallEtale (rationalGeometricPoint K x).hom).sheafFiber :=
  GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom X (galoisPointHom K σ x))

/-- The identity acts as the identity on the stalk functor. -/
@[simp]
lemma galoisStalkAction_one (x : Spec (.of k) ⟶ X) :
    galoisStalkAction A K (1 : K ≃ₐ[k] K) x = 𝟙 _ := by
  rw [galoisStalkAction,
    smallEtalePointHom_id (galoisPointHom K (1 : K ≃ₐ[k] K) x)
      (by rw [galoisPointHom_hom]; rw [show CommRingCat.ofHom
        (AlgEquiv.toAlgHom (1 : K ≃ₐ[k] K)).toRingHom = 𝟙 (CommRingCat.of K) from rfl,
        Spec.map_id])]
  exact GrothendieckTopology.Point.Hom.sheafFiber_id _

/-- The Galois group acts on the left on the stalk functor. -/
@[sga "4 VIII 3.12" "partial"]
lemma galoisStalkAction_mul (σ τ : K ≃ₐ[k] K) (x : Spec (.of k) ⟶ X) :
    galoisStalkAction A K (σ * τ) x = galoisStalkAction A K τ x ≫ galoisStalkAction A K σ x := by
  rw [galoisStalkAction, galoisStalkAction, galoisStalkAction,
    smallEtalePointHom_comp (galoisPointHom K σ x) (galoisPointHom K τ x)
      (galoisPointHom K (σ * τ) x) (by
        rw [galoisPointHom_hom, galoisPointHom_hom, galoisPointHom_hom, ← Spec.map_comp]
        rfl)]
  exact GrothendieckTopology.Point.Hom.sheafFiber_comp _ _

/-- Automorphisms with `τ * σ = 1` act on the stalk functor by mutually inverse maps, in the
order `σ` then `τ`. -/
private theorem galoisStalkAction_comp_eq_id (σ τ : K ≃ₐ[k] K) (x : Spec (.of k) ⟶ X)
    (h : τ * σ = 1) : galoisStalkAction A K σ x ≫ galoisStalkAction A K τ x = 𝟙 _ := by
  rw [← galoisStalkAction_mul, h, galoisStalkAction_one]

variable [Fintype k] (p f : ℕ) [Fact p.Prime] [CharP K p]

/-- **Stacks Project, Tag 03SW.** The geometric Frobenius at a rational point `x` of a scheme
over a finite field `k` with `p ^ f` elements, as an endomorphism of the étale stalk functor at
the geometric point over `x`: it is the action of the inverse of the arithmetic Frobenius. -/
@[stacks 03SW "on the stalk functor",
  sga "7 XXI 5.0" "F_x acts on G_x̄",
  sga "7 I 6.3",
  sga "7 XXII 2.2.4" "The element φ_q"]
def geometricFrobeniusStalkFunctor (hcard : Fintype.card k = p ^ f) (x : Spec (.of k) ⟶ X) :
    (Scheme.pointSmallEtale (rationalGeometricPoint K x).hom).sheafFiber (A := A) ⟶
      (Scheme.pointSmallEtale (rationalGeometricPoint K x).hom).sheafFiber :=
  galoisStalkAction A K (arithmeticFrobenius k K p f hcard).symm x

/-- **Stacks Project, Tag 03SW.** The geometric Frobenius at a rational point `x`, acting on
the étale stalk of a sheaf `F` at the geometric point over `x`. -/
@[stacks 03SW, sga "7 XXI 5.0" "F_x acts on G_x̄"]
def geometricFrobeniusStalk (hcard : Fintype.card k = p ^ f) (x : Spec (.of k) ⟶ X)
    (F : Sheaf X.smallEtaleTopology A) :
    (Scheme.pointSmallEtale (rationalGeometricPoint K x).hom).sheafFiber.obj F ⟶
      (Scheme.pointSmallEtale (rationalGeometricPoint K x).hom).sheafFiber.obj F :=
  (geometricFrobeniusStalkFunctor A K p f hcard x).app F

/-- The geometric Frobenius is the action of the inverse of any automorphism of `K` over `k`
raising to the power the cardinality of `k`; in particular it does not depend on the
construction of the arithmetic Frobenius. -/
@[sga "7 I 6.3" "partial"]
lemma geometricFrobeniusStalkFunctor_eq (hcard : Fintype.card k = p ^ f)
    (x : Spec (.of k) ⟶ X) (σ : K ≃ₐ[k] K) (hσ : ∀ y : K, σ y = y ^ Fintype.card k) :
    geometricFrobeniusStalkFunctor A K p f hcard x = galoisStalkAction A K σ.symm x := by
  rw [geometricFrobeniusStalkFunctor, eq_arithmeticFrobenius k K p f hcard σ hσ]

/-- The geometric Frobenius is a right inverse of the action of the arithmetic Frobenius. -/
lemma galoisStalkAction_comp_geometricFrobeniusStalkFunctor (hcard : Fintype.card k = p ^ f)
    (x : Spec (.of k) ⟶ X) :
    galoisStalkAction A K (arithmeticFrobenius k K p f hcard) x ≫
        geometricFrobeniusStalkFunctor A K p f hcard x = 𝟙 _ :=
  galoisStalkAction_comp_eq_id A K _ _ x (by rw [← AlgEquiv.aut_inv]; exact inv_mul_cancel _)

/-- The geometric Frobenius is a left inverse of the action of the arithmetic Frobenius. -/
lemma geometricFrobeniusStalkFunctor_comp_galoisStalkAction (hcard : Fintype.card k = p ^ f)
    (x : Spec (.of k) ⟶ X) :
    geometricFrobeniusStalkFunctor A K p f hcard x ≫
        galoisStalkAction A K (arithmeticFrobenius k K p f hcard) x = 𝟙 _ :=
  galoisStalkAction_comp_eq_id A K _ _ x (by rw [← AlgEquiv.aut_inv]; exact mul_inv_cancel _)

end StalkAction

/-! ### Section 59.56, the Galois action on stalks

`galoisStalkAction`, with `galoisStalkAction_one` and `galoisStalkAction_mul`, is the action of
Section 03QW at the geometric point over a rational point of a scheme over `k`, on the stalk
functor of Mathlib's small étale site. Section 03QW itself, the action of `Aut(κ(s̄)/κ(s))` and of
`Gal_{κ(s)}` on the stalk at a geometric point of an arbitrary scheme, is
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisActionStalks.SchemeStalkAction`.
-/

end Stacks.Frobenius

end
