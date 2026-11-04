module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.CategoryTheory.Sites.Representable.EffectiveEpiFamily

/-!
# Global sections along a family of morphisms of affine schemes

Effective descent of global sections of quasi-coherent modules along a family of morphisms
of affine schemes is phrased with the canonical pullback map on global sections and with the
pairwise fibre products of the family, taken in schemes after forgetting affineness. This
file provides those maps.

## Main definitions

* `AlgebraicGeometry.pullbackGlobalSections` is the canonical pullback map from the global
  sections of a module to the global sections of its pullback.
* `AlgebraicGeometry.affineOver` regards a member of a family of affine schemes as a scheme
  over the target.
* `AlgebraicGeometry.pairwiseOver` is the scheme-theoretic pairwise fibre product of two
  members, regarded as a scheme over the target, and
  `AlgebraicGeometry.pairwiseFst`, `AlgebraicGeometry.pairwiseSnd` are its two projections.

## Implementation notes

Pairwise intersections are taken in schemes after forgetting that the given schemes are
affine; these fibre products are affine and agree canonically with the fibre products formed
in affine schemes, so nothing is lost by working in schemes.

## References

* [Stacks Project, Lemma 35.13.2 (Tag 0EUA)](https://stacks.math.columbia.edu/tag/0EUA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

/-- The canonical pullback map from global sections of a module to global sections of
its pullback. -/
noncomputable def pullbackGlobalSections {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Y.Modules) : Γ(F, ⊤) ⟶ Γ((Scheme.Modules.pullback f).obj F, ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app ⊤ ≫
    ((Scheme.Modules.pullback f).obj F).presheaf.map (eqToHom (by simp)).op

/-- A member of a family of affine schemes, regarded as a scheme over the target. -/
noncomputable def affineOver {I : Type w} (X : AffineScheme.{u})
    (U : I → AffineScheme.{u}) (f : ∀ i, U i ⟶ X) (i : I) : Over X.obj :=
  Over.mk (AffineScheme.forgetToScheme.map (f i))

/-- The scheme-theoretic pairwise fibre product, regarded as a scheme over the target. -/
noncomputable def pairwiseOver {I : Type w} (X : AffineScheme.{u})
    (U : I → AffineScheme.{u}) (f : ∀ i, U i ⟶ X) (i j : I) : Over X.obj :=
  Over.mk (pullback.fst (AffineScheme.forgetToScheme.map (f i))
    (AffineScheme.forgetToScheme.map (f j)) ≫ AffineScheme.forgetToScheme.map (f i))

/-- The first projection from a pairwise fibre product, as a morphism over the target. -/
noncomputable def pairwiseFst {I : Type w} (X : AffineScheme.{u})
    (U : I → AffineScheme.{u}) (f : ∀ i, U i ⟶ X) (i j : I) :
    pairwiseOver X U f i j ⟶ affineOver X U f i :=
  Over.homMk (pullback.fst (AffineScheme.forgetToScheme.map (f i))
    (AffineScheme.forgetToScheme.map (f j))) rfl

/-- The second projection from a pairwise fibre product, as a morphism over the target. -/
noncomputable def pairwiseSnd {I : Type w} (X : AffineScheme.{u})
    (U : I → AffineScheme.{u}) (f : ∀ i, U i ⟶ X) (i j : I) :
    pairwiseOver X U f i j ⟶ affineOver X U f j :=
  Over.homMk (pullback.snd (AffineScheme.forgetToScheme.map (f i))
    (AffineScheme.forgetToScheme.map (f j))) pullback.condition.symm

end AlgebraicGeometry
