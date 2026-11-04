module

public import StacksFrontier.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicGeometry.Limits

/-!
# The Čech nerve of a morphism of schemes lies over its base

Let `f : X ⟶ Y` be a morphism of schemes. Because `Scheme` has finite limits, the wide pullbacks
`X ×_Y ⋯ ×_Y X` of finitely many copies of `f` exist, so `f` has a Čech nerve: the simplicial
scheme whose term in degree `n` is the `(n + 1)`-fold fibre product of `X` over `Y`. This Čech
nerve is augmented over `Y`, the augmentation in degree `n` being the structural map of the wide
pullback to its base, and the simplicial structure maps are the maps that reindex the factors.

This file records the degreewise names for that nerve and the one compatibility they satisfy: a
coface map, which deletes one of the factors of a fibre product, commutes with the augmentation to
`Y`. Equivalently, every term of the Čech nerve is a scheme over `Y` and every face map is a
morphism over `Y`. This is the statement that lets the Čech nerve of a finite surjection be used
for cohomological descent (Tag 09Z2), where it supplies the comparison of the base-change functors
along two successive fibre products with the base-change functor along the composite.

The underlying general fact — a structure map of the Čech nerve of an arrow followed by the map to
the base is the map to the base — is `CategoryTheory.Arrow.cechNerve_map_base`; everything here is
its specialization to the cofaces of the Čech nerve of a morphism of schemes.

## Main definitions

* `Stacks.EtaleCohomology.cechScheme` — the degree-`n` term of the Čech nerve of `f`, the
  `(n + 1)`-fold fibre product of `X` over `Y`.
* `Stacks.EtaleCohomology.cechProjection` — the augmentation `cechScheme f n ⟶ Y`.
* `Stacks.EtaleCohomology.cechFaceProjection` — the coface map `cechScheme f (n + 1) ⟶
  cechScheme f n` deleting the `i`-th factor.

## Main results

* `Stacks.EtaleCohomology.cechFaceProjection_comp` — a face projection lies over the base of the
  Čech nerve.

## References

* [Stacks Project, Tag 09Z2](https://stacks.math.columbia.edu/tag/09Z2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u

namespace Stacks.EtaleCohomology

/-- The `(n + 1)`-fold fibre product in the Čech nerve of `f`. -/
abbrev cechScheme {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) : Scheme.{u} :=
  (Arrow.mk f).cechNerve.obj (op ⦋n⦌)

/-- The projection from a level of the Čech nerve to the base scheme. -/
abbrev cechProjection {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    cechScheme f n ⟶ Y :=
  (Arrow.mk f).augmentedCechNerve.hom.app (op ⦋n⦌)

/-- The face projection deleting the `i`-th factor of a Čech fibre product. -/
abbrev cechFaceProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) (i : Fin (n + 2)) : cechScheme f (n + 1) ⟶ cechScheme f n :=
  (Arrow.mk f).cechNerve.map (SimplexCategory.δ i).op

/-- A face projection lies over the base of the Čech nerve. -/
theorem cechFaceProjection_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) (i : Fin (n + 2)) :
    cechFaceProjection f n i ≫ cechProjection f n = cechProjection f (n + 1) := by
  have : (Arrow.mk f).HasCechPullbacks := ⟨fun _ => inferInstance⟩
  exact Arrow.cechNerve_map_base (Arrow.mk f) (SimplexCategory.δ i).op

end Stacks.EtaleCohomology
