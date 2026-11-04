module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkGerm
public import StacksFrontier.RingTheory.Length.SemilinearTransfer

/-!
# The length of a module at a geometric point of an algebraic space

Let `X` be an algebraic space over a scheme `S`, let `F` be an `𝒪_X`-module and let `x̄` be a
geometric point of `X`. The *length of `F` at `x̄`* is the length of the stalk `F_{x̄}` over the
étale local ring `𝒪_{X, x̄}`, a value in `ℕ∞ = {0, 1, 2, …, ∞}`. This is the quantity named in
condition (1) of Stacks 0EE1, and the one Stacks 0EE2 turns into the definition of "`F` has
length `d` at `x`" for a point `x` of `|X|`.

The two ingredients are already in place: the étale local ring `𝒪_{X, x̄}` of Stacks 04KG
(`AlgebraicGeometry.Space.etaleLocalRing`) and the module stalk `F_{x̄}` of Stacks 05VQ
(`AlgebraicGeometry.Space.geometricModuleStalk`), which is a module over it. This file names
their length and records the two facts any use of it needs: when the value is zero, and that
it is unchanged by a surjection of étale local rings together with a comparison of stalks
over it.

## Main definitions

* `AlgebraicGeometry.Space.geometricLength`: the length of an `𝒪_X`-module at a geometric
  point of `X`.

## Main results

* `AlgebraicGeometry.Space.geometricLength_eq_zero_iff` and
  `AlgebraicGeometry.Space.geometricLength_pos_iff`: the length at `x̄` vanishes exactly when
  every germ at `x̄` of every section near `x̄` vanishes, and is positive exactly when some
  germ does not. So the invariant genuinely sees the module: it is `0` for the zero module and
  nonzero as soon as one germ survives.
* `AlgebraicGeometry.Space.geometricLength_eq_of_surjective_of_addEquiv`: if the germ map
  `𝒪_{X, x̄} → 𝒪_{Y, ȳ}` of étale local rings is surjective and the stalk of `F` at `x̄` is
  isomorphic to the stalk of `G` at `ȳ` by a map semilinear over it, then `F` has the same
  length at `x̄` as `G` has at `ȳ`.

## Implementation notes

The length is taken at a *geometric* point rather than at a point of `|X|`. On an algebraic
space that is the primitive notion: the étale local ring and the module stalk of Stacks 04KG
and 05VQ are attached to a geometric point. The independence of the choice of geometric point
above a given `x ∈ |X|` is the content of Stacks 0EE1, and it is proved in this development,
for a quasi-coherent `F`, as `AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`
(`StacksFrontier/AlgebraicGeometry/Spaces/GeometricLengthPointIndependence.lean:244`), a file that
imports this one. Nothing here uses that fact: no declaration anywhere packages a choice of
geometric point above `x` together with that independence into a value "the length of `F` at
`x`", so nothing in this file carries the tag 0EE2, whose statement is the definition *at a
point of `|X|`* and therefore presupposes such a packaging.

No quasi-coherence is assumed. Stacks 0EE1 and 0EE2 state the definition for a quasi-coherent
module because that is the setting in which the equivalence of conditions holds; the length of
the stalk itself is defined for an arbitrary `𝒪_X`-module, and the two results below hold at
that generality.

`AlgebraicGeometry.Space.geometricLength_eq_of_surjective_of_addEquiv` is the last step of
Stacks 0EE3 for algebraic spaces, isolated from the two geometric inputs that step consumes:
surjectivity of the germ map of a closed immersion, and the identification of the stalk of a
direct image at the image point. It is the algebraic-space counterpart of
`Stacks.ClosedImmersion.length_stalkObj_modulePushforward`, which plays the same role in the
scheme case, and it is stated for an arbitrary pair of algebraic spaces and geometric points
so that it does not have to be restated when those inputs become available.

## References

* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE2](https://stacks.math.columbia.edu/tag/0EE2)
* [Stacks Project, Tag 0EE3](https://stacks.math.columbia.edu/tag/0EE3)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The length of an `𝒪_X`-module at a geometric point.** For an algebraic space `X` over a
scheme `S`, a geometric point `x̄` of `X` and an `𝒪_X`-module `F`, this is the length of the
stalk `F_{x̄}` of Stacks 05VQ as a module over the étale local ring `𝒪_{X, x̄}` of
Stacks 04KG, a value in `ℕ∞ = {0, 1, 2, …, ∞}`.

This is the quantity of condition (1) of Stacks 0EE1; Stacks 0EE2 defines "`F` has length `d`
at a point `x` of `|X|`" to mean that this value is `d` for a geometric point above `x`, which
by Stacks 0EE1 does not depend on the choice — proved, for a quasi-coherent `F`, as
`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq` in
`GeometricLengthPointIndependence.lean`. -/
@[stacks 0EE2 "at a geometric point; no declaration packages a chosen geometric point above a
point of `|X|` together with the independence of Lemma 0EE1
(`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`) into the definition at a point of
`|X|`"]
def geometricLength (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)
    (F : Modules.{u, m} B S hS X.1 X.2) : ℕ∞ :=
  Module.length (etaleLocalRing B S hS X.1 x) (geometricModuleStalk B S hS X x F)

variable {B S hS}

/-- **The length at a geometric point vanishes exactly when every germ there vanishes.** A
module has length `0` at `x̄` precisely when every section of it on every small étale
neighbourhood of `x̄` has zero germ at `x̄`.

The length of a module is `0` exactly when the module has one element
(`Module.length_eq_zero_iff`), and the stalk at `x̄` is nontrivial exactly when some germ is
nonzero (`AlgebraicGeometry.Space.nontrivial_geometricModuleStalk_iff`). -/
theorem geometricLength_eq_zero_iff (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) (F : Modules.{u, m} B S hS X.1 X.2) :
    geometricLength B S hS X x F = 0 ↔
      ∀ (N : SmallEtaleNeighborhood x) (s : F.val.obj (Opposite.op N.chart)),
        geometricModuleStalkGerm B S hS X x F N s = 0 := by
  rw [geometricLength, Module.length_eq_zero_iff, ← not_nontrivial_iff_subsingleton,
    nontrivial_geometricModuleStalk_iff]
  push Not
  rfl

/-- **The length at a geometric point is positive exactly when some germ there is nonzero.**
This is the contrapositive form of
`AlgebraicGeometry.Space.geometricLength_eq_zero_iff`, read through
`Module.length_pos_iff`. -/
theorem geometricLength_pos_iff (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) (F : Modules.{u, m} B S hS X.1 X.2) :
    0 < geometricLength B S hS X x F ↔
      ∃ (N : SmallEtaleNeighborhood x) (s : F.val.obj (Opposite.op N.chart)),
        geometricModuleStalkGerm B S hS X x F N s ≠ 0 := by
  rw [geometricLength, Module.length_pos_iff, nontrivial_geometricModuleStalk_iff]

/-- **Length transfer along a surjection of étale local rings.** Let `X` and `Y` be algebraic
spaces over `S`, let `x̄` and `ȳ` be geometric points of them, let `F` be an `𝒪_X`-module and
`G` an `𝒪_Y`-module. Suppose the germ map `φ : 𝒪_{X, x̄} → 𝒪_{Y, ȳ}` is surjective and the
stalk of `F` at `x̄` is isomorphic, as an additive group, to the stalk of `G` at `ȳ` by a map
semilinear over `φ`. Then `F` has the same length at `x̄` as `G` has at `ȳ`.

Restriction of scalars along a surjection does not change the lattice of submodules, hence not
its Krull dimension, which is the length
(`Module.length_eq_of_surjective_of_addEquiv`).

This is the final step of Stacks 0EE3 for algebraic spaces: for a closed immersion
`i : Y ⟶ X`, with `G` an `𝒪_Y`-module, `F = i_*G` and `x̄` the image of `ȳ`, the hypotheses are
surjectivity of the germ map of `i` and the computation of the stalk of a direct image at the
image point. -/
theorem geometricLength_eq_of_surjective_of_addEquiv {X Y : AlgebraicSpaces B S hS}
    (x : GeometricPoint B S hS X.1) (y : GeometricPoint B S hS Y.1)
    (F : Modules.{u, m} B S hS X.1 X.2) (G : Modules.{u, m} B S hS Y.1 Y.2)
    (φ : etaleLocalRing B S hS X.1 x →+* etaleLocalRing B S hS Y.1 y)
    (hφ : Function.Surjective φ)
    (e : geometricModuleStalk B S hS X x F ≃+ geometricModuleStalk B S hS Y y G)
    (he : ∀ (r : etaleLocalRing B S hS X.1 x) (s : geometricModuleStalk B S hS X x F),
      e (r • s) = φ r • e s) :
    geometricLength B S hS X x F = geometricLength B S hS Y y G :=
  Module.length_eq_of_surjective_of_addEquiv φ hφ e.symm fun r n =>
    e.injective (by rw [e.apply_symm_apply, he, e.apply_symm_apply])

end AlgebraicGeometry.Space

end
