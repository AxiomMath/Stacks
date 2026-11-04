module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel
public import StacksFrontier.RingTheory.Nilpotent.Ideal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional

/-!
# Compatible systems of pseudo-coherent complexes over an inverse system of bases

Let `(Aₙ)` be an inverse system of rings whose transition maps are surjective with locally
nilpotent kernels and let `A = lim Aₙ`. Over `Spec A` fix a scheme `X` which is proper, flat and
of finite presentation, and write `Xₙ = X ×_{Spec A} Spec Aₙ`, viewed as a closed subscheme of
`X`. Grothendieck's existence theorem in this generality starts from a compatible system
`(Kₙ, φₙ)` of pseudo-coherent objects of `D(𝒪_{Xₙ})`, where `φₙ` exhibits `Kₙ` as the derived
restriction of `Kₙ₊₁`, and produces a pseudo-coherent object of `D(𝒪_X)` restricting to all of
them. This module records the standing data of that theorem.

## Main definitions

* `AlgebraicGeometry.GrothendieckExistence.limitBase`: the spectrum of the inverse-limit ring.
* `AlgebraicGeometry.GrothendieckExistence.baseAt`,
  `AlgebraicGeometry.GrothendieckExistence.baseProjection` and
  `AlgebraicGeometry.GrothendieckExistence.baseTransition`: the affine base at a level, its
  morphism to the inverse-limit base, and the transition between consecutive levels.
* `AlgebraicGeometry.GrothendieckExistence.schemeAt` and
  `AlgebraicGeometry.GrothendieckExistence.schemeProjection`: the base change of a scheme over
  the inverse-limit base to a level, and its morphism to that scheme.
* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation`: the rings, the scheme and
  the compatible family of pseudo-coherent derived objects.

## Implementation notes

The index `n : ℕ` stands for the level `n + 1` of the source, so that the system of transitions
is indexed by `n ↦ n + 1` rather than by `n ↦ n - 1`; the inverse system is a functor out of
`ℕᵒᵖ`, whose transition morphisms are the images of `homOfLE (Nat.le_succ n)`.

The scheme over the inverse-limit base is given as an object of `Over (limitBase system)`,
which packages the scheme together with its structure morphism. The transition morphisms
`Xₙ ⟶ Xₙ₊₁` between the base changes are recorded as data together with the two equations
saying that they commute with the projections to `X` and to the affine bases; those two
equations characterize them, by the universal property of the fibre product.

The comparison `φₙ` is stated in its adjoint form: the source gives a map
`Kₙ₊₁ ⟶ Riₙ,* Kₙ` and asks that the adjoint `Liₙ^* Kₙ₊₁ ⟶ Kₙ` be an isomorphism, so recording
the adjoint together with its invertibility is exactly the derived base-change requirement.

## References

* [Stacks Project, Tag 0DIB](https://stacks.math.columbia.edu/tag/0DIB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.GrothendieckExistence

attribute [local instance] HasDerivedCategory.standard

variable (F : ℕᵒᵖ ⥤ CommRingCat.{u})

/-- The spectrum of the inverse-limit ring of an inverse system of rings indexed by `ℕᵒᵖ`. -/
public abbrev limitBase : Scheme.{u} := Spec (limit F)

/-- The spectrum of the ring at level `n` of an inverse system of rings. -/
public abbrev baseAt (n : ℕ) : Scheme.{u} := Spec (F.obj (op n))

/-- The canonical morphism from the base at level `n` to the inverse-limit base, the spectrum
of the projection out of the limit. -/
public abbrev baseProjection (n : ℕ) : baseAt F n ⟶ limitBase F :=
  Spec.map (limit.π F (op n))

/-- The transition morphism of affine bases, from level `n` to level `n + 1`. -/
public abbrev baseTransition (n : ℕ) : baseAt F n ⟶ baseAt F (n + 1) :=
  Spec.map (F.map (homOfLE (Nat.le_succ n)).op)

variable (X : Over (limitBase F))

/-- The base change of a scheme over the inverse-limit base to the base at level `n`. -/
public abbrev schemeAt (n : ℕ) : Scheme.{u} := pullback X.hom (baseProjection F n)

/-- The morphism from the base change at level `n` to the scheme itself; under the hypotheses
of `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation` it is a closed
immersion, so it presents the base change as a closed subscheme. -/
public abbrev schemeProjection (n : ℕ) : schemeAt F X n ⟶ X.left :=
  pullback.fst X.hom (baseProjection F n)

/-- **Stacks Project, Tag 0DIB.** The standing data of Grothendieck's existence theorem in its
derived form: an inverse system of rings with surjective, locally nilpotent transitions, a
proper flat scheme of finite presentation over the inverse-limit ring, and a compatible system
of pseudo-coherent objects on its base changes. -/
@[stacks 0DIB]
public structure DerivedExistenceSituation where
  /-- The inverse system of rings. -/
  system : ℕᵒᵖ ⥤ CommRingCat.{u}
  /-- Its consecutive transition maps are surjective. -/
  transition_surjective (n : ℕ) :
    Function.Surjective (system.map (homOfLE (Nat.le_succ n)).op).hom
  /-- The kernels of those transition maps are locally nilpotent. -/
  transition_locallyNilpotent (n : ℕ) :
    (RingHom.ker (system.map (homOfLE (Nat.le_succ n)).op).hom).LocallyNilpotent
  /-- The scheme over the inverse-limit ring. -/
  X : Over (limitBase system)
  /-- The scheme is proper over the inverse-limit ring. -/
  proper : IsProper X.hom
  /-- The scheme is flat over the inverse-limit ring. -/
  flat : Flat X.hom
  /-- The scheme is of finite presentation over the inverse-limit ring. -/
  finitePresentation : FinitePresentation X.hom
  /-- Each base change is a closed subscheme of the scheme. -/
  closedSchemeProjection (n : ℕ) : IsClosedImmersion (schemeProjection system X n)
  /-- The canonical inclusion of the base change at level `n` into the one at level `n + 1`. -/
  transitionScheme (n : ℕ) : schemeAt system X n ⟶ schemeAt system X (n + 1)
  /-- Consecutive base changes are related by a closed immersion. -/
  closedTransitionScheme (n : ℕ) : IsClosedImmersion (transitionScheme n)
  /-- The transition morphism lies over the scheme. -/
  transition_fst (n : ℕ) :
    transitionScheme n ≫ schemeProjection system X (n + 1) = schemeProjection system X n
  /-- The transition morphism lies over the transition of affine bases. -/
  transition_snd (n : ℕ) :
    transitionScheme n ≫ pullback.snd X.hom (baseProjection system (n + 1)) =
      pullback.snd X.hom (baseProjection system n) ≫ baseTransition system n
  /-- The derived object on the base change at level `n`. -/
  K (n : ℕ) :
    DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} (schemeAt system X n).toRingedSpace)
  /-- Each derived object is pseudo-coherent. -/
  pseudoCoherent (n : ℕ) :
    RingedSpace.IsPseudoCoherent (X := (schemeAt system X n).toRingedSpace) (K n)
  /-- The comparison map, the adjoint of the transition map into the derived pushforward. -/
  φ (n : ℕ) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (transitionScheme n).toLRSHom.toShHom).obj (K (n + 1)) ⟶ K n
  /-- The comparison map is an isomorphism: the derived restriction of the object at level
  `n + 1` is the object at level `n`. -/
  φ_isIso (n : ℕ) : IsIso (φ n)

end AlgebraicGeometry.GrothendieckExistence
