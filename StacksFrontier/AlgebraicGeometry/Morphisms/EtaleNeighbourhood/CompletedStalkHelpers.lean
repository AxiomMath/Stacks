module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Reading a local homomorphism off the morphism it induces on spectra

A local homomorphism `f : 𝒪_{X, x} ⟶ R` out of the local ring of a scheme at a point and the
morphism `Spec.map f ≫ X.fromSpecStalk x : Spec R ⟶ X` which it induces determine one another.
This file collects the small lemmas passing between the two, together with the completed local
ring of a scheme at a point as an object of `CommRingCat`.

They are used by the files which prove the clauses of Tag 0GDX. Those files do not import one
another, so the helpers live here, in a leaf module they can all import.

Nothing here mentions `AlgebraicGeometry.Scheme.Hom.stalkHomAt`, so this module imports only
Mathlib. The two helpers which do mention it are in
`StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.StalkHomAtHelpers`, which imports
this module; keeping them apart is what lets a consumer needing only the lemmas below --
`CompletedStalkClosedPoint.lean` is one -- stay off the import closure of
`IsomorphismApproximation.lean`, where `stalkHomAt` is defined.

## Main results

* `StacksDraft.ArtinApproximation.specMap_fromSpecStalk_closedPoint`: the morphism attached to a
  local homomorphism out of `𝒪_{X, x}` carries the closed point to `x`.
* `StacksDraft.ArtinApproximation.stalkCongr_comp_stalkClosedPointTo`: the local homomorphism
  which that morphism induces on the stalk at the image of the closed point is `f` again.
* `StacksDraft.ArtinApproximation.stalkCongr_comp_stalkClosedPointTo_congr`: that local
  homomorphism depends only on the morphism, so an equality of morphisms transports it.

## Implementation notes

The type of `AlgebraicGeometry.Scheme.stalkClosedPointTo f` is indexed by `f (closedPoint R)`, and
`↥(Spec R)` is `PrimeSpectrum ↑R` only after unfolding `Spec`. Goals mentioning such a point are
therefore not type-correct at the transparency level at which `rw` abstracts its pattern, and `rw`
reports the pattern as missing even where it is plainly present. The proofs below take the same
steps with `congrArg`, `Eq.trans` and `change`, which elaborate at default transparency.

## References

* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
* [Stacks Project, Tag 0CAW](https://stacks.math.columbia.edu/tag/0CAW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AdicCompletion

universe u

namespace StacksDraft.ArtinApproximation

/-- The completed local ring of a scheme at a point, as an object of `CommRingCat`. -/
public abbrev completedStalkObj (S : Scheme.{u}) (s : S) : CommRingCat.{u} :=
  CommRingCat.of (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))

/-- The germ on an open, followed by the transport of stalks along an equality of points, is the
germ at the other point. -/
public theorem germ_comp_stalkCongr_hom {X : Scheme.{u}} {a b : X} (hab : a = b) (U : X.Opens)
    (ha : a ∈ U) :
    X.presheaf.germ U a ha ≫ (X.presheaf.stalkCongr (.of_eq hab)).hom =
      X.presheaf.germ U b (hab ▸ ha) := by
  cases hab
  simp

/-- The morphism `Spec.map f ≫ X.fromSpecStalk x` attached to a local homomorphism out of the
local ring at `x` carries the closed point to `x`. -/
public theorem specMap_fromSpecStalk_closedPoint {X : Scheme.{u}} {x : X} {R : CommRingCat.{u}}
    [IsLocalRing R] (f : X.presheaf.stalk x ⟶ R) [IsLocalHom f.hom] :
    (Spec.map f ≫ X.fromSpecStalk x) (closedPoint R) = x :=
  (congrArg (fun z => (X.fromSpecStalk x) z) (Spec_closedPoint (f := f))).trans
    Scheme.fromSpecStalk_closedPoint

/-- The local homomorphism attached to a morphism out of the spectrum of a local ring depends
only on that morphism, so it may be transported along an equality of morphisms. -/
public theorem stalkCongr_comp_stalkClosedPointTo_congr {X : Scheme.{u}} {R : CommRingCat.{u}}
    [IsLocalRing R] (m₁ m₂ : Spec R ⟶ X) (hm : m₁ = m₂) {x : X}
    (h₁ : m₁ (closedPoint R) = x) (h₂ : m₂ (closedPoint R) = x) :
    (X.presheaf.stalkCongr (.of_eq h₁.symm)).hom ≫ Scheme.stalkClosedPointTo m₁ =
      (X.presheaf.stalkCongr (.of_eq h₂.symm)).hom ≫ Scheme.stalkClosedPointTo m₂ := by
  subst hm
  rfl

/-- The local homomorphism `𝒪_{X, x} ⟶ R` which `Spec.map f ≫ X.fromSpecStalk x` induces on the
stalk at the image of the closed point is `f` itself, read through the transport identifying that
image with `x`. -/
public theorem stalkCongr_comp_stalkClosedPointTo {X : Scheme.{u}} {x : X}
    {R : CommRingCat.{u}} [IsLocalRing R] (f : X.presheaf.stalk x ⟶ R) [IsLocalHom f.hom]
    (h : (Spec.map f ≫ X.fromSpecStalk x) (closedPoint R) = x) :
    (X.presheaf.stalkCongr (.of_eq h.symm)).hom ≫
        Scheme.stalkClosedPointTo (Spec.map f ≫ X.fromSpecStalk x) = f := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU => ?_
  have hU : (Spec.map f ≫ X.fromSpecStalk x) (closedPoint R) ∈ U :=
    (congrArg (fun z : X => z ∈ U) h.symm).mp hxU
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ Scheme.stalkClosedPointTo (Spec.map f ≫ X.fromSpecStalk x))
      (germ_comp_stalkCongr_hom h.symm U hxU))).trans
    (Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk f U hU)

end StacksDraft.ArtinApproximation

end
