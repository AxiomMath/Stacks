module

public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.Stratification
public import Mathlib.AlgebraicGeometry.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# The spectrum of the ring of a finite vanishing-pattern stratification

For a finite subset `E` of a commutative ring `A`, the ring `A_E` is the finite product, over the
decompositions `E = E' ⨿ E''`, of the localizations `A^~_{Z(E', E'')}`. Its spectrum
`X_E = Spec(A_E)` is the disjoint union of the spectra `X_{E', E''} = Spec(A^~_{Z(E', E'')})`.

## Main definitions

* `AlgebraicGeometry.ProEtale.specStratificationRingIso`: the isomorphism between `Spec(A_E)`
  and the coproduct of the schemes `X_{E', E''}`.

## Main results

* `AlgebraicGeometry.ProEtale.ι_specStratificationRingIso_inv`: on the summand indexed by a
  decomposition, the isomorphism is `Spec` of the projection of `A_E` onto that factor.

## References

* [Stacks Project, Tag 0970](https://stacks.math.columbia.edu/tag/0970)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

universe u

variable {A : Type u} [CommRing A]

/-- The spectrum `X_E = Spec(A_E)` of the stratification ring is the coproduct of the spectra
`X_{E', E''} = Spec(A^~_{Z(E', E'')})` over all decompositions `E = E' ⨿ E''`. -/
@[stacks 0970]
def specStratificationRingIso (E : Finset A) :
    Spec (.of (stratificationRing E)) ≅
      ∐ fun E' : {E' : Finset A // E' ⊆ E} =>
        Spec (.of (localizationRing (stratumIdeal E E') (stratumOpenElement E'.val))) :=
  have : Finite {E' : Finset A // E' ⊆ E} :=
    Finite.of_injective (fun E' => (⟨E'.val, Finset.mem_powerset.mpr E'.property⟩ :
      {s // s ∈ E.powerset})) fun _ _ h =>
        Subtype.ext (congrArg (fun k : {s // s ∈ E.powerset} => k.val) h)
  (asIso (sigmaSpec fun E' : {E' : Finset A // E' ⊆ E} =>
    CommRingCat.of (localizationRing (stratumIdeal E E') (stratumOpenElement E'.val)))).symm

/-- The summand `X_{E', E''}` of `X_E` is embedded by `Spec` of the projection of `A_E` onto the
factor `A^~_{Z(E', E'')}`. -/
theorem ι_specStratificationRingIso_inv (E : Finset A) (E' : {E' : Finset A // E' ⊆ E}) :
    Sigma.ι (fun E' : {E' : Finset A // E' ⊆ E} =>
        Spec (.of (localizationRing (stratumIdeal E E') (stratumOpenElement E'.val)))) E' ≫
      (specStratificationRingIso E).inv =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun E' : {E' : Finset A // E' ⊆ E} =>
        localizationRing (stratumIdeal E E') (stratumOpenElement E'.val)) E')) :=
  ι_sigmaSpec _ E'

end AlgebraicGeometry.ProEtale

end
