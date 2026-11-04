module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.RegularModelSurface

/-!
# The standing situation of a regular proper model

A regular proper model `(X, p, e)` of a smooth projective curve `C` over the fraction field `K` of
a discrete valuation ring `R` with `H⁰(C, 𝒪_C) = K`, in the sense of [Stacks, Tag 0C2S] and
[Stacks, Tag 0C2V], is packaged here as an instance of the standing situation
`Stacks.Models.RegularProperModelSituation` of [Stacks, Tag 0C61], with a chosen uniformizer and
the canonical residue field. The ring, fields, curve and model are the given ones
definitionally, so the geometry of a regular model developed for the situation applies to the
model.

## Main definitions

* `Stacks.Models.regularProperModelSituation` — the situation attached to a regular proper model.

## Main results

* `Stacks.Models.isIntegralRegularSurface_of_isModel` — the total space of a regular proper model
  is an integral Noetherian scheme regular of dimension two.

## References

* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C2V](https://stacks.math.columbia.edu/tag/0C2V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The standing situation of [Stacks, Tag 0C61] attached to a regular proper model `(X, p, e)` of
a smooth projective curve `c : C ⟶ Spec K` with `H⁰(C, 𝒪_C) = K`: the uniformizer is a chosen
irreducible element of `R` and the residue field is `IsLocalRing.ResidueField R`. -/
def regularProperModelSituation {C X : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsCurve K c]
    [Smooth c] (hproj : Stacks.HProjective.IsHProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hmod : IsModel c p e) [IsProper p] (hreg : IsRegular X) :
    RegularProperModelSituation.{u} :=
  haveI : Flat p := hmod.1
  haveI : LocallyOfFiniteType p := hmod.2.1
  haveI : QuasiCompact p := hmod.2.2.1
  { R := R
    K := K
    k := IsLocalRing.ResidueField R
    residueEquiv := AlgEquiv.refl
    C := C
    C_to_K := c
    X := X
    X_to_R := p
    regular := hreg
    genericFiberIso := e
    genericFiberIso_over_K := hmod.2.2.2
    π := (IsDiscreteValuationRing.exists_irreducible R).choose
    uniformizer := (IsDiscreteValuationRing.exists_irreducible R).choose_spec
    curveProjective := hproj }

/-- **The total space of a regular proper model is an integral Noetherian scheme regular of
dimension two.** -/
theorem isIntegralRegularSurface_of_isModel {C X : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsCurve K c] [Smooth c] (hproj : Stacks.HProjective.IsHProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hmod : IsModel c p e) [IsProper p] (hreg : IsRegular X) :
    Stacks.ResolutionOfSurfaces.IsIntegralRegularSurface X :=
  (regularProperModelSituation c hproj p e hmod hreg).isIntegralRegularSurface

end Stacks.Models

end
