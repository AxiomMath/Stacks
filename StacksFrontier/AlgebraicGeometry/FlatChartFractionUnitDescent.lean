module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.RingTheory.FaithfullyFlatFractionUnit

/-!
# A total fraction which becomes a unit on a flat affine chart over a local ring

Let `R` be a local ring, let `g : Y ⟶ Spec R` be a flat morphism with `Y` affine and let `y ∈ Y`
lie over the closed point. If a total fraction `c` of `Γ(Spec R)` restricts, in the total
fractions of `Γ(Y)`, to the image of a *unit* regular function on `Y`, then `c` is already the
image of a unit regular function on `Spec R`.

The descent is through the **local ring** `𝒪_{Y, y}`, not through `Γ(Y)`: the point of taking a
point over the closed point is that `Γ(Spec R) → 𝒪_{Y, y}` is then a *local* homomorphism of
local rings, which together with flatness makes it faithfully flat
(`Module.FaithfullyFlat.of_flat_of_isLocalHom`). The chart `Γ(Y)` itself need not be faithfully
flat over `Γ(Spec R)` — an étale chart can miss points — and `Mathlib`'s only constructor for
faithful flatness from flatness needs both rings local, so no statement about `Γ(Y)` alone
would do.

Both halves of the factorisation `Γ(Spec R) → 𝒪_{Y, y}` are supplied by the hypotheses: the
germ of `Spec R` at the closed point is an *isomorphism* onto `Γ(Spec R)`
(`AlgebraicGeometry.isIso_germ_top_of_eq_closedPoint`, from Mathlib's
`AlgebraicGeometry.stalkClosedPointIso`), and the stalk map of `g` is flat and local because `g`
is flat and a morphism of schemes. Flatness of `Γ(Y) → 𝒪_{Y, y}` is the localization of an
affine chart at a prime.

## Main results

* `AlgebraicGeometry.isIso_germ_top_of_eq_closedPoint`: the germ of the spectrum of a local
  ring at its closed point is an isomorphism.
* `AlgebraicGeometry.exists_isUnit_eq_appTop_of_isUnit_of_flat`: the descent above.

## References

* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

/-- **The germ of the spectrum of a local ring at its closed point is an isomorphism.** It is
the global-sections comparison `Γ(Spec R, ⊤) ≅ R` followed by the inverse of Mathlib's
`AlgebraicGeometry.stalkClosedPointIso`.

The point is given as any point equal to the closed point, so that a consumer holding the
equality `g.base y = IsLocalRing.closedPoint R` can substitute it rather than rewrite under the
dependent type of the germ. -/
theorem isIso_germ_top_of_eq_closedPoint (R : CommRingCat.{u}) [IsLocalRing R]
    (p : Spec R) (hp : p = IsLocalRing.closedPoint R) :
    IsIso ((Spec R).presheaf.germ ⊤ p trivial) := by
  subst hp
  have h : (Spec R).presheaf.germ ⊤ (IsLocalRing.closedPoint R) trivial =
      (Scheme.ΓSpecIso R).hom ≫ (stalkClosedPointIso R).inv :=
    (stalkClosedPointIso R).eq_comp_inv.mpr (germ_stalkClosedPointIso_hom R)
  rw [h]
  infer_instance

/-- **A total fraction which becomes a unit on a flat affine chart over a local ring was already
the image of a unit.** Let `g : Y ⟶ Spec R` be flat with `Y` affine and `R` local, and let
`y ∈ Y` lie over the closed point. If `ρ` is any ring map between the total rings of fractions
of `Γ(Spec R, ⊤)` and of `Γ(Y, ⊤)` over `g.appTop`, and `ρ c` is the image of a unit of
`Γ(Y, ⊤)`, then `c` is the image of a unit of `Γ(Spec R, ⊤)`.

The descent goes through the local ring `𝒪_{Y, y}`, which is faithfully flat over
`Γ(Spec R, ⊤)`: flat because `g` is, and local over it because `y` lies over the closed point.

The four instance arguments carrying the two total rings of fractions are *named*, so that a
consumer holding them at another (definitionally equal) spelling of the two rings of regular
functions can pass them by name: instance search bridges no two spellings of the ring of regular
functions on a chart, and the ones the small étale site produces are not the ones written
here. -/
theorem exists_isUnit_eq_appTop_of_isUnit_of_flat
    (R : CommRingCat.{u}) [IsLocalRing R] (Y : Scheme.{u}) [IsAffine Y]
    (g : Y ⟶ Spec R) [AlgebraicGeometry.Flat g] (y : Y)
    (hy : g.base y = IsLocalRing.closedPoint R)
    {K KO : Type*} [CommRing K] [CommRing KO]
    [algK : Algebra ↥Γ(Spec R, ⊤) K] [fracK : IsFractionRing ↥Γ(Spec R, ⊤) K]
    [algKO : Algebra ↥Γ(Y, ⊤) KO] [fracKO : IsFractionRing ↥Γ(Y, ⊤) KO]
    (ρ : K →+* KO)
    (hρ : ∀ a : ↥Γ(Spec R, ⊤),
      ρ (algebraMap ↥Γ(Spec R, ⊤) K a) = algebraMap ↥Γ(Y, ⊤) KO (g.appTop.hom a))
    {c : K} {v : ↥Γ(Y, ⊤)} (hv : IsUnit v) (hc : ρ c = algebraMap ↥Γ(Y, ⊤) KO v) :
    ∃ a : ↥Γ(Spec R, ⊤), IsUnit a ∧ c = algebraMap ↥Γ(Spec R, ⊤) K a := by
  -- `Γ(Spec R, ⊤)` is a local ring, being isomorphic to `R`.
  have hlocA : IsLocalRing ↥Γ(Spec R, ⊤) :=
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.isLocalRing
  -- The three algebra structures, chosen so that the scalar tower is an identity.
  let algAO : Algebra ↥Γ(Spec R, ⊤) ↥Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  let algOD : Algebra ↥Γ(Y, ⊤) ↥(Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, trivial⟩ : (⊤ : Y.Opens))
  let algAD : Algebra ↥Γ(Spec R, ⊤) ↥(Y.presheaf.stalk y) :=
    ((Y.presheaf.germ ⊤ y trivial).hom.comp g.appTop.hom).toAlgebra
  have htower : IsScalarTower ↥Γ(Spec R, ⊤) ↥Γ(Y, ⊤) ↥(Y.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- The germ of `Spec R` at the image of `y` is an isomorphism, `y` lying over the closed point.
  have hgiso : IsIso ((Spec R).presheaf.germ ⊤ (g.base y) trivial) :=
    isIso_germ_top_of_eq_closedPoint R _ hy
  have hgbij : Function.Bijective ((Spec R).presheaf.germ ⊤ (g.base y) trivial).hom :=
    (asIso ((Spec R).presheaf.germ ⊤ (g.base y) trivial)).commRingCatIsoToRingEquiv.bijective
  have hgloc : IsLocalHom ((Spec R).presheaf.germ ⊤ (g.base y) trivial).hom :=
    IsLocalHom.of_surjective _ hgbij.surjective
  -- `Γ(Spec R, ⊤) → 𝒪_{Y, y}` is that germ followed by the stalk map of `g`.
  have hfac : (algebraMap ↥Γ(Spec R, ⊤) ↥(Y.presheaf.stalk y)) =
      (g.stalkMap y).hom.comp ((Spec R).presheaf.germ ⊤ (g.base y) trivial).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.germ_stalkMap g (⊤ : (Spec R).Opens) y trivial).symm
  -- Flatness and locality of `Γ(Spec R, ⊤) → 𝒪_{Y, y}`.
  have hADflat : Module.Flat ↥Γ(Spec R, ⊤) ↥(Y.presheaf.stalk y) := by
    rw [← RingHom.flat_algebraMap_iff, hfac]
    exact (RingHom.Flat.of_bijective hgbij).comp (AlgebraicGeometry.Flat.stalkMap g y)
  have hADloc : IsLocalHom (algebraMap ↥Γ(Spec R, ⊤) ↥(Y.presheaf.stalk y)) := by
    rw [hfac]
    infer_instance
  -- Flatness of `Γ(Y, ⊤) → 𝒪_{Y, y}`: the local ring of an affine chart is a localization.
  have hloc : IsLocalization.AtPrime ↥(Y.presheaf.stalk y)
      ((isAffineOpen_top Y).primeIdealOf (⟨y, trivial⟩ : (⊤ : Y.Opens))).asIdeal :=
    (isAffineOpen_top Y).isLocalization_stalk (⟨y, trivial⟩ : (⊤ : Y.Opens))
  have hODflat : Module.Flat ↥Γ(Y, ⊤) ↥(Y.presheaf.stalk y) :=
    IsLocalization.flat ↥(Y.presheaf.stalk y)
      ((isAffineOpen_top Y).primeIdealOf (⟨y, trivial⟩ : (⊤ : Y.Opens))).asIdeal.primeCompl
  exact exists_isUnit_eq_algebraMap_of_isUnit_of_flat_of_isLocalHom hADflat hADloc hODflat ρ hρ
    hv hc

end AlgebraicGeometry

end
