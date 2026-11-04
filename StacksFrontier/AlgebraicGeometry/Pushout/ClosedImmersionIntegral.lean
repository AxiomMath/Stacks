module

public import StacksFrontier.AlgebraicGeometry.Pushout.Affine

/-!
# The affine chart of the pushout along a closed immersion and an integral morphism

In the situation of [Stacks Project, Tag 0ECI] -- a closed immersion `i : Z ⟶ X` and an
integral morphism `j : Z ⟶ Y` -- the pushout `Y ⨿_Z X` of [Stacks Project, Tag 0E25] is
constructed by gluing the affine model `Spec (Γ(Y) ×_{Γ(Z)} Γ(X))` over compatible affine
charts.  This file builds that affine model and establishes, for affine `X`, `Y` and `Z`,
every assertion of Tag 0E25 except the universal property itself: the square is a fibre
square, the map from `Y` is a closed immersion, and the map from `X` is integral.

## Main definitions

* `Stacks.Pushout.affineModel` is the affine model `Spec (Γ(Y, ⊤) ×_{Γ(Z, ⊤)} Γ(X, ⊤))`.
* `Stacks.Pushout.affineModelInl` and `Stacks.Pushout.affineModelInr` are the two canonical
  maps into it, from `X` and from `Y` respectively.

## Main results

* `Stacks.Pushout.isPullback_affineModel`: the square `i`, `j`, `affineModelInl`,
  `affineModelInr` is a fibre square.
* `Stacks.Pushout.isClosedImmersion_affineModelInr`: the map from `Y` is a closed immersion.
* `Stacks.Pushout.isIntegralHom_affineModelInl`: the map from `X` is integral.

## Implementation notes

The three assertions are transported from the ring-theoretic statements of
`StacksFrontier.AlgebraicGeometry.Pushout.Affine` along the canonical isomorphisms
`AlgebraicGeometry.Scheme.isoSpec` of the three affine schemes; the comparison squares are
`AlgebraicGeometry.Scheme.isoSpec_hom_naturality`.  The ring-theoretic hypotheses are supplied
by `AlgebraicGeometry.Scheme.Hom.app_surjective` for the closed immersion `i` and by
`AlgebraicGeometry.IsIntegralHom.isIntegral_app` for the integral morphism `j`, both applied to
the affine open `⊤`.

The universal property of the pushout, that is the colimit statement of Tag 0E25 together with
its affine case [Stacks Project, Tag 0ET0], is not proved here; see the discussion in the
module documentation of `StacksFrontier.AlgebraicGeometry.Pushout.Affine`.

## References

* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Pushout

variable {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)

/-- The ring of the affine model of the pushout: the fibre product `Γ(Y, ⊤) ×_{Γ(Z, ⊤)} Γ(X, ⊤)`
of the two rings of global sections over the ring of global sections of `Z`. -/
abbrev affineModelRing : CommRingCat.{u} :=
  CommRingCat.of (j.appTop.hom.pullback i.appTop.hom)

/-- The affine model of the pushout `Y ⨿_Z X`, namely the spectrum of the fibre product of the
rings of global sections. -/
noncomputable abbrev affineModel : Scheme.{u} := Spec (affineModelRing i j)

/-- The canonical map from `X` to the affine model of the pushout.  It is the integral leg. -/
noncomputable def affineModelInl [IsAffine X] : X ⟶ affineModel i j :=
  X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (j.appTop.hom.pullbackSnd i.appTop.hom))

/-- The canonical map from `Y` to the affine model of the pushout.  It is the closed
immersion. -/
noncomputable def affineModelInr [IsAffine Y] : Y ⟶ affineModel i j :=
  Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (j.appTop.hom.pullbackFst i.appTop.hom))

/-- A closed immersion with affine target is surjective on global sections. -/
theorem surjective_appTop_of_isClosedImmersion [IsAffine X] [IsClosedImmersion i] :
    Function.Surjective i.appTop.hom :=
  i.app_surjective ⊤ (isAffineOpen_top X)

/-- An integral morphism with affine target is integral on global sections. -/
theorem isIntegral_appTop_of_isIntegralHom [IsAffine Y] [IsIntegralHom j] :
    j.appTop.hom.IsIntegral :=
  IsIntegralHom.isIntegral_app j ⊤ (isAffineOpen_top Y)

variable [IsAffine X] [IsAffine Y] [IsAffine Z]

/-- **The fibre square, affine case of Stacks Tag 0E25.** For affine `X`, `Y` and `Z` and a
closed immersion `i : Z ⟶ X`, the square formed by `i`, `j` and the two canonical maps into the
affine model is cartesian. -/
theorem isPullback_affineModel [IsClosedImmersion i] :
    IsPullback i j (affineModelInl i j) (affineModelInr i j) := by
  refine (isPullback_specMap_pullback j.appTop.hom i.appTop.hom
    (surjective_appTop_of_isClosedImmersion i)).of_iso'
      Z.isoSpec X.isoSpec Y.isoSpec (Iso.refl _) (Scheme.isoSpec_hom_naturality i)
      (Scheme.isoSpec_hom_naturality j) ?_ ?_
  · simp [affineModelInl]
  · simp [affineModelInr]

/-- **The closed immersion, affine case of Stacks Tag 0E25.** The canonical map from `Y` to the
affine model of the pushout is a closed immersion. -/
instance isClosedImmersion_affineModelInr [IsClosedImmersion i] :
    IsClosedImmersion (affineModelInr i j) := by
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (j.appTop.hom.pullbackFst i.appTop.hom))) :=
    isClosedImmersion_specMap_pullbackFst j.appTop.hom i.appTop.hom
      (surjective_appTop_of_isClosedImmersion i)
  exact inferInstanceAs (IsClosedImmersion (Y.isoSpec.hom ≫ _))

/-- **The integral morphism, affine case of Stacks Tag 0E25.** The canonical map from `X` to the
affine model of the pushout is integral. -/
instance isIntegralHom_affineModelInl [IsClosedImmersion i] [IsIntegralHom j] :
    IsIntegralHom (affineModelInl i j) := by
  have : IsIntegralHom
      (Spec.map (CommRingCat.ofHom (j.appTop.hom.pullbackSnd i.appTop.hom))) :=
    isIntegralHom_specMap_pullbackSnd j.appTop.hom i.appTop.hom
      (surjective_appTop_of_isClosedImmersion i) (isIntegral_appTop_of_isIntegralHom j)
  exact inferInstanceAs (IsIntegralHom (X.isoSpec.hom ≫ _))

end Stacks.Pushout

end
