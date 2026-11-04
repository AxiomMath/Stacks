module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionFromNeighborhoods
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout

/-!
# The neighbourhoods of a closed subscheme are unchanged by a thickening of the ambient scheme

Let `i : X' ⟶ X` be a thickening, that is a closed immersion which is surjective on points, so
that `i` is a homeomorphism of underlying spaces.  Let `Y ⊆ X` and `Y' ⊆ X'` be closed subschemes,
given by their ideal sheaves, and suppose `Y' ⊆ Y` is a thickening over `i`.

The open subschemes of `X` containing `Y`, ordered by reverse inclusion, are then in
inclusion-preserving bijection with the open subschemes of `X'` containing `Y'`: taking the
inverse image along `i` in one direction and the image under the homeomorphism in the other.  This
file records that bijection together with the compatibilities satisfied by the restrictions of `i`
over the members of it: those restrictions are again thickenings, by
`Stacks.Thickenings.IsThickening.morphismRestrict`, and they are compatible both with shrinking a
neighbourhood and with the inclusions of the two closed subschemes.

## Main definitions

* `Stacks.FundamentalGroup.Neighborhood.preimage` — the neighbourhood of `Y'` in `X'` underlying a
  neighbourhood of `Y` in `X`.
* `Stacks.FundamentalGroup.Neighborhood.image` — the neighbourhood of `Y` in `X` whose inverse
  image is a given neighbourhood of `Y'` in `X'`.

## Main results

* `Stacks.FundamentalGroup.support_eq_preimage_support_of_isThickening` — the two closed
  subschemes have the same underlying set, read through the homeomorphism.
* `Stacks.FundamentalGroup.support_le_iff_preimage_of_isThickening` — an open of `X` contains `Y`
  exactly when its inverse image contains `Y'`.
* `Stacks.FundamentalGroup.Neighborhood.preimage_image` — the two constructions are inverse.
* `Stacks.FundamentalGroup.Neighborhood.subschemeHom_comp_morphismRestrict` — the inclusion of
  `Y'` into a neighbourhood of `X'`, followed by the restriction of `i`, is the inclusion of `Y`
  into the corresponding neighbourhood of `X` precomposed with `Y' ⟶ Y`.
* `Stacks.FundamentalGroup.morphismRestrict_comp_homOfLE` — the restrictions of `i` to two nested
  opens of `X` commute with the two inclusions.

## Implementation notes

A neighbourhood is `Stacks.FundamentalGroup.Neighborhood`, the order dual of the subtype of opens
through which the closed immersion of the subscheme factors; by
`Stacks.FundamentalGroup.Neighborhood.support_subset_open` that subtype is cut out by the
set-theoretic containment of the support, and the factorisation itself is recovered from the
containment by `AlgebraicGeometry.IsOpenImmersion.lift`.  Since the defining property is a
proposition, two neighbourhoods with the same underlying open are equal, which is what makes the
two constructions below mutually inverse on the nose.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Thickenings

universe u

namespace Stacks.FundamentalGroup

/-! ### Factoring a closed subscheme through an open -/

/-- **A closed subscheme factors through an open subscheme containing its support.** -/
theorem exists_lift_of_support_le {Z : Scheme.{u}} (J : Z.IdealSheafData) (W : Z.Opens)
    (hW : (J.support : Set Z) ⊆ (W : Set Z)) :
    ∃ r : J.subscheme ⟶ W.toScheme, r ≫ W.ι = J.subschemeι := by
  have hr : Set.range J.subschemeι.base ⊆ Set.range W.ι.base := by
    rwa [Scheme.Opens.range_ι, J.range_subschemeι]
  exact ⟨IsOpenImmersion.lift W.ι J.subschemeι hr, IsOpenImmersion.lift_fac _ _ _⟩

/-- **Taking inverse images of opens is monotone.** -/
theorem opens_preimage_mono {Z W : Scheme.{u}} (f : Z ⟶ W) {U V : W.Opens} (h : U ≤ V) :
    f ⁻¹ᵁ U ≤ f ⁻¹ᵁ V := fun _ hx => h hx

/-! ### The two closed subschemes of a thickening have the same support -/

variable {X X' : Scheme.{u}} {i : X' ⟶ X} (hi : IsThickening i)
  (Y : X.IdealSheafData) (Y' : X'.IdealSheafData) (jY : Y'.subscheme ⟶ Y.subscheme)
  (hjY : jY ≫ Y.subschemeι = Y'.subschemeι ≫ i) (hjYt : IsThickening jY)

include hi hjY hjYt

/-- **The support of the smaller closed subscheme is the inverse image of the support of the
larger one.**  The inclusion of `Y'` into `X'` followed by `i` is the inclusion of `Y` into `X`
precomposed with the surjection `Y' ⟶ Y`, so the image of the support of `Y'` is the support of
`Y`; and `i` is injective on points. -/
theorem support_eq_preimage_support_of_isThickening :
    (Y'.support : Set X') = i.base ⁻¹' (Y.support : Set X) := by
  have hz : ∀ z, i (Y'.subschemeι z) = Y.subschemeι (jY z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← hjY, Scheme.Hom.comp_apply]
  apply Set.Subset.antisymm
  · intro y hy
    rw [← Y'.range_subschemeι] at hy
    obtain ⟨z, rfl⟩ := hy
    show i.base (Y'.subschemeι.base z) ∈ (Y.support : Set X)
    rw [hz, ← Y.range_subschemeι]
    exact ⟨jY z, rfl⟩
  · intro y hy
    obtain ⟨w, hw⟩ : i y ∈ Set.range Y.subschemeι.base := by rwa [Y.range_subschemeι]
    obtain ⟨z, rfl⟩ := hjYt.2 w
    rw [← Y'.range_subschemeι, ← hi.isHomeomorph.bijective.injective ((hz z).trans hw)]
    exact ⟨z, rfl⟩

/-- **An open of `X` contains `Y` exactly when its inverse image contains `Y'`.** -/
theorem support_le_iff_preimage_of_isThickening (W : X.Opens) :
    (Y.support : Set X) ⊆ (W : Set X) ↔
      (Y'.support : Set X') ⊆ ((i ⁻¹ᵁ W : X'.Opens) : Set X') := by
  rw [support_eq_preimage_support_of_isThickening hi Y Y' jY hjY hjYt]
  refine ⟨fun hW _ hy => hW hy, fun hW x hx => ?_⟩
  obtain ⟨y, rfl⟩ := hi.2 x
  exact hW hx

/-! ### The bijection between the two sets of neighbourhoods -/

/-- The neighbourhood of `Y'` in `X'` underlying a neighbourhood of `Y` in `X`: its inverse image
along `i`. -/
abbrev Neighborhood.preimage (V : Neighborhood X Y) : Neighborhood X' Y' :=
  OrderDual.toDual ⟨i ⁻¹ᵁ Neighborhood.open X Y V,
    exists_lift_of_support_le Y' _
      ((support_le_iff_preimage_of_isThickening hi Y Y' jY hjY hjYt _).mp
        (Neighborhood.support_subset_open X Y V))⟩

/-- The open underlying `Neighborhood.preimage V` is the inverse image along `i` of the open
underlying `V`. -/
@[simp]
theorem Neighborhood.open_preimage (V : Neighborhood X Y) :
    Neighborhood.open X' Y' (Neighborhood.preimage hi Y Y' jY hjY hjYt V) =
      i ⁻¹ᵁ Neighborhood.open X Y V :=
  rfl

/-- The neighbourhood of `Y` in `X` whose inverse image along `i` is a given neighbourhood of `Y'`
in `X'`; the underlying open is the image of the given one under the homeomorphism. -/
abbrev Neighborhood.image (V' : Neighborhood X' Y') : Neighborhood X Y :=
  OrderDual.toDual ⟨hi.opensCongr (Neighborhood.open X' Y' V'),
    exists_lift_of_support_le Y _
      ((support_le_iff_preimage_of_isThickening hi Y Y' jY hjY hjYt _).mpr
        (by rw [hi.preimage_opensCongr]; exact Neighborhood.support_subset_open X' Y' V'))⟩

/-- The open underlying `Neighborhood.image V'` is the image of the open underlying `V'` under the
homeomorphism `hi.opensCongr`. -/
@[simp]
theorem Neighborhood.open_image (V' : Neighborhood X' Y') :
    Neighborhood.open X Y (Neighborhood.image hi Y Y' jY hjY hjYt V') =
      hi.opensCongr (Neighborhood.open X' Y' V') :=
  rfl

/-- The inverse image of the neighbourhood of `Y` attached to a neighbourhood of `Y'` is the
neighbourhood of `Y'` one started with. -/
theorem Neighborhood.preimage_image (V' : Neighborhood X' Y') :
    Neighborhood.preimage hi Y Y' jY hjY hjYt (Neighborhood.image hi Y Y' jY hjY hjYt V') = V' :=
  Subtype.ext (hi.preimage_opensCongr _)

/-- The neighbourhood of `Y` attached to the inverse image of a neighbourhood of `Y` is that
neighbourhood again. -/
theorem Neighborhood.image_preimage (V : Neighborhood X Y) :
    Neighborhood.image hi Y Y' jY hjY hjYt (Neighborhood.preimage hi Y Y' jY hjY hjYt V) = V :=
  Subtype.ext (hi.opensCongr_preimage _)

/-- Taking inverse images preserves the order on neighbourhoods. -/
theorem Neighborhood.preimage_le_preimage {V W : Neighborhood X Y} (h : V ≤ W) :
    Neighborhood.preimage hi Y Y' jY hjY hjYt V ≤ Neighborhood.preimage hi Y Y' jY hjY hjYt W :=
  show i ⁻¹ᵁ Neighborhood.open X Y W ≤ i ⁻¹ᵁ Neighborhood.open X Y V from
    opens_preimage_mono i h

/-- Taking images preserves the order on neighbourhoods. -/
theorem Neighborhood.image_le_image {V' W' : Neighborhood X' Y'} (h : V' ≤ W') :
    Neighborhood.image hi Y Y' jY hjY hjYt V' ≤ Neighborhood.image hi Y Y' jY hjY hjYt W' :=
  show hi.opensCongr (Neighborhood.open X' Y' W') ≤ hi.opensCongr (Neighborhood.open X' Y' V') from
    hi.opensCongr.monotone h

/-! ### The restrictions of the thickening to the neighbourhoods -/

/-- **The restriction of a thickening to an open commutes with shrinking the open.** -/
theorem morphismRestrict_comp_homOfLE {W W₂ : X.Opens} (h : W₂ ≤ W) :
    (i ∣_ W₂) ≫ X.homOfLE h =
      X'.homOfLE (opens_preimage_mono i h) ≫ (i ∣_ W) := by
  apply (cancel_mono W.ι).1
  rw [Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, Category.assoc, morphismRestrict_ι,
    ← Category.assoc, Scheme.homOfLE_ι]

/-- **The inclusion of `Y'` into a neighbourhood, followed by the restriction of the thickening,
is the inclusion of `Y` into the corresponding neighbourhood precomposed with `Y' ⟶ Y`.** -/
theorem Neighborhood.subschemeHom_comp_morphismRestrict (V : Neighborhood X Y) :
    Neighborhood.toSchemeHom X' Y' (Neighborhood.preimage hi Y Y' jY hjY hjYt V) ≫
        (i ∣_ Neighborhood.open X Y V) =
      jY ≫ Neighborhood.toSchemeHom X Y V := by
  have hfac : Neighborhood.toSchemeHom X' Y' (Neighborhood.preimage hi Y Y' jY hjY hjYt V) ≫
      (i ⁻¹ᵁ Neighborhood.open X Y V).ι = Y'.subschemeι :=
    Neighborhood.toSchemeHom_fac X' Y' (Neighborhood.preimage hi Y Y' jY hjY hjYt V)
  refine (cancel_mono (Neighborhood.open X Y V).ι).1 ?_
  rw [Category.assoc jY, Neighborhood.toSchemeHom_fac X Y, hjY]
  erw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hfac]

end Stacks.FundamentalGroup

end
