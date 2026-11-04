module

public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Transporting along the restriction isomorphisms of a base change

A morphism `f : Y ⟶ X` and an open `U` of `X` give a base change `Y ×_X U`, canonically
isomorphic to the inverse image `f ⁻¹ᵁ U` in `Y` by
`AlgebraicGeometry.pullbackRestrictIsoRestrict`, under which the second projection corresponds to
the restriction `f ∣_ U`. This file records what that identification transports.

For an inclusion `U ≤ V` of opens there are two such base changes, and a morphism between them
commuting with the first projections is, after transport along the two isomorphisms, the
inclusion `f ⁻¹ᵁ U ⟶ f ⁻¹ᵁ V`.

For a single open, a property of morphisms respecting isomorphisms cannot tell the restriction
and the base change apart: the two spellings of "`f` has `P` over `U`" agree.

## Main results

* `AlgebraicGeometry.prop_morphismRestrict_iff_pullback_snd`: a morphism property respecting
  isomorphisms holds for `f ∣_ U` exactly when it holds for `pullback.snd f U.ι`.
* `AlgebraicGeometry.pullbackRestrictIsoRestrict_trans_eq_homOfLE`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **A property of morphisms holds for the restriction of `f` to an open of its target exactly
when it holds for the base change of `f` along the inclusion of that open.** The two morphisms
differ by the isomorphism `AlgebraicGeometry.pullbackRestrictIsoRestrict`, which a property
respecting isomorphisms cannot see. -/
lemma prop_morphismRestrict_iff_pullback_snd (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) :
    P (f ∣_ U) ↔ P (Limits.pullback.snd f U.ι) := by
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f U,
    P.cancel_left_of_respectsIso (pullbackRestrictIsoRestrict f U).hom (f ∣_ U)]

/-- Transport a morphism of base changes of `f` along the canonical identifications of those
base changes with the inverse images of the opens. -/
lemma pullbackRestrictIsoRestrict_trans_eq_homOfLE
    {Y X : Scheme.{u}} (f : Y ⟶ X) {U V : X.Opens} (hUV : U ≤ V)
    (t : Limits.pullback f U.ι ⟶ Limits.pullback f V.ι)
    (ht : t ≫ Limits.pullback.fst f V.ι = Limits.pullback.fst f U.ι) :
    (pullbackRestrictIsoRestrict f U).inv ≫ t ≫ (pullbackRestrictIsoRestrict f V).hom =
      Y.homOfLE (f.preimage_mono hUV) := by
  rw [← cancel_mono (Scheme.Opens.ι (f ⁻¹ᵁ V)), Category.assoc, Category.assoc,
    pullbackRestrictIsoRestrict_hom_ι, ht, pullbackRestrictIsoRestrict_inv_fst,
    Scheme.homOfLE_ι]

end AlgebraicGeometry

end
