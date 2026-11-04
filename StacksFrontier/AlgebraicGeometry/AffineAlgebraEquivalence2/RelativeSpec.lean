module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative spectrum of a quasi-coherent algebra

Let `S` be a scheme and let `A` be a quasi-coherent sheaf of commutative `𝒪_S`-algebras. The
spectra `Spec A(U)`, for `U` an affine open of `S`, glue to a scheme affine over `S`: this is
the relative spectrum of `A`, and it is the object needed for the essential surjectivity of the
anti-equivalence of Stacks Tag 01SA.

## Main definitions

* `specSectionsFunctor` is the functor `U ↦ Spec A(U)` on the affine opens of `S`, and
  `specSectionsToBase` is the natural transformation to the open subschemes `U`.
* `relativeSpecGluingData` is the resulting relative gluing datum over the directed affine cover
  of `S`, `relativeSpec` is the glued scheme and `relativeSpecToBase` its structure morphism.

## Main results

* `isAffineOpen_preimage_relativeSpecToBase`: the preimage of an affine open `U` of `S` under
  the structure morphism is affine, with `Spec A(U)` as an open immersion onto it.
* `isAffineHom_relativeSpecToBase`: the structure morphism of the relative spectrum is an affine
  morphism.

## Implementation notes

The gluing is Mathlib's `AlgebraicGeometry.Scheme.Cover.RelativeGluingData` (Stacks Tag 01LH)
over `AlgebraicGeometry.Scheme.directedAffineCover`, the cover of `S` by *all* its affine opens,
which is locally directed because the affine opens form a basis. The equifibered condition of
the gluing datum is exactly the family of cartesian squares
`Stacks.RelativeSpec.isPullback_specMap_restriction`, i.e. Stacks Tag 01LN; the naturality of
`specSectionsToBase` is the commutativity of those same squares.

Affineness of the preimage of an affine open is read off from
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData.toBase_preimage_eq_opensRange_ι`: the
preimage of `U` is the range of the open immersion `Spec A(U) ⟶ relativeSpec A`, hence affine.

## References

* [Stacks Project, Tag 01LN](https://stacks.math.columbia.edu/tag/01LN)
* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.AffineAlgebraEquivalence

section

variable {S : Scheme.{u}} (A : Stacks.RelativeSpec.AlgebraSheaf S)

/-- The affine open of `S` indexing an object of the directed affine cover of `S`. -/
public abbrev coverOpen (U : S.directedAffineCover.I₀) : S.affineOpens := U

/-- The restriction map of an algebra sheaf along an inclusion of affine opens. -/
public noncomputable abbrev secRes {U V : S.affineOpens} (h : U ⟶ V) :
    A.right.obj.obj (op (V : S.Opens)) ⟶ A.right.obj.obj (op (U : S.Opens)) :=
  A.right.obj.map (homOfLE (leOfHom h)).op

/-- The restriction map of an algebra sheaf along an identity is the identity. -/
public theorem secRes_id (U : S.affineOpens) :
    secRes A (𝟙 U) = 𝟙 (A.right.obj.obj (op (U : S.Opens))) :=
  A.right.obj.map_id (op (U : S.Opens))

/-- The restriction maps of an algebra sheaf compose. -/
public theorem secRes_comp {U V W : S.affineOpens} (h₁ : U ⟶ V) (h₂ : V ⟶ W) :
    secRes A (h₁ ≫ h₂) = secRes A h₂ ≫ secRes A h₁ :=
  A.right.obj.map_comp _ _

/-- The functor on the affine opens of `S` sending `U` to `Spec A(U)`. -/
public noncomputable def specSectionsFunctor : S.affineOpens ⥤ Scheme.{u} where
  obj U := Spec (A.right.obj.obj (op (U : S.Opens)))
  map {U V} h := Spec.map (secRes A h)
  map_id U := by rw [secRes_id, Spec.map_id]
  map_comp h₁ h₂ := by rw [secRes_comp, Spec.map_comp]

variable [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A]

/-- The relative-spectrum situation attached to a quasi-coherent algebra sheaf. -/
public noncomputable abbrev situation : Stacks.RelativeSpec.RelativeSpecSituation.{u} :=
  { base := S, algebra := A }

/-- The natural transformation from `U ↦ Spec A(U)` to the open subschemes `U`, given by the
structure morphism of `A` followed by the canonical isomorphism `Spec Γ(S, U) ≅ U`. -/
public noncomputable def specSectionsToBase :
    specSectionsFunctor A ⟶ S.directedAffineCover.functorOfLocallyDirected :=
  { app := fun (U : S.affineOpens) ↦
      Spec.map (A.hom.hom.app (op (U : S.Opens))) ≫ U.2.isoSpec.inv
    naturality := fun (U V : S.affineOpens) (h : U ⟶ V) ↦
      (Stacks.RelativeSpec.isPullback_specMap_restriction (situation A) (U : S.Opens)
        (V : S.Opens) U.2 V.2 (leOfHom h)).w }

/-- The relative gluing datum, over the directed affine cover of `S`, whose glued scheme is the
relative spectrum of `A`. Its equifibered condition is Stacks Tag 01LN. -/
public noncomputable def relativeSpecGluingData :
    Scheme.Cover.RelativeGluingData S.directedAffineCover where
  functor := specSectionsFunctor A
  natTrans := specSectionsToBase A
  equifibered := fun (U V : S.affineOpens) (h : U ⟶ V) ↦
    Stacks.RelativeSpec.isPullback_specMap_restriction (situation A) (U : S.Opens)
      (V : S.Opens) U.2 V.2 (leOfHom h)

/-- The relative spectrum of a quasi-coherent algebra sheaf. -/
public noncomputable def relativeSpec : Scheme.{u} :=
  (relativeSpecGluingData A).glued

/-- The structure morphism of the relative spectrum. -/
public noncomputable def relativeSpecToBase : relativeSpec A ⟶ S :=
  (relativeSpecGluingData A).toBase

/-- The preimage in the relative spectrum of an affine open of the base, indexed by the
directed affine cover, is affine: it is the range of the open immersion from `Spec A(U)`. -/
public theorem isAffineOpen_preimage_toBase (U : S.directedAffineCover.I₀) :
    IsAffineOpen ((relativeSpecGluingData A).toBase ⁻¹ᵁ (coverOpen U : S.Opens)) := by
  have h2 : (S.directedAffineCover.f U).opensRange = (coverOpen U : S.Opens) :=
    Scheme.Opens.opensRange_ι _
  have h := (relativeSpecGluingData A).toBase_preimage_eq_opensRange_ι U
  rw [h2] at h
  rw [h]
  have : IsAffine ((relativeSpecGluingData A).functor.obj U) :=
    inferInstanceAs (IsAffine (Spec (A.right.obj.obj (op (coverOpen U : S.Opens)))))
  exact isAffineOpen_opensRange (colimit.ι (relativeSpecGluingData A).functor U)

/-- **Stacks Project, Tag 01LX(1).** The preimage of an affine open of the base in the relative
spectrum is affine. -/
@[stacks 01LX "affine_inverse_image", sga "3 I 4.2" "Spec(A) affine over S"]
public theorem isAffineOpen_preimage_relativeSpecToBase (U : S.affineOpens) :
    IsAffineOpen (relativeSpecToBase A ⁻¹ᵁ (U : S.Opens)) :=
  isAffineOpen_preimage_toBase A U

/-- The structure morphism of the relative spectrum is an affine morphism. -/
public instance isAffineHom_relativeSpecToBase : IsAffineHom (relativeSpecToBase A) := by
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun x ↦ ?_
  obtain ⟨U, hU, hxU, -⟩ :=
    Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens (show x ∈ (⊤ : S.Opens) from trivial)
  exact ⟨U, hxU, hU, isAffineOpen_preimage_relativeSpecToBase A ⟨U, hU⟩⟩

/-- The relative spectrum, as an object of the category of schemes affine over the base. -/
public noncomputable def relativeSpecAffineOver : AffineOver S :=
  ⟨Over.mk (relativeSpecToBase A), isAffineHom_relativeSpecToBase A⟩

end

end Stacks.AffineAlgebraEquivalence

end
