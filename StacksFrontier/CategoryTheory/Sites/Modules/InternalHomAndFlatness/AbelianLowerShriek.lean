module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Lower shriek for abelian sheaves along a continuous functor

Let `u : C ⥤ D` be a functor between small sites. Restriction along `u` is the functor `u^p`
sending an abelian presheaf `G` on `D` to `G ∘ u`, and on abelian sheaves it is the inverse image
`g^{-1}` of the induced morphism of topoi, provided `u` is continuous. Its left adjoint on abelian
sheaves is lower shriek `g_!`, the sheafification of the left Kan extension along `u.op`.

The construction is the composite `sheafToPresheaf ⋙ u.op.lan ⋙ presheafToSheaf`, so that
`(g_! F)(V)` is the sheafification of the colimit `colim_{V → u U} F(U)`, and the adjunction
`g_! ⊣ g^{-1}` is the left Kan extension adjunction composed with the sheafification adjunction,
restricted along the fully faithful inclusion of sheaves into presheaves.

## Main definitions

* `Stacks.Sites.abelianRestriction`: restriction `u^p` of abelian presheaves along `u`.
* `Stacks.Sites.abelianInverseImage`: the inverse image `g^{-1}` of abelian sheaves.
* `Stacks.Sites.abelianShriek`: lower shriek `g_!` of abelian sheaves.

## Main results

* `Stacks.Sites.abelianShriekAdjunction`: `g_! ⊣ g^{-1}`.
* `Stacks.Sites.abelianInverseImage_comp_sheafToPresheaf` and
  `Stacks.Sites.abelianInverseImageUnderlyingIso`: the underlying presheaf of `g^{-1} G` is `u^p`
  of the underlying presheaf of `G`, naturally in `G`.

## Implementation notes

The three functors are reducible abbreviations rather than definitions. The identifications they
satisfy — restriction commutes with forgetting the group structure, and the underlying presheaf of
an inverse image is a restriction — then hold by `rfl` and are available to `simp` and to instance
search, instead of needing the elaborator to unfold definitions at reduced transparency.

## References

* [Stacks Project, Tag 04BG](https://stacks.math.columbia.edu/tag/04BG)
* [Stacks Project, Tag 04BF](https://stacks.math.columbia.edu/tag/04BF), lower shriek on
  presheaves.
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR), the identification of
  the inverse image with restriction.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace Stacks.Sites

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]

/-- Restriction `u^p` of abelian presheaves along `u`, sending `G` to `G ∘ u`. On sections it is
`(u^p G)(U) = G(u U)`. -/
noncomputable abbrev abelianRestriction (u : C ⥤ D) :
    (Dᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{u}).obj u.op

/-- The inverse image `g^{-1}` of abelian sheaves along a continuous functor. Since `u` is
continuous, restriction carries sheaves to sheaves, so this is the restriction of
`abelianRestriction` to abelian sheaves. -/
noncomputable abbrev abelianInverseImage (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [u.IsContinuous J K] :
    Sheaf K AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
  u.sheafPushforwardContinuous AddCommGrpCat.{u} J K

/-- Lower shriek `g_!` of abelian sheaves: sheafify the left Kan extension along `u.op` of the
underlying abelian presheaf. -/
noncomputable abbrev abelianShriek (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) :
    Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u} :=
  sheafToPresheaf J AddCommGrpCat.{u} ⋙ u.op.lan ⋙ presheafToSheaf K AddCommGrpCat.{u}

/-- The underlying presheaf of `g^{-1} G` is `u^p` of the underlying presheaf of `G`, naturally
in `G`. -/
theorem abelianInverseImage_comp_sheafToPresheaf (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [u.IsContinuous J K] :
    abelianInverseImage u J K ⋙ sheafToPresheaf J AddCommGrpCat.{u} =
      sheafToPresheaf K AddCommGrpCat.{u} ⋙ abelianRestriction u :=
  rfl

/-- The identification of the previous theorem, read as an isomorphism of functors. -/
noncomputable abbrev abelianInverseImageUnderlyingIso (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [u.IsContinuous J K] :
    abelianInverseImage u J K ⋙ sheafToPresheaf J AddCommGrpCat.{u} ≅
      sheafToPresheaf K AddCommGrpCat.{u} ⋙ abelianRestriction u :=
  Iso.refl _

/-- Lower shriek is left adjoint to the inverse image: `g_! ⊣ g^{-1}`. -/
noncomputable def abelianShriekAdjunction (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [u.IsContinuous J K] :
    abelianShriek u J K ⊣ abelianInverseImage u J K :=
  ((u.op.lanAdjunction AddCommGrpCat.{u}).comp
      (sheafificationAdjunction K AddCommGrpCat.{u})).restrictFullyFaithful
    (iC := sheafToPresheaf J AddCommGrpCat.{u}) (iD := 𝟭 (Sheaf K AddCommGrpCat.{u}))
    (fullyFaithfulSheafToPresheaf J AddCommGrpCat.{u}) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _)

end Stacks.Sites
