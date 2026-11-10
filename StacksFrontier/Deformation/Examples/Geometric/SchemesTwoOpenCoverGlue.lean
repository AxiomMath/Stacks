module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTwoOpenCover
public import StacksFrontier.Deformation.Smooth.FullVertical

/-!
# The glueing quasi-inverse of Tag 0DYZ on morphisms

This file supplies the two steps of [Stacks Project, Tag 0DYZ] whose verification the source
omits, and which are what the smoothness assertion of [Stacks Project, Tag 0DZN] needs. Let `X`
be a scheme over `k` covered by two opens `U₁`, `U₂`, let `Q` be an object of the `2`-fibre
product `Def_{U₁} ×_{Def_{U₁₂}} Def_{U₂}` and let `glueDeformation Q` be the deformation of `X`
glued from it (`Deformation.Examples.glueDeformation`).

* The two chart isomorphisms `Deformation.Examples.restrictGlueDeformationLeft` and
  `Deformation.Examples.restrictGlueDeformationRight` of the glued deformation are compatible
  with the comparison isomorphism of `Q`, so they are the two components of a *single*
  isomorphism `comparison (glueDeformation Q) ≅ Q` of the `2`-fibre product
  (`Deformation.Examples.comparisonGlueHom`), and that isomorphism is vertical over `𝒞_Λ`.
* A morphism `Q ⟶ comparison P` of the `2`-fibre product into the comparison of a deformation
  `P` of `X` glues to a morphism `glueDeformation Q ⟶ P` of deformations of `X`
  (`Deformation.Examples.glueDeformationHom`), and the triangle formed by the three of them
  commutes.

Together these are exactly the data a lifting problem for smoothness asks for, and
`Deformation.Examples.isSmooth_twoOpenComparisonBasedFunctor` assembles them.

## Main definitions

* `Deformation.Examples.overlapι`: the inclusion of the overlap chart of a deformation of an
  open `U` into it, for a smaller open `V ≤ U`. This is the `Deformation.Examples.nestedι` of
  an arbitrary deformation of `U` rather than of a restriction, and it is the form in which the
  restriction functor's naturality is stated.
* `Deformation.Examples.coverOfRestrictions`: the two opens that `U₁` and `U₂` cut out in the
  total space of a deformation of `X`, as an open cover of that total space.
* `Deformation.Examples.overlapLeft`, `Deformation.Examples.overlapRight`: the two inclusions of
  the open cut out by `U₁ ⊓ U₂` into the opens cut out by `U₁` and by `U₂`.
* `Deformation.Examples.glueDefι₁`, `Deformation.Examples.glueDefι₂`,
  `Deformation.Examples.glueDefι₀`: the three charts of the glued scheme, read as morphisms into
  the total space of the glued *deformation*.
* `Deformation.Examples.comparisonGlueHom`: the comparison morphism
  `comparison (glueDeformation Q) ⟶ Q`.
* `Deformation.Examples.glueDeformationHom`: the glued morphism `glueDeformation Q ⟶ P`.

## Main results

* `Deformation.Examples.restrictedOpen_sup_eq_top`, `Deformation.Examples.restrictedOpen_inf`:
  the opens cut out in a deformation by two opens covering `X` cover it, and the open cut out by
  an intersection is the intersection of the opens cut out.
* `Deformation.Examples.comparisonGlue_w`: the compatibility of the two chart isomorphisms with
  the comparison isomorphism of `Q`.
* `Deformation.Examples.isHomLift_comparisonGlueHom`: the comparison morphism is vertical.
* `Deformation.Examples.glueHomLeft_base_eq_glueHomRight_base`: the two restrictions of the
  glued morphism lie over the same morphism of `𝒞_Λ`, which is where the verticality of the
  comparison isomorphism of the datum is used a second time.
* `Deformation.Examples.twoOpenComparisonFunctor_map_glueDeformationHom`: the triangle
  `comparison (glued morphism) = comparison morphism ≫ given morphism` commutes.
* `Deformation.Examples.isSmooth_twoOpenComparisonBasedFunctor`: **Stacks 0DYZ** in the form
  Tag 0DZN uses it — the comparison morphism of a two-open cover is smooth.

## Implementation notes

All the morphisms of schemes here are morphisms between total spaces of deformations, and the
types in which they are stated matter: `(restrictDeformation U P).scheme` and
`(restrictedOpen P U).toScheme` are equal only by unfolding a semireducible definition, which
`rewrite` does not do when it abstracts a motive. Every statement below is therefore written
through the deformations — `Deformation.Examples.restrictDeformationι`,
`Deformation.Examples.overlapι`, `Deformation.Examples.glueDefι₁` — and never through the
underlying opens; `Deformation.Examples.glueDefι₁` and its companions exist only to move the
charts of `Deformation.Examples.glueScheme` into that spelling.

Verticality of the comparison isomorphism of `Q` is used twice, and only through
`Deformation.Examples.glueBaseIso_comp_eqToHom`: for the base compatibility of the two chart
isomorphisms, which lie over the two *different* identifications `Q.x.base = Q.base` and
`Q.y.base = Q.base`, and for the identification of the base morphism of the glued morphism with
that of its first component.

## References

* [Stacks Project, Tag 0DYZ](https://stacks.math.columbia.edu/tag/0DYZ)
* [Stacks Project, Tag 0DZN](https://stacks.math.columbia.edu/tag/0DZN)
* [Stacks Project, Tag 06HG](https://stacks.math.columbia.edu/tag/06HG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {X : Over (Spec (.of k))}

/-! ### The opens cut out in the total space of a deformation -/

/-- Two opens covering `X` cut out two opens covering the total space of any deformation
of `X`, the special-fibre immersion being a homeomorphism of underlying spaces. -/
theorem restrictedOpen_sup_eq_top (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    {U₁ U₂ : X.left.Opens} (hcover : U₁ ⊔ U₂ = ⊤) :
    restrictedOpen P U₁ ⊔ restrictedOpen P U₂ = ⊤ := by
  refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun y => ?_)
  obtain ⟨x, hx⟩ := deformationSpecialMap_surjective P y
  have hx' : x ∈ U₁ ⊔ U₂ := by rw [hcover]; trivial
  rcases hx' with h | h
  · exact Or.inl ⟨x, h, hx⟩
  · exact Or.inr ⟨x, h, hx⟩

/-- The open cut out in the total space of a deformation by an intersection of two opens is the
intersection of the two opens cut out, the special-fibre immersion being injective. -/
theorem restrictedOpen_inf (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (U V : X.left.Opens) :
    restrictedOpen P (U ⊓ V) = restrictedOpen P U ⊓ restrictedOpen P V :=
  TopologicalSpace.Opens.ext
    (Set.image_inter (deformationSpecialMap_isHomeomorph P).injective)

/-- An open of the total space of a deformation is determined by the open it cuts out on the
special fibre, that fibre being all of the total space. -/
theorem eq_restrictedOpen_of_specialMap_preimage
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) X} {V : P.scheme.Opens}
    {U : X.left.Opens} (h : P.specialMap ⁻¹ᵁ V = U) : V = restrictedOpen P U := by
  refine TopologicalSpace.Opens.ext (Set.eq_of_subset_of_subset ?_ ?_)
  · intro y hy
    obtain ⟨x, hx⟩ := deformationSpecialMap_surjective P y
    refine ⟨x, ?_, hx⟩
    have hxV : x ∈ P.specialMap ⁻¹ᵁ V := show P.specialMap x ∈ V from hx ▸ hy
    rwa [h] at hxV
  · rintro y ⟨x, hxU, rfl⟩
    have hxV : x ∈ P.specialMap ⁻¹ᵁ V := by rw [h]; exact hxU
    exact hxV

/-- A morphism of total spaces compatible with the special-fibre immersions pulls the open cut
out by `U` back to the open cut out by `U`. -/
theorem preimage_restrictedOpen_of_specialMap_comp
    {P G : SchemeDeformationCategory (Λ := Λ) (k := k) X} (m : P.scheme ⟶ G.scheme)
    (hm : P.specialMap ≫ m = G.specialMap) (U : X.left.Opens) :
    m ⁻¹ᵁ restrictedOpen G U = restrictedOpen P U := by
  refine eq_restrictedOpen_of_specialMap_preimage ?_
  rw [← TopologicalSpace.Opens.map_comp_obj, ← Scheme.Hom.comp_base, hm,
    specialMap_preimage_restrictedOpen]

/-- The two opens that `U₁` and `U₂` cut out in the total space of a deformation of `X`, as an
open cover of that total space. -/
def coverOfRestrictions (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    {U₁ U₂ : X.left.Opens} (hcover : U₁ ⊔ U₂ = ⊤) : P.scheme.OpenCover :=
  Scheme.Cover.mkOfCovers Bool
    (fun b => bif b then (restrictDeformation U₂ P).scheme else (restrictDeformation U₁ P).scheme)
    (fun b => Bool.rec (restrictDeformationι U₁ P) (restrictDeformationι U₂ P) b)
    (fun y => by
      have hy : y ∈ restrictedOpen P U₁ ⊔ restrictedOpen P U₂ := by
        rw [restrictedOpen_sup_eq_top P hcover]; trivial
      rcases hy with h | h
      · exact ⟨false, ⟨y, h⟩, rfl⟩
      · exact ⟨true, ⟨y, h⟩, rfl⟩)
    (fun b => by cases b <;> exact inferInstance)

/-- The first member of the cover is the open cut out by `U₁`. -/
theorem coverOfRestrictions_f_false (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    {U₁ U₂ : X.left.Opens} (hcover : U₁ ⊔ U₂ = ⊤) :
    (coverOfRestrictions P hcover).f false = restrictDeformationι U₁ P :=
  rfl

/-- The second member of the cover is the open cut out by `U₂`. -/
theorem coverOfRestrictions_f_true (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    {U₁ U₂ : X.left.Opens} (hcover : U₁ ⊔ U₂ = ⊤) :
    (coverOfRestrictions P hcover).f true = restrictDeformationι U₂ P :=
  rfl

/-! ### Restriction along an inclusion of opens, on morphisms -/

/-- The inclusion of the open cut out by `V ≤ U` in a deformation of the open subscheme `U` into
that deformation. For a deformation restricted from `X` this is
`Deformation.Examples.nestedι`. -/
def overlapι {U V : X.left.Opens} (h : V ≤ U)
    (D : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk (U.ι ≫ X.hom))) :
    ((openRestrictionLEFunctor (Λ := Λ) (k := k) h).obj D).scheme ⟶ D.scheme :=
  (restrictedOpen D (U.ι ⁻¹ᵁ V)).ι

/-- Restricting a morphism of deformations of an open `U` to a smaller open `V` is compatible
with the inclusions of the cut-out opens. -/
@[reassoc]
theorem openRestrictionLEFunctor_map_map_comp_overlapι {U V : X.left.Opens} (h : V ≤ U)
    {D D' : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk (U.ι ≫ X.hom))} (c : D ⟶ D') :
    ((openRestrictionLEFunctor (Λ := Λ) (k := k) h).map c).map ≫ overlapι h D =
      overlapι h D' ≫ c.map := by
  have key : Scheme.Hom.resLE c.map (restrictedOpen D (U.ι ⁻¹ᵁ V))
        (restrictedOpen D' (U.ι ⁻¹ᵁ V)) (le_map_preimage_restrictedOpen c) ≫
      (restrictedOpen D (U.ι ⁻¹ᵁ V)).ι = (restrictedOpen D' (U.ι ⁻¹ᵁ V)).ι ≫ c.map :=
    Scheme.Hom.resLE_comp_ι c.map (le_map_preimage_restrictedOpen c)
  exact key

/-- The inclusion of the twice-restricted total space is the inclusion of the overlap chart. -/
theorem nestedι_eq (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) {U V : X.left.Opens}
    (h : V ≤ U) : nestedι P h = overlapι h (restrictDeformation U P) :=
  rfl

/-! ### The two overlap inclusions inside a deformation of `X` -/

section Overlap

variable (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) (U₁ U₂ : X.left.Opens)

/-- The inclusion of the open cut out by `U₁ ⊓ U₂` into the open cut out by `U₁`. -/
def overlapLeft :
    (restrictDeformation (U₁ ⊓ U₂) P).scheme ⟶ (restrictDeformation U₁ P).scheme :=
  (nestedOpenIso P (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).inv ≫
    nestedι P (inf_le_left : U₁ ⊓ U₂ ≤ U₁)

/-- The inclusion of the open cut out by `U₁ ⊓ U₂` into the open cut out by `U₂`. -/
def overlapRight :
    (restrictDeformation (U₁ ⊓ U₂) P).scheme ⟶ (restrictDeformation U₂ P).scheme :=
  (nestedOpenIso P (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).inv ≫
    nestedι P (inf_le_right : U₁ ⊓ U₂ ≤ U₂)

/-- The left-hand overlap inclusion followed by the inclusion of the open cut out by `U₁` is the
inclusion of the open cut out by `U₁ ⊓ U₂`. -/
@[reassoc]
theorem overlapLeft_comp_ι :
    overlapLeft P U₁ U₂ ≫ restrictDeformationι U₁ P = restrictDeformationι (U₁ ⊓ U₂) P :=
  (Category.assoc _ _ _).trans
    (nestedOpenIso_inv_comp P (inf_le_left : U₁ ⊓ U₂ ≤ U₁))

/-- The right-hand overlap inclusion followed by the inclusion of the open cut out by `U₂` is the
inclusion of the open cut out by `U₁ ⊓ U₂`. -/
@[reassoc]
theorem overlapRight_comp_ι :
    overlapRight P U₁ U₂ ≫ restrictDeformationι U₂ P = restrictDeformationι (U₁ ⊓ U₂) P :=
  (Category.assoc _ _ _).trans
    (nestedOpenIso_inv_comp P (inf_le_right : U₁ ⊓ U₂ ≤ U₂))

/-- The left-hand overlap inclusion, unfolded. -/
theorem overlapLeft_eq :
    overlapLeft P U₁ U₂ =
      (nestedOpenIso P (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).inv ≫
        nestedι P (inf_le_left : U₁ ⊓ U₂ ≤ U₁) :=
  rfl

/-- The right-hand overlap inclusion, unfolded. -/
theorem overlapRight_eq :
    overlapRight P U₁ U₂ =
      (nestedOpenIso P (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).inv ≫
        nestedι P (inf_le_right : U₁ ⊓ U₂ ≤ U₂) :=
  rfl

/-- The right-hand overlap inclusion is an open immersion. -/
instance isOpenImmersion_overlapRight : IsOpenImmersion (overlapRight P U₁ U₂) := by
  rw [overlapRight_eq]
  infer_instance

/-- The open an inclusion of a cut-out open has as its range is that open. -/
theorem opensRange_restrictDeformationι (U : X.left.Opens) :
    (restrictDeformationι U P).opensRange = restrictedOpen P U :=
  Scheme.Opens.opensRange_ι _

/-- The range of the right-hand overlap inclusion is the open that `U₁ ⊓ U₂` cuts out in the
restriction of `P` to `U₂`. -/
theorem opensRange_overlapRight :
    (overlapRight P U₁ U₂).opensRange =
      restrictedOpen (restrictDeformation U₂ P) (U₂.ι ⁻¹ᵁ (U₁ ⊓ U₂)) := by
  have h : ((nestedOpenIso P (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).inv ≫
        nestedι P (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).opensRange =
      restrictedOpen (restrictDeformation U₂ P) (U₂.ι ⁻¹ᵁ (U₁ ⊓ U₂)) := by
    rw [Scheme.Hom.opensRange_comp_of_isIso]
    exact Scheme.Opens.opensRange_ι _
  exact h

/-- Inside the restriction of `P` to `U₂`, the open cut out by `U₁` is the open cut out by
`U₁ ⊓ U₂`. -/
theorem restrictDeformationι_preimage_restrictedOpen :
    restrictDeformationι U₂ P ⁻¹ᵁ restrictedOpen P U₁ =
      restrictedOpen (restrictDeformation U₂ P) (U₂.ι ⁻¹ᵁ (U₁ ⊓ U₂)) := by
  refine eq_restrictedOpen_of_specialMap_preimage ?_
  rw [← TopologicalSpace.Opens.map_comp_obj, ← Scheme.Hom.comp_base,
    restrictDeformation_specialMap_comp_ι, Scheme.Hom.comp_base,
    TopologicalSpace.Opens.map_comp_obj, specialMap_preimage_restrictedOpen,
    Scheme.Hom.preimage_inf, U₂.ι_preimage_self, inf_top_eq]

/-- **The open cut out by `U₁ ⊓ U₂` is the intersection of the opens cut out by `U₁` and
`U₂`**, as a cartesian square of the two inclusions. -/
theorem isPullback_overlap :
    IsPullback (overlapLeft P U₁ U₂) (overlapRight P U₁ U₂)
      (restrictDeformationι U₁ P) (restrictDeformationι U₂ P) :=
  IsOpenImmersion.isPullback (overlapLeft P U₁ U₂) (overlapRight P U₁ U₂)
    (restrictDeformationι U₁ P) (restrictDeformationι U₂ P)
    ((overlapRight_comp_ι P U₁ U₂).trans (overlapLeft_comp_ι P U₁ U₂).symm)
    (by
      rw [opensRange_restrictDeformationι, opensRange_overlapRight,
        restrictDeformationι_preimage_restrictedOpen])

end Overlap

/-! ### Consequences of the verticality of the comparison isomorphism -/

section Vertical

variable (X) (U₁ U₂ : X.left.Opens) (Q : TwoOpenDeformations (Λ := Λ) X U₁ U₂)

/-- **Verticality of the comparison isomorphism, as a compatibility of the two identifications
of the base.** The isomorphism of bases underlying the transition isomorphism carries the
identification `Q.x.base = Q.base` of the first chart to that of the second. -/
theorem glueBaseIso_comp_eqToHom :
    glueBaseIso X U₁ U₂ Q ≫ eqToHom Q.hx = eqToHom Q.hy := by
  have hvert := Q.vertical
  have hfac : Q.iso.hom.base = eqToHom Q.hx ≫ eqToHom Q.hy.symm := by
    have h := IsHomLift.fac'
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk ((U₁ ⊓ U₂).ι ≫ X.hom)))
      (𝟙 Q.base) Q.iso.hom
    rw [Category.id_comp] at h
    exact h
  have hIso : glueBaseIsoInv X U₁ U₂ Q = Q.iso.hom.base := rfl
  calc glueBaseIso X U₁ U₂ Q ≫ eqToHom Q.hx
      = (glueBaseIso X U₁ U₂ Q ≫ eqToHom Q.hx ≫ eqToHom Q.hy.symm) ≫ eqToHom Q.hy := by
        simp
    _ = eqToHom Q.hy := by
        rw [← hfac, ← hIso, glueBaseIso_comp_glueBaseIsoInv, Category.id_comp]

/-- The transition isomorphism of the datum, as an isomorphism of total spaces, is inverse to
the first component of the comparison isomorphism. -/
theorem isoHom_map_comp_glueTransition :
    Q.iso.hom.map ≫ glueTransition X U₁ U₂ Q = 𝟙 _ :=
  congrArg SchemeDeformationCategory.Hom.map Q.iso.inv_hom_id

end Vertical

/-! ### The charts of the glued scheme, read in the glued deformation -/

section Charts

variable (X) (U₁ U₂ : X.left.Opens) (Q : TwoOpenDeformations (Λ := Λ) X U₁ U₂)
  (hcover : U₁ ⊔ U₂ = ⊤)

/-- The first chart of the glued scheme, as a morphism into the total space of the glued
deformation. -/
def glueDefι₁ : Q.x.scheme ⟶ (glueDeformation X U₁ U₂ Q hcover).scheme :=
  glueι₁ X U₁ U₂ Q

/-- The second chart of the glued scheme, as a morphism into the total space of the glued
deformation. -/
def glueDefι₂ : Q.y.scheme ⟶ (glueDeformation X U₁ U₂ Q hcover).scheme :=
  glueι₂ X U₁ U₂ Q

/-- The overlap chart of the glued scheme, as a morphism into the total space of the glued
deformation. -/
def glueDefι₀ :
    ((openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).obj Q.x).scheme ⟶
      (glueDeformation X U₁ U₂ Q hcover).scheme :=
  glueι₀ X U₁ U₂ Q

/-- The overlap inclusion into the first deformation followed by the first chart of the glued
deformation is the overlap chart. -/
@[reassoc]
theorem overlapι_comp_glueDefι₁ :
    overlapι (inf_le_left : U₁ ⊓ U₂ ≤ U₁) Q.x ≫ glueDefι₁ X U₁ U₂ Q hcover =
      glueDefι₀ X U₁ U₂ Q hcover :=
  glueOverlapι₁_comp_glueι₁ X U₁ U₂ Q

/-- The transition map followed by the overlap inclusion into the second deformation and the
second chart of the glued deformation is the overlap chart. -/
@[reassoc]
theorem glueTransition_comp_overlapι_comp_glueDefι₂ :
    glueTransition X U₁ U₂ Q ≫
        overlapι (inf_le_right : U₁ ⊓ U₂ ≤ U₂) Q.y ≫ glueDefι₂ X U₁ U₂ Q hcover =
      glueDefι₀ X U₁ U₂ Q hcover :=
  glueOverlapι₂_comp_glueι₂ X U₁ U₂ Q

/-- The comparison isomorphism of the datum carries the overlap chart of the glued scheme onto
the overlap chart of the second deformation. -/
@[reassoc]
theorem isoHom_map_comp_glueDefι₀ :
    Q.iso.hom.map ≫ glueDefι₀ X U₁ U₂ Q hcover =
      overlapι (inf_le_right : U₁ ⊓ U₂ ≤ U₂) Q.y ≫ glueDefι₂ X U₁ U₂ Q hcover := by
  rw [← glueTransition_comp_overlapι_comp_glueDefι₂, ← Category.assoc,
    isoHom_map_comp_glueTransition, Category.id_comp]

/-- The underlying morphism of `restrictGlueDeformationLeftHom` followed by the inclusion of the
open cut out by `U₁` is the first chart `glueDefι₁` of the glued deformation. -/
@[reassoc]
theorem restrictGlueDeformationLeftHom_map_comp_ι :
    (restrictGlueDeformationLeftHom X U₁ U₂ Q hcover).map ≫
        restrictDeformationι U₁ (glueDeformation X U₁ U₂ Q hcover) =
      glueDefι₁ X U₁ U₂ Q hcover :=
  glueChartLeftIso_hom_comp_ι X U₁ U₂ Q hcover

/-- The underlying morphism of `restrictGlueDeformationRightHom` followed by the inclusion of the
open cut out by `U₂` is the second chart `glueDefι₂` of the glued deformation. -/
@[reassoc]
theorem restrictGlueDeformationRightHom_map_comp_ι :
    (restrictGlueDeformationRightHom X U₁ U₂ Q hcover).map ≫
        restrictDeformationι U₂ (glueDeformation X U₁ U₂ Q hcover) =
      glueDefι₂ X U₁ U₂ Q hcover :=
  glueChartRightIso_hom_comp_ι X U₁ U₂ Q hcover

/-! ### The comparison morphism out of the glued deformation -/

/-- **The two chart isomorphisms of the glued deformation are compatible with the comparison
isomorphism of the datum.** This is the `CategoryTheory.TwoFibreProductOver.Hom.w` of the pair,
that is, what makes `Deformation.Examples.restrictGlueDeformationLeft` and
`Deformation.Examples.restrictGlueDeformationRight` the two components of a *single* morphism of
the `2`-fibre product. The source of Tag 0DYZ says only "we omit the verification". -/
@[stacks 0DYZ "the compatibility of the two chart isomorphisms of the glueing with the \
comparison isomorphism of the datum, i.e. that the two of them are one morphism of the 2-fibre \
product; the equivalence itself is not proved here"]
theorem comparisonGlue_w :
    (openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).map
        (restrictGlueDeformationLeftHom X U₁ U₂ Q hcover) ≫ Q.iso.hom =
      (restrictDeformationLEIso (glueDeformation X U₁ U₂ Q hcover)
            (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≪≫
          (restrictDeformationLEIso (glueDeformation X U₁ U₂ Q hcover)
            (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).symm).hom ≫
        (openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).map
          (restrictGlueDeformationRightHom X U₁ U₂ Q hcover) := by
  refine SchemeDeformationCategory.Hom.ext ?_ ?_
  · change glueBaseIso X U₁ U₂ Q ≫ Q.iso.hom.base =
      (𝟙 Q.y.base ≫ 𝟙 Q.y.base) ≫ 𝟙 Q.y.base
    simp only [Category.comp_id]
    exact glueBaseIso_comp_glueBaseIsoInv X U₁ U₂ Q
  · refine (cancel_mono (nestedι (glueDeformation X U₁ U₂ Q hcover)
      (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫
        restrictDeformationι U₁ (glueDeformation X U₁ U₂ Q hcover))).mp ?_
    change (Q.iso.hom.map ≫
        ((openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).map
          (restrictGlueDeformationLeftHom X U₁ U₂ Q hcover)).map) ≫
        (nestedι (glueDeformation X U₁ U₂ Q hcover) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫
          restrictDeformationι U₁ (glueDeformation X U₁ U₂ Q hcover)) =
      (((openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).map
            (restrictGlueDeformationRightHom X U₁ U₂ Q hcover)).map ≫
          ((nestedOpenIso (glueDeformation X U₁ U₂ Q hcover)
              (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).hom ≫
            (nestedOpenIso (glueDeformation X U₁ U₂ Q hcover)
              (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).inv)) ≫
        (nestedι (glueDeformation X U₁ U₂ Q hcover) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫
          restrictDeformationι U₁ (glueDeformation X U₁ U₂ Q hcover))
    rw [Category.assoc, Category.assoc, Category.assoc,
      nestedOpenIso_inv_comp, nestedOpenIso_hom_comp,
      nestedι_eq (glueDeformation X U₁ U₂ Q hcover) (inf_le_left : U₁ ⊓ U₂ ≤ U₁),
      openRestrictionLEFunctor_map_map_comp_overlapι_assoc
        (inf_le_left : U₁ ⊓ U₂ ≤ U₁) (restrictGlueDeformationLeftHom X U₁ U₂ Q hcover),
      restrictGlueDeformationLeftHom_map_comp_ι, overlapι_comp_glueDefι₁,
      nestedι_eq (glueDeformation X U₁ U₂ Q hcover) (inf_le_right : U₁ ⊓ U₂ ≤ U₂),
      openRestrictionLEFunctor_map_map_comp_overlapι_assoc
        (inf_le_right : U₁ ⊓ U₂ ≤ U₂) (restrictGlueDeformationRightHom X U₁ U₂ Q hcover),
      restrictGlueDeformationRightHom_map_comp_ι,
      ← glueTransition_comp_overlapι_comp_glueDefι₂, ← Category.assoc,
      isoHom_map_comp_glueTransition, Category.id_comp]

/-- **Stacks 0DYZ**, the comparison morphism out of the glueing. The two chart isomorphisms of
the glued deformation are the two components of one morphism of the `2`-fibre product from the
comparison of the glued deformation to the datum it was glued from. -/
@[stacks 0DYZ "the comparison morphism from the comparison of the glued deformation to the \
datum, built from the two chart isomorphisms; it is an isomorphism, but only the morphism is \
constructed here, and the equivalence of Tag 0DYZ is not proved"]
def comparisonGlueHom :
    (twoOpenComparisonFunctor (Λ := Λ) X U₁ U₂).obj (glueDeformation X U₁ U₂ Q hcover) ⟶ Q where
  hbase := eqToHom Q.hy
  a := restrictGlueDeformationLeftHom X U₁ U₂ Q hcover
  b := restrictGlueDeformationRightHom X U₁ U₂ Q hcover
  ha := by
    refine IsHomLift.of_fac' _ (eqToHom Q.hy) _ rfl Q.hx ?_
    have hGB : glueBaseIso X U₁ U₂ Q = eqToHom Q.hy ≫ eqToHom Q.hx.symm := by
      rw [← glueBaseIso_comp_eqToHom X U₁ U₂ Q, Category.assoc, eqToHom_trans, eqToHom_refl,
        Category.comp_id]
    exact hGB.trans (Category.id_comp _).symm
  hb := by
    refine IsHomLift.of_fac' _ (eqToHom Q.hy) _ rfl Q.hy ?_
    have hId : (𝟙 Q.y.base : Q.y.base ⟶ Q.y.base) = eqToHom Q.hy ≫ eqToHom Q.hy.symm := by
      rw [eqToHom_trans, eqToHom_refl]
      rfl
    exact hId.trans (Category.id_comp _).symm
  w := comparisonGlue_w X U₁ U₂ Q hcover

/-- The comparison morphism out of the glueing is vertical over `𝒞_Λ`. -/
theorem isHomLift_comparisonGlueHom :
    (TwoFibreProductOver.structureFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U₁.ι ≫ X.hom)))
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U₂.ι ≫ X.hom)))
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk ((U₁ ⊓ U₂).ι ≫ X.hom)))
      (openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
      (openRestrictionLEFunctor (Λ := Λ) (k := k)
        (inf_le_right : U₁ ⊓ U₂ ≤ U₂))).IsHomLift (𝟙 Q.base)
      (comparisonGlueHom X U₁ U₂ Q hcover) := by
  refine IsHomLift.of_fac' _ (𝟙 Q.base) _ Q.hy rfl ?_
  have h : (eqToHom Q.hy : (schemeDeformationCategoryProjection
        (Λ := Λ) (k := k) (Over.mk (U₂.ι ≫ X.hom))).obj Q.y ⟶ Q.base) =
      eqToHom Q.hy ≫ 𝟙 Q.base ≫ eqToHom (rfl : Q.base = Q.base) := by
    rw [eqToHom_refl, Category.comp_id, Category.comp_id]
  exact h

end Charts

/-! ### The glued morphism of deformations -/

section GlueHom

variable (X) (U₁ U₂ : X.left.Opens) (Q : TwoOpenDeformations (Λ := Λ) X U₁ U₂)
  (hcover : U₁ ⊔ U₂ = ⊤) (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
  (g : Q ⟶ (twoOpenComparisonFunctor (Λ := Λ) X U₁ U₂).obj P)

/-- The first component of a morphism of the `2`-fibre product into the comparison of a
deformation `P`, read as a morphism of deformations of `U₁`. -/
def comparisonComponentLeft : Q.x ⟶ restrictDeformation U₁ P := g.a

/-- The second component, read as a morphism of deformations of `U₂`. -/
def comparisonComponentRight : Q.y ⟶ restrictDeformation U₂ P := g.b

/-- The restriction of the glued morphism to `U₁`: the first chart isomorphism of the glued
deformation followed by the first component of the given morphism. Its cartesian square is the
one the glued morphism needs over the first chart. -/
def glueHomLeft :
    restrictDeformation U₁ (glueDeformation X U₁ U₂ Q hcover) ⟶ restrictDeformation U₁ P :=
  restrictGlueDeformationLeftHom X U₁ U₂ Q hcover ≫ comparisonComponentLeft X U₁ U₂ Q P g

/-- The restriction of the glued morphism to `U₂`. -/
def glueHomRight :
    restrictDeformation U₂ (glueDeformation X U₁ U₂ Q hcover) ⟶ restrictDeformation U₂ P :=
  restrictGlueDeformationRightHom X U₁ U₂ Q hcover ≫ comparisonComponentRight X U₁ U₂ Q P g

/-- The `U₁`-component of the composite of the comparison morphism with the given morphism is
the restriction of the glued morphism to `U₁`. -/
theorem comparisonGlueHom_comp_a :
    (comparisonGlueHom X U₁ U₂ Q hcover ≫ g).a = glueHomLeft X U₁ U₂ Q hcover P g :=
  rfl

/-- The `U₂`-component likewise. -/
theorem comparisonGlueHom_comp_b :
    (comparisonGlueHom X U₁ U₂ Q hcover ≫ g).b = glueHomRight X U₁ U₂ Q hcover P g :=
  rfl

/-- **The two restrictions of the glued morphism lie over the same morphism of `𝒞_Λ`.** Both
are the base morphism of the composite of the comparison morphism with the given morphism, read
through the two components; that the two readings agree is the verticality of the comparison
isomorphism, used in `Deformation.Examples.comparisonGlueHom`. -/
theorem glueHomLeft_base_eq_glueHomRight_base :
    (glueHomLeft X U₁ U₂ Q hcover P g).base = (glueHomRight X U₁ U₂ Q hcover P g).base := by
  have ha := (comparisonGlueHom X U₁ U₂ Q hcover ≫ g).ha
  have hb := (comparisonGlueHom X U₁ U₂ Q hcover ≫ g).hb
  have h₁ := IsHomLift.fac'
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U₁.ι ≫ X.hom)))
    (comparisonGlueHom X U₁ U₂ Q hcover ≫ g).hbase
    (comparisonGlueHom X U₁ U₂ Q hcover ≫ g).a
  have h₂ := IsHomLift.fac'
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U₂.ι ≫ X.hom)))
    (comparisonGlueHom X U₁ U₂ Q hcover ≫ g).hbase
    (comparisonGlueHom X U₁ U₂ Q hcover ≫ g).b
  exact h₁.trans h₂.symm

/-- The underlying morphism of `glueHomLeft` followed by the inclusion of the open cut out by `U₁`
is the underlying morphism of `comparisonComponentLeft` followed by the first chart. -/
@[reassoc]
theorem glueHomLeft_map_comp_ι :
    (glueHomLeft X U₁ U₂ Q hcover P g).map ≫
        restrictDeformationι U₁ (glueDeformation X U₁ U₂ Q hcover) =
      (comparisonComponentLeft X U₁ U₂ Q P g).map ≫ glueDefι₁ X U₁ U₂ Q hcover := by
  have h : (glueHomLeft X U₁ U₂ Q hcover P g).map =
      (comparisonComponentLeft X U₁ U₂ Q P g).map ≫
        (restrictGlueDeformationLeftHom X U₁ U₂ Q hcover).map := rfl
  rw [h, Category.assoc, restrictGlueDeformationLeftHom_map_comp_ι]

/-- The underlying morphism of `glueHomRight` followed by the inclusion of the open cut out by
`U₂` is the underlying morphism of `comparisonComponentRight` followed by the second chart. -/
@[reassoc]
theorem glueHomRight_map_comp_ι :
    (glueHomRight X U₁ U₂ Q hcover P g).map ≫
        restrictDeformationι U₂ (glueDeformation X U₁ U₂ Q hcover) =
      (comparisonComponentRight X U₁ U₂ Q P g).map ≫ glueDefι₂ X U₁ U₂ Q hcover := by
  have h : (glueHomRight X U₁ U₂ Q hcover P g).map =
      (comparisonComponentRight X U₁ U₂ Q P g).map ≫
        (restrictGlueDeformationRightHom X U₁ U₂ Q hcover).map := rfl
  rw [h, Category.assoc, restrictGlueDeformationRightHom_map_comp_ι]

/-- **The two components of the given morphism agree on the overlap**, after being carried into
the glued scheme. This is the content of the comparison square of the given morphism, and it is
what lets the two of them be glued. -/
theorem overlap_comparisonComponent :
    overlapLeft P U₁ U₂ ≫
        (comparisonComponentLeft X U₁ U₂ Q P g).map ≫ glueDefι₁ X U₁ U₂ Q hcover =
      overlapRight P U₁ U₂ ≫
        (comparisonComponentRight X U₁ U₂ Q P g).map ≫ glueDefι₂ X U₁ U₂ Q hcover := by
  have key : ((nestedOpenIso P (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).hom ≫
        (nestedOpenIso P (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).inv) ≫
        ((openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).map
          (comparisonComponentLeft X U₁ U₂ Q P g)).map =
      ((openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).map
          (comparisonComponentRight X U₁ U₂ Q P g)).map ≫ Q.iso.hom.map :=
    congrArg SchemeDeformationCategory.Hom.map g.w
  have step1 : (nestedOpenIso P (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).inv ≫
        ((openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).map
          (comparisonComponentLeft X U₁ U₂ Q P g)).map =
      (nestedOpenIso P (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).inv ≫
        ((openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).map
          (comparisonComponentRight X U₁ U₂ Q P g)).map ≫ Q.iso.hom.map := by
    rw [← key, Category.assoc, Iso.inv_hom_id_assoc]
  rw [overlapLeft_eq, overlapRight_eq, Category.assoc, Category.assoc,
    nestedι_eq P (inf_le_left : U₁ ⊓ U₂ ≤ U₁),
    nestedι_eq P (inf_le_right : U₁ ⊓ U₂ ≤ U₂),
    ← openRestrictionLEFunctor_map_map_comp_overlapι_assoc
      (inf_le_left : U₁ ⊓ U₂ ≤ U₁) (comparisonComponentLeft X U₁ U₂ Q P g),
    ← openRestrictionLEFunctor_map_map_comp_overlapι_assoc
      (inf_le_right : U₁ ⊓ U₂ ≤ U₂) (comparisonComponentRight X U₁ U₂ Q P g),
    overlapι_comp_glueDefι₁, ← isoHom_map_comp_glueDefι₀, ← Category.assoc, step1]
  simp only [Category.assoc]

/-- The glued morphism of total spaces: the two components of the given morphism, carried into
the glued scheme and glued over the cover of the total space of `P` by the two opens that `U₁`
and `U₂` cut out. -/
def glueDeformationHomMap : P.scheme ⟶ (glueDeformation X U₁ U₂ Q hcover).scheme :=
  (coverOfRestrictions P hcover).glueMorphisms
    (fun b => Bool.rec
      ((comparisonComponentLeft X U₁ U₂ Q P g).map ≫ glueDefι₁ X U₁ U₂ Q hcover)
      ((comparisonComponentRight X U₁ U₂ Q P g).map ≫ glueDefι₂ X U₁ U₂ Q hcover) b)
    (by
      intro b b'
      cases b <;> cases b'
      · change pullback.fst (restrictDeformationι U₁ P) (restrictDeformationι U₁ P) ≫ _ =
          pullback.snd (restrictDeformationι U₁ P) (restrictDeformationι U₁ P) ≫ _
        rw [(cancel_mono (restrictDeformationι U₁ P)).mp
          (pullback.condition (f := restrictDeformationι U₁ P) (g := restrictDeformationι U₁ P))]
      · change pullback.fst (restrictDeformationι U₁ P) (restrictDeformationι U₂ P) ≫
            ((comparisonComponentLeft X U₁ U₂ Q P g).map ≫ glueDefι₁ X U₁ U₂ Q hcover) =
          pullback.snd (restrictDeformationι U₁ P) (restrictDeformationι U₂ P) ≫
            ((comparisonComponentRight X U₁ U₂ Q P g).map ≫ glueDefι₂ X U₁ U₂ Q hcover)
        rw [← cancel_epi (isPullback_overlap P U₁ U₂).isoPullback.hom]
        simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
          IsPullback.isoPullback_hom_snd]
        simpa only [Category.assoc] using overlap_comparisonComponent X U₁ U₂ Q hcover P g
      · change pullback.fst (restrictDeformationι U₂ P) (restrictDeformationι U₁ P) ≫
            ((comparisonComponentRight X U₁ U₂ Q P g).map ≫ glueDefι₂ X U₁ U₂ Q hcover) =
          pullback.snd (restrictDeformationι U₂ P) (restrictDeformationι U₁ P) ≫
            ((comparisonComponentLeft X U₁ U₂ Q P g).map ≫ glueDefι₁ X U₁ U₂ Q hcover)
        rw [← cancel_epi (pullbackSymmetry (restrictDeformationι U₁ P)
          (restrictDeformationι U₂ P)).hom]
        simp only [← Category.assoc, pullbackSymmetry_hom_comp_fst,
          pullbackSymmetry_hom_comp_snd]
        rw [← cancel_epi (isPullback_overlap P U₁ U₂).isoPullback.hom]
        simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
          IsPullback.isoPullback_hom_snd]
        simpa only [Category.assoc] using
          (overlap_comparisonComponent X U₁ U₂ Q hcover P g).symm
      · change pullback.fst (restrictDeformationι U₂ P) (restrictDeformationι U₂ P) ≫ _ =
          pullback.snd (restrictDeformationι U₂ P) (restrictDeformationι U₂ P) ≫ _
        rw [(cancel_mono (restrictDeformationι U₂ P)).mp
          (pullback.condition (f := restrictDeformationι U₂ P)
            (g := restrictDeformationι U₂ P))])

/-- On the open cut out by `U₁`, the glued morphism `glueDeformationHomMap` restricts to the
underlying morphism of `glueHomLeft`. -/
@[reassoc]
theorem restrictDeformationι_comp_glueDeformationHomMap_left :
    restrictDeformationι U₁ P ≫ glueDeformationHomMap X U₁ U₂ Q hcover P g =
      (glueHomLeft X U₁ U₂ Q hcover P g).map ≫
        restrictDeformationι U₁ (glueDeformation X U₁ U₂ Q hcover) := by
  rw [glueHomLeft_map_comp_ι]
  exact (coverOfRestrictions P hcover).ι_glueMorphisms _ _ false

/-- On the open cut out by `U₂`, the glued morphism `glueDeformationHomMap` restricts to the
underlying morphism of `glueHomRight`. -/
@[reassoc]
theorem restrictDeformationι_comp_glueDeformationHomMap_right :
    restrictDeformationι U₂ P ≫ glueDeformationHomMap X U₁ U₂ Q hcover P g =
      (glueHomRight X U₁ U₂ Q hcover P g).map ≫
        restrictDeformationι U₂ (glueDeformation X U₁ U₂ Q hcover) := by
  rw [glueHomRight_map_comp_ι]
  exact (coverOfRestrictions P hcover).ι_glueMorphisms _ _ true


/-- The glued morphism is compatible with the two special-fibre immersions. -/
theorem specialMap_comp_glueDeformationHomMap :
    P.specialMap ≫ glueDeformationHomMap X U₁ U₂ Q hcover P g =
      (glueDeformation X U₁ U₂ Q hcover).specialMap := by
  refine (coverOfTwoOpens X U₁ U₂ hcover).hom_ext _ _ ?_
  intro b
  cases b
  · change U₁.ι ≫ P.specialMap ≫ glueDeformationHomMap X U₁ U₂ Q hcover P g =
      U₁.ι ≫ (glueDeformation X U₁ U₂ Q hcover).specialMap
    rw [← Category.assoc, ← restrictDeformation_specialMap_comp_ι U₁ P, Category.assoc,
      restrictDeformationι_comp_glueDeformationHomMap_left, ← Category.assoc,
      (glueHomLeft X U₁ U₂ Q hcover P g).special_compat,
      restrictDeformation_specialMap_comp_ι]
  · change U₂.ι ≫ P.specialMap ≫ glueDeformationHomMap X U₁ U₂ Q hcover P g =
      U₂.ι ≫ (glueDeformation X U₁ U₂ Q hcover).specialMap
    rw [← Category.assoc, ← restrictDeformation_specialMap_comp_ι U₂ P, Category.assoc,
      restrictDeformationι_comp_glueDeformationHomMap_right, ← Category.assoc,
      (glueHomRight X U₁ U₂ Q hcover P g).special_compat,
      restrictDeformation_specialMap_comp_ι]

/-- The glued morphism lies over the base morphism of its first restriction. -/
theorem glueDeformationHomMap_comp_toBase :
    glueDeformationHomMap X U₁ U₂ Q hcover P g ≫ (glueDeformation X U₁ U₂ Q hcover).toBase =
      P.toBase ≫ baseSpecMap (glueHomLeft X U₁ U₂ Q hcover P g).base := by
  refine (coverOfRestrictions P hcover).hom_ext _ _ ?_
  intro b
  cases b
  · change restrictDeformationι U₁ P ≫ glueDeformationHomMap X U₁ U₂ Q hcover P g ≫
        (glueDeformation X U₁ U₂ Q hcover).toBase =
      restrictDeformationι U₁ P ≫ P.toBase ≫
        baseSpecMap (glueHomLeft X U₁ U₂ Q hcover P g).base
    rw [← Category.assoc, restrictDeformationι_comp_glueDeformationHomMap_left, Category.assoc,
      ← Category.assoc (restrictDeformationι U₁ P)]
    exact (glueHomLeft X U₁ U₂ Q hcover P g).cartesian.w
  · change restrictDeformationι U₂ P ≫ glueDeformationHomMap X U₁ U₂ Q hcover P g ≫
        (glueDeformation X U₁ U₂ Q hcover).toBase =
      restrictDeformationι U₂ P ≫ P.toBase ≫
        baseSpecMap (glueHomLeft X U₁ U₂ Q hcover P g).base
    rw [← Category.assoc, restrictDeformationι_comp_glueDeformationHomMap_right, Category.assoc,
      ← Category.assoc (restrictDeformationι U₂ P),
      glueHomLeft_base_eq_glueHomRight_base X U₁ U₂ Q hcover P g]
    exact (glueHomRight X U₁ U₂ Q hcover P g).cartesian.w

/-- The first component of the given morphism, carried into the glued scheme, is the glued
morphism restricted to the first chart. -/
@[reassoc]
theorem restrictDeformationι_comp_glueDeformationHomMap_left' :
    restrictDeformationι U₁ P ≫ glueDeformationHomMap X U₁ U₂ Q hcover P g =
      (comparisonComponentLeft X U₁ U₂ Q P g).map ≫ glueDefι₁ X U₁ U₂ Q hcover :=
  (coverOfRestrictions P hcover).ι_glueMorphisms _ _ false

/-- The second component likewise. -/
@[reassoc]
theorem restrictDeformationι_comp_glueDeformationHomMap_right' :
    restrictDeformationι U₂ P ≫ glueDeformationHomMap X U₁ U₂ Q hcover P g =
      (comparisonComponentRight X U₁ U₂ Q P g).map ≫ glueDefι₂ X U₁ U₂ Q hcover :=
  (coverOfRestrictions P hcover).ι_glueMorphisms _ _ true

/-- A morphism of total spaces over `m`, restricting over the open cut out by `U` to the
underlying morphism of `φ`, is cartesian over the open cut out by `U` as `φ` is. -/
private theorem isPullback_restrict_of_hom {P G : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (m : P.scheme ⟶ G.scheme) (hm : P.specialMap ≫ m = G.specialMap) (U : X.left.Opens)
    (φ : restrictDeformation U G ⟶ restrictDeformation U P) (β : G.base ⟶ P.base)
    (hφ : restrictDeformationι U P ≫ m = φ.map ≫ restrictDeformationι U G) (hβ : φ.base = β) :
    IsPullback (m ∣_ restrictedOpen G U) ((m ⁻¹ᵁ restrictedOpen G U).ι ≫ P.toBase)
      ((restrictedOpen G U).ι ≫ G.toBase) (baseSpecMap β) := by
  subst hβ
  have hpre := preimage_restrictedOpen_of_specialMap_comp m hm U
  have hiso := P.scheme.isoOfEq_inv_ι hpre
  have hchain : ((P.scheme.isoOfEq hpre).inv ≫ (m ∣_ restrictedOpen G U)) ≫
      restrictDeformationι U G = restrictDeformationι U P ≫ m :=
    (Category.assoc _ _ _).trans ((congrArg (fun t => (P.scheme.isoOfEq hpre).inv ≫ t)
      (morphismRestrict_ι m (restrictedOpen G U))).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ m) hiso)))
  refine φ.cartesian.of_iso (P.scheme.isoOfEq hpre).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans ((cancel_mono (restrictDeformationι U G)).mp
      (hφ.symm.trans hchain.symm))
  · exact (Category.comp_id _).trans (((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ P.toBase) hiso)).symm)
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **The glued morphism exhibits `P` as the base change of the glued deformation.** The square
is cartesian over each of the two charts of the glued scheme, where it is the cartesian square
of the corresponding component of the given morphism, and being cartesian is local on the
target of the top edge. -/
theorem isPullback_glueDeformationHomMap :
    IsPullback (glueDeformationHomMap X U₁ U₂ Q hcover P g) P.toBase
      (glueDeformation X U₁ U₂ Q hcover).toBase
      (baseSpecMap (glueHomLeft X U₁ U₂ Q hcover P g).base) := by
  refine isPullback_of_iSup_eq_top (glueDeformationHomMap_comp_toBase X U₁ U₂ Q hcover P g)
    (fun b : Bool => bif b then restrictedOpen (glueDeformation X U₁ U₂ Q hcover) U₂
      else restrictedOpen (glueDeformation X U₁ U₂ Q hcover) U₁) ?_ ?_
  · rw [iSup_bool_eq, sup_comm]
    exact restrictedOpen_sup_eq_top (glueDeformation X U₁ U₂ Q hcover) hcover
  · intro b
    cases b
    · exact isPullback_restrict_of_hom X _
        (specialMap_comp_glueDeformationHomMap X U₁ U₂ Q hcover P g)
        U₁ _ _ (restrictDeformationι_comp_glueDeformationHomMap_left X U₁ U₂ Q hcover P g) rfl
    · exact isPullback_restrict_of_hom X _
        (specialMap_comp_glueDeformationHomMap X U₁ U₂ Q hcover P g)
        U₂ _ _ (restrictDeformationι_comp_glueDeformationHomMap_right X U₁ U₂ Q hcover P g)
        (glueHomLeft_base_eq_glueHomRight_base X U₁ U₂ Q hcover P g).symm

/-- **Stacks 0DYZ**, the glueing quasi-inverse on morphisms. A morphism of the `2`-fibre product
from a datum `Q` to the comparison of a deformation `P` of `X` glues to a morphism from the
deformation glued from `Q` to `P`. The source of Tag 0DYZ says only "we omit the
verification". -/
@[stacks 0DYZ "the glueing construction of the proof on morphisms: a morphism of the 2-fibre \
product into the comparison of a deformation is glued to a morphism of deformations of X; the \
equivalence of Tag 0DYZ is not proved here"]
def glueDeformationHom : glueDeformation X U₁ U₂ Q hcover ⟶ P where
  base := (glueHomLeft X U₁ U₂ Q hcover P g).base
  map := glueDeformationHomMap X U₁ U₂ Q hcover P g
  cartesian := isPullback_glueDeformationHomMap X U₁ U₂ Q hcover P g
  special_compat := specialMap_comp_glueDeformationHomMap X U₁ U₂ Q hcover P g

/-- The underlying morphism of `glueDeformationHom` is `glueDeformationHomMap`. -/
theorem glueDeformationHom_map :
    (glueDeformationHom X U₁ U₂ Q hcover P g).map =
      glueDeformationHomMap X U₁ U₂ Q hcover P g :=
  rfl

/-- The base morphism of `glueDeformationHom` is the base morphism of `glueHomLeft`. -/
theorem glueDeformationHom_base :
    (glueDeformationHom X U₁ U₂ Q hcover P g).base =
      (glueHomLeft X U₁ U₂ Q hcover P g).base :=
  rfl

/-- **The triangle of the lifting problem commutes**: the comparison of the glued morphism is
the comparison morphism out of the glueing followed by the given morphism. -/
@[stacks 0DYZ "the compatibility of the glued morphism with the comparison morphism out of the \
glueing; the equivalence of Tag 0DYZ is not proved here"]
theorem twoOpenComparisonFunctor_map_glueDeformationHom :
    (twoOpenComparisonFunctor (Λ := Λ) X U₁ U₂).map (glueDeformationHom X U₁ U₂ Q hcover P g) =
      comparisonGlueHom X U₁ U₂ Q hcover ≫ g := by
  refine TwoFibreProductOver.Hom.ext' ?_ ?_
  · change restrictDeformationHom U₁ (glueDeformationHom X U₁ U₂ Q hcover P g) =
      glueHomLeft X U₁ U₂ Q hcover P g
    refine SchemeDeformationCategory.Hom.ext rfl ?_
    refine (cancel_mono (restrictDeformationι U₁ (glueDeformation X U₁ U₂ Q hcover))).mp ?_
    rw [restrictDeformationHom_map_comp_restrictDeformationι, glueDeformationHom_map,
      restrictDeformationι_comp_glueDeformationHomMap_left]
  · change restrictDeformationHom U₂ (glueDeformationHom X U₁ U₂ Q hcover P g) =
      glueHomRight X U₁ U₂ Q hcover P g
    refine SchemeDeformationCategory.Hom.ext
      (glueHomLeft_base_eq_glueHomRight_base X U₁ U₂ Q hcover P g) ?_
    refine (cancel_mono (restrictDeformationι U₂ (glueDeformation X U₁ U₂ Q hcover))).mp ?_
    rw [restrictDeformationHom_map_comp_restrictDeformationι, glueDeformationHom_map,
      restrictDeformationι_comp_glueDeformationHomMap_right]

end GlueHom

/-! ### Smoothness of the comparison morphism -/

section Smooth

variable (X) (U₁ U₂ : X.left.Opens)

/-- Restriction of deformations along an inclusion of opens, as a morphism of categories
over `𝒞_Λ`. -/
@[sga "7 VI 4.1(d)"]
def openRestrictionLEBasedFunctor {U V : X.left.Opens} (h : V ≤ U) :
    BasedFunctor
      (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U.ι ≫ X.hom))))
      (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k)
          (Over.mk (V.ι ≫ X.hom)))) where
  toFunctor := openRestrictionLEFunctor h
  w := openRestrictionLEFunctor_comp_projection h

/-- **Stacks 0DYZ**, the comparison morphism of a two-open cover as a morphism of categories
cofibered in groupoids over `𝒞_Λ`. -/
def twoOpenComparisonBasedFunctor :
    BasedFunctor
      (BasedCategory.ofFunctor (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
      (twoFibreProductBasedCategory
        (openRestrictionLEBasedFunctor X (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
        (openRestrictionLEBasedFunctor X (inf_le_right : U₁ ⊓ U₂ ≤ U₂))) where
  toFunctor := twoOpenComparisonFunctor X U₁ U₂
  w := twoOpenComparisonFunctor_comp_structureFunctor X U₁ U₂

/-- **Stacks 0DYZ in the form Tag 0DZN uses it.** If the two opens cover `X` then the comparison
morphism `Def_X ⟶ Def_{U₁} ×_{Def_{U₁ ⊓ U₂}} Def_{U₂}` is smooth: a lifting problem is solved by
glueing the datum over the smaller object of `𝒞_Λ` to a deformation of `X`, glueing the given
morphism to a morphism of deformations of `X`, and comparing the glued deformation with the
datum by the two chart isomorphisms. -/
@[stacks 0DYZ "smoothness of the comparison morphism Def_X ⟶ Def_{U_1} ×_{Def_{U_12}} Def_{U_2}, \
which is what Tag 0DZN consumes; that the comparison morphism is an *equivalence* — the full \
assertion of 0DYZ — is not proved, and neither is the translation into the ring deformation \
categories Def_{P_i}"]
theorem isSmooth_twoOpenComparisonBasedFunctor (hcover : U₁ ⊔ U₂ = ⊤) :
    IsSmooth (twoOpenComparisonBasedFunctor (Λ := Λ) X U₁ U₂) := by
  intro B A f _ y x gg hgg
  have hgg' : (TwoFibreProductOver.structureFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U₁.ι ≫ X.hom)))
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U₂.ι ≫ X.hom)))
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk ((U₁ ⊓ U₂).ι ≫ X.hom)))
      (openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
      (openRestrictionLEFunctor (Λ := Λ) (k := k)
        (inf_le_right : U₁ ⊓ U₂ ≤ U₂))).IsHomLift f gg := hgg
  have hB : (TwoFibreProductOver.structureFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U₁.ι ≫ X.hom)))
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U₂.ι ≫ X.hom)))
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk ((U₁ ⊓ U₂).ι ≫ X.hom)))
      (openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
      (openRestrictionLEFunctor (Λ := Λ) (k := k)
        (inf_le_right : U₁ ⊓ U₂ ≤ U₂))).obj y = B :=
    IsHomLift.domain_eq _ f gg
  subst hB
  have hvert : (twoFibreProductBasedCategory
      (openRestrictionLEBasedFunctor X (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
      (openRestrictionLEBasedFunctor X (inf_le_right : U₁ ⊓ U₂ ≤ U₂))).p.IsHomLift
      (𝟙 y.base) (comparisonGlueHom X U₁ U₂ y hcover) :=
    isHomLift_comparisonGlueHom X U₁ U₂ y hcover
  refine ⟨glueDeformation X U₁ U₂ y hcover,
    glueDeformationHom X U₁ U₂ y hcover x gg, comparisonGlueHom X U₁ U₂ y hcover, ?_, hvert,
    twoOpenComparisonFunctor_map_glueDeformationHom X U₁ U₂ y hcover x gg⟩
  refine (BasedFunctor.isHomLift_iff (twoOpenComparisonBasedFunctor (Λ := Λ) X U₁ U₂) f
    (glueDeformationHom X U₁ U₂ y hcover x gg)).mp ?_
  have htri : (twoOpenComparisonBasedFunctor (Λ := Λ) X U₁ U₂).map
      (glueDeformationHom X U₁ U₂ y hcover x gg) =
      comparisonGlueHom X U₁ U₂ y hcover ≫ gg :=
    twoOpenComparisonFunctor_map_glueDeformationHom X U₁ U₂ y hcover x gg
  rw [htri]
  exact IsHomLift.comp_lift_id_left'
    (twoFibreProductBasedCategory
      (openRestrictionLEBasedFunctor X (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
      (openRestrictionLEBasedFunctor X (inf_le_right : U₁ ⊓ U₂ ≤ U₂))).p
    y.base (comparisonGlueHom X U₁ U₂ y hcover) f gg

end Smooth

end Deformation.Examples

end
