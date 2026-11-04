module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleSheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.UniversallyOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale descent of the closed subset of a section of Artin's contraction functor

In the situation of Stacks 0GH8, a section of Artin's contraction functor `F` of Stacks 0GHA
over a locally Noetherian scheme `V` over `S` is a triple `(Z, u', x̂)` whose first component
is a closed subset `Z ⊆ |V|`. This file descends that first component along an étale covering
`{V_i ⟶ V}`: given closed subsets `Z_i ⊆ |V_i|` which agree on overlaps, there is a unique
closed `Z ⊆ |V|` with `Z_i` as its inverse images. That is the first of the four missing
descent statements of Stacks 0GHG, and the uniqueness half of it is already
`AlgebraicGeometry.Artin.ContractionSituation.Z_eq_of_mapTriple_eq`.

## Main results

* `AlgebraicGeometry.isOpenMap_of_etale`: an étale morphism of schemes is an open map.
* `AlgebraicGeometry.Space.exists_fieldSpec_pointsMap_eq`: two points of representable
  presheaves with the same image in a common target are the images of a single point of a
  field spectrum over which the two morphisms to the target agree.
* `AlgebraicGeometry.LocallyNoetherianOver.etale_of_isEtaleCovering`: every member of an étale
  covering family of the locally Noetherian site over `S` is an étale morphism.
* `AlgebraicGeometry.Artin.ContractionSituation.descendZ`,
  `AlgebraicGeometry.Artin.ContractionSituation.isClosed_descendZ` and
  `AlgebraicGeometry.Artin.ContractionSituation.pointsMap_preimage_descendZ`: the descended
  closed subset, its closedness, and the identification of its inverse images.

## What is and is not proved

Nothing is assumed; every declaration is proved outright. Nothing here carries a Stacks
attribute.

In particular *no fibre products are needed*, although the descent of a closed subset along a
covering family looks as though it should need them. The reason is
`AlgebraicGeometry.Space.exists_fieldSpec_pointsMap_eq`: by Stacks 03BU two points of `|V_i|`
and `|V_j|` with the same image in `|V|` are, by definition, two field-valued points with a
common field-valued extension, and that extension is itself an object of the site — the
spectrum of a field, hence Noetherian, hence an object of the *locally Noetherian* site, to
which a compatibility datum for `F` applies. So the compatibility of a family of triples on the
locally Noetherian site already separates points, with no appeal to Stacks 0GE1 part (3).

The one input beyond the definitions is that an étale morphism is open, which is needed only to
see that the descended subset is closed.

## References

* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BY](https://stacks.math.columbia.edu/tag/03BY)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
* [Stacks Project, Tag 0GHG](https://stacks.math.columbia.edu/tag/0GHG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An étale morphism of schemes is an open map: it is flat and locally of finite
presentation, hence universally open by Stacks 01UA. -/
@[sga "3 X 4.7" "étale morphisms are open"]
theorem isOpenMap_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Etale f) : IsOpenMap ⇑f := by
  obtain ⟨_, -, _⟩ := Etale.iff_flat_and_formallyUnramified.mp hf
  have : UniversallyOpen f := universallyOpen_of_flat_of_locallyOfFinitePresentation f
  exact f.isOpenMap

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **Two points with the same image come from one point of a field spectrum.** Let
`f₁ : V₁ ⟶ V` and `f₂ : V₂ ⟶ V` be morphisms of the big fppf site of `S` and let `x₁`, `x₂`
be points of the presheaves they represent with the same image in `|V|`. Then there is an
object `Y` of the site whose underlying scheme is the spectrum of a field — in particular
locally Noetherian — morphisms `g₁ : Y ⟶ V₁` and `g₂ : Y ⟶ V₂` with `g₁ ≫ f₁ = g₂ ≫ f₂`, and
a point `z` of `Y` whose images are `x₁` and `x₂`.

This is the separation statement that the descent of a closed subset along a covering family
needs, and it needs *no* fibre products: equality of points of `|V|` is, by Stacks 03BU, the
existence of a common field-valued extension, and such an extension *is* the required object
`Y` together with the two morphisms out of it. -/
theorem exists_fieldSpec_pointsMap_eq {V V₁ V₂ : BigFppfOver B S hS} (f₁ : V₁ ⟶ V)
    (f₂ : V₂ ⟶ V) {x₁ : points B S hS (yoneda.obj V₁)}
    {x₂ : points B S hS (yoneda.obj V₂)}
    (hx : pointsMap B S hS (yoneda.obj V₁) (yoneda.map f₁) x₁ =
      pointsMap B S hS (yoneda.obj V₂) (yoneda.map f₂) x₂) :
    ∃ (Y : BigFppfOver B S hS) (g₁ : Y ⟶ V₁) (g₂ : Y ⟶ V₂)
        (z : points B S hS (yoneda.obj Y)),
      IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Y) ∧ g₁ ≫ f₁ = g₂ ≫ f₂ ∧
        pointsMap B S hS (yoneda.obj Y) (yoneda.map g₁) z = x₁ ∧
        pointsMap B S hS (yoneda.obj Y) (yoneda.map g₂) z = x₂ := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep x₁
  obtain ⟨q, rfl⟩ := Quot.exists_rep x₂
  obtain ⟨r, ⟨σ, hσ⟩, ⟨τ, hτ⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS (yoneda.obj V) _ _).mp hx
  have hσ' : σ ≫ p.value ≫ f₁ = r.value := hσ
  have hτ' : τ ≫ q.value ≫ f₂ = r.value := hτ
  refine ⟨r.siteObject, σ ≫ p.value, τ ≫ q.value,
    FieldValuedPoint.class B S hS (yoneda.obj r.siteObject)
      { carrier := r.carrier, field := r.field, contained := r.contained, toBase := r.toBase
        value := 𝟙 r.siteObject },
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of r.carrier))), ?_, ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans (hσ'.trans (hτ'.symm.trans (Category.assoc _ _ _).symm))
  · exact FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS (yoneda.obj V₁)
      ⟨_, FieldValuedPoint.dominates_refl B S hS (yoneda.obj V₁) _, σ,
        (Category.id_comp (σ ≫ p.value)).symm⟩
  · exact FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS (yoneda.obj V₂)
      ⟨_, FieldValuedPoint.dominates_refl B S hS (yoneda.obj V₂) _, τ,
        (Category.id_comp (τ ≫ q.value)).symm⟩

end Space

namespace LocallyNoetherianOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every member of an étale covering family of the locally Noetherian site over `S` is an
étale morphism of the big fppf site over `S`. -/
theorem etale_of_isEtaleCovering {E : Covering (LocallyNoetherianOver B S hS)}
    (hE : IsEtaleCovering B S hS E) (i : E.2.I₀) :
    Etale ((BigFppfOver.toScheme B S hS).map (E.2.f i).hom) :=
  ((Scheme.ofArrows_mem_precoverage_iff
    (P := (@Etale.{u} : MorphismProperty Scheme.{u}))).mp
      (ofArrows_mem_etalePrecoverage_of_isEtaleCovering B S hS hE)).2 i

end LocallyNoetherianOver

namespace Artin

attribute [local instance] Space.pointTopology

namespace ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)

/-- **The closed subset descended from a family of triples.** Given a covering family
`{V_i ⟶ V}` of locally Noetherian schemes over `S` and a triple `t i` over each `V_i`, the
candidate first component of a triple over `V` is the complement of the union of the images
of the open complements `|V_i| ∖ Z_i`.

This is the only possible choice: by
`AlgebraicGeometry.Artin.ContractionSituation.Z_eq_of_mapTriple_eq` a triple's first
component is determined by its pullbacks along a jointly surjective family. -/
def descendZ {E : Covering (LocallyNoetherianOver B S hS)}
    (t : (i : E.2.I₀) → Triple c (E.2.X i).obj) :
    Set (Space.points B S hS (yoneda.obj E.1.obj)) :=
  (⋃ i, Space.pointsMap B S hS (yoneda.obj (E.2.X i).obj)
    (yoneda.map (E.2.f i).hom) '' ((t i).Z)ᶜ)ᶜ

/-- **The descended subset is closed.** Each `|V_i| ∖ Z_i` is open and the map on points of
an étale morphism is open, so the union of the images is open. -/
theorem isClosed_descendZ {E : Covering (LocallyNoetherianOver B S hS)}
    (hE : LocallyNoetherianOver.IsEtaleCovering B S hS E)
    (t : (i : E.2.I₀) → Triple c (E.2.X i).obj) :
    IsClosed (descendZ c t) :=
  isClosed_compl_iff.mpr (isOpen_iUnion fun i =>
    Space.isOpenMap_pointsMap_yonedaMap_of_etale B S hS (E.2.f i).hom
      (LocallyNoetherianOver.etale_of_isEtaleCovering B S hS hE i) _
      (t i).isClosed_Z.isOpen_compl)

/-- **The descended subset pulls back to the given ones.** This is the existence half of the
descent of the first component of a triple, and it is proved without any fibre products: the
one input beyond the definition is
`AlgebraicGeometry.Space.exists_fieldSpec_pointsMap_eq`, which produces, from two points of
two members of the family with the same image, a *field spectrum* in the site mapping to both
over the common target — and a field spectrum is Noetherian, so it is an object of the
locally Noetherian site and the compatibility hypothesis applies to it. -/
theorem pointsMap_preimage_descendZ {E : Covering (LocallyNoetherianOver B S hS)}
    (t : (i : E.2.I₀) → Triple c (E.2.X i).obj)
    (ht : ∀ (i j : E.2.I₀) (Y : LocallyNoetherianOver B S hS) (gi : Y ⟶ E.2.X i)
      (gj : Y ⟶ E.2.X j), gi ≫ E.2.f i = gj ≫ E.2.f j →
        mapTriple c gi.hom (t i) = mapTriple c gj.hom (t j)) (i : E.2.I₀) :
    Space.pointsMap B S hS (yoneda.obj (E.2.X i).obj) (yoneda.map (E.2.f i).hom) ⁻¹'
        descendZ c t = (t i).Z := by
  ext x
  simp only [descendZ, Set.mem_preimage, Set.mem_compl_iff, Set.mem_iUnion]
  constructor
  · intro h
    by_contra hx
    exact h ⟨i, x, hx, rfl⟩
  · rintro hx ⟨j, y, hy, hyx⟩
    obtain ⟨Y, gj, gi, z, hY, hcomm, hzj, hzi⟩ :=
      Space.exists_fieldSpec_pointsMap_eq B S hS (E.2.f j).hom (E.2.f i).hom hyx
    have hkey : Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map gj) ⁻¹' (t j).Z =
        Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map gi) ⁻¹' (t i).Z :=
      congrArg Triple.Z (ht j i ⟨Y, hY⟩ (ObjectProperty.homMk gj)
        (ObjectProperty.homMk gi) (ObjectProperty.hom_ext _ hcomm))
    have hmem : z ∈ Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map gi) ⁻¹' (t i).Z := by
      rwa [Set.mem_preimage, hzi]
    rw [← hkey, Set.mem_preimage, hzj] at hmem
    exact hy hmem

end ContractionSituation

end Artin

end AlgebraicGeometry

end
