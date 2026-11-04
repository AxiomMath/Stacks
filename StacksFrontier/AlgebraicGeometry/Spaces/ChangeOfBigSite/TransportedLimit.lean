module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite.Limit
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionAlgebraicLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteEnlargement

/-!
# Transporting a limit of algebraic spaces to an enlarged big site

Let `(X_i)` be a cofiltered inverse system of quasi-compact algebraic spaces over `S` with affine
transition morphisms satisfying the chapter's standing convention of Section 70.2 (tag 07SD,
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`), so that `X = lim X_i` is an algebraic
space of the big fppf site `B` (Stacks 07SF). No condition is placed on the size of the index
category. Enlarging `B` to a site `B'` whose cutoff has cofinality above the size of the
index category, the inverse image of Stacks 04W1 carries `X` to the limit of the transported
system. Fibre products are carried to fibre products up to isomorphisms on the legs.

## Main results

* `AlgebraicGeometry.Space.isPullback_changeBigSite_map_of_iso`: a cartesian square, transported
  to the larger site and composed with isomorphisms on the legs, is cartesian.
* `AlgebraicGeometry.Space.exists_changeBigSite_limit_iso`: an enlargement of the site in which
  the limit of the transported system is the transport of the limit.

## References

* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

/-! ### Transported fibre products -/

section Pullback

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- **A cartesian square of algebraic spaces, transported to the larger site and composed with
isomorphisms on the two legs, is cartesian.** -/
theorem isPullback_changeBigSite_map_of_iso {P X Y Z : AlgebraicSpaces B S hS} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (hpb : IsPullback fst.hom snd.hom f.hom g.hom)
    {X' Y' : (BigFppfOver B' S (largerContains h hS))ᵒᵖ ⥤ Type u}
    (eX : ((changeBigSite B B' h S hS).obj X).obj ≅ X')
    (eY : ((changeBigSite B B' h S hS).obj Y).obj ≅ Y')
    (f' : X' ⟶ ((changeBigSite B B' h S hS).obj Z).obj)
    (g' : Y' ⟶ ((changeBigSite B B' h S hS).obj Z).obj)
    (hf : eX.hom ≫ f' = ((changeBigSite B B' h S hS).map f).hom)
    (hg : eY.hom ≫ g' = ((changeBigSite B B' h S hS).map g).hom) :
    IsPullback (((changeBigSite B B' h S hS).map fst).hom ≫ eX.hom)
      (((changeBigSite B B' h S hS).map snd).hom ≫ eY.hom) f' g' :=
  (isPullback_changeBigSite_map B B' h S hS hpb).of_iso (Iso.refl _) eX eY (Iso.refl _)
    (Category.id_comp _).symm (Category.id_comp _).symm
    ((Category.comp_id _).trans hf.symm) ((Category.comp_id _).trans hg.symm)

end Pullback

/-! ### The comparison of limits -/

section Limit

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
  (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
variable (hconv : SiteContainsBaseChangeLimits B S hS D)
  (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))

/-- **There is an enlargement of the big fppf site in which the limit of the transported system
is the transport of the limit.** The site `B'` is chosen with the size of the index category
and of its morphism types below the cofinality of its cutoff
(`AlgebraicGeometry.BigFppfSite.exists_isContained_lt_cof`), and the change of big site
preserves the limit of the system (`AlgebraicGeometry.Space.isLimitChangeBigSiteMapCone`). The
limit is an algebraic space of `B` by Stacks 07SF under the chapter's convention
(`AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits`). -/
theorem exists_changeBigSite_limit_iso :
    ∃ (B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B'),
      #I < B'.cutoff.ord.cof ∧ (∀ i j : I, #(i ⟶ j) < B'.cutoff.ord.cof) ∧
      ∃ eL : ((changeBigSite B B' h S hS).obj ⟨limit D,
          isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD hAffine
            hQc⟩).obj ≅ limit (changeBigSiteSystem B B' h S hS (ObjectProperty.lift _ D hD)),
        ∀ i, eL.hom ≫ limit.π (changeBigSiteSystem B B' h S hS (ObjectProperty.lift _ D hD)) i =
          ((changeBigSite B B' h S hS).map
            (ObjectProperty.homMk (limit.π D i) :
              (⟨limit D, isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD
                hAffine hQc⟩ : AlgebraicSpaces B S hS) ⟶
                  (ObjectProperty.lift _ D hD).obj i)).hom := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨B', h, hcof⟩ := BigFppfSite.exists_isContained_lt_cof B (max #I #(Σ i j : I, i ⟶ j))
  have hSize' : #I < B'.cutoff.ord.cof := (le_max_left _ _).trans_lt hcof
  have hHomSize' : ∀ i j : I, #(i ⟶ j) < B'.cutoff.ord.cof := fun i j =>
    (Cardinal.mk_le_of_injective (f := fun a : i ⟶ j => (⟨i, j, a⟩ : Σ i j : I, i ⟶ j))
      (fun a b hab => by simpa using hab)).trans_lt ((le_max_right _ _).trans_lt hcof)
  refine ⟨B', h, hSize', hHomSize', ?_⟩
  let Da := ObjectProperty.lift _ D hD
  let c : Cone Da :=
    { pt := ⟨limit D,
        isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD hAffine hQc⟩
      π := { app := fun i => ObjectProperty.homMk (limit.π D i)
             naturality := fun i j f => ObjectProperty.hom_ext _
               ((Category.id_comp _).trans (limit.w D f).symm) } }
  have hc : IsLimit ((ObjectProperty.ι _).mapCone c) := limit.isLimit D
  have hlim := isLimitChangeBigSiteMapCone B B' h S hS Da hSize' hHomSize' (fun f => hAffine f)
    hconv i₀ (hQc i₀) c hc
  exact ⟨hlim.conePointUniqueUpToIso (limit.isLimit _),
    fun i => hlim.conePointUniqueUpToIso_hom_comp (limit.isLimit _) i⟩

end Limit

end AlgebraicGeometry.Space

end
