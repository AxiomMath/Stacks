module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleOnSite

/-!
# The slice of the small étale site at a chart, as a site of schemes

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `X` be
an étale chart of `F`, with underlying scheme `U`. The slice `Over X` of the small étale site of
`F` at `X` is a site of schemes over `U`: an object of the slice is an étale chart of `F`
together with a morphism of charts to `X`, and the morphism of charts is an étale morphism of
schemes onto `U`.

The projection to `CategoryTheory.Over U` is `CategoryTheory.Over.post` of the projection taking
a chart to its scheme; it is fully faithful, its objects are étale over `U`, and its essential
image is exactly the schemes étale over `U` which `B` contains. So the slice is the small étale
site of the scheme `U`, cut down to the size bound of `B`. Moreover:

* the presheaf of global functions on the slice read as a site of schemes,
  `Stacks.Sites.structurePresheaf U (sliceToOver …)`, is definitionally the restriction of the
  structure sheaf `𝒪_F` to the slice;
* hence `Stacks.Sites.siteStructureSheaf` at the slice is the sheaf of rings `(𝒪_F)|_X` over
  which the restriction `M|_X` of an `𝒪_F`-module lives;
* hence `Stacks.Sites.siteAssociatedModule`, the module `Mᵃ` of Tag 03DU, may be formed on the
  slice over that same sheaf of rings, in the same category as `M|_X`.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtale.sliceToOver` reads the slice of the small étale site at a
  chart as a category of schemes over the chart's scheme.
* `AlgebraicGeometry.Space.SmallEtale.IsEtaleOverChart` and
  `AlgebraicGeometry.Space.SmallEtale.EtaleOverChart` are the schemes over the chart's scheme
  which are étale over it and contained in `B`, and
  `AlgebraicGeometry.Space.SmallEtale.sliceToEtaleOverChart` is the corestriction of
  `sliceToOver` to them.
* `AlgebraicGeometry.Space.SmallEtale.sliceRingSheaf` is the restriction of the structure sheaf
  of the small étale ringed site to the slice at a chart.
* `AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule` is the module `Mᵃ` of Tag 03DU
  formed on the slice, for a quasi-coherent module `M` on the chart's scheme.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.etale_sliceToOver_obj_hom`: a morphism of charts over `X`
  is an étale morphism of schemes onto the chart's scheme.
* `AlgebraicGeometry.Space.SmallEtale.instFullSliceToOver` and
  `AlgebraicGeometry.Space.SmallEtale.exists_sliceToOver_obj_eq`: the projection is full, and
  every scheme étale over the chart's scheme which `B` contains is *on the nose* the image of an
  object of the slice.
* `AlgebraicGeometry.Space.SmallEtale.sliceEquivalence`: the slice at `X` is equivalent to the
  schemes étale over the chart's scheme contained in `B`, by the projection itself.
* `AlgebraicGeometry.Space.SmallEtale.sliceRingSheaf_obj`: the structure presheaf of the slice
  read as a site of schemes is the restriction of `𝒪_F`, by `rfl`;
  `AlgebraicGeometry.Space.SmallEtale.siteStructureSheaf_eq` is the same statement for the
  sheaves of rings.
* `AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule_presheaf`: the sections of `Mᵃ` over
  an object of the slice are the global sections of the pullback of `M`.

## Implementation notes

The projection to the schemes over the chart's scheme is `CategoryTheory.Over.post` of
`AlgebraicGeometry.Space.SmallEtale.toOver ⋙ AlgebraicGeometry.BigFppfOver.toScheme`. Since
`CategoryTheory.Over.post_forget_eq_forget_comp` is `rfl`, the composite of the projection with
`CategoryTheory.Over.forget` is the slice projection followed by the chart's scheme, which is the
functor defining `AlgebraicGeometry.Space.structurePresheaf`; so
`AlgebraicGeometry.Space.SmallEtale.sliceRingSheaf_obj` holds by `rfl`.

Fullness is not formal: `CategoryTheory.CostructuredArrow.proj` is faithful but not full. It
holds here because a morphism of schemes over the chart's scheme between two charts commutes
with the charts' morphisms to `F`: both factor through `X`.

Essential surjectivity is an equality of objects: the chart built from a scheme `W` étale over
the chart's scheme is `yoneda.map l ≫ X.obj.hom` for `l` the morphism over `S` induced by
`W ⟶ U`, and the projection returns `W ⟶ U` unchanged.

The module universe of `AlgebraicGeometry.Space.SmallEtale.sliceModule` is free, since
restricting a sheaf of modules along `CategoryTheory.Over.forget` uses only continuity of the
forgetful functor. The module universe of
`AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule` is `u`, since the sections of `Mᵃ` are
global sections of a pullback of `M`.

`AlgebraicGeometry.Space.SmallEtale.EtaleOverChart` is the full subcategory of
`AlgebraicGeometry.EtaleOver` of the chart's scheme on the objects that `B` contains.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### The slice at a chart as a category of schemes -/

variable (hF : IsAlgebraicSpace B S hS F) (X : SmallEtale B S hS F)

/-- Every étale chart of `F` is contained in `B`, being an object of its underlying category. -/
theorem contains_chartScheme : B.Contains (chartScheme X) :=
  X.obj.left.left.property

/-- The slice of the small étale site of `F` at the chart `X`, read as a category of schemes
over the scheme underlying `X`: an object of the slice is sent to its underlying scheme, with
the morphism of schemes underlying its structure morphism to `X`. -/
abbrev sliceToOver : Over X ⥤ Over (chartScheme X) :=
  Over.post (toOver B S hS F ⋙ BigFppfOver.toScheme B S hS)

/-- Forgetting the structure morphism to the chart's scheme recovers the slice projection
followed by the underlying scheme of a chart. -/
theorem sliceToOver_comp_forget :
    sliceToOver B S hS F X ⋙ Over.forget (chartScheme X) =
      Over.forget X ⋙ toOver B S hS F ⋙ BigFppfOver.toScheme B S hS :=
  rfl

/-- A morphism of étale charts of `F` over `X` is an étale morphism of schemes onto the scheme
underlying `X`. -/
theorem etale_sliceToOver_obj_hom (Z : Over X) :
    Etale ((sliceToOver B S hS F X).obj Z).hom :=
  etale_of_comp_etale_chart B S hS Z.left.property X.property (CostructuredArrow.w Z.hom.hom)

/-- The slice projection to the schemes over the chart's scheme is full. -/
noncomputable instance instFullSliceToOver : (sliceToOver B S hS F X).Full := by
  constructor
  intro Z₁ Z₂ g
  have hbmap : B.inclusion.map (B.inclusion.preimage g.left) = g.left :=
    B.inclusion.map_preimage _
  have hstar : B.inclusion.preimage g.left ≫ Z₂.hom.hom.left.left = Z₁.hom.hom.left.left :=
    B.inclusion.map_injective (by rw [Functor.map_comp, hbmap]; exact Over.w g)
  have hover : B.inclusion.preimage g.left ≫ Z₂.left.obj.left.hom = Z₁.left.obj.left.hom := by
    rw [← Over.w Z₂.hom.hom.left, ← Category.assoc, hstar, Over.w Z₁.hom.hom.left]
  have hlstar : (Over.homMk (B.inclusion.preimage g.left) hover :
      Z₁.left.obj.left ⟶ Z₂.left.obj.left) ≫ Z₂.hom.hom.left = Z₁.hom.hom.left :=
    Over.OverMorphism.ext hstar
  have htriangle : yoneda.map (Over.homMk (B.inclusion.preimage g.left) hover :
        Z₁.left.obj.left ⟶ Z₂.left.obj.left) ≫ Z₂.left.obj.hom = Z₁.left.obj.hom := by
    rw [← CostructuredArrow.w Z₂.hom.hom, ← Category.assoc, ← Functor.map_comp, hlstar,
      CostructuredArrow.w Z₁.hom.hom]
  refine ⟨Over.homMk (ObjectProperty.homMk (CostructuredArrow.homMk _ htriangle)) ?_, ?_⟩
  · exact ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ hlstar)
  · exact Over.OverMorphism.ext hbmap

/-- Every scheme étale over the chart's scheme which `B` contains is equal to the image of an
object of the slice. -/
theorem exists_sliceToOver_obj_eq (Y : Over (chartScheme X)) (hY : Etale Y.hom)
    (hYc : B.Contains Y.left) : ∃ Z : Over X, (sliceToOver B S hS F X).obj Z = Y := by
  obtain ⟨W, f, rfl⟩ := Y.mk_surjective
  let b : B.obj hYc ⟶ X.obj.left.left := B.inclusion.preimage f
  have hbf : B.inclusion.map b = f :=
    B.inclusion.map_preimage (X := B.obj hYc) (Y := X.obj.left.left) f
  let l : Over.mk (b ≫ X.obj.left.hom) ⟶ X.obj.left := Over.homMk b (by simp)
  have hl : Etale ((BigFppfOver.toScheme B S hS).map l) := by
    change Etale (B.inclusion.map b)
    rwa [hbf]
  exact ⟨Over.mk (Y := ⟨CostructuredArrow.mk (yoneda.map l ≫ X.obj.hom),
      etale_comp_of_scheme B S hS l X.obj.hom hl X.property⟩)
      (ObjectProperty.homMk (CostructuredArrow.homMk l rfl)), congrArg Over.mk hbf⟩

/-! ### The site of schemes étale over the chart's scheme -/

/-- The property of a scheme over the scheme underlying the chart `X` that it is étale over it
and contained in `B`. The first conjunct is `AlgebraicGeometry.IsEtaleOver` of the chart's
scheme, definitionally. -/
abbrev IsEtaleOverChart : ObjectProperty (Over (chartScheme X)) :=
  fun Y ↦ Etale Y.hom ∧ B.Contains Y.left

/-- The small étale site of the scheme underlying the chart `X`, inside `B`: the schemes over
that scheme which are étale over it and are contained in `B`. -/
abbrev EtaleOverChart := (IsEtaleOverChart B S hS F X).FullSubcategory

/-- The slice of the small étale site of `F` at `X`, read as the small étale site of the chart's
scheme inside `B`. -/
abbrev sliceToEtaleOverChart : Over X ⥤ EtaleOverChart B S hS F X :=
  (IsEtaleOverChart B S hS F X).lift (sliceToOver B S hS F X) fun Z ↦
    ⟨etale_sliceToOver_obj_hom B S hS F X Z, Z.left.obj.left.left.property⟩

/-- The corestriction of the slice projection is the slice projection. -/
theorem sliceToEtaleOverChart_comp_ι :
    sliceToEtaleOverChart B S hS F X ⋙ (IsEtaleOverChart B S hS F X).ι =
      sliceToOver B S hS F X :=
  rfl

/-- The corestricted slice projection is essentially surjective; in fact every object of the
target is an image on the nose. -/
noncomputable instance instEssSurjSliceToEtaleOverChart :
    (sliceToEtaleOverChart B S hS F X).EssSurj where
  mem_essImage Y := by
    obtain ⟨Z, hZ⟩ :=
      exists_sliceToOver_obj_eq B S hS F X Y.obj Y.property.1 Y.property.2
    exact ⟨Z, ⟨ObjectProperty.isoMk (P := IsEtaleOverChart B S hS F X) (eqToIso hZ)⟩⟩

/-- The corestricted slice projection is an equivalence of categories, being full, faithful and
essentially surjective. -/
noncomputable instance instIsEquivalenceSliceToEtaleOverChart :
    (sliceToEtaleOverChart B S hS F X).IsEquivalence where

/-- The slice of the small étale site of `F` at the étale chart `X` is equivalent to the small
étale site of the scheme underlying `X` inside `B`, by the projection taking a chart over `X` to
its underlying scheme. -/
noncomputable def sliceEquivalence : Over X ≌ EtaleOverChart B S hS F X :=
  (sliceToEtaleOverChart B S hS F X).asEquivalence

/-- The equivalence of `AlgebraicGeometry.Space.SmallEtale.sliceEquivalence` is given by the
slice projection itself. -/
theorem sliceEquivalence_functor :
    (sliceEquivalence B S hS F X).functor = sliceToEtaleOverChart B S hS F X :=
  rfl

/-! ### The structure sheaf of the slice -/

/-- The restriction of the structure sheaf of the small étale ringed site of `F` to the slice at
the chart `X`, as a sheaf of rings. -/
noncomputable abbrev sliceRingSheaf : Sheaf ((topology B S hS F).over X) RingCat.{u} :=
  ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over X

/-- The presheaf of global functions on the slice at `X`, read as a site of schemes over the
chart's scheme, is equal to the restriction to the slice of the structure sheaf `𝒪_F`. -/
theorem sliceRingSheaf_obj :
    (sliceRingSheaf B S hS F hF X).obj =
      Stacks.Sites.structurePresheaf (chartScheme X) (sliceToOver B S hS F X) :=
  rfl

include hF in
/-- The presheaf of global functions on the slice at `X`, read as a site of schemes over the
chart's scheme, is a sheaf for the localized small étale topology. -/
theorem isSheaf_sliceStructurePresheaf :
    Presheaf.IsSheaf ((topology B S hS F).over X)
      (Stacks.Sites.structurePresheaf (chartScheme X) (sliceToOver B S hS F X)) :=
  (sliceRingSheaf B S hS F hF X).property

/-- The structure sheaf of rings of the slice at `X`, read as a site of schemes over the chart's
scheme, is the restriction of `𝒪_F` to the slice. -/
theorem siteStructureSheaf_eq :
    Stacks.Sites.siteStructureSheaf (chartScheme X) (sliceToOver B S hS F X)
        ((topology B S hS F).over X) (isSheaf_sliceStructurePresheaf B S hS F hF X) =
      sliceRingSheaf B S hS F hF X :=
  rfl

/-- The restriction of an `𝒪_F`-module to the slice at the chart `X`. -/
noncomputable abbrev sliceModule (M : Modules.{u, m} B S hS F hF) :
    SheafOfModules.{m} (sliceRingSheaf B S hS F hF X) :=
  M.over X

/-! ### The associated module on the slice -/

/-- The module `Mᵃ` of Tag 03DU, formed on the slice at a chart: for a quasi-coherent module
`M` on the scheme underlying the chart `X`, and given the sheaf condition for its presheaf of
pullback sections, the sheaf of modules over `AlgebraicGeometry.Space.SmallEtale.sliceRingSheaf`
whose sections over a chart over `X` are the global sections of the pullback of `M` to that
chart's scheme. -/
noncomputable def sliceAssociatedModule (M : (chartScheme X).Modules)
    [M.IsQuasicoherent]
    (hM : Presheaf.IsSheaf ((topology B S hS F).over X)
      (Stacks.Sites.associatedPresheaf (chartScheme X) M (sliceToOver B S hS F X))) :
    SheafOfModules.{u} (sliceRingSheaf B S hS F hF X) :=
  Stacks.Sites.siteAssociatedModule (chartScheme X) M (sliceToOver B S hS F X)
    ((topology B S hS F).over X) (isSheaf_sliceStructurePresheaf B S hS F hF X) hM

/-- The sections of `Mᵃ` over an object of the slice at `X` are the global sections of the
pullback of `M` to the scheme of that object. -/
@[simp]
theorem sliceAssociatedModule_presheaf (M : (chartScheme X).Modules)
    [M.IsQuasicoherent]
    (hM : Presheaf.IsSheaf ((topology B S hS F).over X)
      (Stacks.Sites.associatedPresheaf (chartScheme X) M (sliceToOver B S hS F X))) :
    (sliceAssociatedModule B S hS F hF X M hM).val.presheaf =
      Stacks.Sites.associatedPresheaf (chartScheme X) M (sliceToOver B S hS F X) :=
  rfl

end AlgebraicGeometry.Space.SmallEtale

end
