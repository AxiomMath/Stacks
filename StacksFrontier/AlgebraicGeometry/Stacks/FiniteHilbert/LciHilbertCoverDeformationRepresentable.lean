module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FirstOrderThickeningLciDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RegularImmersionFollowedByEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciHilbertDeformation
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.StackOverMap
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrictYoneda

/-!
# Deforming a finite locally free cover into a representable algebraic space

`AlgebraicGeometry.Stack.FiniteHilbert.HasCoverDeformations` is the deformation problem that the
proof of **Stacks 06D9** meets: for a first-order thickening `U ⊂ U'` of affine objects of the
big fppf site, an algebraic space `X'` over `U'` which is flat and locally of finite
presentation, a degree-`d` finite locally free cover `q : Z ⟶ U` and a morphism `f : Z ⟶ X` into
the special fibre `X = U ×_{U'} X'` which is unramified and a local complete intersection
morphism, produce a degree-`d` finite locally free cover `q' : Z' ⟶ U'` presenting `Z` as
`U ×_{U'} Z'` together with a morphism `Z' ⟶ X'` restricting to `f`.

This file solves that problem for an `X'` which is the representable presheaf of an object `T'`
of the big fppf site of `U'`, and deduces the problem itself for a site all of whose flat,
locally finitely presented algebraic spaces over an affine object are representable.

The input is the scheme-level deformation
`Stacks.Thickenings.exists_finiteLocallyFreeOfRank_deformation`, and the work is the passage
between the two languages. In one direction: the special fibre of a representable is
representable — it is the fibre product `U ×_{U'} T'` taken in the size-bounded category of the
site (**Stacks 021U**), and
`CategoryTheory.OverShriek.isIso_restrictYonedaHom_of_isPullback` identifies its representable
presheaf with the restriction of the presheaf of `T'`, so the Yoneda lemma turns `f` into a
morphism `fs` of the site; the four conditions carried by presheaf morphisms —
`AlgebraicGeometry.Space.IsFlat`, `AlgebraicGeometry.Space.IsLocallyOfFinitePresentation`,
`AlgebraicGeometry.Space.IsUnramified` and
`AlgebraicGeometry.Space.IsLocalCompleteIntersection` — are, on a morphism of the site, the
corresponding conditions on its morphism of schemes, which is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff` at each of the four properties.
In the other direction: the scheme `Z'` produced is quasi-compact and of finite type over the
underlying scheme of `U'`, hence belongs to the site by **Stacks 000R (5)**, and a square of
schemes is cartesian in the site exactly when it is cartesian as a square of schemes, because
the inclusion of the size-bounded category is fully faithful and the slice projection reflects
pullbacks (`CategoryTheory.Over.isPullback_iff_left`).

Two of the conditions the problem carries go unused on the representable side: the scheme-level
deformation asks for flatness of `X'` over `U'` and for affineness of `U`, and for neither local
finite presentation of `X'` nor affineness of `U'`.

## Main results

* `AlgebraicGeometry.Stack.FiniteHilbert.exists_coverDeformation_of_siteDeformation`: the
  deformation of the cover, from a deformation of the underlying schemes.
* `AlgebraicGeometry.Stack.FiniteHilbert.exists_coverDeformation_of_yoneda`: **the deformation
  problem of `AlgebraicGeometry.Stack.FiniteHilbert.HasCoverDeformations` for the representable
  presheaf of an object of the big fppf site of `U'`.**
* `AlgebraicGeometry.Stack.FiniteHilbert.hasCoverDeformations_of_isRepresentable`: **the
  deformation problem itself, for a site whose flat, locally finitely presented algebraic spaces
  over an affine object are representable.**

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
* [Stacks Project, Tag 06D9](https://stacks.math.columbia.edu/tag/06D9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Stack.FiniteHilbert

/-! ### The produced cover, read in the site -/

/-- **The deformation of the cover, from a deformation of the underlying schemes.** Given a
morphism `i : U ⟶ U'` of the big fppf site of `S`, a cover `q : Z ⟶ U`, an object `T'` of the
big fppf site of `U'`, an object `T` of the big fppf site of `U` with a morphism
`κ : U' ∘ T ⟶ T'` and a morphism `fs : Z ⟶ T` over `U`, together with a scheme `Zs` in the site
carrying a cartesian square over `i` above `q`, a degree-`d` finite locally free structure
morphism to the underlying scheme of `U'` and a morphism to the underlying scheme of `T'`
compatible with `fs` and `κ`: the scheme `Zs` is the cover asked for, as an object of the big
fppf site of `S`.

The structure morphism over `S` is the composite with that of `U'`, and all four conditions are
checked after applying the fully faithful inclusion of the size-bounded category of the site:
the cartesian square by `CategoryTheory.Over.isPullback_iff_left` followed by
`CategoryTheory.IsPullback.of_map_of_faithful`, and the three commutations by injectivity on
morphisms. -/
theorem exists_coverDeformation_of_siteDeformation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (d : ℕ) {U U' : BigFppfOver B S hS} (i : U ⟶ U')
    {Z : BigFppfOver B S hS} (q : Z ⟶ U)
    {T' : BigFppfOver B U'.left.1 U'.left.2} {T : BigFppfOver B U.left.1 U.left.2}
    (κ : (Over.map i.left).obj T ⟶ T')
    (fs : (Over.mk q.left : BigFppfOver B U.left.1 U.left.2) ⟶ T)
    {Zs : Scheme.{u}} (hZs : B.Contains Zs)
    (iZ : B.inclusion.obj Z.left ⟶ Zs) (pZ' : Zs ⟶ B.inclusion.obj U'.left)
    (fZ' : Zs ⟶ B.inclusion.obj T'.left)
    (hflf : Stacks.Morphisms.IsFiniteLocallyFreeOfRank pZ' d)
    (hpbZ : IsPullback iZ (B.inclusion.map q.left) pZ' (B.inclusion.map i.left))
    (hcomp : iZ ≫ fZ' = B.inclusion.map fs.left ≫ B.inclusion.map κ.left)
    (hbase : fZ' ≫ B.inclusion.map T'.hom = pZ') :
    ∃ (Z' : BigFppfOver B S hS) (q' : Z' ⟶ U') (g : Z ⟶ Z') (hg : IsPullback g q q' i),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q') d ∧
        ∃ f' : yoneda.obj (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2) ⟶ yoneda.obj T',
          OverShriek.restrictYonedaHom i.left (coverComparisonOfSquare hg.w) ≫
              (OverShriek.relocalizeRestrict i.left).map f' =
            yoneda.map fs ≫ OverShriek.restrictYonedaHom i.left κ := by
  have hfZ'w : (ObjectProperty.homMk fZ' : B.obj hZs ⟶ T'.left) ≫ T'.hom =
      (ObjectProperty.homMk pZ' : B.obj hZs ⟶ U'.left) := by
    refine B.inclusion.map_injective ?_
    rw [B.inclusion.map_comp]
    exact hbase
  have hgw : (ObjectProperty.homMk iZ : Z.left ⟶ B.obj hZs) ≫
      (ObjectProperty.homMk pZ' : B.obj hZs ⟶ U'.left) ≫ U'.hom = Z.hom := by
    refine B.inclusion.map_injective ?_
    rw [B.inclusion.map_comp, B.inclusion.map_comp]
    show iZ ≫ pZ' ≫ B.inclusion.map U'.hom = B.inclusion.map Z.hom
    calc iZ ≫ pZ' ≫ B.inclusion.map U'.hom
        = (iZ ≫ pZ') ≫ B.inclusion.map U'.hom := by rw [Category.assoc]
      _ = (B.inclusion.map q.left ≫ B.inclusion.map i.left) ≫ B.inclusion.map U'.hom := by
          rw [hpbZ.w]
      _ = B.inclusion.map (q.left ≫ i.left ≫ U'.hom) := by
          rw [B.inclusion.map_comp, B.inclusion.map_comp, Category.assoc]
      _ = B.inclusion.map Z.hom := by rw [Over.w i, Over.w q]
  have hsq : (Over.homMk (ObjectProperty.homMk iZ) hgw :
        Z ⟶ (Over.map U'.hom).obj (Over.mk (ObjectProperty.homMk pZ' : B.obj hZs ⟶ U'.left))) ≫
        (Over.homMk (ObjectProperty.homMk pZ') rfl :
          (Over.map U'.hom).obj (Over.mk (ObjectProperty.homMk pZ' : B.obj hZs ⟶ U'.left)) ⟶ U') =
      q ≫ i := by
    refine Over.OverMorphism.ext (B.inclusion.map_injective ?_)
    simp only [Over.comp_left]
    rw [B.inclusion.map_comp, B.inclusion.map_comp]
    show iZ ≫ pZ' = B.inclusion.map q.left ≫ B.inclusion.map i.left
    exact hpbZ.w
  have hgpb : IsPullback
      (Over.homMk (ObjectProperty.homMk iZ) hgw :
        Z ⟶ (Over.map U'.hom).obj (Over.mk (ObjectProperty.homMk pZ' : B.obj hZs ⟶ U'.left)))
      q
      (Over.homMk (ObjectProperty.homMk pZ') rfl :
        (Over.map U'.hom).obj (Over.mk (ObjectProperty.homMk pZ' : B.obj hZs ⟶ U'.left)) ⟶ U')
      i := by
    rw [Over.isPullback_iff_left _ _ _ _ hsq]
    refine IsPullback.of_map_of_faithful B.inclusion ?_
    exact hpbZ
  refine ⟨_, _, _, hgpb, hflf, yoneda.map (Over.homMk (ObjectProperty.homMk fZ') hfZ'w), ?_⟩
  rw [OverShriek.restrictYonedaHom_comp_yoneda_map,
    OverShriek.yoneda_map_comp_restrictYonedaHom]
  refine congrArg (OverShriek.restrictYonedaHom i.left) ?_
  refine Over.OverMorphism.ext (B.inclusion.map_injective ?_)
  simp only [Over.comp_left, Over.map_map_left]
  rw [B.inclusion.map_comp, B.inclusion.map_comp]
  show iZ ≫ fZ' = B.inclusion.map fs.left ≫ B.inclusion.map κ.left
  exact hcomp

/-! ### The deformation problem for a representable presheaf -/

attribute [local instance] AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes

/-- A property holding on every étale chart of `f = yoneda.map fs ≫ φ`, with `φ` an isomorphism of
presheaves, holds on the morphism of schemes underlying `fs`. -/
private theorem toScheme_map_of_yoneda_map_comp_iso (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {P : MorphismProperty Scheme.{u}} (hP : IsEtaleLocalOnSourceAndTarget P)
    {V W : BigFppfOver B S hS} (fs : V ⟶ W) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (φ : yoneda.obj W ⟶ Y) [IsIso φ] {f : yoneda.obj V ⟶ Y} (hf : yoneda.map fs ≫ φ = f)
    (h : Space.HoldsOnEveryEtaleChart B S hS P f) : P ((BigFppfOver.toScheme B S hS).map fs) := by
  refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS hP fs).1 ?_
  refine (Space.holdsOnEveryEtaleChart_comp_iso_iff B S hS _ (yoneda.map fs) φ).1 ?_
  rwa [hf]

/-- **The deformation problem of
`AlgebraicGeometry.Stack.FiniteHilbert.HasCoverDeformations` for the representable presheaf of
an object `T'` of the big fppf site of `U'`.**

The special fibre is the fibre product `U ×_{U'} T'` of the size-bounded category of the site,
whose representable presheaf is the restriction of the presheaf of `T'`
(`CategoryTheory.OverShriek.isIso_restrictYonedaHom_of_isPullback`), so `f` is represented by a
morphism `fs` of the big fppf site of `U`. Unramifiedness and the local complete intersection
condition pass to the morphism of schemes under `fs` by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff`, and unramifiedness implies
formal unramifiedness, so
`Stacks.Thickenings.exists_finiteLocallyFreeOfRank_deformation` applies and
`AlgebraicGeometry.Stack.FiniteHilbert.exists_coverDeformation_of_siteDeformation` reads its
output back in the site.

Flatness of `T'` over `U'` is used; local finite presentation of `T'`, and affineness of `U'`,
are not. -/
theorem exists_coverDeformation_of_yoneda (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (d : ℕ) {U U' : BigFppfOver B S hS} (i : U ⟶ U')
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hi : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    (T' : BigFppfOver B U'.left.1 U'.left.2)
    (hflat : Space.IsFlat B U'.left.1 U'.left.2
      (Space.toYonedaId B U'.left.1 U'.left.2 (yoneda.obj T')))
    {Z : BigFppfOver B S hS} (q : Z ⟶ U)
    (hq : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) d)
    (f : yoneda.obj (Over.mk q.left : BigFppfOver B U.left.1 U.left.2) ⟶
      (OverShriek.relocalizeRestrict i.left).obj (yoneda.obj T'))
    (hunr : Space.IsUnramified B U.left.1 U.left.2 f)
    (hlci : Space.IsLocalCompleteIntersection B U.left.1 U.left.2 f) :
    ∃ (Z' : BigFppfOver B S hS) (q' : Z' ⟶ U') (g : Z ⟶ Z') (hg : IsPullback g q q' i),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q') d ∧
        ∃ f' : yoneda.obj (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2) ⟶ yoneda.obj T',
          OverShriek.restrictYonedaHom i.left (coverComparisonOfSquare hg.w) ≫
              (OverShriek.relocalizeRestrict i.left).map f' = f := by
  have : IsAffine (B.inclusion.obj U.left) := hU
  -- the special fibre, as an object of the big fppf site of `U`
  obtain ⟨T, κ, hpb⟩ : ∃ (T : BigFppfOver B U.left.1 U.left.2)
      (κ : (Over.map i.left).obj T ⟶ T'), IsPullback κ.left T.hom T'.hom i.left :=
    ⟨Over.mk (pullback.snd T'.hom i.left),
      Over.homMk (pullback.fst T'.hom i.left) pullback.condition,
      IsPullback.of_hasPullback _ _⟩
  have hiso : IsIso (OverShriek.restrictYonedaHom i.left κ) :=
    OverShriek.isIso_restrictYonedaHom_of_isPullback i.left κ hpb
  -- the morphism into the special fibre, as a morphism of the site
  obtain ⟨fs, hfs⟩ : ∃ fs : (Over.mk q.left : BigFppfOver B U.left.1 U.left.2) ⟶ T,
      yoneda.map fs ≫ OverShriek.restrictYonedaHom i.left κ = f := by
    refine ⟨yoneda.preimage (f ≫ inv (OverShriek.restrictYonedaHom i.left κ)), ?_⟩
    rw [Functor.map_preimage, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  -- the hypotheses of the scheme-level deformation
  have hflatT' : Flat (B.inclusion.map T'.hom) := by
    refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B U'.left.1 U'.left.2
      Flat.isEtaleLocalOnSourceAndTarget
      (Over.homMk T'.hom (by simp) : T' ⟶ Over.mk (𝟙 (B.obj U'.left.2)))).1 ?_
    rw [eq_toYonedaId B U'.left.1 U'.left.2
      (yoneda.map (Over.homMk T'.hom (by simp) : T' ⟶ Over.mk (𝟙 (B.obj U'.left.2))))]
    exact hflat
  have hunrs : Unramified (B.inclusion.map fs.left) :=
    toScheme_map_of_yoneda_map_comp_iso B U.left.1 U.left.2
      unramified_isEtaleLocalOnSourceAndTarget fs _ hfs hunr
  have hlcis : IsLocalCompleteIntersectionMorphism (B.inclusion.map fs.left) :=
    toScheme_map_of_yoneda_map_comp_iso B U.left.1 U.left.2
      (isEtaleLocalOnSourceAndTarget_isLocalCompleteIntersectionMorphism
        isLocalCompleteIntersectionMorphism_isLocalAtSource_etale) fs _ hfs hlci
  have : FormallyUnramified (B.inclusion.map fs.left) := formallyUnramified_of_unramified _
  have hfZcomp : B.inclusion.map fs.left ≫ B.inclusion.map T.hom = B.inclusion.map q.left := by
    rw [← B.inclusion.map_comp]
    exact congrArg B.inclusion.map (Over.w fs)
  obtain ⟨Zs, iZ, pZ', fZ', -, hflf, hpbZ, hcomp, hbase⟩ :=
    Stacks.Thickenings.exists_finiteLocallyFreeOfRank_deformation
      (B.inclusion.map i.left) hi (B.inclusion.map T'.hom) (B.inclusion.map κ.left)
      (B.inclusion.map T.hom) (hpb.map B.inclusion) (B.inclusion.map q.left) d hq
      (B.inclusion.map fs.left) hlcis hfZcomp
  -- the produced cover belongs to the site
  have : Stacks.Morphisms.IsFiniteLocallyFree pZ' :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree pZ' d
  have : IsFinite pZ' := Stacks.Morphisms.IsFiniteLocallyFree.isFinite pZ'
  obtain ⟨Z', q', g, hg, hrank, f', hf'⟩ :=
    exists_coverDeformation_of_siteDeformation B S hS d i q κ fs
      (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact pZ' U'.left.2) iZ pZ' fZ'
      hflf hpbZ hcomp hbase
  exact ⟨Z', q', g, hg, hrank, f', by rw [hf', hfs]⟩

/-- **The deformation problem of
`AlgebraicGeometry.Stack.FiniteHilbert.HasCoverDeformations`, for a big fppf site over `S` whose
flat, locally finitely presented algebraic spaces over an affine object with affine first-order
thickening are representable.**

The representing object is transported along the isomorphism `CategoryTheory.Functor.reprW`: the
structural morphism to the terminal object is the unique such morphism
(`AlgebraicGeometry.Stack.eq_toYonedaId`), and the every-étale-chart condition of
**Stacks 03MJ** is unchanged by composition with an isomorphism of presheaves
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iso_comp_iff` and its companion), so the
hypotheses pass to the representable presheaf;
`AlgebraicGeometry.Stack.FiniteHilbert.exists_coverDeformation_of_yoneda` solves the problem
there, and the produced morphism is composed back with the inverse of the isomorphism. -/
theorem hasCoverDeformations_of_isRepresentable (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (d : ℕ)
    (hrep : ∀ (U U' : BigFppfOver B S hS) (i : U ⟶ U'),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj U') →
      Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i) →
      ∀ X' : (BigFppfOver B U'.left.1 U'.left.2)ᵒᵖ ⥤ Type u,
        IsAlgebraicSpace B U'.left.1 U'.left.2 X' →
        Space.IsFlat B U'.left.1 U'.left.2 (Space.toYonedaId B U'.left.1 U'.left.2 X') →
        Space.IsLocallyOfFinitePresentation B U'.left.1 U'.left.2
          (Space.toYonedaId B U'.left.1 U'.left.2 X') →
        X'.IsRepresentable) :
    HasCoverDeformations B S hS d := by
  intro U U' i hU hU' hi X' hX' hflat hlfp Z q hq f hunr hlci
  have := hrep U U' i hU hU' hi X' hX' hflat hlfp
  -- the representing object and the isomorphism naming it
  have hflatT' : Space.IsFlat B U'.left.1 U'.left.2
      (Space.toYonedaId B U'.left.1 U'.left.2 (yoneda.obj X'.reprX)) := by
    rw [← eq_toYonedaId B U'.left.1 U'.left.2
      ((X'.reprW).hom ≫ Space.toYonedaId B U'.left.1 U'.left.2 X')]
    exact (Space.holdsOnEveryEtaleChart_iso_comp_iff B U'.left.1 U'.left.2 _ (X'.reprW).hom
      (Space.toYonedaId B U'.left.1 U'.left.2 X')).2 hflat
  have hunrT' : Space.IsUnramified B U.left.1 U.left.2
      (f ≫ (OverShriek.relocalizeRestrict i.left).map (X'.reprW).inv) :=
    (Space.holdsOnEveryEtaleChart_comp_iso_iff B U.left.1 U.left.2 _ f
      ((OverShriek.relocalizeRestrict i.left).map (X'.reprW).inv)).2 hunr
  have hlciT' : Space.IsLocalCompleteIntersection B U.left.1 U.left.2
      (f ≫ (OverShriek.relocalizeRestrict i.left).map (X'.reprW).inv) :=
    (Space.holdsOnEveryEtaleChart_comp_iso_iff B U.left.1 U.left.2 _ f
      ((OverShriek.relocalizeRestrict i.left).map (X'.reprW).inv)).2 hlci
  obtain ⟨Z', q', g, hg, hrank, f', hf'⟩ :=
    exists_coverDeformation_of_yoneda B S hS d i hU hi X'.reprX hflatT' q hq
      (f ≫ (OverShriek.relocalizeRestrict i.left).map (X'.reprW).inv) hunrT' hlciT'
  refine ⟨Z', q', g, hg, hrank, f' ≫ (X'.reprW).hom, ?_⟩
  rw [Functor.map_comp, ← Category.assoc, hf', Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]

end AlgebraicGeometry.Stack.FiniteHilbert

end
