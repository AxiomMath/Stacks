module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpBaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankLocalOnCover

/-!
# Étale base change for the direct image of the structure sheaf

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale.  Then `f'_*𝒪_{X'} = (f_*𝒪_X)|_{Y'}` in `Mod(𝒪_{Y'})`: the direct image of the
structure sheaf which Stacks 03ZV uses to define finite local freeness commutes with étale base
change.  Consequently the module conjunct of Stacks 03ZV for `f'` may be read on the étale
restriction of `f_*𝒪_X`, both without a rank and for a fixed rank.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.pushforwardStructureModuleEtaleBaseChangeIso`: the direct image of
  the structure sheaf commutes with étale base change.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_pushforwardStructureModule_baseChange_iff`
  and
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_pushforwardStructureModule_baseChange_iff`:
  the module conjunct of Stacks 03ZV for the base-changed morphism, read on the étale
  restriction of the direct image of the structure sheaf of `X`.
* `SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso`: finite local freeness on a site depends
  only on the isomorphism class of the module.
* `AlgebraicGeometry.Space.isAffineHom_of_presheaf_isFiniteLocallyFree`: a representable
  morphism all of whose represented base changes are finite locally free is affine.

## Implementation notes

The isomorphism is `AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso`, Stacks 03LX
for the ordinary direct image, evaluated at the unit module of `𝒪_X`, together with
`AlgebraicGeometry.Space.etaleModulePullback_obj_unit`: étale restriction only reindexes
sections, so it carries the unit module of `𝒪_X` to the unit module of `𝒪_{X'}` on the nose.

The restriction appearing here is `AlgebraicGeometry.Space.etaleModulePullback`, restriction
along `AlgebraicGeometry.Space.smallEtalePostcomp`, which is the restriction along an étale
morphism of algebraic *spaces*; it is not the restriction `SheafOfModules.over` to a slice of
the small étale site of `Y` at a chart.  Comparing the two is the content of the slice form of
Stacks 04M0, `AlgebraicGeometry.Space.SmallEtale.postcompOverEquivalence`, carried over to
sheaves of modules, and that comparison is not made here.

*Affineness is part of the comparison at a chart.*  The module conjunct of Stacks 03ZV does
not by itself bound the morphism: for `X = 𝐏¹_k` over `Y = Spec k` the direct image `f_*𝒪_X`
is the structure sheaf, hence of rank `1` by
`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_unit`, while `f` is not affine.  So no
equivalence between the rank of `(f_*𝒪_X)|_V` at an étale chart `V` and finite local freeness
of rank `r` of the base change `V ×_Y X ⟶ V` as a morphism of schemes can hold without an
affineness hypothesis on `f`, since `Stacks.Morphisms.IsFiniteLocallyFreeOfRank` extends
`AlgebraicGeometry.IsAffineHom`.

## References

* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

/-! ### Finite local freeness on a site is invariant under isomorphism -/

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- Finite local freeness of a sheaf of modules on a site depends only on its isomorphism
class. -/
theorem IsFiniteLocallyFreeOnSite.of_iso {F G : SheafOfModules.{w} R} (e : F ≅ G)
    (h : IsFiniteLocallyFreeOnSite F) : IsFiniteLocallyFreeOnSite G := by
  rw [SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isColimit] at h ⊢
  intro U
  obtain ⟨I, V, f, hcov, hfree⟩ := h U
  refine ⟨I, V, f, hcov, fun i => ?_⟩
  obtain ⟨n, ι, ⟨hc⟩⟩ := hfree i
  refine ⟨n, fun j => ι j ≫ ((SheafOfModules.overFunctor R (V i)).mapIso e).hom, ⟨?_⟩⟩
  exact IsColimit.ofIsoColimit hc
    (Cocone.ext ((SheafOfModules.overFunctor R (V i)).mapIso e) (fun _ => rfl))

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-! ### Affineness from the represented base changes -/

/-- A representable morphism of algebraic spaces over `S` all of whose represented base changes
are finite locally free is affine.

This is Stacks 03WG, (1) implies (2), `AlgebraicGeometry.Space.isAffineHom_of_presheaf`, applied
after weakening the property along `Stacks.Morphisms.IsFiniteLocallyFree.toIsAffineHom`. -/
theorem isAffineHom_of_presheaf_isFiniteLocallyFree
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : F ⟶ G}
    (h : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p) :
    IsAffineHom B S hS p := by
  refine isAffineHom_of_presheaf ⟨h.rep, ?_⟩
  intro a b q fst snd sq
  have hq : Stacks.Morphisms.IsFiniteLocallyFree
      ((BigFppfOver.toScheme B S hS).map snd) := h.property q fst snd sq
  exact hq.toIsAffineHom

/-! ### The direct image of the structure sheaf under étale base change -/

/-- Étale restriction carries the structure sheaf of `X`, read as the unit `𝒪_X`-module, to the
structure sheaf of `X'`: restriction along small étale postcomposition only reindexes sections,
and the underlying scheme of a chart is unchanged. -/
theorem etaleModulePullback_obj_unit (hi : IsEtale B S hS i.hom) :
    (etaleModulePullback B S hS i hi).obj
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) =
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O) :=
  rfl

/-- **The direct image of the structure sheaf commutes with étale base change.** For a
cartesian square with `g : Y' ⟶ Y` étale, the étale restriction to `Y'` of `f_*𝒪_X` is
`f'_*𝒪_{X'}`.

This is Stacks 03LX for the ordinary direct image,
`AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso`, evaluated at the unit module of
`𝒪_X`. -/
noncomputable def pushforwardStructureModuleEtaleBaseChangeIso
    (sq : IsPullback i f' f g) (hg : IsEtale B S hS g.hom) :
    (etaleModulePullback B S hS g hg).obj (pushforwardStructureModule B S hS f) ≅
      pushforwardStructureModule B S hS f' :=
  ((modulePushforwardEtaleBaseChangeIso B S hS i f' f g sq hg).app
      (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).symm ≪≫
    eqToIso (congrArg (modulePushforward B S hS f').obj
      (etaleModulePullback_obj_unit B S hS i
        (isEtale_of_isPullback B S hS f' i g f sq.flip hg)))

/-! ### The module conjunct of Stacks 03ZV along an étale base change -/

/-- The direct image of the structure sheaf of the source of the base-changed morphism is
finite locally free exactly when the étale restriction to `Y'` of `f_*𝒪_X` is.

This is the module conjunct of Stacks 03ZV for `f'`, read on `Y'` through
`AlgebraicGeometry.Space.pushforwardStructureModuleEtaleBaseChangeIso`. -/
theorem isFiniteLocallyFreeOnSite_pushforwardStructureModule_baseChange_iff
    (sq : IsPullback i f' f g) (hg : IsEtale B S hS g.hom) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (pushforwardStructureModule B S hS f') ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite
        ((etaleModulePullback B S hS g hg).obj (pushforwardStructureModule B S hS f)) :=
  ⟨SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
      (pushforwardStructureModuleEtaleBaseChangeIso B S hS i f' f g sq hg).symm,
    SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
      (pushforwardStructureModuleEtaleBaseChangeIso B S hS i f' f g sq hg)⟩

/-- The direct image of the structure sheaf of the source of the base-changed morphism has
rank `r` exactly when the étale restriction to `Y'` of `f_*𝒪_X` has rank `r`.

This is the rank clause of Stacks 03ZV for `f'`, read on `Y'` through
`AlgebraicGeometry.Space.pushforwardStructureModuleEtaleBaseChangeIso`. -/
theorem isFiniteLocallyFreeOfRank_pushforwardStructureModule_baseChange_iff
    (sq : IsPullback i f' f g) (hg : IsEtale B S hS g.hom) (r : ℕ) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y'.1 Y'.2)
        (pushforwardStructureModule B S hS f') r ↔
      RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y'.1 Y'.2)
        ((etaleModulePullback B S hS g hg).obj (pushforwardStructureModule B S hS f)) r :=
  ⟨RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _
      (pushforwardStructureModuleEtaleBaseChangeIso B S hS i f' f g sq hg).symm,
    RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _
      (pushforwardStructureModuleEtaleBaseChangeIso B S hS i f' f g sq hg)⟩

/-- Finite local freeness of a morphism of algebraic spaces, in the sense of Stacks 03ZV, is
affineness together with finite local freeness of the étale restriction to `Y'` of `f_*𝒪_X`,
when the morphism is the base change of `f` along an étale `g : Y' ⟶ Y`. -/
theorem isFiniteLocallyFree_baseChange_iff (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    IsFiniteLocallyFree B S hS f' ↔
      IsAffineHom B S hS f'.hom ∧
        SheafOfModules.IsFiniteLocallyFreeOnSite
          ((etaleModulePullback B S hS g hg).obj (pushforwardStructureModule B S hS f)) :=
  and_congr_right fun _ =>
    isFiniteLocallyFreeOnSite_pushforwardStructureModule_baseChange_iff B S hS i f' f g sq hg

/-- Having rank `r`, for a morphism of algebraic spaces in the sense of Stacks 03ZV, is
affineness together with rank `r` of the étale restriction to `Y'` of `f_*𝒪_X`, when the
morphism is the base change of `f` along an étale `g : Y' ⟶ Y`. -/
theorem isFiniteLocallyFreeOfRank_baseChange_iff (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (r : ℕ) :
    IsFiniteLocallyFreeOfRank B S hS f' r ↔
      IsAffineHom B S hS f'.hom ∧
        RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y'.1 Y'.2)
          ((etaleModulePullback B S hS g hg).obj (pushforwardStructureModule B S hS f)) r := by
  rw [isFiniteLocallyFreeOfRank_iff]
  exact and_congr_right fun _ =>
    isFiniteLocallyFreeOfRank_pushforwardStructureModule_baseChange_iff B S hS i f' f g sq hg r

end AlgebraicGeometry.Space
