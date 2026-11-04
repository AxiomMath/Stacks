module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreePushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSiteComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleFree

/-!
# Étale restriction of modules compared with restriction to a slice at a chart

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `V` be an étale chart of `X`.  The slice of the small étale site of `X`
at `V` is equivalent to the slice of the small étale site of `Y` at the composite chart, by the
slice form of Stacks 04M0, and that equivalence matches the two structure sheaves.  Hence a
module on `Y` is finite locally free, respectively of rank `r`, on the slice at the composite
chart exactly when its étale restriction to `X` is on the slice at `V`.

Combined with Stacks 03LX for the structure sheaf this reads the module conjunct of Stacks 03ZV
for the base change `f' : X' ⟶ Y'` of a morphism `f : X ⟶ Y` along an étale `g : Y' ⟶ Y` on the
chart of `Y` obtained from a chart of `Y'` by postcomposition with `g`.

The slice at a chart also carries the modules `Mᵃ` of Stacks 03DU; the file records that the
presheaf of Stacks 03DS defining them is a sheaf, so that the free modules of the slice at an
affine chart are unconditionally of that form.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleRingedSitePostcomp` and
  `AlgebraicGeometry.Space.smallEtaleRingedSitePostcompOverEquivalence` are postcomposition with
  an étale morphism of algebraic spaces and its slice comparison, stated for the projections of
  `AlgebraicGeometry.Space.smallEtaleRingedSite`.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_over_etaleModulePullback_iff` and
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_over_etaleModulePullback_iff`: finite local
  freeness, respectively rank `r`, of the restriction of a module to the slice at a chart is
  unchanged by étale restriction.
* `Space.isFiniteLocallyFreeOnSite_over_pushforwardStructureModule_baseChange_iff` and
  `Space.isFiniteLocallyFreeOfRank_over_pushforwardStructureModule_baseChange_iff` are the
  module conjunct and the rank clause of Stacks 03ZV for an étale base change, read on a chart of
  the base of the base-changed morphism.
* `AlgebraicGeometry.quasiCoherentPresheafForget_isSheaf_fpqc`: **Stacks 03DT in the underlying
  types**, and
  `AlgebraicGeometry.Space.SmallEtale.isSheaf_sliceAssociatedPresheaf'` and
  `AlgebraicGeometry.Space.SmallEtale.exists_sliceAssociatedModule_iso_free'`, its two
  consequences on the slice at a chart, the second being the free case of Stacks 03DX (2).

## Implementation notes

The slice comparison `AlgebraicGeometry.Space.SmallEtale.postcompOverEquivalence` and its
continuity and dense-subsite instances are stated for `AlgebraicGeometry.Space.SmallEtale.topology`
over the category `AlgebraicGeometry.Space.SmallEtale`, whereas `AlgebraicGeometry.Space.Modules`
forces the projections of `AlgebraicGeometry.Space.smallEtaleRingedSite`.  Since the latter is a
definition, an object of the site carries two spellings of its ambient category which instance
search does not identify, and `CategoryTheory.Over` of such an object then has no `Category`
instance at reducible transparency.  The comparison is therefore restated here for the
projections, exactly as
`AlgebraicGeometry.Space.smallEtaleRingedSite_isContinuous_smallEtalePostcomp` restates
continuity of postcomposition itself.

The two transport statements are `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_reindex_iff` and
`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_reindex_iff` applied to that equivalence.
No comparison isomorphism intervenes: restriction along postcomposition leaves the underlying
scheme of a chart unchanged, so the transported structure sheaf is the structure sheaf of the
slice of the small étale ringed site of `X` on the nose, and likewise for the transported module.

The sheaf condition of Stacks 03DT is stated in the tree for presheaves of abelian groups and is
consumed, through `AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule`, in the underlying
types.  The two spellings are bridged by `CategoryTheory.isSheaf_iff_isSheaf_of_type` at the
`Type`-valued presheaf of module homomorphisms out of the structure sheaf, which
`AlgebraicGeometry.quasiCoherentPresheafIsoPresheafHom` identifies with the presheaf of Tag 03DS.

## References

* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The slice comparison of Stacks 04M0 on the small étale ringed sites -/

/-- Postcomposition with an étale morphism `f : X ⟶ Y` of algebraic spaces, between the
underlying categories of the small étale ringed sites. -/
noncomputable abbrev smallEtaleRingedSitePostcomp (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (smallEtaleRingedSite B S hS X.1 X.2).C ⥤ (smallEtaleRingedSite B S hS Y.1 Y.2).C :=
  smallEtalePostcomp B S hS f hf

/-- **Stacks 04M0, slice form.** Postcomposition with an étale morphism `f : X ⟶ Y` of algebraic
spaces is an equivalence from the slice of the small étale ringed site of `X` at a chart `V` onto
the slice of the small étale ringed site of `Y` at the composite chart. -/
noncomputable def smallEtaleRingedSitePostcompOverEquivalence (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    Over V ≌ Over ((smallEtaleRingedSitePostcomp B S hS f hf).obj V) :=
  SmallEtale.postcompOverEquivalence B S hS f hf V

/-- The slice comparison is continuous for the localized topologies of the small étale ringed
sites. -/
instance smallEtaleRingedSite_isContinuous_postcompOverEquivalence_functor (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V).functor.IsContinuous
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over V)
      ((smallEtaleRingedSite B S hS Y.1 Y.2).J.over
        ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)) :=
  SmallEtale.isContinuous_overPostcomp B S hS f hf V

/-- The inverse of the slice comparison is continuous for the localized topologies of the small
étale ringed sites. -/
instance smallEtaleRingedSite_isContinuous_postcompOverEquivalence_inverse (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V).inverse.IsContinuous
      ((smallEtaleRingedSite B S hS Y.1 Y.2).J.over
        ((smallEtaleRingedSitePostcomp B S hS f hf).obj V))
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over V) :=
  SmallEtale.isContinuous_postcompOverInverse B S hS f hf V

/-- The slice comparison is an equivalence of sites in the dense-subsite sense, for the localized
topologies of the small étale ringed sites. -/
instance smallEtaleRingedSite_isDenseSubsite_postcompOverEquivalence_inverse (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V).inverse.IsDenseSubsite
      ((smallEtaleRingedSite B S hS Y.1 Y.2).J.over
        ((smallEtaleRingedSitePostcomp B S hS f hf).obj V))
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over V) :=
  SmallEtale.isDenseSubsite_postcompOverInverse B S hS f hf V

/-! ### Finite local freeness on a slice under étale restriction -/

/-- **Finite local freeness on a slice is unchanged by étale restriction.** For an étale
`f : X ⟶ Y` and an étale chart `V` of `X`, the restriction of the étale pullback of an
`𝒪_Y`-module to the slice at `V` is finite locally free exactly when the restriction of the
module itself to the slice at the composite chart is. -/
theorem isFiniteLocallyFreeOnSite_over_etaleModulePullback_iff (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    SheafOfModules.IsFiniteLocallyFreeOnSite
        (((etaleModulePullback B S hS f hf).obj M).over V) ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite
        (M.over ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)) :=
  Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_reindex_iff
    (J' := (smallEtaleRingedSite B S hS X.1 X.2).J.over V)
    (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V)
    (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).over
      ((smallEtaleRingedSitePostcomp B S hS f hf).obj V))
    (M.over ((smallEtaleRingedSitePostcomp B S hS f hf).obj V))

/-- **The rank on a slice is unchanged by étale restriction.** For an étale `f : X ⟶ Y` and an
étale chart `V` of `X`, the restriction of the étale pullback of an `𝒪_Y`-module to the slice at
`V` has rank `r` exactly when the restriction of the module itself to the slice at the composite
chart has. -/
theorem isFiniteLocallyFreeOfRank_over_etaleModulePullback_iff (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C) (r : ℕ) :
    RingedSite.IsFiniteLocallyFreeOfRank ((smallEtaleRingedSite B S hS X.1 X.2).over V)
        (((etaleModulePullback B S hS f hf).obj M).over V) r ↔
      RingedSite.IsFiniteLocallyFreeOfRank
        ((smallEtaleRingedSite B S hS Y.1 Y.2).over
          ((smallEtaleRingedSitePostcomp B S hS f hf).obj V))
        (M.over ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)) r := by
  have _ : (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V).functor.IsContinuous
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over V)
      ((smallEtaleRingedSite B S hS Y.1 Y.2).over
        ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)).J :=
    SmallEtale.isContinuous_overPostcomp B S hS f hf V
  have _ : (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V).inverse.IsContinuous
      ((smallEtaleRingedSite B S hS Y.1 Y.2).over
        ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)).J
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over V) :=
    SmallEtale.isContinuous_postcompOverInverse B S hS f hf V
  have _ : (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V).inverse.IsDenseSubsite
      ((smallEtaleRingedSite B S hS Y.1 Y.2).over
        ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)).J
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over V) :=
    SmallEtale.isDenseSubsite_postcompOverInverse B S hS f hf V
  exact RingedSite.isFiniteLocallyFreeOfRank_reindex_iff
    ((smallEtaleRingedSite B S hS Y.1 Y.2).over
      ((smallEtaleRingedSitePostcomp B S hS f hf).obj V))
    ((smallEtaleRingedSite B S hS X.1 X.2).J.over V)
    (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V)
    (M.over ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)) r

/-! ### The module conjunct of Stacks 03ZV for an étale base change, at a chart -/

section BaseChange

variable {X' Y' : AlgebraicSpaces B S hS}

/-- **The module conjunct of Stacks 03ZV for an étale base change, read at a chart.** For a
cartesian square with `g : Y' ⟶ Y` étale and an étale chart `V` of `Y'`, the restriction of
`f'_*𝒪_{X'}` to the slice at `V` is finite locally free exactly when the restriction of
`f_*𝒪_X` to the slice at the composite chart of `Y` is. -/
theorem isFiniteLocallyFreeOnSite_over_pushforwardStructureModule_baseChange_iff
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (V : (smallEtaleRingedSite B S hS Y'.1 Y'.2).C) :
    SheafOfModules.IsFiniteLocallyFreeOnSite
        ((pushforwardStructureModule B S hS f').over V) ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite
        ((pushforwardStructureModule B S hS f).over
          ((smallEtaleRingedSitePostcomp B S hS g hg).obj V)) :=
  Iff.trans
    ⟨SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
        ((SheafOfModules.overFunctor _ V).mapIso
          (pushforwardStructureModuleEtaleBaseChangeIso B S hS i f' f g sq hg)).symm,
      SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
        ((SheafOfModules.overFunctor _ V).mapIso
          (pushforwardStructureModuleEtaleBaseChangeIso B S hS i f' f g sq hg))⟩
    (isFiniteLocallyFreeOnSite_over_etaleModulePullback_iff B S hS g hg
      (pushforwardStructureModule B S hS f) V)

/-- **The rank clause of Stacks 03ZV for an étale base change, read at a chart.** For a cartesian
square with `g : Y' ⟶ Y` étale and an étale chart `V` of `Y'`, the restriction of `f'_*𝒪_{X'}` to
the slice at `V` has rank `r` exactly when the restriction of `f_*𝒪_X` to the slice at the
composite chart of `Y` has. -/
theorem isFiniteLocallyFreeOfRank_over_pushforwardStructureModule_baseChange_iff
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (V : (smallEtaleRingedSite B S hS Y'.1 Y'.2).C) (r : ℕ) :
    RingedSite.IsFiniteLocallyFreeOfRank ((smallEtaleRingedSite B S hS Y'.1 Y'.2).over V)
        ((pushforwardStructureModule B S hS f').over V) r ↔
      RingedSite.IsFiniteLocallyFreeOfRank
        ((smallEtaleRingedSite B S hS Y.1 Y.2).over
          ((smallEtaleRingedSitePostcomp B S hS g hg).obj V))
        ((pushforwardStructureModule B S hS f).over
          ((smallEtaleRingedSitePostcomp B S hS g hg).obj V)) r :=
  Iff.trans
    ⟨RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _
        ((SheafOfModules.overFunctor _ V).mapIso
          (pushforwardStructureModuleEtaleBaseChangeIso B S hS i f' f g sq hg)).symm,
      RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _
        ((SheafOfModules.overFunctor _ V).mapIso
          (pushforwardStructureModuleEtaleBaseChangeIso B S hS i f' f g sq hg))⟩
    (isFiniteLocallyFreeOfRank_over_etaleModulePullback_iff B S hS g hg
      (pushforwardStructureModule B S hS f) V r)

end BaseChange

end AlgebraicGeometry.Space

/-! ### The sheaf condition of Stacks 03DT in the underlying types -/

namespace AlgebraicGeometry

/-- **Stacks 03DT, in the underlying types.** The presheaf of Tag 03DS of a quasi-coherent
module on a scheme `T`, read in the underlying types, is a sheaf for the fpqc topology on the
schemes over `T`.

This is `AlgebraicGeometry.isSheaf_presheafHom'` transported along
`AlgebraicGeometry.quasiCoherentPresheafIsoPresheafHom`, which identifies that presheaf with the
presheaf of module homomorphisms out of the structure sheaf; the transport happens in the
underlying types, where the sheaf condition is the one of Tag 023T. -/
theorem quasiCoherentPresheafForget_isSheaf_fpqc (T : Scheme.{u}) :
    ∀ (M : T.Modules) (_ : M.IsQuasicoherent),
      Presieve.IsSheaf (Scheme.fpqcTopology.{u}.over T)
        (quasiCoherentPresheafFunctor T M ⋙ CategoryTheory.forget AddCommGrpCat.{u}) :=
  fun M hM =>
    (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_of_iso_iff (@quasiCoherentPresheafIsoPresheafHom T M hM)).mpr
        (@isSheaf_presheafHom' T (Scheme.unitModule T) M _ hM))

namespace Space.SmallEtale

open _root_.AlgebraicGeometry.Space

/-- **The presheaf of Tag 03DS of a quasi-coherent module on the scheme of an étale chart is a
sheaf on the slice of the small étale site at that chart.**  This is
`AlgebraicGeometry.Space.SmallEtale.isSheaf_sliceAssociatedPresheaf` with its instance of
Stacks 03DT discharged. -/
theorem isSheaf_sliceAssociatedPresheaf' (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (Y : SmallEtale B S hS F) :
    ∀ (M : (chartScheme Y).Modules) (_ : M.IsQuasicoherent),
      Presheaf.IsSheaf ((topology B S hS F).over Y)
        (Stacks.Sites.associatedPresheaf (chartScheme Y) M (sliceToOver B S hS F Y)) :=
  fun M hM => isSheaf_sliceAssociatedPresheaf B S hS F Y M
    (quasiCoherentPresheafForget_isSheaf_fpqc (chartScheme Y) M hM)

/-- **A free module on the slice of the small étale site at an affine chart is the module `Mᵃ` of
Tag 03DU of a quasi-coherent module on the chart's scheme.**  This is
`AlgebraicGeometry.Space.SmallEtale.exists_sliceAssociatedModule_iso_free` with its instance of
Stacks 03DT discharged. -/
theorem exists_sliceAssociatedModule_iso_free' (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (Y : SmallEtale B S hS F) (hY : IsAffine (chartScheme Y)) (I : Type u) :
    ∃ (M : (chartScheme Y).Modules) (_ : M.IsQuasicoherent)
      (hM : Presheaf.IsSheaf ((topology B S hS F).over Y)
        (Stacks.Sites.associatedPresheaf (chartScheme Y) M (sliceToOver B S hS F Y))),
      Nonempty (SheafOfModules.free (R := sliceRingSheaf B S hS F hF Y) I ≅
        sliceAssociatedModule B S hS F hF Y M hM) :=
  exists_sliceAssociatedModule_iso_free B S hS F hF Y hY I
    (isSheaf_sliceAssociatedPresheaf' B S hS F Y)

end Space.SmallEtale

end AlgebraicGeometry

end
