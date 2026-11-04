module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSliceEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallSiteMonoidalClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenSplittingDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraCoextendScalarsInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.EmptyOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleQuasiFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFinitePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreePushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompCocontinuous
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompSlice
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale localization on the base of the direct image along an affine morphism

Let `π : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B` and let `g : U ⟶ X` be étale, with base change

```
V --q--> Y
|p       |π
U --g--> X
```

Stacks 03LX identifies `(π_*𝒢)|_U` with `p_*(𝒢|_V)`, and this file supplies the two further
localizations on the base that the proof of [Stacks, Tag 0GUZ] performs after that
identification.

**The clopen splitting.**  When the base change `V = U ×_X Y` decomposes into two open and
closed pieces, `p_*(𝒢|_V)` splits as a biproduct; that is
`AlgebraicGeometry.Space.modulePushforwardBaseChangeBiprodIsoOfClopen`.  Such a decomposition
is produced by [Stacks, Tag 0ADU], `AlgebraicGeometry.Space.exists_etale_finite_clopen_part`,
which delivers it as a pair of complementary `CategoryTheory.Subfunctor`s of the fibre product,
whereas the biproduct isomorphism asks for a pair of morphisms of algebraic spaces which are
étale closed immersions whose images on points are disjoint and cover the fibre product.  The
first half of this file converts the one datum into the other.

**The relative dualizing module.**  The second half proves that `π_*ω_{Y/X}` localizes:

`(π_*ω_{Y/X})|_U ≅ p_*ω_{V/U}`

for `π` affine, which the source states without proof.  Its ingredient of independent interest
is that the internal Hom commutes with étale restriction,

`𝓗om_{𝒪_X}(ℳ, 𝒩)|_U ≅ 𝓗om_{𝒪_U}(ℳ|_U, 𝒩|_U)`,

with no flatness and no finiteness hypothesis.

## Main results

* `AlgebraicGeometry.Space.disjoint_range_pointsMap_ι_of_inf_eq_sheafify_bot`: two subfunctors
  whose meet is the sheafification of the bottom subfunctor have disjoint images on points.
* `AlgebraicGeometry.Space.exists_etale_neighbourhood_modulePushforward_biprod`: the splitting
  of the restriction of a direct image to an étale neighbourhood of a point of the target.
* `AlgebraicGeometry.Space.etaleModulePullbackInternalHomSmallIso`: **the internal Hom commutes
  with étale restriction.**
* `AlgebraicGeometry.Space.smallEtaleInternalHomSmallCongrLeft`: the internal Hom transported
  along an isomorphism of its first argument.
* `AlgebraicGeometry.Space.etaleModulePullbackDualizingPushforwardIso`: **the dual
  `𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` commutes with étale restriction on the base.**
* `AlgebraicGeometry.Space.etaleModulePullbackModulePushforwardRelativeDualizingModuleIso`:
  **`π_*ω_{Y/X}` commutes with étale restriction on the base.**

## Implementation notes

### The clopen splitting

The two point-set conditions are the whole content of that conversion; the two morphism
conditions are immediate.  A piece `W` of the decomposition is an algebraic space because
`AlgebraicGeometry.Space.IsOpenSubspace` includes that clause, and the inclusion `W.ι`,
promoted to a morphism of algebraic spaces by `CategoryTheory.ObjectProperty.homMk`, is étale
because an open immersion is (`AlgebraicGeometry.Space.isEtale_of_isOpenImmersion`) and is a
closed immersion by the second clause of `AlgebraicGeometry.Space.IsClosedSubspace`.

* Joint surjectivity on points is the existing
  `AlgebraicGeometry.Space.mem_range_pointsMap_ι_or_of_sheafify_sup_eq_top`, which turns the
  condition `(W ⊔ W').sheafify = ⊤` of [Stacks, Tag 0ADU] into membership of one of the two
  images, pointwise; it needs no hypothesis that the ambient functor is an algebraic space.
* Disjointness is proved here.  A point lying in both images gives, by the Cartesian square
  `CategoryTheory.Subfunctor.isPullback_inf` exhibiting `W ⊓ W'` as the fibre product of the
  two inclusions, a point of `W ⊓ W'`; and `W ⊓ W'` is the sheafification of the bottom
  subfunctor, which has no points by
  `AlgebraicGeometry.Space.range_pointsMap_ι_sheafify_bot`.

The ambient algebraic space is `AlgebraicGeometry.Space.AlgebraicSpaces.fiberProduct`, whose
underlying functor is the pullback of presheaves that [Stacks, Tag 0ADU] states its
decomposition inside, so the subfunctors transfer with no rewriting; the Cartesian square is
`AlgebraicGeometry.Space.AlgebraicSpaces.isPullback_fiberProduct` flipped.

### The internal Hom under étale restriction

This is **not** Stacks 0GN2, the comparison for a flat morphism and a finitely presented first
argument.  That result is in the development, as
`Stacks.SheafOfModules.InternalHom.isIso_pullbackInternalHomMap_of_isFinitePresentationOnSite`,
but only for a `AlgebraicGeometry.RingedSite.{u, u, u}`, whereas
`AlgebraicGeometry.Space.smallEtaleRingedSite` is a `AlgebraicGeometry.RingedSite.{u + 1, u, u}`
— the same universe obstruction that
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallSiteSheafHomComparison.lean`
records.

What is used instead is
`Stacks.SheafOfModules.InternalHom.sliceEquivInternalHomSmallIso`, which holds at free
universes and with no flatness or finiteness, for restriction along any functor of sites which
is continuous, cocontinuous and an equivalence on every slice.  Étale restriction is such a
restriction on the nose: `AlgebraicGeometry.Space.etaleModulePullback` *is*
`SheafOfModules.pushforward` of the identity along
`AlgebraicGeometry.Space.smallEtalePostcomp`, whose continuity, cocontinuity (Stacks 03LP) and
slice equivalence (Stacks 04M0) are all already instances.  Every argument is supplied
explicitly: left to unification the instantiation does not elaborate within the heartbeat
budget.

Transport along an isomorphism of the first argument of the internal Hom goes through the
monoidal closed structure of `AlgebraicGeometry.Space.modulesMonoidalClosed`, whose internal
Hom is `AlgebraicGeometry.Space.smallEtaleInternalHomSmall` by `rfl`; the existing
`AlgebraicGeometry.Space.smallEtaleInternalHomMapLeft` is the functoriality of
`AlgebraicGeometry.Space.smallEtaleInternalHom`, the model with sections in `u + 1`, and does
not apply.

### What the localization of `π_*ω_{Y/X}` is built from

`AlgebraicGeometry.Space.modulePushforward_relativeDualizingModuleIso` identifies
`π_*ω_{Y/X}` with the dual `𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)`; the internal Hom is restricted by the
isomorphism above; the first argument is moved by
`AlgebraicGeometry.Space.pushforwardStructureModuleEtaleBaseChangeIso`, which is Stacks 03LX at
the structure sheaf; and the second argument needs no move at all, étale restriction carrying
the unit module to the unit module by `rfl`
(`AlgebraicGeometry.Space.etaleModulePullback_obj_unit`).  Affineness of the base-changed `p`
comes from `AlgebraicGeometry.Space.isAffineHom_hom_of_isPullback`.

Finite presentation of `p_*𝒪_V` is a hypothesis, as it is of every result about `ω_{Y/X}` in
the development: it is a statement about coverings of the small étale site of `U`, and the
transport of `SheafOfModules.IsFinitePresentationOnSite` along étale restriction is not in the
library.  It is a genuine condition on the morphism, not a stand-in for any unproved result.

### What is not proved

**No part of [Stacks, Tag 0GUZ] is claimed, and nothing here carries `@[stacks 0GUZ]`.**  Two
steps of that tag's proof remain after this file.

* The compatibility of the localization with the **trace**: that
  `AlgebraicGeometry.Space.dualizingTrace` for `π`, restricted to `U`, agrees with the trace
  for `p` under `AlgebraicGeometry.Space.etaleModulePullbackDualizingPushforwardIso`.  The
  trace is defined at the raised module universe, as
  `AlgebraicGeometry.Space.dualizingTraceLift`, and pushing the slice equivalence through that
  universe lift is not done here.
* The step that produces the sections: finitely many generators of `π^!ℱ` over the affine chart
  `V` of [Stacks, Tag 0GUY], extended to morphisms `ℐ^{n_i} ⟶ π^!ℱ` by [Stacks, Tag 07UM]
  (`AlgebraicGeometry.Space.canonicalMapToSections_bijective`), whose images under
  `AlgebraicGeometry.Space.resolutionSituationSigma` are the maps `σ_i` whose joint
  surjectivity is the assertion of [Stacks, Tag 0GUZ].  The splitting that the surjectivity is
  checked over must also be refined so that the finite piece maps *isomorphically* onto `U`,
  which is Stacks 04HL; that tag is proved for schemes, as
  `AlgebraicGeometry.exists_etaleNeighborhood_openCopies_cover_fibers` in
  `StacksFrontier/AlgebraicGeometry/Morphisms/Etale/LocalStructure/OpenCopies.lean`, and not for
  algebraic spaces.

## References

* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ)
* [Stacks Project, Tag 0GUY](https://stacks.math.columbia.edu/tag/0GUY)
* [Stacks Project, Tag 0ADU](https://stacks.math.columbia.edu/tag/0ADU)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The clopen splitting of an étale neighbourhood -/

section Clopen

attribute [local instance 5000] SheafOfModules.instAbelian

/-- **Two subfunctors whose meet is the sheafification of the bottom subfunctor have disjoint
images on points.**

A point in both images is, by the Cartesian square exhibiting `W ⊓ W'` as the fibre product of
the two inclusions (`CategoryTheory.Subfunctor.isPullback_inf`), the image of a point of
`W ⊓ W'`; and the sheafification of the bottom subfunctor has no points at all, by
`AlgebraicGeometry.Space.range_pointsMap_ι_sheafify_bot`.

This is the disjointness clause that
`AlgebraicGeometry.Space.modulePushforwardBaseChangeBiprodIsoOfClopen` asks for, read off the
condition `W ⊓ W' = ⊥` in the sheafified sense that [Stacks, Tag 0ADU] delivers. -/
theorem disjoint_range_pointsMap_ι_of_inf_eq_sheafify_bot
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W W' : Subfunctor F)
    (hinf : W ⊓ W' = (⊥ : Subfunctor F).sheafify (BigFppfOver.topology B S hS)) :
    Disjoint (Set.range (pointsMap B S hS W.toFunctor W.ι))
      (Set.range (pointsMap B S hS W'.toFunctor W'.ι)) := by
  refine Set.disjoint_left.2 ?_
  rintro z ⟨p, rfl⟩ ⟨p', hp'⟩
  obtain ⟨w, -, -⟩ := exists_points_of_isPullback B S hS
    (Subfunctor.isPullback_inf W W') p' p hp'
  have hempty := range_pointsMap_ι_sheafify_bot B S hS F
  rw [← hinf] at hempty
  exact absurd (Set.mem_range_self
    (f := pointsMap B S hS (W ⊓ W').toFunctor (W ⊓ W').ι) w) (by rw [hempty]; exact id)

/-- **The restriction of a direct image to an étale neighbourhood splits along the clopen
decomposition of [Stacks, Tag 0ADU].**

Let `π : Y ⟶ X` be a morphism of algebraic spaces over `S` which is locally of finite type,
separated, and quasi-finite at a point `y` of `|Y|`, and let `𝒢` be an `𝒪_Y`-module.  Then there
are an étale `g : U ⟶ X` and a point of `|U|` over the image of `y`, together with a
decomposition of the base change `U ×_X Y` into two pieces `W` and `W'`, such that `W ⟶ U` is
finite, some point of `|W|` lies over `y` and over the chosen point of `|U|`, and

`(π_*𝒢)|_U ≅ (p_W)_*(𝒢|_W) ⊞ (p_{W'})_*(𝒢|_{W'})`.

The decomposition is [Stacks, Tag 0ADU],
`AlgebraicGeometry.Space.exists_etale_finite_clopen_part`; the isomorphism is
`AlgebraicGeometry.Space.modulePushforwardBaseChangeBiprodIsoOfClopen`, whose four hypotheses
on the pieces are supplied by `AlgebraicGeometry.Space.isEtale_of_isOpenImmersion`, the
closed-immersion clause of `AlgebraicGeometry.Space.IsClosedSubspace`,
`AlgebraicGeometry.Space.mem_range_pointsMap_ι_or_of_sheafify_sup_eq_top` and
`AlgebraicGeometry.Space.disjoint_range_pointsMap_ι_of_inf_eq_sheafify_bot`. -/
theorem exists_etale_neighbourhood_modulePushforward_biprod
    {X Y : AlgebraicSpaces B S hS} (π : Y ⟶ X) (y : points B S hS Y.1)
    (hft : IsLocallyOfFiniteType B S hS π.hom) (hsep : IsSeparated B S hS π.hom)
    (hqf : IsQuasiFiniteAt B S hS π.hom y) (G : Modules.{u, u} B S hS Y.1 Y.2) :
    ∃ (U : AlgebraicSpaces B S hS) (g : U ⟶ X) (pt : points B S hS U.1),
      IsEtale B S hS g.hom ∧
      pointsMap B S hS U.1 g.hom pt = pointsMap B S hS Y.1 π.hom y ∧
      ∃ (W W' : AlgebraicSpaces B S hS) (iW : W ⟶ Y) (pW : W ⟶ U)
        (iW' : W' ⟶ Y) (pW' : W' ⟶ U),
        IsFinite B S hS pW.hom ∧
        (∃ w : points B S hS W.1, pointsMap B S hS W.1 iW.hom w = y ∧
          pointsMap B S hS W.1 pW.hom w = pt) ∧
        Nonempty
          ((modulePullback B S hS g).obj ((modulePushforward B S hS π).obj G) ≅
            (modulePushforward B S hS pW).obj ((modulePullback B S hS iW).obj G) ⊞
              (modulePushforward B S hS pW').obj ((modulePullback B S hS iW').obj G)) := by
  obtain ⟨U, g, pt, W', W, hg, hgpt, hW'o, hW'c, hWo, hWc, hsup, hinf, hWfin, w, hwy, hwu⟩ :=
    exists_etale_finite_clopen_part B S hS π y hft hsep hqf
  -- the ambient algebraic space of the decomposition, and the Cartesian square
  set P : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS g π with hP
  set pP : P ⟶ U := ObjectProperty.homMk (pullback.fst g.hom π.hom) with hpP
  set iP : P ⟶ Y := ObjectProperty.homMk (pullback.snd g.hom π.hom) with hiP
  have sqP : IsPullback iP pP π g :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS g π).flip
  -- the two pieces, as algebraic spaces over the fibre product
  set Wsp : AlgebraicSpaces B S hS := ⟨W.toFunctor, hWo.1⟩ with hWsp
  set W'sp : AlgebraicSpaces B S hS := ⟨W'.toFunctor, hW'o.1⟩ with hW'sp
  set a : Wsp ⟶ P := ObjectProperty.homMk W.ι with ha
  set a' : W'sp ⟶ P := ObjectProperty.homMk W'.ι with ha'
  have hcov : Set.range (pointsMap B S hS Wsp.1 a.hom) ∪
      Set.range (pointsMap B S hS W'sp.1 a'.hom) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    rcases mem_range_pointsMap_ι_or_of_sheafify_sup_eq_top B S hS W' W hsup z with hz | hz
    · exact Or.inr hz
    · exact Or.inl hz
  have hdisj : Disjoint (Set.range (pointsMap B S hS Wsp.1 a.hom))
      (Set.range (pointsMap B S hS W'sp.1 a'.hom)) :=
    disjoint_range_pointsMap_ι_of_inf_eq_sheafify_bot B S hS W W'
      (by rw [inf_comm]; exact hinf)
  refine ⟨U, g, pt, hg, hgpt, Wsp, W'sp, a ≫ iP, a ≫ pP, a' ≫ iP, a' ≫ pP, hWfin,
    ⟨w, hwy, hwu⟩, ⟨modulePushforwardBaseChangeBiprodIsoOfClopen B S hS a a' π g hg iP pP sqP
      (isEtale_of_isOpenImmersion B S hS hWo.2) (isEtale_of_isOpenImmersion B S hS hW'o.2)
      hWc.2 hW'c.2 hcov hdisj G⟩⟩

end Clopen

/-! ### The internal Hom under étale restriction -/

variable {X Y : AlgebraicSpaces B S hS}

/-- **The internal Hom commutes with étale restriction**: for an étale morphism `f : X ⟶ Y` of
algebraic spaces and `𝒪_Y`-modules `ℳ`, `𝒩`,

`𝓗om_{𝒪_Y}(ℳ, 𝒩)|_X ≅ 𝓗om_{𝒪_X}(ℳ|_X, 𝒩|_X)`,

with no flatness and no finite presentation hypothesis.

Étale restriction of modules is restriction along small étale postcomposition, which is
continuous, cocontinuous (Stacks 03LP) and an equivalence on every slice (Stacks 04M0); for
such a functor of sites the internal Hom is preserved by
`Stacks.SheafOfModules.InternalHom.sliceEquivInternalHomSmallIso`.  See the module
documentation for why Stacks 0GN2, the comparison for a flat morphism, is not what is used. -/
@[sga "4 IV 12.3" "b)"]
def etaleModulePullbackInternalHomSmallIso (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (M N : Modules.{u, u} B S hS Y.1 Y.2) :
    (etaleModulePullback B S hS f hf).obj (smallEtaleInternalHomSmall B S hS Y.1 Y.2 M N) ≅
      smallEtaleInternalHomSmall B S hS X.1 X.2
        ((etaleModulePullback B S hS f hf).obj M)
        ((etaleModulePullback B S hS f hf).obj N) :=
  @Stacks.SheafOfModules.InternalHom.sliceEquivInternalHomSmallIso.{u + 1, u, u, u}
    (smallEtaleRingedSite B S hS Y.1 Y.2) (smallEtaleRingedSite B S hS X.1 X.2)
    (smallEtalePostcomp B S hS f hf)
    (smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS f hf)
    (smallEtalePostcomp_isCocontinuous B S hS f hf)
    (fun W => SmallEtale.isEquivalence_overPostcomp B S hS f hf W)
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
    (IsIso.id _) M N
    (instEssentiallySmallSmallEtaleRingedSite B S hS Y.1 Y.2)
    (instEssentiallySmallSmallEtaleRingedSite B S hS X.1 X.2)

section Monoidal

attribute [local instance] modulesMonoidalCategory modulesBraidedCategory modulesMonoidalClosed

/-- **The internal Hom transported along an isomorphism of its first argument.**

The internal Hom of `AlgebraicGeometry.Space.modulesMonoidalClosed` is
`AlgebraicGeometry.Space.smallEtaleInternalHomSmall` by `rfl`, so this is the contravariant
functoriality of `CategoryTheory.MonoidalClosed.internalHom` in its first variable. -/
def smallEtaleInternalHomSmallCongrLeft (Z : AlgebraicSpaces B S hS)
    {M M' : Modules.{u, u} B S hS Z.1 Z.2} (e : M ≅ M') (N : Modules.{u, u} B S hS Z.1 Z.2) :
    smallEtaleInternalHomSmall B S hS Z.1 Z.2 M N ≅
      smallEtaleInternalHomSmall B S hS Z.1 Z.2 M' N :=
  (MonoidalClosed.internalHom.mapIso e.symm.op).app N

end Monoidal

/-! ### Étale localization of the relative dualizing module -/

/-- **The dual `𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` commutes with étale restriction on the base.**  For a
Cartesian square

```
V --q--> Y
|p       |π
U --g--> X
```

with `g` étale, the restriction to `U` of `𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` is
`𝓗om_{𝒪_U}(p_*𝒪_V, 𝒪_U)`.

The internal Hom is restricted by
`AlgebraicGeometry.Space.etaleModulePullbackInternalHomSmallIso`; its first argument is then
moved by `AlgebraicGeometry.Space.pushforwardStructureModuleEtaleBaseChangeIso`, which is
Stacks 03LX at the structure sheaf, and its second argument is already the unit module of `U`,
étale restriction carrying the unit module to the unit module by `rfl`. -/
def etaleModulePullbackDualizingPushforwardIso {U V : AlgebraicSpaces B S hS}
    (π : Y ⟶ X) (g : U ⟶ X) (q : V ⟶ Y) (p : V ⟶ U)
    (sq : IsPullback q p π g) (hg : IsEtale B S hS g.hom) :
    (etaleModulePullback B S hS g hg).obj (dualizingPushforward B S hS π) ≅
      dualizingPushforward B S hS p :=
  etaleModulePullbackInternalHomSmallIso B S hS g hg (pushforwardStructureModule B S hS π)
      (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) ≪≫
    smallEtaleInternalHomSmallCongrLeft B S hS U
      (pushforwardStructureModuleEtaleBaseChangeIso B S hS q p π g sq hg)
      (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS U.1 U.2).O))

/-- **`π_*ω_{Y/X}` commutes with étale restriction on the base**, for an affine morphism
`π : Y ⟶ X` of algebraic spaces: for a Cartesian square

```
V --q--> Y
|p       |π
U --g--> X
```

with `g` étale,

`(π_*ω_{Y/X})|_U ≅ p_*ω_{V/U}`.

This is the compatibility of the relative dualizing module with étale localization on the base
that the proof of [Stacks, Tag 0GUZ] uses and states without proof.  The two sides are
identified with the duals of `π_*𝒪_Y` and of `p_*𝒪_V` by
`AlgebraicGeometry.Space.modulePushforward_relativeDualizingModuleIso`, and those duals are
matched by `AlgebraicGeometry.Space.etaleModulePullbackDualizingPushforwardIso`.  Affineness of
`p` is affineness of `π` base changed,
`AlgebraicGeometry.Space.isAffineHom_hom_of_isPullback`. -/
def etaleModulePullbackModulePushforwardRelativeDualizingModuleIso
    {U V : AlgebraicSpaces B S hS} (π : Y ⟶ X) (g : U ⟶ X) (q : V ⟶ Y) (p : V ⟶ U)
    (sq : IsPullback q p π g) (hg : IsEtale B S hS g.hom)
    (hπ : IsAffineHom B S hS π.hom)
    (hfp : (pushforwardStructureModule B S hS π).IsFinitePresentationOnSite)
    (hfp' : (pushforwardStructureModule B S hS p).IsFinitePresentationOnSite) :
    (etaleModulePullback B S hS g hg).obj
        ((modulePushforward B S hS π).obj (relativeDualizingModule B S hS π)) ≅
      (modulePushforward B S hS p).obj (relativeDualizingModule B S hS p) :=
  (etaleModulePullback B S hS g hg).mapIso
      (modulePushforward_relativeDualizingModuleIso B S hS π hπ hfp) ≪≫
    etaleModulePullbackDualizingPushforwardIso B S hS π g q p sq hg ≪≫
    (modulePushforward_relativeDualizingModuleIso B S hS p
      (isAffineHom_hom_of_isPullback sq hπ) hfp').symm

end AlgebraicGeometry.Space

end
