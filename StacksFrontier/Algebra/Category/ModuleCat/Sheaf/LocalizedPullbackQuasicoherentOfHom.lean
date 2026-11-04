module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiCoversTop
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.PullbackToposSquare

/-!
# Pullback preserves quasi-coherence on a site with no final object

`Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos` proves the quasi-coherent
clause of Stacks 03DO for a morphism of ringed sites `(f, f♯) : (C, O) ⟶ (D, O')` under
`[HasFiniteLimits Y.C]` and `[PreservesFiniteLimits f.u]`. Those hypotheses are used for exactly
two things:

* to produce a terminal object `⊤_ Y.C` and to know that `u` carries it to a terminal object of
  `C`, which is what `Stacks.Sheaves.LocalizedPullback.coversTop_map` consumes in order to carry
  a family covering the final object of `D` to one covering the final object of `C`; and
* to know that `u` is a morphism of sites, in the three places where Stacks 04J0's square needs
  it — an assertion a morphism of ringed sites already carries as the field
  `AlgebraicGeometry.RingedSite.Hom.isMorphismOfSites`.

The second is removed outright by
`AlgebraicGeometry.RingedSite.Hom.localizedPullbackToposSquare`. The first is replaced by
the hypothesis `∀ A : C, ∃ T : D, Nonempty (A ⟶ u(T))`, under which
`Stacks.CategoryTheory.coversTop_map_of_forall_exists_hom` carries a covering of the final object
along `u` with no terminal object anywhere. That hypothesis is what a site with no final object
can satisfy, and it is the form the implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ZariskiRingedTopos.lean` name as the missing input for
Stacks 07TI on the total Zariski site of a simplicial scheme: "a form of Stacks 04J0 that asks
for a covering of the final object as a hypothesis instead of deriving it from terminality".

## Main definitions

* `Stacks.Sheaves.LocalizedPullback.localizedPullbackMapData_ofHom`: the localized pullback datum
  of Section 03DG, with no finite-limit hypothesis and no terminal object.

## Main results

* `Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos_of_quasicoherentData_ofHom`
  and `.isQuasicoherentOnSite_pullbackTopos_ofHom`: **the pullback of a quasi-coherent sheaf of
  modules along a morphism of ringed sites is quasi-coherent**, with neither site asked to have
  finite limits and neither asked to have a final object.
* `Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos_ofHom_of_coversTop` and
  `.isQuasicoherentOnSite_pullbackTopos_of_quasicoherentData_ofHom_of_coversTop`: the same, with
  the hypothesis on `u` weakened to the family of images of `u` covering the final object of
  `C`, `X.J.CoversTop f.u.obj`; the datum is
  `Stacks.Sheaves.LocalizedPullback.localizedPullbackMapData_ofHom_of_coversTop`.

## Implementation notes

No attribute is placed here. The library statement
`Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos` carries the 03DO and 03DG
attributes, and the statements below have the extra hypothesis
`∀ A : C, ∃ T : D, Nonempty (A ⟶ u(T))`, which Stacks 03DO does not have; they are strictly more
general than that one in the finite-limit hypotheses and strictly less general in that
one, so neither supersedes the other and the attribute stays where it is.

The hypothesis is genuinely weaker than terminality rather than a repackaging of it: when `D` has
a terminal object `T` and `u(T)` is terminal in `C`, the unique arrow `A ⟶ u(T)` supplies it, so
the tagged statement is the case `T` constant.

The covering form `X.J.CoversTop f.u.obj` is weaker still, and it is the form the small étale
site of an algebraic space inside a category fibred in groupoids representable by it satisfies:
a scheme chart of the space admits no arrow to an étale chart in general, it is only covered by
schemes that do. `Stacks.CategoryTheory.coversTop_obj_of_forall_exists_hom` recovers it from the
arrow form, and `Stacks.CategoryTheory.coversTop_map_of_coversTop_obj` carries a covering of the
final object along `u` under it.

## References

* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.Sheaves.LocalizedPullback

universe u ww

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Y.C, HasWeakSheafify (Y.J.over W) AddCommGrpCat.{u}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}

/-- **The localized pullback datum of Section 03DG for the quasi-coherent property, under a
covering of the final object by the image of `u`.** This is
`Stacks.Sheaves.LocalizedPullback.localizedPullbackMapData_ofHom` with its hypothesis `hu`
weakened to `X.J.CoversTop f.u.obj`: the family `{u(W_i)}` covers the final object of `C` by
`Stacks.CategoryTheory.coversTop_map_of_coversTop_obj`. -/
def localizedPullbackMapData_ofHom_of_coversTop
    (hu : X.J.CoversTop f.u.obj) (q : M.QuasicoherentData.{ww}) :
    Stacks.SheafOfModules.QuasicoherentData.MapData
      f.toRingedToposSiteHom.pullbackTopos q where
  I := q.I
  X i := f.u.obj (q.X i)
  coversTop := Stacks.CategoryTheory.coversTop_map_of_coversTop_obj f.u hu q.coversTop
  index i := i
  functor i := (f.localized (q.X i)).toRingedToposSiteHom.pullbackTopos
  preservesColimits i :=
    ((f.localized (q.X i)).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
      ).leftAdjoint_preservesColimits
  unitIso i := pullbackToposUnitIso (f.localized (q.X i))
  overIso i := ((f.localizedPullbackToposSquare (q.X i)).app M).symm

/-- **The quasi-coherent clause of Stacks 03DO for a morphism of ringed sites whose image covers
the final object of the source site.** The pullback of a sheaf of `O'`-modules admitting
quasi-coherent data is quasi-coherent on the site, provided the family of images `u(T)` covers
the final object of the source site. -/
theorem isQuasicoherentOnSite_pullbackTopos_of_quasicoherentData_ofHom_of_coversTop
    (hu : X.J.CoversTop f.u.obj) (q : M.QuasicoherentData.{ww}) :
    (f.toRingedToposSiteHom.pullbackTopos.obj M).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_mapData
    (localizedPullbackMapData_ofHom_of_coversTop f hu q)

/-- **The quasi-coherent clause of Stacks 03DO for a morphism of ringed sites whose image covers
the final object of the source site**, with the hypothesis in the form the clause states it: if a
sheaf of `O'`-modules is quasi-coherent on the site, so is its pullback. This is
`Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos_ofHom` with its hypothesis
`hu` weakened to `X.J.CoversTop f.u.obj`. -/
theorem isQuasicoherentOnSite_pullbackTopos_ofHom_of_coversTop
    [∀ W : Y.C, EssentiallySmall.{u} (Over W)]
    (hu : X.J.CoversTop f.u.obj) (hM : M.IsQuasicoherentOnSite) :
    (f.toRingedToposSiteHom.pullbackTopos.obj M).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_pullbackTopos_of_quasicoherentData_ofHom_of_coversTop f hu
    (Stacks.SheafOfModules.nonempty_quasicoherentData_of_isQuasicoherentOnSite M hM).some

/-- **The localized pullback datum of Section 03DG for the quasi-coherent property, with no
finite-limit hypothesis and no terminal object.** Let `(f, f♯) : (C, O) ⟶ (D, O')` be a morphism
of ringed sites such that every object of `C` admits an arrow into the image of `u`, and let `q`
be quasi-coherent data for a sheaf of `O'`-modules `M`: a family `{W_i}` covering the final
object of `D` together with a global presentation of `M|_{W_i}` for each `i`. Then the family
`{u(W_i)}` covers the final object of `C`, and pullback along the localized morphism of ringed
topoi of Stacks 04J0 carries `M|_{W_i}` to `(f^*M)|_{u(W_i)}` and the structure sheaf to the
structure sheaf, and preserves colimits.

This is `Stacks.Sheaves.LocalizedPullback.localizedPullbackMapData` with its two finite-limit
hypotheses traded for `hu`. It is
`Stacks.Sheaves.LocalizedPullback.localizedPullbackMapData_ofHom_of_coversTop` at the covering of
the final object by the image of `u` that `hu` gives,
`Stacks.CategoryTheory.coversTop_obj_of_forall_exists_hom`. -/
def localizedPullbackMapData_ofHom
    (hu : ∀ A : X.C, ∃ T : Y.C, Nonempty (A ⟶ f.u.obj T)) (q : M.QuasicoherentData.{ww}) :
    Stacks.SheafOfModules.QuasicoherentData.MapData
      f.toRingedToposSiteHom.pullbackTopos q :=
  localizedPullbackMapData_ofHom_of_coversTop f
    (Stacks.CategoryTheory.coversTop_obj_of_forall_exists_hom f.u hu) q

/-- **The quasi-coherent clause of Stacks 03DO for a morphism of ringed sites, with no
finite-limit hypothesis and no terminal object.** The pullback of a sheaf of `O'`-modules
admitting quasi-coherent data is quasi-coherent on the site, provided every object of the source
site admits an arrow into the image of `u`.

The data is transported by
`Stacks.Sheaves.LocalizedPullback.localizedPullbackMapData_ofHom` and the transported
presentations assemble into quasi-coherence on the site by
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_mapData`. -/
theorem isQuasicoherentOnSite_pullbackTopos_of_quasicoherentData_ofHom
    (hu : ∀ A : X.C, ∃ T : Y.C, Nonempty (A ⟶ f.u.obj T)) (q : M.QuasicoherentData.{ww}) :
    (f.toRingedToposSiteHom.pullbackTopos.obj M).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_mapData
    (localizedPullbackMapData_ofHom f hu q)

/-- **The quasi-coherent clause of Stacks 03DO for a morphism of ringed sites, with the
hypothesis in the form the clause states it, with no finite-limit hypothesis and no terminal
object.** If a sheaf of `O'`-modules is quasi-coherent on the site, so is its pullback along a
morphism of ringed sites every object of whose source site admits an arrow into the image of `u`.

The slices of the target site are asked to be essentially small in the universe of the module
sections, which is what
`Stacks.SheafOfModules.nonempty_quasicoherentData_of_isQuasicoherentOnSite` needs in order to
recover a `SheafOfModules.Presentation` from the `SheafOfModules.HasGlobalPresentation` that
`SheafOfModules.IsQuasicoherentOnSite` records. -/
theorem isQuasicoherentOnSite_pullbackTopos_ofHom [∀ W : Y.C, EssentiallySmall.{u} (Over W)]
    (hu : ∀ A : X.C, ∃ T : Y.C, Nonempty (A ⟶ f.u.obj T)) (hM : M.IsQuasicoherentOnSite) :
    (f.toRingedToposSiteHom.pullbackTopos.obj M).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_pullbackTopos_ofHom_of_coversTop f
    (Stacks.CategoryTheory.coversTop_obj_of_forall_exists_hom f.u hu) hM

end Stacks.Sheaves.LocalizedPullback

end
