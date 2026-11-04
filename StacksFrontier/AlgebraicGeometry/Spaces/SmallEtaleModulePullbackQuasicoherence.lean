module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackGlobalPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackPresentationAssembly
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpaceGlobalPresentation
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Pullback of modules along a morphism of algebraic spaces and quasi-coherence

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  Stacks 03GA asserts that the pullback functor
`f^* : Mod(𝒪_Y) ⟶ Mod(𝒪_X)` of Stacks 03LU carries quasi-coherent modules to quasi-coherent
modules, and so induces a functor `QCoh(𝒪_Y) ⥤ QCoh(𝒪_X)`.  Its proof is a single appeal to
the quasi-coherent clause of Stacks 03DO, the general statement for a morphism of ringed topoi.

Because `AlgebraicGeometry.Space.modulePullback` is *by definition* the pullback of modules of
Stacks 03D6 (2) attached to the morphism of small étale ringed topoi of Stacks 03G8, every
clause of Stacks 03DO applies to it on the nose, with no comparison isomorphism and with every
typeclass hypothesis already available on the small étale site of an algebraic space.  Four
cases of Stacks 03GA are proved here outright: `f` arbitrary and `F` globally presented, `f`
arbitrary and `F` of finite presentation, `f` étale with `F` merely quasi-coherent, and `f`
factoring through an étale chart of `Y` with affine underlying scheme, again with `F` merely
quasi-coherent.  For an arbitrary `f` and an arbitrary quasi-coherent `F` the statement is
reduced to the inverse-image factor of the quasi-coherent clause of Stacks 03DO, isolated as
`AlgebraicGeometry.Space.HasLocalInverseImagePresentations`.

## Main definitions

* `AlgebraicGeometry.Space.InverseImageLocallyPresented`: the inverse image `f⁻¹F` of
  Stacks 03D2 of a single `𝒪_Y`-module admits a `SheafOfModules.Presentation` over
  `f⁻¹𝒪_Y` on the members of some covering of each étale chart of `X`.
* `AlgebraicGeometry.Space.HasLocalInverseImagePresentations`: the inverse-image factor of the
  quasi-coherent clause of Stacks 03DO for `f`, namely that every quasi-coherent `𝒪_Y`-module
  has that property.
* `AlgebraicGeometry.Space.quasicoherentPullback`: the functor
  `QCoh(𝒪_Y) ⥤ QCoh(𝒪_X)` of Stacks 03GA, defined once the inverse-image factor is known.
* `AlgebraicGeometry.Space.quasicoherentPullbackOfIsEtale`: that functor along an étale
  morphism, where no further input is needed.
* `AlgebraicGeometry.Space.quasicoherentPullbackOfAffineChartFactorization`: that functor along
  a morphism factoring through an affine étale chart of the target.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_inverseImage_local` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback`: **Stacks 03GA, reduced to the
  inverse-image factor of Stacks 03DO.**  The pullback of a quasi-coherent `𝒪_Y`-module along a
  morphism of algebraic spaces is quasi-coherent.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_presentation`: **Stacks 03GA
  for a module with a global presentation**, along an arbitrary morphism of algebraic spaces.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isFinitePresentation`:
  **Stacks 03GA for a module of finite presentation**, along an arbitrary morphism of algebraic
  spaces.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isEtale`: **Stacks 03GA
  along an étale morphism**, for an arbitrary quasi-coherent module.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_affineChartFactorization`:
  **Stacks 03GA along a morphism factoring through an affine étale chart of the target**, for an
  arbitrary quasi-coherent module.
* `AlgebraicGeometry.Space.inverseImageLocallyPresented_of_presentation`: the inverse-image
  factor for a single globally presented module, on the trivial covering.

## Implementation notes

**What the four unconditional cases rest on.**  For a globally presented `F` the inverse image
`f⁻¹F` carries the same presentation, because `f⁻¹` is a left adjoint and takes `𝒪_Y` to
`f⁻¹𝒪_Y`; that is
`Stacks.Sheaves.Quasicoherence.isQuasicoherentOnSite_pullbackModules_of_presentation`.  For an
`F` of finite presentation a finite presentation over an object is a point of a sheaf of sets
indexed by `ℕ × ℕ`, which transports along `f⁻¹`, so the sibling clause 03DL (7) holds
outright; quasi-coherence then follows from
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_quasicoherentData`.  For an étale `f` the
pullback of Stacks 03LU is restriction of sections along postcomposition of étale charts
(Stacks' Equation 03LW), along which global presentations transfer chartwise.  For an `f`
factoring as `k ≫ φ` with `φ` the structure morphism of an étale chart `V` of `Y` whose
underlying scheme is affine, Stacks 03DX presents `F|_V`, the comparison of Stacks 04M0 turns
that into a *global* presentation of `φ^*F` on the chart space
(`AlgebraicGeometry.Space.nonempty_presentation_modulePullback_chartToSpace_of_isAffine`), and
the globally presented case applies to `k`; the two pullbacks are matched by
`AlgebraicGeometry.Space.modulePullbackCompIso`, the composition comparison of Stacks 03LU.

**The general case is proved elsewhere, and needs nothing from this file.**  The affine-chart
case is the general case localized at *one* chart of the target, and the geometric input that
completes it is that the étale charts of `X` whose composite with `f` factors through an affine
étale chart of `Y` cover `X`.  That input is available, proved directly as
`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram` of
`StacksFrontier/AlgebraicGeometry/Spaces/AffineChartDiagramCover.lean`, and the general case
follows from it with the affine-chart case,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_coversTop_etaleModulePullback` and
`AlgebraicGeometry.Space.modulePullbackCompIso`:
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackQuasicoherentFromChartDiagrams.lean` is
Stacks 03GA for an arbitrary morphism and an arbitrary quasi-coherent module, unconditionally.

The covering is obtained directly, without descending a covering of the spaces-étale site of
Stacks 03G0 through the comparison of Stacks 03G1.

**So `HasLocalInverseImagePresentations` is not what Stacks 03GA needs.**  It is the
inverse-image factor — a statement about `f⁻¹F` *before* extension of scalars — and the
chart-diagram route to 03GA bypasses `f⁻¹F` entirely.  It remains undischarged, and the
statements below that assume it are therefore weaker than
`isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`, not alternatives to it.  The
predicate is kept, isolated rather than left inline in the style of
`AlgebraicGeometry.Space.HasAffineChartPresentations`, because it is the hypothesis of the
reduction of Stacks 03DO to its inverse-image factor and a consumer may still wish to carry it;
but a caller wanting 03GA should use the unconditional statement instead.

The typeclass hypotheses of the general statement — sheafification of presheaves of abelian
groups on the small étale site and on each of its slices, and the agreement of local
equivalences with locally bijective morphisms there — are the instances
`AlgebraicGeometry.Space.SmallEtale.instHasSheafify`,
`AlgebraicGeometry.Space.SmallEtale.instHasSheafifyOver`,
`AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective` and
`AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijectiveOver` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleSite.lean`, all of which rest on
`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`.  They are found by instance search
with nothing to say here.

The module universe is the universe of the structure rings, as it is for
`AlgebraicGeometry.Space.modulePullback`; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullback.lean`.

## References

* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules (inverseImageModules)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The inverse image `f⁻¹F` of Stacks 03D2 of an `𝒪_Y`-module `F` along a morphism `f : X ⟶ Y`
of algebraic spaces is locally presented: over each étale chart `U` of `X` there is a covering
on each member `V` of which `(f⁻¹F)|_V` admits a presentation by free `f⁻¹𝒪_Y`-modules.

This is the hypothesis of
`Stacks.Sheaves.Quasicoherence.isQuasicoherentOnSite_pullbackModules_of_inverseImage_local`, the
quasi-coherent clause of Stacks 03DO reduced to its inverse-image factor, at the morphism of
small étale ringed topoi of Stacks 03G8. -/
def InverseImageLocallyPresented (f : X ⟶ Y) (F : Modules.{u, u} B S hS Y.1 Y.2) : Prop :=
  ∀ U : SmallEtale B S hS X.1, ∃ T : (SmallEtale.topology B S hS X.1).Cover U,
    ∀ (V : SmallEtale B S hS X.1) (g : V ⟶ U), T g →
      Nonempty ((((inverseImageModules
        (smallEtaleRingedToposModulesHom B S hS f).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)).obj F).over
          V).Presentation)

/-- **The inverse-image factor of the quasi-coherent clause of Stacks 03DO**, for a morphism
`f : X ⟶ Y` of algebraic spaces: the inverse image of every quasi-coherent `𝒪_Y`-module is
locally presented on the small étale site of `X`.

Granted it, pullback along `f` preserves quasi-coherence.  It is *not* an input Stacks 03GA
needs: 03GA holds unconditionally, by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`, whose
route bypasses `f⁻¹F`.  This predicate is the inverse-image factor of Stacks 03DO and remains
undischarged in its own right. -/
def HasLocalInverseImagePresentations (f : X ⟶ Y) : Prop :=
  ∀ F : Modules.{u, u} B S hS Y.1 Y.2, F.IsQuasicoherentOnSite →
    InverseImageLocallyPresented B S hS f F

/-- **Stacks 03GA for a single module, reduced to the inverse-image factor of Stacks 03DO.**  If
the inverse image of the `𝒪_Y`-module `F` is locally presented on the small étale site of `X`,
then the pullback `f^*F = 𝒪_X ⊗_{f⁻¹𝒪_Y} f⁻¹F` of Stacks 03LU is quasi-coherent.

Quasi-coherence of `F` itself is not used: it enters only through the hypothesis, which it is
the business of the inverse-image factor to deduce from it. -/
theorem isQuasicoherentOnSite_modulePullback_of_inverseImage_local (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : InverseImageLocallyPresented B S hS f F) :
    ((modulePullback B S hS f).obj F).IsQuasicoherentOnSite :=
  Stacks.Sheaves.Quasicoherence.isQuasicoherentOnSite_pullbackModules_of_inverseImage_local
    (smallEtaleRingedToposModulesHom B S hS f) F hF

/-- **Stacks 03GA, reduced to the inverse-image factor of Stacks 03DO.**  The pullback functor
`f^* : Mod(𝒪_Y) ⟶ Mod(𝒪_X)` of Stacks 03LU along a morphism of algebraic spaces preserves
quasi-coherence. -/
theorem isQuasicoherentOnSite_modulePullback (f : X ⟶ Y)
    (hf : HasLocalInverseImagePresentations B S hS f)
    (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsQuasicoherentOnSite) :
    ((modulePullback B S hS f).obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_inverseImage_local B S hS f F (hf F hF)

/-- **Stacks 03GA**, in the form the source states it, reduced to the inverse-image factor of
Stacks 03DO: the pullback of Stacks 03LU restricts to a functor
`QCoh(𝒪_Y) ⥤ QCoh(𝒪_X)` between the categories of quasi-coherent modules of Stacks 03G9. -/
noncomputable def quasicoherentPullback (f : X ⟶ Y)
    (hf : HasLocalInverseImagePresentations B S hS f) :
    QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2 ⥤
      QuasicoherentSheaves.{u, u} B S hS X.1 X.2 :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ modulePullback B S hS f)
    fun F => isQuasicoherentOnSite_modulePullback B S hS f hf F.obj F.property

/-! ### Cases of Stacks 03GA that need no further input -/

/-- **Stacks 03GA for a module with a global presentation.**  If an `𝒪_Y`-module `F` admits a
`SheafOfModules.Presentation` then its pullback `f^*F` of Stacks 03LU along an arbitrary
morphism `f : X ⟶ Y` of algebraic spaces is quasi-coherent.

The inverse image of Stacks 03D2 is a left adjoint carrying `𝒪_Y` to `f⁻¹𝒪_Y`, so it carries
the presentation along; extension of scalars to `𝒪_X` carries it further. -/
@[stacks 03GA "the pullback of a module with a global presentation is quasi-coherent"]
theorem isQuasicoherentOnSite_modulePullback_of_presentation (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS Y.1 Y.2) (P : F.Presentation) :
    ((modulePullback B S hS f).obj F).IsQuasicoherentOnSite :=
  Stacks.Sheaves.Quasicoherence.isQuasicoherentOnSite_pullbackModules_of_presentation
    (smallEtaleRingedToposModulesHom B S hS f) P

/-- **The inverse-image factor for a single globally presented module.**  If `F` admits a
`SheafOfModules.Presentation` then `f⁻¹F` admits one over every étale chart of `X`, so the
covering asked for by `AlgebraicGeometry.Space.InverseImageLocallyPresented` may be taken to be
the trivial one. -/
theorem inverseImageLocallyPresented_of_presentation (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS Y.1 Y.2) (P : F.Presentation) :
    InverseImageLocallyPresented B S hS f F := fun U =>
  Stacks.Sheaves.Quasicoherence.inverseImageLocallyPresented_of_presentation
    (smallEtaleRingedToposModulesHom B S hS f) F P U

/-- **Stacks 03GA for a module of finite presentation.**  The pullback `f^*F` of Stacks 03LU of
an `𝒪_Y`-module of finite presentation along an arbitrary morphism `f : X ⟶ Y` of algebraic
spaces is quasi-coherent.

Unlike the globally presented case this assumes only *local* presentations, which transport
along `f⁻¹` because a finite presentation over an object is a point of a sheaf of sets indexed
by `ℕ × ℕ`.  The clause 03DL (7) of Stacks 03DO therefore holds outright, and a module of
finite presentation is quasi-coherent. -/
@[stacks 03GA "the pullback of a module of finite presentation is quasi-coherent"]
theorem isQuasicoherentOnSite_modulePullback_of_isFinitePresentation (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsFinitePresentation) :
    ((modulePullback B S hS f).obj F).IsQuasicoherentOnSite := by
  let F' : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O) := F
  have hF' : F'.IsFinitePresentation := hF
  have hfp : ((modulePullback B S hS f).obj F).IsFinitePresentation :=
    Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules
      (smallEtaleRingedToposModulesHom B S hS f) F'
  exact Stacks.SheafOfModules.isQuasicoherentOnSite_of_quasicoherentData
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((modulePullback B S hS f).obj F)).choose

/-- **Stacks 03GA along an étale morphism.**  The pullback functor
`f^* : Mod(𝒪_Y) ⟶ Mod(𝒪_X)` of Stacks 03LU along an étale morphism `f : X ⟶ Y` of algebraic
spaces preserves quasi-coherence, with no hypothesis on the module beyond quasi-coherence.

Along an étale morphism the pullback of Stacks 03LU is restriction of sections along
postcomposition of étale charts, by Stacks' Equation 03LW, and quasi-coherence is inherited by
that restriction. -/
@[stacks 03GA "the pullback functor preserves quasi-coherence along an étale morphism"]
theorem isQuasicoherentOnSite_modulePullback_of_isEtale (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (F : Modules.{u, u} B S hS Y.1 Y.2)
    (hF : F.IsQuasicoherentOnSite) :
    ((modulePullback B S hS f).obj F).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((modulePullbackIsoEtaleModulePullback B S hS f hf).app F).symm
    (isQuasicoherentOnSite_etaleModulePullback B S hS f hf F hF)

/-- **Stacks 03GA along an étale morphism, in the form the source states it**: the pullback of
Stacks 03LU along an étale morphism of algebraic spaces restricts to a functor
`QCoh(𝒪_Y) ⥤ QCoh(𝒪_X)` between the categories of quasi-coherent modules of Stacks 03G9. -/
@[stacks 03GA "the induced functor on quasi-coherent modules, along an étale morphism"]
noncomputable def quasicoherentPullbackOfIsEtale (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2 ⥤
      QuasicoherentSheaves.{u, u} B S hS X.1 X.2 :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ modulePullback B S hS f)
    fun F => isQuasicoherentOnSite_modulePullback_of_isEtale B S hS f hf F.obj F.property

/-! ### The case of a morphism factoring through an affine étale chart of the target -/

/-- **Stacks 03GA for a morphism factoring through an affine étale chart of the target.**  The
pullback of Stacks 03LU of a quasi-coherent `𝒪_Y`-module along a composite
`k ≫ φ : X ⟶ Y`, where `φ` is the structure morphism of an étale chart `V` of `Y` whose
underlying scheme is affine and `k` is arbitrary, is quasi-coherent.

By Stacks 03DX the restriction `F|_V` has a global presentation, which the comparison of
Stacks 04M0 turns into a global presentation of `φ^*F` on the small étale site of the chart
space; the globally presented case of Stacks 03GA then applies to `k`, and the two pullbacks are
matched by the composition comparison of Stacks 03LU. -/
theorem isQuasicoherentOnSite_modulePullback_comp_chartToSpace_of_isAffine
    (V : SmallEtale B S hS Y.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)))
    (k : X ⟶ chartSpace B S hS Y V) (F : Modules.{u, u} B S hS Y.1 Y.2)
    (hF : F.IsQuasicoherentOnSite) :
    ((modulePullback B S hS (k ≫ chartToSpace B S hS Y V)).obj F).IsQuasicoherentOnSite := by
  obtain ⟨P⟩ :=
    nonempty_presentation_modulePullback_chartToSpace_of_isAffine B S hS Y F hF V hV
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((modulePullbackCompIso B S hS k (chartToSpace B S hS Y V)).app F)
    (isQuasicoherentOnSite_modulePullback_of_presentation B S hS k _ P)

/-- **Stacks 03GA along a morphism factoring through an affine étale chart of the target.**  If
`f : X ⟶ Y` factors as `k ≫ φ` with `φ` the structure morphism of an étale chart of `Y` whose
underlying scheme is affine, then `f^*` carries quasi-coherent `𝒪_Y`-modules to quasi-coherent
`𝒪_X`-modules, with no hypothesis on `k` and none on the module beyond quasi-coherence.

This is the general case of Stacks 03GA localized at one chart of the target; see the
implementation notes for what the general case still needs. -/
@[stacks 03GA "the pullback along a morphism factoring through an affine chart of the target"]
theorem isQuasicoherentOnSite_modulePullback_of_affineChartFactorization (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)))
    (k : X ⟶ chartSpace B S hS Y V) (hk : f = k ≫ chartToSpace B S hS Y V)
    (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsQuasicoherentOnSite) :
    ((modulePullback B S hS f).obj F).IsQuasicoherentOnSite := by
  subst hk
  exact isQuasicoherentOnSite_modulePullback_comp_chartToSpace_of_isAffine B S hS V hV k F hF

/-- **Stacks 03GA along a morphism factoring through an affine étale chart of the target, in the
form the source states it**: the pullback of Stacks 03LU along `k ≫ φ`, with `φ` the structure
morphism of an affine étale chart of `Y`, restricts to a functor `QCoh(𝒪_Y) ⥤ QCoh(𝒪_X)`
between the categories of quasi-coherent modules of Stacks 03G9. -/
@[stacks 03GA "the induced functor on quasi-coherent modules, through an affine chart"]
noncomputable def quasicoherentPullbackOfAffineChartFactorization (V : SmallEtale B S hS Y.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)))
    (k : X ⟶ chartSpace B S hS Y V) :
    QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2 ⥤
      QuasicoherentSheaves.{u, u} B S hS X.1 X.2 :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ modulePullback B S hS (k ≫ chartToSpace B S hS Y V))
    fun F => isQuasicoherentOnSite_modulePullback_comp_chartToSpace_of_isAffine B S hS V hV k
      F.obj F.property

end AlgebraicGeometry.Space

end
