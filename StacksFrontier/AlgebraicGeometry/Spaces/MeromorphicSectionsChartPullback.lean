module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsChartPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullbackModule
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSections

/-!
# The chartwise pullback of meromorphic sections of a module

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` for which pullbacks of
meromorphic functions are defined (Stacks 0EN8) and let `M` be a sheaf of `𝒪_Y`-modules on the
small étale site.  Over a commuting square of étale charts `U` of `X` above `V` of `Y` this file
builds the rule

`m ⊗ a ↦ (f^*m) ⊗ (f^♯a)`

carrying `M(V) ⊗_{𝒪_Y(V)} 𝒦_Y(V)` into `(f^*M)(U) ⊗_{𝒪_X(U)} 𝒦_X(U)`, and shows that the
chartwise rules form an `f`-map of Stacks 03G3.

This is `AlgebraicGeometry.Space.chartPullbackMeromorphicSections` with the presheaf of
sectionwise localizations `𝒮⁻¹𝒪` replaced throughout by the *sheaf* `𝒦` of meromorphic
functions, which is the extension of scalars that
`AlgebraicGeometry.Space.meromorphicSectionPresheaf` — and hence Stacks 0EN5's sheaf
`𝒦(M)` of meromorphic sections and Stacks 0ENB's regularity — is taken over.  The coefficient
rule is `AlgebraicGeometry.Space.chartMeromorphicFunctionPullback` in place of
`AlgebraicGeometry.Space.chartPullbackMeromorphicFunctions`; the numerator rule is the same.

## Main definitions

* `AlgebraicGeometry.Space.meromorphicChartSheaf` is `𝒦_F` and
  `AlgebraicGeometry.Space.chartMeromorphicPullbackHom` the chartwise pullback of meromorphic
  functions, each at the spelling of its type in which the module instances are found.
* `AlgebraicGeometry.Space.chartMeromorphicAlgebra` is the `𝒪_F(U)`-algebra structure on
  `𝒦_F(U)` that the change-of-rings presheaf of meromorphic sections is taken over.
* `AlgebraicGeometry.Space.meromorphicSectionModule` is the presheaf `M ⊗_{𝒪_F} 𝒦_F` of
  meromorphic sections before the universe lift of
  `AlgebraicGeometry.Space.meromorphicSectionPresheaf`.
* `AlgebraicGeometry.Space.chartPullbackMeromorphicSectionsSheaf` is the chartwise rule, and
  `AlgebraicGeometry.Space.fmapMeromorphicSectionsSheaf` the `f`-map they form.

## Main results

* `AlgebraicGeometry.Space.chartMeromorphicFunctionPullback_algebraMap` is the square of
  coefficient rings that makes the rule well defined.
* `AlgebraicGeometry.Space.chartPullbackMeromorphicSectionsSheaf_tmul` is the rule in closed
  form and `AlgebraicGeometry.Space.chartPullbackMeromorphicSectionsSheaf_comp` its
  compatibility with simultaneous étale restriction of the two charts of a diagram.

## Implementation notes

The `Algebra` structure on `𝒦_F(U)` over `𝒪_F(U)` is `RingHom.toAlgebra` of the component of
`AlgebraicGeometry.Space.toMeromorphicFunctionSheaf`, which is the one the change-of-rings
presheaf carries; as in
`AlgebraicGeometry.Space.chartPullbackMeromorphicSections_comp` the restriction
compatibility is proved by induction on the section with the tensor product coming from the
goal, and the steps are assembled with `congrArg` and `Eq.trans` rather than with `rw`, so that
every instance stays the one the presheaf was built with.

Both `𝒦_F` and the chartwise pullback are restated here at a second spelling of their types,
`AlgebraicGeometry.Space.meromorphicChartSheaf` and
`AlgebraicGeometry.Space.chartMeromorphicPullbackHom`, and that is not cosmetic.  The
change-of-rings presheaf of Stacks 03CU tensors over `𝒪.obj U` as the *source presheaf of the
coefficient map spells it*, and the module structure on the sections of an `𝒪_F`-module over a
chart is registered at `AlgebraicGeometry.Space.chartRing`, which reaches the ring of sections
through the projections of the small étale ringed site.  So the coefficient map has to be
`AlgebraicGeometry.Space.toMeromorphicFunctionSheaf` read as
`AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.toLocalizationSheaf`, whose source *is*
spelled that way — with `AlgebraicGeometry.Space.structureSheaf` instead, the tensor product is
over a ring of sections at which `Module (chartRing …) …` is not found, and the statements do
not elaborate.  The two spellings agree definitionally, which is why each restatement is an
`abbrev` with no proof.

## References

* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0EN8](https://stacks.math.columbia.edu/tag/0EN8)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct
open Stacks.PresheafOfModules.ChangeOfRings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sheaf `𝒦_F` of meromorphic functions, at the spelling of the sheafified localization of
Stacks 0EMC through which `AlgebraicGeometry.Space.toMeromorphicFunctionSheaf` reaches it.  Only
the spelling of the type differs from `AlgebraicGeometry.Space.meromorphicFunctionSheaf`: the
site and its topology are reached through the projections of the small étale *ringed* site, and
that is the spelling in which the module instances on the sections of an `𝒪_F`-module are
found. -/
noncomputable abbrev meromorphicChartSheaf (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    Sheaf (smallEtaleRingedSite B S hS F hF).J CommRingCat.{u} :=
  (presheafToSheaf (smallEtaleRingedSite B S hS F hF).J CommRingCat.{u}).obj
    (regularSectionsSubpresheaf B S hS F hF).localizationPresheaf

/-- The `𝒪_F(U)`-algebra structure on the sections `𝒦_F(U)` of the sheaf of meromorphic
functions carried by the change-of-rings presheaf of
`AlgebraicGeometry.Space.meromorphicSectionPresheaf`: restriction of scalars along the component
of `𝒪_F ⟶ 𝒦_F`.  Not an instance: it is the one the tensor products of meromorphic sections are
taken over. -/
@[instance_reducible]
noncomputable def chartMeromorphicAlgebra (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (U : SmallEtale B S hS F) :
    Algebra (chartRing B S hS F hF U)
      ((meromorphicChartSheaf B S hS F hF).obj.obj (op U)) :=
  ((regularSectionsSubpresheaf B S hS F hF).toLocalizationSheaf.hom.app (op U)).hom.toAlgebra

attribute [local instance] chartMeromorphicAlgebra

/-- The presheaf `M ⊗_{𝒪_F} 𝒦_F` of meromorphic sections of a sheaf of `𝒪_F`-modules: the
extension of scalars of `M` along `𝒪_F ⟶ 𝒦_F`, before the universe lift that
`AlgebraicGeometry.Space.meromorphicSectionPresheaf` applies to it. -/
noncomputable def meromorphicSectionModule (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (M : Modules.{u, u} B S hS F hF) :
    PMod (meromorphicChartSheaf B S hS F hF).obj :=
  (changeOfRings (regularSectionsSubpresheaf B S hS F hF).toLocalizationSheaf.hom).obj M.val

section FractionRule

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)
  (hf : PullbacksMeromorphicSections B S hS f.hom)

/-- `AlgebraicGeometry.Space.chartMeromorphicFunctionPullback` at the spelling of the sections
of the sheaf of meromorphic functions that the change-of-rings presheaf of meromorphic sections
is built over.  Only the spelling of the type differs. -/
noncomputable abbrev chartMeromorphicPullbackHom (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (meromorphicChartSheaf B S hS Y.1 Y.2).obj.obj (op d.V) →+*
      (meromorphicChartSheaf B S hS X.1 X.2).obj.obj (op d.U) :=
  chartMeromorphicFunctionPullback B S hS f hf d

/-- **The square of coefficient rings over which the pullback of meromorphic sections is the
universal map out of a tensor product**: pulling a regular function back and then viewing it as
meromorphic is viewing it as meromorphic and then applying the chartwise pullback of meromorphic
functions. -/
theorem chartMeromorphicFunctionPullback_algebraMap
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (chartMeromorphicPullbackHom B S hS f hf d).comp
        (algebraMap (chartRing B S hS Y.1 Y.2 d.V)
          ((meromorphicChartSheaf B S hS Y.1 Y.2).obj.obj (op d.V))) =
      (algebraMap (chartRing B S hS X.1 X.2 d.U)
          ((meromorphicChartSheaf B S hS X.1 X.2).obj.obj (op d.U))).comp
        (chartDiagramRestrict B S hS f d) :=
  RingHom.ext fun r ↦
    chartMeromorphicFunctionPullback_toMeromorphicFunctionSheaf B S hS f hf d r

/-- **The chartwise pullback of meromorphic sections.**  When pullbacks of meromorphic functions
are defined for `f`, the pullback along a chart diagram carries the meromorphic sections
`M(V) ⊗_{𝒪_Y(V)} 𝒦_Y(V)` of a sheaf of `𝒪_Y`-modules `M` into
`(f^*M)(U) ⊗_{𝒪_X(U)} 𝒦_X(U)`: the module component is pulled back by the chart component of
the unit of the Stacks 03D7 adjunction and the coefficient by the chartwise pullback of
meromorphic functions. -/
noncomputable def chartPullbackMeromorphicSectionsSheaf
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (meromorphicSectionModule B S hS Y.1 Y.2 M).obj (op d.V) →+
      (meromorphicSectionModule B S hS X.1 X.2
        ((modulePullback B S hS f).obj M)).obj (op d.U) :=
  tmulMap (chartRing B S hS Y.1 Y.2 d.V)
    ((meromorphicChartSheaf B S hS Y.1 Y.2).obj.obj (op d.V))
    (chartRing B S hS X.1 X.2 d.U)
    ((meromorphicChartSheaf B S hS X.1 X.2).obj.obj (op d.U))
    (chartDiagramRestrict B S hS f d)
    (chartMeromorphicPullbackHom B S hS f hf d)
    (chartMeromorphicFunctionPullback_algebraMap B S hS f hf d)
    (M.val.obj (op d.V)) (((modulePullback B S hS f).obj M).val.obj (op d.U))
    (chartNumeratorPullback B S hS f M d) (chartNumeratorPullback_smul B S hS f M d)

/-- **The chartwise pullback of meromorphic sections in closed form.**  A meromorphic section
`a ⊗ m` over the chart `V` goes to `(f^♯a) ⊗ (f^*m)` over the chart `U`. -/
theorem chartPullbackMeromorphicSectionsSheaf_tmul
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (a : (meromorphicChartSheaf B S hS Y.1 Y.2).obj.obj (op d.V))
    (m : M.val.obj (op d.V)) :
    chartPullbackMeromorphicSectionsSheaf B S hS f M hf d
        (a ⊗ₜ[chartRing B S hS Y.1 Y.2 d.V] m) =
      (chartMeromorphicPullbackHom B S hS f hf d a) ⊗ₜ[
        chartRing B S hS X.1 X.2 d.U] ((modulePullbackChartFMap B S hS f M).app d m) :=
  tmulMap_tmul (chartRing B S hS Y.1 Y.2 d.V)
    ((meromorphicChartSheaf B S hS Y.1 Y.2).obj.obj (op d.V))
    (chartRing B S hS X.1 X.2 d.U)
    ((meromorphicChartSheaf B S hS X.1 X.2).obj.obj (op d.U))
    (chartDiagramRestrict B S hS f d)
    (chartMeromorphicPullbackHom B S hS f hf d)
    (chartMeromorphicFunctionPullback_algebraMap B S hS f hf d)
    (M.val.obj (op d.V)) (((modulePullback B S hS f).obj M).val.obj (op d.U))
    (chartNumeratorPullback B S hS f M d) (chartNumeratorPullback_smul B S hS f M d) a m

/-- **The chartwise pullback of meromorphic sections is compatible with simultaneous étale
restriction of the two charts of a diagram.**  This is what assembles the chartwise rules into
an `f`-map of Stacks 03G3, exactly as
`AlgebraicGeometry.Space.chartPullbackMeromorphicSections_comp` does over the presheaf of
sectionwise localizations.

Both sides are additive, so the identity is checked by induction on the section: on `a ⊗ m` the
two closed forms are `AlgebraicGeometry.Space.chartPullbackMeromorphicSectionsSheaf_tmul` for
the pullback and `Stacks.PresheafOfModules.ChangeOfRings.cofMap_tmul` for étale restriction, and
the identity reduces to its two components —
`AlgebraicGeometry.Space.chartMeromorphicFunctionPullback_comp` on coefficients and the
naturality field of `AlgebraicGeometry.Space.modulePullbackChartFMap` on module elements. -/
theorem chartPullbackMeromorphicSectionsSheaf_comp
    (d d' : ChartDiagram B S hS X.1 Y.1 f.hom) (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V)
    (h : (SmallEtale.toOver B S hS X.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS Y.1).map j)
    (t : (meromorphicSectionModule B S hS Y.1 Y.2 M).obj (op d.V)) :
    chartPullbackMeromorphicSectionsSheaf B S hS f M hf d'
        (((meromorphicSectionModule B S hS Y.1 Y.2 M).map j.op).hom t) =
      ((meromorphicSectionModule B S hS X.1 X.2
          ((modulePullback B S hS f).obj M)).map i.op).hom
        (chartPullbackMeromorphicSectionsSheaf B S hS f M hf d t) := by
  have hcoeff : ∀ a : (meromorphicChartSheaf B S hS Y.1 Y.2).obj.obj (op d.V),
      chartMeromorphicPullbackHom B S hS f hf d'
          (((meromorphicChartSheaf B S hS Y.1 Y.2).obj.map j.op).hom a) =
        ((meromorphicChartSheaf B S hS X.1 X.2).obj.map i.op).hom
          (chartMeromorphicPullbackHom B S hS f hf d a) := fun a ↦
    chartMeromorphicFunctionPullback_comp B S hS f hf d d' i j h a
  have hnum : ∀ x : M.val.obj (op d.V),
      (modulePullbackChartFMap B S hS f M).app d' ((M.val.map j.op).hom x) =
        (((modulePullback B S hS f).obj M).val.map i.op).hom
          ((modulePullbackChartFMap B S hS f M).app d x) := fun x ↦
    (modulePullbackChartFMap B S hS f M).naturality d d' i j h x
  induction t using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact ((congrArg (fun z ↦ chartPullbackMeromorphicSectionsSheaf B S hS f M hf d' z)
          (map_add ((meromorphicSectionModule B S hS Y.1 Y.2 M).map j.op).hom x y)).trans
        (map_add (chartPullbackMeromorphicSectionsSheaf B S hS f M hf d') _ _)).trans
      (((congrArg₂ (· + ·) hx hy).trans
          (map_add ((meromorphicSectionModule B S hS X.1 X.2
            ((modulePullback B S hS f).obj M)).map i.op).hom _ _).symm).trans
        (congrArg (fun z ↦ ((meromorphicSectionModule B S hS X.1 X.2
            ((modulePullback B S hS f).obj M)).map i.op).hom z)
          (map_add (chartPullbackMeromorphicSectionsSheaf B S hS f M hf d) x y).symm))
  | tmul a m =>
    refine Eq.trans (congrArg (chartPullbackMeromorphicSectionsSheaf B S hS f M hf d')
      (cofMap_tmul (toMeromorphicFunctionSheaf B S hS Y.1 Y.2).hom M.val j.op a m)) ?_
    refine Eq.trans (chartPullbackMeromorphicSectionsSheaf_tmul B S hS f M hf d' _ _) ?_
    refine Eq.trans ?_ (congrArg
      (fun z ↦ ((meromorphicSectionModule B S hS X.1 X.2
          ((modulePullback B S hS f).obj M)).map i.op).hom z)
      (chartPullbackMeromorphicSectionsSheaf_tmul B S hS f M hf d a m).symm)
    refine Eq.trans ?_ (cofMap_tmul
      (regularSectionsSubpresheaf B S hS X.1 X.2).toLocalizationSheaf.hom
      ((modulePullback B S hS f).obj M).val i.op
      (chartMeromorphicPullbackHom B S hS f hf d a)
      ((modulePullbackChartFMap B S hS f M).app d m)).symm
    exact congrArg₂
      (fun (x : (meromorphicChartSheaf B S hS X.1 X.2).obj.obj (op d'.U))
          (y : ((modulePullback B S hS f).obj M).val.obj (op d'.U)) ↦
        x ⊗ₜ[chartRing B S hS X.1 X.2 d'.U] y)
      (hcoeff a) (hnum m)

/-- **The chartwise pullbacks of meromorphic sections form an `f`-map of Stacks 03G3** from the
presheaf `M ⊗_{𝒪_Y} 𝒦_Y` of meromorphic sections of `M` to `(f^*M) ⊗_{𝒪_X} 𝒦_X`. -/
noncomputable def fmapMeromorphicSectionsSheaf :
    FMap B S hS X.1 Y.1 f.hom
      ((meromorphicSectionModule B S hS X.1 X.2
          ((modulePullback B S hS f).obj M)).presheaf ⋙
        CategoryTheory.forget AddCommGrpCat.{u})
      ((meromorphicSectionModule B S hS Y.1 Y.2 M).presheaf ⋙
        CategoryTheory.forget AddCommGrpCat.{u}) where
  app d := chartPullbackMeromorphicSectionsSheaf B S hS f M hf d
  naturality d d' i j h s :=
    chartPullbackMeromorphicSectionsSheaf_comp B S hS f M hf d d' i j h s

end FractionRule

end AlgebraicGeometry.Space

end
