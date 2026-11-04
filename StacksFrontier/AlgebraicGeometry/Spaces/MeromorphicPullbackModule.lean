module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullback

/-!
# The chartwise pullback of meromorphic sections of a module

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` for which pullbacks of
meromorphic functions are defined (Stacks 0EN8) and let `M` be a sheaf of `𝒪_Y`-modules on the
small étale site.  This file carries the fraction rule of
`AlgebraicGeometry.Space.chartPullbackMeromorphicFunctions` over from the structure sheaf to
`M`: over a commuting square of étale charts `U` of `X` above `V` of `Y` the rule

`m/b ↦ (f^*m)/(f^♯b)`

carries the sectionwise localization `𝒮_Y(V)⁻¹M(V)` into `𝒮_X(U)⁻¹(f^*M)(U)`.

The numerator is pulled back by the chart component
`AlgebraicGeometry.Space.modulePullbackChartFMap` of the unit of the Stacks 03D7 adjunction,
which is additive and semilinear over `f^♯`; the denominator by the fraction rule on the
structure sheaf, which inverts it because `f^♯b` is again regular.  So the two assemble by the
universal property of a tensor product over a square of coefficient rings,
`Stacks.PresheafOfModules.ChangeOfRings.tmulMap`.

## Main definitions

* `AlgebraicGeometry.Space.regularSectionsLocalizationModule` is the presheaf `𝒮_F⁻¹M` of
  sectionwise localizations of a module, the extension of scalars of `M` along
  `𝒪_F ⟶ 𝒮_F⁻¹𝒪_F`.
* `AlgebraicGeometry.Space.chartPullbackMeromorphicSections` is the fraction rule
  `m/b ↦ (f^*m)/(f^♯b)` over a chart diagram.

## Main results

* `AlgebraicGeometry.Space.chartPullbackMeromorphicSections_tmul` computes the rule on a
  fraction with its numerator; read with
  `AlgebraicGeometry.Space.chartPullbackMeromorphicFunctions_mk'`, which computes the
  structure-sheaf rule as `a/b ↦ f^♯a/f^♯b`, it is the closed form `m/b ↦ (f^*m)/(f^♯b)`.
* `AlgebraicGeometry.Space.chartNumeratorPullback_smul` is the semilinearity of the numerator
  pullback and `AlgebraicGeometry.Space.chartPullbackMeromorphicFunctions_algebraMap` the
  compatibility of the denominator rule with the coefficient rings; together they are what
  makes the fraction rule well defined.
* `AlgebraicGeometry.Space.chartPullbackMeromorphicSections_comp` is the compatibility of the
  fraction rule with simultaneous étale restriction of the two charts of a diagram, the
  analogue for `M` of `AlgebraicGeometry.Space.chartPullbackMeromorphicFunctions_comp`.

## Implementation notes

The presheaf of sectionwise localizations of `M` is built with the change-of-rings functor of
Stacks 03CU along `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.toLocalizationPresheaf`
rather than by localizing each `M(U)` by hand, so that its restriction maps are already the
`Stacks.PresheafOfModules.ChangeOfRings.cofMap` whose value on a tensor is
`Stacks.PresheafOfModules.ChangeOfRings.cofMap_tmul`.

The restriction-compatibility of the fraction rule is an identity between two composites of
`Stacks.PresheafOfModules.ChangeOfRings.tmulMap`s, through the two different intermediate
charts, whose components are
`AlgebraicGeometry.Space.chartPullbackMeromorphicFunctions_comp` on denominators and the
naturality field of `AlgebraicGeometry.Space.modulePullbackChartFMap` on numerators.  It is
proved by induction on a section of the tensor product, and that induction has to be performed
on the sections of the change-of-rings presheaf *as the presheaf spells them*: the sectionwise
localization carries two equal but not interchangeable algebra structures over the ring of
sections — the `Localization` one of
`AlgebraicGeometry.Space.regularSectionsLocalizationAlgebra` and the
`RingHom.toAlgebra` one of `AlgebraicGeometry.Space.chartLocalizationAlgebra` — and the
localization's additive structure is `OreLocalization`'s, whose definition this module does not
have exposed, so the two cannot be reconciled by unfolding.  Writing the induction so that the
tensor product comes from the goal keeps every instance the one the presheaf was built with;
for the same reason the steps are assembled with `congrArg` and `Eq.trans`, which decide
definitional equality, rather than with `rw`, whose keyed matching does not see through the two
spellings of the ring of sections.

Likewise the `Algebra` instance on the sectionwise localization used throughout is
`RingHom.toAlgebra` of the component of `toLocalizationPresheaf`, which is the one the
change-of-rings presheaf carries, and not the `Localization` instance of
`AlgebraicGeometry.Space.regularSectionsLocalizationAlgebra`; the two agree, the component
*being* the algebra map, but only the first is the one instance search finds inside the
presheaf.

The module universe is the universe `u` of the structure rings: that is where the inverse image
of modules of Stacks 03LU, `AlgebraicGeometry.Space.modulePullback`, lives, and the fraction
rule needs the pullback `f^*M` to form its numerators.

The sheafifications are treated elsewhere.  The global map
`Γ(Y, 𝒦_Y(F)) ⟶ Γ(X, 𝒦_X(f^*F))` of Stacks 0ENC, part (1) that the `f`-map here descends to is
`AlgebraicGeometry.Space.pullbackSheafifiedRegularSections`, for `𝒦(F)` read as the *first* of
the two descriptions in Stacks 0EN5 — the sheafification of the presheaf of sectionwise
localizations built here.  For `AlgebraicGeometry.Space.MeromorphicSection`, which realizes
Stacks 0EN5 through the other description there, the sheafification of `F ⊗_{𝒪} 𝒦`, it is
`AlgebraicGeometry.Space.pullbackMeromorphicSection`, built over the chartwise rule
`AlgebraicGeometry.Space.chartPullbackMeromorphicSectionsSheaf`.  Neither map uses Stacks 0EMD,
which identifies the two descriptions.  Part (2), stated through
`AlgebraicGeometry.Space.IsRegularMeromorphicSection`, is
`AlgebraicGeometry.Space.isRegularMeromorphicSection_pullbackMeromorphicSection` for an
invertible module.

## References

* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EN8](https://stacks.math.columbia.edu/tag/0EN8)
* [Stacks Project, Tag 0EMC](https://stacks.math.columbia.edu/tag/0EMC)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct
open Stacks.PresheafOfModules.ChangeOfRings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The presheaf `𝒮_F⁻¹M` of sectionwise localizations of a sheaf of `𝒪_F`-modules: the
extension of scalars of `M` along the canonical map `𝒪_F ⟶ 𝒮_F⁻¹𝒪_F` into the presheaf of
sectionwise localizations of Stacks 0EMC. -/
noncomputable def regularSectionsLocalizationModule (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (M : Modules.{u, u} B S hS F hF) :
    PMod (regularSectionsSubpresheaf B S hS F hF).localizationPresheaf :=
  (changeOfRings (regularSectionsSubpresheaf B S hS F hF).toLocalizationPresheaf).obj M.val

/-! ### The local fraction rule for pullback of meromorphic sections -/

section FractionRule

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)

/-- The `𝒪_Y(V)`-algebra structure on the sectionwise localization `𝒮_Y(V)⁻¹𝒪_Y(V)` carried by
the change-of-rings presheaf: restriction of scalars along the component of
`toLocalizationPresheaf`.  Not an instance: it is one of two agreeing algebra structures on the
same ring, and this is the one the tensor products below are taken over. -/
@[instance_reducible]
noncomputable def chartLocalizationAlgebra (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (U : SmallEtale B S hS F) :
    Algebra (chartRing B S hS F hF U)
      ((regularSectionsSubpresheaf B S hS F hF).localizationPresheaf.obj (op U)) :=
  ((regularSectionsSubpresheaf B S hS F hF).toLocalizationPresheaf.app (op U)).hom.toAlgebra

attribute [local instance] chartLocalizationAlgebra

/-- Pullback of the numerator: the chart component of the unit of the Stacks 03D7 adjunction
over a chart diagram, as an additive map of sections. -/
noncomputable def chartNumeratorPullback (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    M.val.obj (op d.V) →+ ((modulePullback B S hS f).obj M).val.obj (op d.U) :=
  AddMonoidHom.mk' ((modulePullbackChartFMap B S hS f M).app d)
    ((modulePullbackChartFMap B S hS f M).map_add d)

/-- The numerator pullback is the chart component of the unit of the Stacks 03D7 adjunction. -/
@[simp] theorem chartNumeratorPullback_apply (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (m : M.val.obj (op d.V)) :
    chartNumeratorPullback B S hS f M d m =
      (modulePullbackChartFMap B S hS f M).app d m :=
  rfl

/-- The numerator pullback is semilinear over the pullback of regular functions along the
vertical scheme morphism of the diagram. -/
theorem chartNumeratorPullback_smul (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (r : chartRing B S hS Y.1 Y.2 d.V) (m : M.val.obj (op d.V)) :
    chartNumeratorPullback B S hS f M d (r • m) =
      chartDiagramRestrict B S hS f d r • chartNumeratorPullback B S hS f M d m :=
  (modulePullbackChartFMap B S hS f M).map_smul d r m

/-- The square of coefficient rings over which the fraction rule is the universal map out of a
tensor product: pulling a regular function back and then viewing it as a fraction is viewing it
as a fraction and then applying the fraction rule. -/
theorem chartPullbackMeromorphicFunctions_algebraMap
    (hf : PullbacksMeromorphicSections B S hS f.hom)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (chartPullbackMeromorphicFunctions B S hS X.2 Y.2 hf d).comp
        (algebraMap (chartRing B S hS Y.1 Y.2 d.V)
          ((regularSectionsSubpresheaf B S hS Y.1 Y.2).localizationPresheaf.obj (op d.V))) =
      (algebraMap (chartRing B S hS X.1 X.2 d.U)
          ((regularSectionsSubpresheaf B S hS X.1 X.2).localizationPresheaf.obj
            (op d.U))).comp (chartDiagramRestrict B S hS f d) :=
  RingHom.ext fun r ↦
    chartPullbackMeromorphicFunctions_toLocalizationPresheaf B S hS X.2 Y.2 hf d r

/-- **The local fraction rule `m/b ↦ (f^*m)/(f^♯b)`.**  When pullbacks of meromorphic functions
are defined for `f`, the pullback along a chart diagram carries the sectionwise localization
`𝒮_Y(V)⁻¹M(V)` of a sheaf of `𝒪_Y`-modules `M` into `𝒮_X(U)⁻¹(f^*M)(U)`: the numerator is
pulled back by the chart component of the unit of the Stacks 03D7 adjunction and the
denominator by the fraction rule on the structure sheaf, which inverts it. -/
@[stacks 0ENC "part (1), chartwise for an arbitrary sheaf of 𝒪_Y-modules F: the local \
fraction rule m/b ↦ (f^*m)/(f♯b) on the sectionwise localizations over an étale chart \
diagram. This generalizes the structure-sheaf case \
AlgebraicGeometry.Space.chartPullbackMeromorphicFunctions from F = 𝒪_Y to an arbitrary F. \
The global map Γ(Y, 𝒦_Y(F)) ⟶ Γ(X, 𝒦_X(f^*F)) of part (1) is asserted for ONE of the two \
spellings of 𝒦(F): AlgebraicGeometry.Space.pullbackSheafifiedRegularSections gives it with \
𝒦(F) read as the first description in Stacks 0EN5, the sheafification of this presheaf of \
sectionwise localizations, and AlgebraicGeometry.Space.pullbackMeromorphicSection gives it for \
the other description there, the sheafification of F ⊗_𝒪 𝒦, which is the one \
AlgebraicGeometry.Space.MeromorphicSection uses. Stacks 0EMD, which identifies the two \
descriptions, is not proved and neither map uses it. Part (2), stated through \
AlgebraicGeometry.Space.IsRegularMeromorphicSection, is not asserted here; it is proved for an \
invertible module by \
AlgebraicGeometry.Space.isRegularMeromorphicSection_pullbackMeromorphicSection"]
noncomputable def chartPullbackMeromorphicSections
    (hf : PullbacksMeromorphicSections B S hS f.hom)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (regularSectionsLocalizationModule B S hS Y.1 Y.2 M).obj (op d.V) →+
      (regularSectionsLocalizationModule B S hS X.1 X.2
        ((modulePullback B S hS f).obj M)).obj (op d.U) :=
  tmulMap (chartRing B S hS Y.1 Y.2 d.V)
    ((regularSectionsSubpresheaf B S hS Y.1 Y.2).localizationPresheaf.obj (op d.V))
    (chartRing B S hS X.1 X.2 d.U)
    ((regularSectionsSubpresheaf B S hS X.1 X.2).localizationPresheaf.obj (op d.U))
    (chartDiagramRestrict B S hS f d)
    (chartPullbackMeromorphicFunctions B S hS X.2 Y.2 hf d)
    (chartPullbackMeromorphicFunctions_algebraMap B S hS f hf d)
    (M.val.obj (op d.V)) (((modulePullback B S hS f).obj M).val.obj (op d.U))
    (chartNumeratorPullback B S hS f M d) (chartNumeratorPullback_smul B S hS f M d)

/-- **The fraction rule in closed form.**  A fraction `a` over the chart `V` with numerator `m`
goes to the fraction `f^♯a` over the chart `U` with numerator `f^*m`.  Read together with
`AlgebraicGeometry.Space.chartPullbackMeromorphicFunctions_mk'`, which computes the fraction
rule on the structure sheaf as `a/b ↦ f^♯a/f^♯b`, this is the rule
`m/b ↦ (f^*m)/(f^♯b)`. -/
theorem chartPullbackMeromorphicSections_tmul
    (hf : PullbacksMeromorphicSections B S hS f.hom)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (a : (regularSectionsSubpresheaf B S hS Y.1 Y.2).localizationPresheaf.obj (op d.V))
    (m : M.val.obj (op d.V)) :
    chartPullbackMeromorphicSections B S hS f M hf d
        (a ⊗ₜ[chartRing B S hS Y.1 Y.2 d.V] m) =
      (chartPullbackMeromorphicFunctions B S hS X.2 Y.2 hf d a) ⊗ₜ[
        chartRing B S hS X.1 X.2 d.U] ((modulePullbackChartFMap B S hS f M).app d m) :=
  tmulMap_tmul _ _ _ _ _ _ _ _ _ _ _ a m

/-- **The fraction rule is compatible with simultaneous étale restriction of the two charts of a
diagram**: restricting a fraction from the charts of `d` to the charts of `d'` and then pulling
it back is pulling it back and then restricting.  This is what assembles the chartwise rules
into an `f`-map of Stacks 03G3, exactly as
`AlgebraicGeometry.Space.chartPullbackMeromorphicFunctions_comp` does for the structure sheaf.

Both sides are additive, so the identity is checked by induction on the section: on a fraction
`a ⊗ₜ m` the two closed forms are
`AlgebraicGeometry.Space.chartPullbackMeromorphicSections_tmul` for the fraction rule and
`Stacks.PresheafOfModules.ChangeOfRings.cofMap_tmul` for étale restriction, and the identity
reduces to its two components — the structure-sheaf fraction rule on denominators and the
naturality of the chart component of the unit on numerators.

The induction is taken on the sections of the change-of-rings presheaf as the presheaf spells
them, and the steps are assembled with `congrArg` and `Eq.trans`; see the implementation notes
of this file for why neither can be replaced by a tensor product written over the other algebra
structure, nor by `rw`. -/
theorem chartPullbackMeromorphicSections_comp
    (hf : PullbacksMeromorphicSections B S hS f.hom)
    (d d' : ChartDiagram B S hS X.1 Y.1 f.hom) (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V)
    (h : (SmallEtale.toOver B S hS X.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS Y.1).map j)
    (t : (regularSectionsLocalizationModule B S hS Y.1 Y.2 M).obj (op d.V)) :
    chartPullbackMeromorphicSections B S hS f M hf d'
        (((regularSectionsLocalizationModule B S hS Y.1 Y.2 M).map j.op).hom t) =
      (((regularSectionsLocalizationModule B S hS X.1 X.2
          ((modulePullback B S hS f).obj M)).map i.op)).hom
        (chartPullbackMeromorphicSections B S hS f M hf d t) := by
  have hcoeff : ∀ a : (regularSectionsSubpresheaf B S hS Y.1 Y.2).localizationPresheaf.obj
        (op d.V),
      chartPullbackMeromorphicFunctions B S hS X.2 Y.2 hf d'
          (((regularSectionsSubpresheaf B S hS Y.1 Y.2).localizationPresheaf.map j.op).hom a) =
        ((regularSectionsSubpresheaf B S hS X.1 X.2).localizationPresheaf.map i.op).hom
          (chartPullbackMeromorphicFunctions B S hS X.2 Y.2 hf d a) := fun a ↦
    RingHom.congr_fun
      (chartPullbackMeromorphicFunctions_comp B S hS X.2 Y.2 hf d d' i j h) a
  have hnum : ∀ x : M.val.obj (op d.V),
      (modulePullbackChartFMap B S hS f M).app d' ((M.val.map j.op).hom x) =
        (((modulePullback B S hS f).obj M).val.map i.op).hom
          ((modulePullbackChartFMap B S hS f M).app d x) := fun x ↦
    (modulePullbackChartFMap B S hS f M).naturality d d' i j h x
  induction t using TensorProduct.induction_on with
  | zero =>
    exact (congrArg (fun z ↦ chartPullbackMeromorphicSections B S hS f M hf d' z)
        (map_zero ((regularSectionsLocalizationModule B S hS Y.1 Y.2 M).map j.op).hom)).trans
      ((map_zero (chartPullbackMeromorphicSections B S hS f M hf d')).trans
        (((congrArg (fun z ↦ ((regularSectionsLocalizationModule B S hS X.1 X.2
                ((modulePullback B S hS f).obj M)).map i.op).hom z)
              (map_zero (chartPullbackMeromorphicSections B S hS f M hf d))).trans
            (map_zero ((regularSectionsLocalizationModule B S hS X.1 X.2
              ((modulePullback B S hS f).obj M)).map i.op).hom)).symm))
  | add x y hx hy =>
    exact ((congrArg (fun z ↦ chartPullbackMeromorphicSections B S hS f M hf d' z)
          (map_add ((regularSectionsLocalizationModule B S hS Y.1 Y.2 M).map j.op).hom
            x y)).trans
        (map_add (chartPullbackMeromorphicSections B S hS f M hf d') _ _)).trans
      (((congrArg₂ (· + ·) hx hy).trans
          (map_add ((regularSectionsLocalizationModule B S hS X.1 X.2
            ((modulePullback B S hS f).obj M)).map i.op).hom _ _).symm).trans
        (congrArg (fun z ↦ ((regularSectionsLocalizationModule B S hS X.1 X.2
            ((modulePullback B S hS f).obj M)).map i.op).hom z)
          (map_add (chartPullbackMeromorphicSections B S hS f M hf d) x y).symm))
  | tmul a m =>
    refine Eq.trans (congrArg (chartPullbackMeromorphicSections B S hS f M hf d')
        (cofMap_tmul (regularSectionsSubpresheaf B S hS Y.1 Y.2).toLocalizationPresheaf M.val
          j.op a m))
      (Eq.trans (chartPullbackMeromorphicSections_tmul B S hS f M hf d' _ _)
        (Eq.trans ?_
          (Eq.trans (Eq.symm (cofMap_tmul
              (regularSectionsSubpresheaf B S hS X.1 X.2).toLocalizationPresheaf
              ((modulePullback B S hS f).obj M).val i.op _ _))
            (Eq.symm (congrArg
              (fun z ↦ ((regularSectionsLocalizationModule B S hS X.1 X.2
                  ((modulePullback B S hS f).obj M)).map i.op).hom z)
              (chartPullbackMeromorphicSections_tmul B S hS f M hf d a m))))))
    rw [hcoeff]
    exact congrArg _ (hnum m)

/-- The chartwise fraction rules for a sheaf of `𝒪_Y`-modules `M` assemble into an `f`-map of
presheaves of sets from the sectionwise localization `𝒮_Y⁻¹M` to `𝒮_X⁻¹(f^*M)`, in the sense of
Stacks 03G3: the rule `m/b ↦ (f^*m)/(f^♯b)` is compatible with étale restriction of both charts
of a diagram.  This is the module-level form of
`AlgebraicGeometry.Space.fmapMeromorphicFunctions`, which is the case `M = 𝒪_Y`. -/
@[stacks 0ENC "part (1), chartwise for an arbitrary sheaf of 𝒪_Y-modules F: the fraction rule \
m/b ↦ (f^*m)/(f♯b) is canonical, being an f-map of Stacks 03G3 from the presheaf of sectionwise \
localizations of F to that of f^*F. This generalizes the structure-sheaf case \
AlgebraicGeometry.Space.fmapMeromorphicFunctions from F = 𝒪_Y to an arbitrary F. It is a \
statement about the presheaves of sectionwise localizations, not about their sheafifications; \
the global map Γ(Y, 𝒦_Y(F)) ⟶ Γ(X, 𝒦_X(f^*F)) of part (1) that this f-map descends to is \
AlgebraicGeometry.Space.pullbackSheafifiedRegularSections, which is part (1) with 𝒦(F) read as \
the first description in Stacks 0EN5, the sheafification of these sectionwise localizations. \
Part (1) for AlgebraicGeometry.Space.MeromorphicSection, which realizes Stacks 0EN5 through \
the other description there, the sheafification of F ⊗_𝒪 𝒦, is \
AlgebraicGeometry.Space.pullbackMeromorphicSection, built over the same rule taken over the \
sheaf 𝒦 instead of the presheaf 𝒮⁻¹𝒪. Part (2), stated through \
AlgebraicGeometry.Space.IsRegularMeromorphicSection, is not asserted here; it is proved for an \
invertible module by \
AlgebraicGeometry.Space.isRegularMeromorphicSection_pullbackMeromorphicSection"]
noncomputable def fmapMeromorphicSections
    (hf : PullbacksMeromorphicSections B S hS f.hom) :
    FMap B S hS X.1 Y.1 f.hom
      ((regularSectionsLocalizationModule B S hS X.1 X.2
          ((modulePullback B S hS f).obj M)).presheaf ⋙
        CategoryTheory.forget AddCommGrpCat.{u})
      ((regularSectionsLocalizationModule B S hS Y.1 Y.2 M).presheaf ⋙
        CategoryTheory.forget AddCommGrpCat.{u}) where
  app d := chartPullbackMeromorphicSections B S hS f M hf d
  naturality d d' i j h s :=
    chartPullbackMeromorphicSections_comp B S hS f M hf d d' i j h s

end FractionRule

end AlgebraicGeometry.Space

end
