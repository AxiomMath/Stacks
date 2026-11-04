module

public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPointTwists
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.Chart
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModule

/-!
# The presentation of a relative Proj over a presentation of its base

Let `π : P ⟶ X` be presented as a relative homogeneous spectrum over the scheme points of `X`
(`AlgebraicGeometry.Space.RelativeProjPoints`, the second assertion of Stacks 084B), and let
`X = U/R` be a presentation of the base (Stacks 0263): a surjective étale atlas `u : U ⟶ X` and
its kernel pair `R = U ×_X U` with projections `t, s : R ⟶ U`.  Base change along `π` turns it into
a presentation `P = P_U/P_R` of `P`, where `P_U = U ×_X P` and `P_R = R ×_X P` are the objects of
the site that `π` supplies over the points `u` and `t ≫ u` of `X`, and the two projections
`P_R ⇉ P_U` are the comparison morphisms of the third assertion of Stacks 084B along `t` and `s`.

The only point to check is that `P_R` is the kernel pair `P_U ×_P P_U` of the chart
`P_U ⟶ P`.  Over the cartesian square `P_U = U ×_X P` this is the cartesian square
`P_R = R ×_U P_U` of Stacks 084B pasted onto `R = U ×_X U`; the rest — that the projections form an
étale equivalence relation — follows from the kernel pair as for any atlas (Stacks 0262).

The descent of Stacks 084D takes place along this presentation: the twists of Stacks 01NR live on
the scheme of `P_U`, and the module `𝒪_{P_U}(n)` they give on the representable algebraic space
`P_U` through Stacks 03DX (2) is recorded here as well.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjPoints.presentation`: **the presentation `P = P_U/P_R` of
  the relative Proj over a presentation `X = U/R` of its base.**
* `AlgebraicGeometry.Space.RelativeProjPoints.fibreTwistQcoh`: the twist `𝒪(n)` on the scheme of
  `T ×_X P`, as a quasi-coherent module, and
  `AlgebraicGeometry.Space.RelativeProjPoints.chartTwist`: the quasi-coherent `𝒪`-module it gives
  on the representable algebraic space `T ×_X P` (Stacks 03DX (2)).

## Main results

* `AlgebraicGeometry.Space.RelativeProjPoints.isPullback_presentationTarget_presentationSource`:
  the relation scheme `R ×_X P` is the kernel pair of the chart `U ×_X P ⟶ P`.
* `AlgebraicGeometry.Space.RelativeProjPoints.presentation_toSpace` and its companions: the
  fields of the presentation, which are the comparison morphisms of Stacks 084B on the nose.

## References

* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X}
  (d : RelativeProjPoints B S hS π) {hX : IsAlgebraicSpace B S hS X}
  (Px : Presentation B S hS X hX)

/-! ### The presentation of `P` over a presentation of `X` -/

/-- The point `R ⟶ X` of the relation of a presentation of the base, through its target. -/
abbrev relationPoint : yoneda.obj Px.R ⟶ X :=
  yoneda.map Px.target ≫ Px.toSpace

/-- The target projection `R ×_X P ⟶ U ×_X P`: the comparison morphism of Stacks 084B along the
target projection of the relation. -/
abbrev presentationTarget : d.fibre Px.R (relationPoint Px) ⟶ d.fibre Px.U Px.toSpace :=
  d.fibreComparison Px.U Px.toSpace Px.target

/-- The source projection `R ×_X P ⟶ U ×_X P`: the comparison morphism of Stacks 084B along the
source projection of the relation, after identifying the two points `t ≫ u = s ≫ u` of `X`. -/
abbrev presentationSource : d.fibre Px.R (relationPoint Px) ⟶ d.fibre Px.U Px.toSpace :=
  eqToHom (congrArg (d.fibre Px.R) Px.isPullback.w) ≫
    d.fibreComparison Px.U Px.toSpace Px.source

/-- The source projection lies over the source projection of the relation. -/
theorem presentationSource_comp_fibreHom :
    d.presentationSource Px ≫ d.fibreHom Px.U Px.toSpace =
      d.fibreHom Px.R (relationPoint Px) ≫ Px.source := by
  rw [Category.assoc, fibreComparison_comp_fibreHom, ← Category.assoc,
    eqToHom_comp_fibreHom (e := Px.isPullback.w)]

/-- The two projections have the same composite with the chart `U ×_X P ⟶ P`. -/
theorem map_presentationTarget_comp_fibreToSpace :
    yoneda.map (d.presentationTarget Px) ≫ d.fibreToSpace Px.U Px.toSpace =
      yoneda.map (d.presentationSource Px) ≫ d.fibreToSpace Px.U Px.toSpace := by
  rw [map_fibreComparison_comp_fibreToSpace, Functor.map_comp, Category.assoc,
    map_fibreComparison_comp_fibreToSpace, map_eqToHom_fibreToSpace (e := Px.isPullback.w)]

/-- **The relation scheme `R ×_X P` is the kernel pair of the chart `U ×_X P ⟶ P`.**  Pasted below
the cartesian square `U ×_X P` over `u`, the square is the cartesian square `R ×_X P = R ×_U P_U`
of Stacks 084B along the target projection, pasted onto the cartesian square `R = U ×_X U`. -/
theorem isPullback_presentationTarget_presentationSource :
    IsPullback (yoneda.map (d.presentationTarget Px)) (yoneda.map (d.presentationSource Px))
      (d.fibreToSpace Px.U Px.toSpace) (d.fibreToSpace Px.U Px.toSpace) := by
  have hrect := (d.isPullback_fibreComparison Px.U Px.toSpace Px.target).paste_vert Px.isPullback
  refine IsPullback.of_bot ?_ (d.map_presentationTarget_comp_fibreToSpace Px)
    (d.isPullback Px.U Px.toSpace)
  rw [← Functor.map_comp, presentationSource_comp_fibreHom, Functor.map_comp,
    (d.isPullback Px.U Px.toSpace).w]
  exact hrect

/-- **The presentation `P = P_U/P_R` of the relative Proj over a presentation `X = U/R` of its
base.**  The presenting scheme is `P_U = U ×_X P`, the relation scheme is `P_R = R ×_X P`, the two
projections are the comparison morphisms of Stacks 084B along the projections of `R`, and the atlas
is the chart `P_U ⟶ P`, the base change of the atlas of `X` along `π`. -/
def presentation (hP : IsAlgebraicSpace B S hS P) : Presentation B S hS P hP where
  U := d.fibre Px.U Px.toSpace
  R := d.fibre Px.R (relationPoint Px)
  target := d.presentationTarget Px
  source := d.presentationSource Px
  isEtaleEquivalenceRelation :=
    have het := d.etale_fibreToSpace Px.etale
    have hrel : MorphismProperty.relative yoneda
        (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
        (d.fibreToSpace Px.U Px.toSpace) := by
      simpa [MorphismProperty.presheaf] using het
    have hkernel := d.isPullback_presentationTarget_presentationSource Px
    have hsrc : PreRelation.source
        (prod.lift ((Over.post B.inclusion).map (d.presentationTarget Px))
          ((Over.post B.inclusion).map (d.presentationSource Px))) =
        (Over.post B.inclusion).map (d.presentationSource Px) :=
      prod.lift_snd _ _
    have htgt : PreRelation.target
        (prod.lift ((Over.post B.inclusion).map (d.presentationTarget Px))
          ((Over.post B.inclusion).map (d.presentationSource Px))) =
        (Over.post B.inclusion).map (d.presentationTarget Px) :=
      prod.lift_fst _ _
    { isEquivalenceRelation := by
        rw [htgt, hsrc]
        exact isEquivalenceRelation_of_isPullback B S hS _ _ _ hkernel
      etale_source := by
        rw [hsrc]
        exact hrel.2 _ _ _ hkernel
      etale_target := by
        rw [htgt]
        exact hrel.2 _ _ _ hkernel.flip }
  toSpace := d.fibreToSpace Px.U Px.toSpace
  surjective := d.surjective_fibreToSpace Px.surjective
  etale := d.etale_fibreToSpace Px.etale
  isPullback := d.isPullback_presentationTarget_presentationSource Px

variable (hP : IsAlgebraicSpace B S hS P)

/-- The presenting scheme of `presentation` is `U ×_X P`. -/
@[simp] theorem presentation_U : (d.presentation Px hP).U = d.fibre Px.U Px.toSpace := rfl

/-- The relation scheme of `presentation` is `R ×_X P`. -/
@[simp] theorem presentation_R : (d.presentation Px hP).R = d.fibre Px.R (relationPoint Px) := rfl

/-- The target projection of `presentation` is `presentationTarget`. -/
@[simp] theorem presentation_target : (d.presentation Px hP).target = d.presentationTarget Px := rfl

/-- The source projection of `presentation` is `presentationSource`. -/
@[simp] theorem presentation_source : (d.presentation Px hP).source = d.presentationSource Px := rfl

/-- The atlas of `presentation` is the chart `U ×_X P ⟶ P`. -/
@[simp] theorem presentation_toSpace :
    (d.presentation Px hP).toSpace = d.fibreToSpace Px.U Px.toSpace := rfl

/-! ### The twists on the presenting scheme -/

variable (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)

/-- The twist `𝒪(n)` of Stacks 01NR on the scheme of `T ×_X P`, as a quasi-coherent module: the
twist on `Proj_T(f^*𝒜)` read through the identification `d.fibreIso T f` of Stacks 084B. -/
abbrev fibreTwistQcoh (n : ℤ) :
    (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj (d.fibre T f)).ringCatSheaf).FullSubcategory :=
  ⟨d.fibreTwist T f n,
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      (d.fibreIso T f).hom.toLRSHom.toShHom (d.pointTwist T f n)
      (d.isQuasicoherent_pointTwist T f n)⟩

/-- **The twist `𝒪(n)` on the étale chart `T ×_X P` of `P`, as a quasi-coherent `𝒪`-module on the
representable algebraic space `T ×_X P`**: the module Stacks 03DX (2) attaches to the twist of
Stacks 01NR on its scheme.  At the presenting scheme of `presentation` this is the module
`𝒪_{P_U}(n)` that the descent of Stacks 084D starts from. -/
def chartTwist (n : ℤ) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedStructureRingSheaf B S hS (d.fibre T f))).FullSubcategory :=
  (representedQuasicoherentSchemeEquivalence B S hS (d.fibre T f)).functor.obj
    (d.fibreTwistQcoh T f n)

/-- The twist on the chart is quasi-coherent on the small étale site of the chart. -/
theorem isQuasicoherentOnSite_chartTwist (n : ℤ) : (d.chartTwist T f n).obj.IsQuasicoherentOnSite :=
  (d.chartTwist T f n).property

end RelativeProjPoints

end AlgebraicGeometry.Space

end
