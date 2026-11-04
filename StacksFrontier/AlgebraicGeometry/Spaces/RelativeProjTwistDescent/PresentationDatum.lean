module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.Datum

/-!
# The descent datum of the twists on the presentation of a relative Proj

In Situation 0849 let `P = Proj_X(𝒜)` be the relative homogeneous spectrum of Stacks 084B and
`X = U/R` a presentation of its base, so that `P = P_U/P_R` with `P_U = U ×_X P` and
`P_R = R ×_X P` (`AlgebraicGeometry.Space.RelativeProjPoints.presentation`).  This file
instantiates the cocycle and unit conditions of the transition of the twists, known at variable
points, at the composable pairs `P_R ×_{P_U} P_R` and the diagonal `P_U ⟶ P_R` of this
presentation: these lie over the composable pairs `R ×_U R` and the diagonal of the presentation
of `X`, through the base change `(R ×_U R) ×_X P`.  The result is the descent datum of the twist
`𝒪(n)` of Stacks 01NR that `AlgebraicGeometry.Space.presentationDescendedModule` (Stacks 03M3)
turns into `𝒪_P(n)` (Stacks 084D).

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjPoints.spacePresentation`: the presentation `P = P_U/P_R`,
  typed as a presentation of the algebraic space `⟨P, hP⟩`, with its structure morphisms
  `…spaceTarget`, `…spaceSource`, `…spaceDoubleFst`, `…spaceDoubleSnd`, `…spaceComp`, `…spaceDiag`
  spelled through the base changes.
* `AlgebraicGeometry.Space.RelativeProjPoints.doubleToFibre`: the morphism of the composable pairs
  of `P_R ⇉ P_U` to the base change `(R ×_U R) ×_X P`.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistTransition`: **the scheme transition
  `t^*𝒪(n) ⟶ s^*𝒪(n)` of the twist on `P_R`**.

## Main results

* `AlgebraicGeometry.Space.RelativeProjPoints.spaceComp_eq`, `…spaceDoubleFst_eq`,
  `…spaceDoubleSnd_eq`: the three morphisms of the composable pairs of `P_R ⇉ P_U` to `P_R` factor
  through `(R ×_U R) ×_X P` by comparison morphisms lying over the composition leg and the two
  projections of `R ×_U R`; `…liesOver_spaceDiag`: the diagonal lies over the diagonal.
* `AlgebraicGeometry.Space.RelativeProjSituation.presentationSchemeCocycle_twistTransition` and
  `…presentationSchemeUnit_twistTransition`: **the cocycle and unit conditions of the transition of
  the twists** on the presentation of `P`.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Space

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X.obj}
  (d : RelativeProjPoints B S hS π) (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P)

/-! ### The presentation of `P`, as a presentation of an algebraic space -/

/-- The presentation `P = P_U/P_R` over a presentation `X = U/R` of the base
(`AlgebraicGeometry.Space.RelativeProjPoints.presentation`), typed as a presentation of the
algebraic space `⟨P, hP⟩`. -/
abbrev spacePresentation :
    Presentation B S hS (⟨P, hP⟩ : AlgebraicSpaces B S hS).obj
      (⟨P, hP⟩ : AlgebraicSpaces B S hS).property :=
  d.presentation Px hP

/-- The target projection `R ×_X P ⟶ U ×_X P`, spelled through the base changes. -/
abbrev spaceTarget : d.fibre Px.R (relationPoint Px) ⟶ d.fibre Px.U Px.toSpace :=
  (d.spacePresentation Px hP).target

/-- The source projection `R ×_X P ⟶ U ×_X P`, spelled through the base changes. -/
abbrev spaceSource : d.fibre Px.R (relationPoint Px) ⟶ d.fibre Px.U Px.toSpace :=
  (d.spacePresentation Px hP).source

/-- The first projection of the composable pairs of `P_R ⇉ P_U`, into `R ×_X P`. -/
abbrev spaceDoubleFst :
    presentationDouble (d.spacePresentation Px hP) ⟶ d.fibre Px.R (relationPoint Px) :=
  presentationDoubleFst (d.spacePresentation Px hP)

/-- The second projection of the composable pairs of `P_R ⇉ P_U`, into `R ×_X P`. -/
abbrev spaceDoubleSnd :
    presentationDouble (d.spacePresentation Px hP) ⟶ d.fibre Px.R (relationPoint Px) :=
  presentationDoubleSnd (d.spacePresentation Px hP)

/-- The composition leg of the composable pairs of `P_R ⇉ P_U`, into `R ×_X P`. -/
abbrev spaceComp :
    presentationDouble (d.spacePresentation Px hP) ⟶ d.fibre Px.R (relationPoint Px) :=
  presentationComp (d.spacePresentation Px hP)

/-- The diagonal `U ×_X P ⟶ R ×_X P` of the presentation of `P`. -/
abbrev spaceDiag : d.fibre Px.U Px.toSpace ⟶ d.fibre Px.R (relationPoint Px) :=
  presentationDiag (d.spacePresentation Px hP)

/-- The target projection of the presentation of `P` lies over the target projection of the
relation. -/
theorem liesOver_spaceTarget : d.LiesOver (d.spaceTarget Px hP) Px.target :=
  liesOver_fibreComparison _ _ _

/-- The source projection of the presentation of `P` lies over the source projection of the
relation. -/
theorem liesOver_spaceSource : d.LiesOver (d.spaceSource Px hP) Px.source :=
  (liesOver_fibreComparison _ _ _).eqToHom_comp Px.isPullback.w

/-- The first projection of the composable pairs of `P_R ⇉ P_U` followed by the source agrees with
the second projection followed by the target. -/
theorem spaceDoubleFst_comp_source :
    d.spaceDoubleFst Px hP ≫ d.spaceSource Px hP = d.spaceDoubleSnd Px hP ≫ d.spaceTarget Px hP :=
  presentationDoubleFst_comp_source _

/-- The composition leg followed by the target agrees with the first projection followed by the
target. -/
theorem spaceComp_comp_target :
    d.spaceComp Px hP ≫ d.spaceTarget Px hP = d.spaceDoubleFst Px hP ≫ d.spaceTarget Px hP :=
  presentationComp_comp_target _

/-- The composition leg followed by the source agrees with the second projection followed by the
source. -/
theorem spaceComp_comp_source :
    d.spaceComp Px hP ≫ d.spaceSource Px hP = d.spaceDoubleSnd Px hP ≫ d.spaceSource Px hP :=
  presentationComp_comp_source _

/-- The diagonal of the presentation of `P` followed by the target is the identity. -/
theorem spaceDiag_comp_target : d.spaceDiag Px hP ≫ d.spaceTarget Px hP = 𝟙 _ :=
  presentationDiag_comp_target _

/-- The diagonal of the presentation of `P` followed by the source is the identity. -/
theorem spaceDiag_comp_source : d.spaceDiag Px hP ≫ d.spaceSource Px hP = 𝟙 _ :=
  presentationDiag_comp_source _

/-! ### The composable pairs of the relation of the base -/

/-- The point of `X` at the composable pairs `R ×_U R`, through the first projection. -/
abbrev doublePoint : yoneda.obj (presentationDouble Px) ⟶ X.obj :=
  yoneda.map (presentationDoubleFst Px) ≫ relationPoint Px

omit Px in
/-- Morphisms into the relation of a presentation agree as soon as their two projections do. -/
theorem presentation_hom_ext (Px : Presentation B S hS X.obj X.property)
    {V : BigFppfOver B S hS} {f g : V ⟶ Px.R}
    (ht : f ≫ Px.target = g ≫ Px.target) (hs : f ≫ Px.source = g ≫ Px.source) : f = g :=
  yoneda.map_injective (Px.isPullback.hom_ext (by rw [← Functor.map_comp, ← Functor.map_comp, ht])
    (by rw [← Functor.map_comp, ← Functor.map_comp, hs]))

/-- The point of `X` at the composable pairs through the second projection is the same. -/
theorem doubleSnd_point : yoneda.map (presentationDoubleSnd Px) ≫ relationPoint Px =
    doublePoint Px := by
  simp only [doublePoint, relationPoint, ← Category.assoc, ← Functor.map_comp]
  rw [← presentationDoubleFst_comp_source, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, Px.isPullback.w]

/-- The point of `X` at the composable pairs through the composition leg is the same. -/
theorem doubleComp_point : yoneda.map (presentationComp Px) ≫ relationPoint Px =
    doublePoint Px := by
  simp only [doublePoint, relationPoint, ← Category.assoc, ← Functor.map_comp,
    presentationComp_comp_target]

/-- The point of `X` at `U` through the diagonal of the relation is the atlas. -/
theorem diag_point : yoneda.map (presentationDiag Px) ≫ relationPoint Px = Px.toSpace := by
  rw [relationPoint, ← Category.assoc, ← Functor.map_comp, presentationDiag_comp_target,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The comparison `(R ×_U R) ×_X P ⟶ R ×_X P` along a morphism `k : R ×_U R ⟶ R` over the
point of the composable pairs. -/
abbrev doubleMap (k : presentationDouble Px ⟶ Px.R)
    (hk : yoneda.map k ≫ relationPoint Px = doublePoint Px) :
    d.fibre (presentationDouble Px) (doublePoint Px) ⟶ d.fibre Px.R (relationPoint Px) :=
  eqToHom (congrArg (d.fibre (presentationDouble Px)) hk.symm) ≫ d.fibreComparison _ _ k

/-- The comparison along `k` lies over `k`. -/
theorem liesOver_doubleMap (k : presentationDouble Px ⟶ Px.R)
    (hk : yoneda.map k ≫ relationPoint Px = doublePoint Px) :
    d.LiesOver (d.doubleMap Px k hk) k :=
  (liesOver_fibreComparison _ _ _).eqToHom_comp (e := hk.symm)

/-! ### The composable pairs of the presentation of `P` over those of the base -/

/-- A morphism into `R ×_X P`, followed by the structure morphism to `R` and the target, is its
composite with the target projection followed by the structure morphism to `U`. -/
private theorem comp_fibreHom_comp_target {V : BigFppfOver B S hS}
    (f : V ⟶ d.fibre Px.R (relationPoint Px)) :
    (f ≫ d.fibreHom Px.R (relationPoint Px)) ≫ Px.target =
      (f ≫ d.spaceTarget Px hP) ≫ d.fibreHom Px.U Px.toSpace := by
  rw [Category.assoc, Category.assoc, (d.liesOver_spaceTarget Px hP).1]

/-- A morphism into `R ×_X P`, followed by the structure morphism to `R` and the source, is its
composite with the source projection followed by the structure morphism to `U`. -/
private theorem comp_fibreHom_comp_source {V : BigFppfOver B S hS}
    (f : V ⟶ d.fibre Px.R (relationPoint Px)) :
    (f ≫ d.fibreHom Px.R (relationPoint Px)) ≫ Px.source =
      (f ≫ d.spaceSource Px hP) ≫ d.fibreHom Px.U Px.toSpace := by
  rw [Category.assoc, Category.assoc, (d.liesOver_spaceSource Px hP).1]

/-- The two projections of the composable pairs of `P_R ⇉ P_U`, followed by the structure
morphism to `R`, form a composable pair of `R ⇉ U`. -/
theorem doubleToBase_condition :
    (d.spaceDoubleFst Px hP ≫ d.fibreHom Px.R (relationPoint Px)) ≫ Px.source =
      (d.spaceDoubleSnd Px hP ≫ d.fibreHom Px.R (relationPoint Px)) ≫ Px.target := by
  rw [d.comp_fibreHom_comp_source Px hP, d.comp_fibreHom_comp_target Px hP,
    spaceDoubleFst_comp_source]

/-- The morphism of the composable pairs of `P_R ⇉ P_U` to the composable pairs of `R ⇉ U`. -/
def doubleToBase : presentationDouble (d.spacePresentation Px hP) ⟶ presentationDouble Px :=
  pullback.lift _ _ (d.doubleToBase_condition Px hP)

/-- `doubleToBase` followed by the first projection of `R ×_U R` is the first projection of the
composable pairs of `P_R ⇉ P_U` followed by the structure morphism to `R`. -/
theorem doubleToBase_fst : d.doubleToBase Px hP ≫ presentationDoubleFst Px =
    d.spaceDoubleFst Px hP ≫ d.fibreHom Px.R (relationPoint Px) :=
  pullback.lift_fst _ _ _

/-- `doubleToBase` followed by the second projection of `R ×_U R` is the second projection of the
composable pairs of `P_R ⇉ P_U` followed by the structure morphism to `R`. -/
theorem doubleToBase_snd : d.doubleToBase Px hP ≫ presentationDoubleSnd Px =
    d.spaceDoubleSnd Px hP ≫ d.fibreHom Px.R (relationPoint Px) :=
  pullback.lift_snd _ _ _

/-- The first projection of the composable pairs of `P_R ⇉ P_U`, followed by the chart of `R ×_X P`
and `π`, agrees with `doubleToBase` followed by the point of `X` at `R ×_U R`. -/
theorem doubleToFibre_condition :
    (yoneda.map (d.spaceDoubleFst Px hP) ≫ d.fibreToSpace Px.R (relationPoint Px)) ≫ π =
      yoneda.map (d.doubleToBase Px hP) ≫ doublePoint Px := by
  rw [Category.assoc, (d.isPullback _ _).w, doublePoint, ← Category.assoc (yoneda.map _),
    ← Functor.map_comp, ← doubleToBase_fst, Functor.map_comp, Category.assoc]

/-- **The composable pairs of `P_R ⇉ P_U` map to the base change `(R ×_U R) ×_X P`.** -/
def doubleToFibre :
    presentationDouble (d.spacePresentation Px hP) ⟶
      d.fibre (presentationDouble Px) (doublePoint Px) :=
  d.fibreLift (d.doubleToBase Px hP) _ (d.doubleToFibre_condition Px hP)

/-- A morphism `H` from the composable pairs of `P_R ⇉ P_U` to `P_R` factors through the base
change `(R ×_U R) ×_X P` by the comparison along `k`, once it lies over `k` after the projection
to the base and has the same composite with the chart as the first projection. -/
theorem eq_doubleToFibre_comp (k : presentationDouble Px ⟶ Px.R)
    (hk : yoneda.map k ≫ relationPoint Px = doublePoint Px)
    (H : presentationDouble (d.spacePresentation Px hP) ⟶ d.fibre Px.R (relationPoint Px))
    (h₁ : H ≫ d.fibreHom Px.R (relationPoint Px) = d.doubleToBase Px hP ≫ k)
    (h₂ : yoneda.map H ≫ d.fibreToSpace Px.R (relationPoint Px) =
      yoneda.map (d.spaceDoubleFst Px hP) ≫ d.fibreToSpace Px.R (relationPoint Px)) :
    H = d.doubleToFibre Px hP ≫ d.doubleMap Px k hk := by
  refine d.fibre_hom_ext ?_ ?_
  · rw [h₁, Category.assoc, (d.liesOver_doubleMap Px k hk).1, ← Category.assoc, doubleToFibre,
      fibreLift_comp_fibreHom]
  · rw [h₂, Functor.map_comp, Category.assoc, (d.liesOver_doubleMap Px k hk).2, doubleToFibre,
      map_fibreLift_comp_fibreToSpace]

/-- A morphism into `R ×_X P`, followed by the chart, is its composite with the target projection
followed by the chart of `U ×_X P`. -/
private theorem map_comp_fibreToSpace_target {V : BigFppfOver B S hS}
    (f : V ⟶ d.fibre Px.R (relationPoint Px)) :
    yoneda.map f ≫ d.fibreToSpace Px.R (relationPoint Px) =
      yoneda.map (f ≫ d.spaceTarget Px hP) ≫ d.fibreToSpace Px.U Px.toSpace := by
  rw [Functor.map_comp, Category.assoc, (d.liesOver_spaceTarget Px hP).2]

/-- A morphism into `R ×_X P`, followed by the chart, is its composite with the source projection
followed by the chart of `U ×_X P`. -/
private theorem map_comp_fibreToSpace_source {V : BigFppfOver B S hS}
    (f : V ⟶ d.fibre Px.R (relationPoint Px)) :
    yoneda.map f ≫ d.fibreToSpace Px.R (relationPoint Px) =
      yoneda.map (f ≫ d.spaceSource Px hP) ≫ d.fibreToSpace Px.U Px.toSpace := by
  rw [Functor.map_comp, Category.assoc, (d.liesOver_spaceSource Px hP).2]

/-- The second projection and the first have the same composite with the chart of `R ×_X P`. -/
theorem map_spaceDoubleSnd_comp_fibreToSpace :
    yoneda.map (d.spaceDoubleSnd Px hP) ≫ d.fibreToSpace Px.R (relationPoint Px) =
      yoneda.map (d.spaceDoubleFst Px hP) ≫ d.fibreToSpace Px.R (relationPoint Px) := by
  rw [d.map_comp_fibreToSpace_target Px hP, ← spaceDoubleFst_comp_source,
    ← d.map_comp_fibreToSpace_source Px hP]

/-- The composition leg and the first projection have the same composite with the chart of
`R ×_X P`. -/
theorem map_spaceComp_comp_fibreToSpace :
    yoneda.map (d.spaceComp Px hP) ≫ d.fibreToSpace Px.R (relationPoint Px) =
      yoneda.map (d.spaceDoubleFst Px hP) ≫ d.fibreToSpace Px.R (relationPoint Px) := by
  rw [d.map_comp_fibreToSpace_target Px hP, spaceComp_comp_target,
    ← d.map_comp_fibreToSpace_target Px hP]

/-- The first projection of the composable pairs of `P_R ⇉ P_U` factors through `doubleToFibre` by
the comparison along the first projection of `R ×_U R`. -/
theorem spaceDoubleFst_eq :
    d.spaceDoubleFst Px hP =
      d.doubleToFibre Px hP ≫ d.doubleMap Px (presentationDoubleFst Px) rfl :=
  d.eq_doubleToFibre_comp Px hP _ rfl _ (d.doubleToBase_fst Px hP).symm rfl

/-- The second projection of the composable pairs of `P_R ⇉ P_U` factors through `doubleToFibre` by
the comparison along the second projection of `R ×_U R`. -/
theorem spaceDoubleSnd_eq :
    d.spaceDoubleSnd Px hP =
      d.doubleToFibre Px hP ≫ d.doubleMap Px (presentationDoubleSnd Px) (doubleSnd_point Px) :=
  d.eq_doubleToFibre_comp Px hP _ _ _ (d.doubleToBase_snd Px hP).symm
    (d.map_spaceDoubleSnd_comp_fibreToSpace Px hP)

/-- The composition leg of the composable pairs of `P_R ⇉ P_U` factors through `doubleToFibre` by
the comparison along the composition leg of `R ×_U R`. -/
theorem spaceComp_eq :
    d.spaceComp Px hP =
      d.doubleToFibre Px hP ≫ d.doubleMap Px (presentationComp Px) (doubleComp_point Px) := by
  refine d.eq_doubleToFibre_comp Px hP _ _ _ ?_ (d.map_spaceComp_comp_fibreToSpace Px hP)
  refine presentation_hom_ext Px ?_ ?_
  · rw [Category.assoc (d.doubleToBase Px hP), presentationComp_comp_target, ← Category.assoc,
      doubleToBase_fst, d.comp_fibreHom_comp_target Px hP, d.comp_fibreHom_comp_target Px hP,
      spaceComp_comp_target]
  · rw [Category.assoc (d.doubleToBase Px hP), presentationComp_comp_source, ← Category.assoc,
      doubleToBase_snd, d.comp_fibreHom_comp_source Px hP, d.comp_fibreHom_comp_source Px hP,
      spaceComp_comp_source]

/-- The diagonal of the presentation of `P` lies over the diagonal of the presentation of `X`. -/
theorem liesOver_spaceDiag : d.LiesOver (d.spaceDiag Px hP) (presentationDiag Px) := by
  refine ⟨presentation_hom_ext Px ?_ ?_, ?_⟩
  · rw [d.comp_fibreHom_comp_target Px hP, spaceDiag_comp_target, Category.assoc,
      presentationDiag_comp_target, Category.comp_id, Category.id_comp]
  · rw [d.comp_fibreHom_comp_source Px hP, spaceDiag_comp_source, Category.assoc,
      presentationDiag_comp_source, Category.comp_id, Category.id_comp]
  · rw [d.map_comp_fibreToSpace_target Px hP, spaceDiag_comp_target,
      CategoryTheory.Functor.map_id, Category.id_comp]

/-! ### The cocycle and unit conditions on the presentation of `P`, spelled through the base
changes -/

section Conditions

variable (M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (d.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory)
  (τ : quasicoherentPullbackObj B S hS (d.spaceTarget Px hP) M ⟶
    quasicoherentPullbackObj B S hS (d.spaceSource Px hP) M)

/-- The cocycle condition of a scheme transition on the presentation `P = P_U/P_R`
(`AlgebraicGeometry.Space.PresentationSchemeCocycle`), from its form spelled through the base
changes `U ×_X P`, `R ×_X P`. -/
theorem presentationSchemeCocycle_spacePresentation
    (h : schemeTransitionReindex B S hS (d.spaceTarget Px hP) (d.spaceSource Px hP) M τ
        (d.spaceComp Px hP) =
      eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M)
          (d.spaceComp_comp_target Px hP)) ≫
        schemeTransitionReindex B S hS (d.spaceTarget Px hP) (d.spaceSource Px hP) M τ
          (d.spaceDoubleFst Px hP) ≫
          eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M)
            (d.spaceDoubleFst_comp_source Px hP)) ≫
            schemeTransitionReindex B S hS (d.spaceTarget Px hP) (d.spaceSource Px hP) M τ
              (d.spaceDoubleSnd Px hP) ≫
              eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M)
                (d.spaceComp_comp_source Px hP).symm)) :
    PresentationSchemeCocycle (d.spacePresentation Px hP) M τ :=
  h

/-- The unit condition of a scheme transition on the presentation `P = P_U/P_R`
(`AlgebraicGeometry.Space.PresentationSchemeUnit`), from its form spelled through the base
changes. -/
theorem presentationSchemeUnit_spacePresentation
    (h : schemeTransitionReindex B S hS (d.spaceTarget Px hP) (d.spaceSource Px hP) M τ
        (d.spaceDiag Px hP) =
      eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M)
        ((d.spaceDiag_comp_target Px hP).trans (d.spaceDiag_comp_source Px hP).symm))) :
    PresentationSchemeUnit (d.spacePresentation Px hP) M τ :=
  h

end Conditions

end RelativeProjPoints

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **The scheme transition of the twist `𝒪(n)` on the presentation `P = P_U/P_R`**: on the
scheme of `P_R = R ×_X P`, the comparison of twists along the target projection followed by the
inverse of the comparison along the source projection, both landing in `𝒪_{P_R}(n)`. -/
def twistTransition (n : ℤ) :
    quasicoherentPullbackObj s.site s.base s.containsBase
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceQcoh Px.U Px.toSpace n) ⟶
      quasicoherentPullbackObj s.site s.base s.containsBase
        (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceQcoh Px.U Px.toSpace n) :=
  (s.twistPieceComparison (u := Px.toSpace) (v := RelativeProjPoints.relationPoint Px) Px.target
      rfl
      (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor) n).hom ≫
    (s.twistPieceComparison (u := Px.toSpace) (v := RelativeProjPoints.relationPoint Px) Px.source
      (s.map_source_comp_toSpace Px)
      (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceSource Px s.isAlgebraicSpace_relativeProjFunctor) n).inv

/-- **The cocycle condition of the transition of the twists `𝒪(n)`** on the scheme of composable
pairs of the presentation `P = P_U/P_R` (Stacks 084D, the descent datum of the twists). -/
theorem presentationSchemeCocycle_twistTransition (n : ℤ) :
    PresentationSchemeCocycle
      (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n) :=
  s.relativeProjPoints.presentationSchemeCocycle_spacePresentation Px
    s.isAlgebraicSpace_relativeProjFunctor _ _ <| by
    have key := s.schemeTransitionReindex_cocycle (u := Px.toSpace)
      (r := RelativeProjPoints.relationPoint Px) (w₃ := RelativeProjPoints.doublePoint Px) Px.target
      Px.source rfl
      (s.map_source_comp_toSpace Px)
      (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceSource Px s.isAlgebraicSpace_relativeProjFunctor) n
      (s.relativeProjPoints.doubleToFibre Px s.isAlgebraicSpace_relativeProjFunctor)
      (presentationComp Px) (presentationDoubleFst Px) (presentationDoubleSnd Px)
      (RelativeProjPoints.doubleComp_point Px) rfl (RelativeProjPoints.doubleSnd_point Px)
      (s.relativeProjPoints.doubleMap Px (presentationComp Px)
        (RelativeProjPoints.doubleComp_point Px))
      (s.relativeProjPoints.doubleMap Px (presentationDoubleFst Px) rfl)
      (s.relativeProjPoints.doubleMap Px (presentationDoubleSnd Px)
        (RelativeProjPoints.doubleSnd_point Px))
      (s.relativeProjPoints.liesOver_doubleMap Px _ _)
      (s.relativeProjPoints.liesOver_doubleMap Px _ _)
      (s.relativeProjPoints.liesOver_doubleMap Px _ _)
      (presentationComp_comp_target Px) (presentationDoubleFst_comp_source Px)
      (presentationComp_comp_source Px).symm
      (s.relativeProjPoints.spaceComp Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.spaceDoubleFst Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.spaceDoubleSnd Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.spaceComp_eq Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.spaceDoubleFst_eq Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.spaceDoubleSnd_eq Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.spaceComp_comp_target Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.spaceDoubleFst_comp_source Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.spaceComp_comp_source Px s.isAlgebraicSpace_relativeProjFunctor).symm
    exact key

/-- **The unit condition of the transition of the twists `𝒪(n)`** along the diagonal of the
presentation `P = P_U/P_R` (Stacks 084D, the descent datum of the twists). -/
theorem presentationSchemeUnit_twistTransition (n : ℤ) :
    PresentationSchemeUnit
      (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n) :=
  s.relativeProjPoints.presentationSchemeUnit_spacePresentation Px
    s.isAlgebraicSpace_relativeProjFunctor _ _ <| by
    have key := s.schemeTransitionReindex_unit (u := Px.toSpace)
      (r := RelativeProjPoints.relationPoint Px) Px.target Px.source rfl
      (s.map_source_comp_toSpace Px)
      (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceSource Px s.isAlgebraicSpace_relativeProjFunctor) n
      (presentationDiag Px) (RelativeProjPoints.diag_point Px)
      (s.relativeProjPoints.spaceDiag Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceDiag Px s.isAlgebraicSpace_relativeProjFunctor)
      (presentationDiag_comp_target Px) (presentationDiag_comp_source Px)
      (s.relativeProjPoints.spaceDiag_comp_target Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.spaceDiag_comp_source Px s.isAlgebraicSpace_relativeProjFunctor)
    exact key

end RelativeProjSituation

end AlgebraicGeometry.Space

end
