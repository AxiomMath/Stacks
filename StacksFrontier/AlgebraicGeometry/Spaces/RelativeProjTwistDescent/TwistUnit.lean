module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistMul
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AlgebraTransport
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTwisting
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackUnitTransport

/-!
# The comparisons of the twists of a relative Proj carry the unit

In Situation 0849 the twists `𝒪(n)` of `P = Proj_X(𝒜)` are descended from the twists
`𝒪_{U ×_X P}(n)` on the scheme of a presentation `U ×_X P` of `P`, along the transitions
`AlgebraicGeometry.Space.RelativeProjSituation.twistTransition`, built from the comparisons
`AlgebraicGeometry.Space.RelativeProjSituation.twistPieceComparison`.  Each comparison is the
degree-`n` piece of an isomorphism of sheaves of graded algebras, so in degree `0` it carries the
unit `𝒪 ⟶ 𝒪(0)` of the twists, read through Stacks 03LU.  This file proves that compatibility
and, from it, descends the unit of the twists to `P` along the presentation (Stacks 084D), given
the compatibility of the identification of Stacks 03DX (2) of the structure sheaf with inverse
images along the two projections of the presentation.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.twistPieceUnit`: the unit `𝒪 ⟶ 𝒪(0)` of the
  twists on the scheme of a base change.
* `AlgebraicGeometry.Space.RelativeProjPoints.TransitionUnitCompat`: the compatibility of a
  morphism out of the structure sheaf with scheme transitions on the presentation `P = P_U/P_R`,
  as a named proposition.
* `AlgebraicGeometry.Space.RelativeProjPoints.spacePresentationDescendedUnit`: the descended unit
  on the presentation `P = P_U/P_R`, with its data spelled through the base changes.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistModuleUnit`: **the unit `𝒪_P ⟶ 𝒪_P(0)` of
  the descended twists**.

## Main results

* `AlgebraicGeometry.Space.oneHom_comp_iso_hom_app_zero`: an isomorphism of sheaves of graded
  algebras on a scheme carries the unit to the unit.
* `AlgebraicGeometry.Space.oneHom_pullbackGradedAlgebra_eq_pullbackUnitIso`: the unit of the
  inverse image of a sheaf of graded algebras is the inverse image of the unit, read through
  Stacks 03LU.
* `AlgebraicGeometry.Space.pullbackIsoOfSquare_hom_one`: the comparison along a square carries
  the unit to the unit.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistPieceComparison_unit`: the comparisons of
  the twists carry the unit to the unit.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistTransition_unit`: the transition of `𝒪(0)`
  carries the unit to the unit.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistModuleUnit_spec`: the inverse image of
  `AlgebraicGeometry.Space.RelativeProjSituation.twistModuleUnit` along the atlas.

## Implementation notes

As for `AlgebraicGeometry.Space.RelativeProjSituation.twistModuleMul`, the compatibility of the
transitions with the unit is passed to the descended unit as the named proposition
`AlgebraicGeometry.Space.RelativeProjPoints.TransitionUnitCompat`, so that the kernel compares it
argument by argument rather than through the deep types of the presentation.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra)
open Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp
open Stacks.AlgebraicGeometry.RelativeProjTwists (SchemeGradedAlgebra)

universe u m

namespace AlgebraicGeometry.Space

/-- **An isomorphism of sheaves of graded algebras on a scheme carries the unit to the unit**, as
morphisms out of the structure sheaf: `1_A ↦ 1_B` in degree `0`
(`SheafOfModules.GradedAlgebra.iso_hom_app_one_eval`), read through the bijection between
morphisms out of the structure sheaf and global sections. -/
theorem oneHom_comp_iso_hom_app_zero {W : Scheme.{u}} {A B : SchemeGradedAlgebra W}
    (e : A ≅ B) :
    SheafOfModules.GradedAlgebra.oneHom A ≫ e.hom.app 0 =
      SheafOfModules.GradedAlgebra.oneHom B :=
  oneHom_comp_app_zero
    { app := e.hom.app
      map_mul := e.hom.map_mul
      map_one := SheafOfModules.GradedAlgebra.iso_hom_app_one_eval e }

/-- **The unit of the inverse image of a sheaf of graded algebras is the inverse image of the
unit**, read through Stacks 03LU: for `h : Z ⟶ Y`, the unit `𝒪_Z ⟶ (h^*G)_0` is
`𝒪_Z ≅ h^*𝒪_Y ⟶ h^*G_0`.  On global sections both are the pullback-unit image of the unit of
`G` (`Stacks.RingedSpace.pullbackGradedAlgebra_one_eval`,
`Stacks.PullbackAlgebra.transportSection_val_top`). -/
theorem oneHom_pullbackGradedAlgebra_eq_pullbackUnitIso {Y Z : Scheme.{u}} (h : Z ⟶ Y)
    (G : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace)) :
    SheafOfModules.GradedAlgebra.oneHom (pbAlgS h G) =
      (Scheme.Modules.pullbackUnitIso h).inv ≫
        (Scheme.Modules.pullback h).map (SheafOfModules.GradedAlgebra.oneHom G) := by
  refine ((pbAlgS h G).piece 0).unitHomEquiv.injective ?_
  refine (SheafOfModules.GradedAlgebra.unitHomEquiv_oneHom (pbAlgS h G)).trans ?_
  refine Stacks.AlgebraicGeometry.AffineTwisting.sections_eq_of_eval_top _ _ _ ?_
  refine (Stacks.RingedSpace.pullbackGradedAlgebra_one_eval h.toLRSHom.toShHom G ⊤).trans ?_
  exact (Stacks.PullbackAlgebra.transportSection_val_top h.toLRSHom.toShHom (G.piece 0)
    G.one).symm

section PullbackSquare

variable {X' X Y' Y : Scheme.{u}} (ιX : X' ⟶ X) (ιY : Y' ⟶ Y) (y : Y' ⟶ X') (pc : Y ⟶ X)
  (e : y ≫ ιX = ιY ≫ pc) {G : SchemeGradedAlgebra X} {N : SchemeGradedAlgebra Y}
  (E : pbAlgS pc G ≅ N)

/-- **The comparison along a commutative square carries the unit to the unit.**  For a square
`y ≫ ιX = ιY ≫ pc` of schemes and an isomorphism `E : pc^*G ≅ N` of sheaves of graded algebras,
the comparison `y^*(ιX^*G_0) ≅ ιY^*N_0` carries the unit of `ιX^*G`, pulled back along `y` and
read through Stacks 03LU, to the unit of `ιY^*N`. -/
theorem pullbackIsoOfSquare_hom_one :
    (Scheme.Modules.pullbackUnitIso y).inv ≫
        (Scheme.Modules.pullback y).map
          (SheafOfModules.GradedAlgebra.oneHom (pbAlgS ιX G)) ≫
        (pullbackIsoOfSquare ιX ιY y pc e (gradedPieceIso pc E 0)).hom =
      SheafOfModules.GradedAlgebra.oneHom (pbAlgS ιY N) := by
  have h1 := oneHom_pullbackGradedAlgebra_eq_pullbackUnitIso y (pbAlgS ιX G)
  have h2 := oneHom_comp_iso_hom_app_zero (pullbackGradedAlgebraIsoOfSquare ιX ιY y pc e E)
  rw [h1] at h2
  exact (Category.assoc _ _ _).symm.trans h2

end PullbackSquare

/-- The abstract shape of `AlgebraicGeometry.Space.RelativeProjSituation.twistTransition_unit`: a
transition made of two comparisons carrying a unit to a common unit carries the unit. -/
private theorem transition_unit_of_comparisons {C : Type*} [Category C]
    {It Is Pt Ps Kt Ks Kr : C} (pt : Pt ≅ It) (ps : Ps ≅ Is) (mt : Pt ⟶ Kt) (ms : Ps ⟶ Ks)
    (Tt : Kt ≅ Kr) (Ts : Ks ≅ Kr) (νt : It ⟶ Kr) (νs : Is ⟶ Kr) (q : It ≅ Is)
    (ht : pt.inv ≫ mt ≫ Tt.hom = νt) (hs : ps.inv ≫ ms ≫ Ts.hom = νs) (hq : q.hom ≫ νs = νt) :
    pt.inv ≫ mt ≫ Tt.hom ≫ Ts.inv = q.hom ≫ ps.inv ≫ ms := by
  have hs' : ps.inv ≫ ms = νs ≫ Ts.inv := by
    rw [← reassoc_of% hs, Iso.hom_inv_id, Category.comp_id]
  rw [hs', reassoc_of% hq, ← reassoc_of% ht]

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X.obj}
  (d : RelativeProjPoints B S hS π) (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P)
  {K : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (d.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  (κ : quasicoherentPullbackObj B S hS (d.spaceTarget Px hP) K ⟶
    quasicoherentPullbackObj B S hS (d.spaceSource Px hP) K)
  (ν : quasicoherentUnitObj B S hS (d.fibre Px.U Px.toSpace) ⟶ K)

/-- The compatibility of a morphism out of the structure sheaf with scheme transitions on the
presentation `P = P_U/P_R`, from its form spelled through the base changes `U ×_X P`,
`R ×_X P`. -/
theorem spacePresentation_unit_transition
    (h : (quasicoherentPullbackUnitIso B S hS (d.spaceTarget Px hP)).inv ≫
        quasicoherentPullbackMap B S hS (d.spaceTarget Px hP) ν ≫ κ =
      (quasicoherentPullbackUnitIso B S hS (d.spaceSource Px hP)).inv ≫
        quasicoherentPullbackMap B S hS (d.spaceSource Px hP) ν) :
    (quasicoherentPullbackUnitIso B S hS (d.spacePresentation Px hP).target).inv ≫
        quasicoherentPullbackMap B S hS (d.spacePresentation Px hP).target ν ≫ κ =
      (quasicoherentPullbackUnitIso B S hS (d.spacePresentation Px hP).source).inv ≫
        quasicoherentPullbackMap B S hS (d.spacePresentation Px hP).source ν :=
  h

/-- **The compatibility of a morphism out of the structure sheaf with the scheme transitions of
the presentation `P = P_U/P_R`**, spelled through the base changes `U ×_X P`, `R ×_X P`: for
`ν : 𝒪 ⟶ K` on the scheme of `P_U` and a transition `κ` of `K` on the scheme of `P_R`, the
transition `κ` carries the pullback of `ν` along the target projection, read through
Stacks 03LU, to the pullback of `ν` along the source projection.

It is a named proposition for the reason given at
`AlgebraicGeometry.Space.RelativeProjPoints.TransitionMulCompat`. -/
def TransitionUnitCompat : Prop :=
  (quasicoherentPullbackUnitIso B S hS (d.spaceTarget Px hP)).inv ≫
      quasicoherentPullbackMap B S hS (d.spaceTarget Px hP) ν ≫ κ =
    (quasicoherentPullbackUnitIso B S hS (d.spaceSource Px hP)).inv ≫
      quasicoherentPullbackMap B S hS (d.spaceSource Px hP) ν

/-- `AlgebraicGeometry.Space.RelativeProjPoints.TransitionUnitCompat`, written out. -/
theorem transitionUnitCompat_iff :
    d.TransitionUnitCompat Px hP κ ν ↔
      (quasicoherentPullbackUnitIso B S hS (d.spaceTarget Px hP)).inv ≫
          quasicoherentPullbackMap B S hS (d.spaceTarget Px hP) ν ≫ κ =
        (quasicoherentPullbackUnitIso B S hS (d.spaceSource Px hP)).inv ≫
          quasicoherentPullbackMap B S hS (d.spaceSource Px hP) ν :=
  Iff.rfl

section Descent

variable (hc : PresentationSchemeCocycle (d.spacePresentation Px hP) K κ)
  (hu : PresentationSchemeUnit (d.spacePresentation Px hP) K κ)
  (hbt : RepresentedC3UnitCompat B S hS (d.spaceTarget Px hP))
  (hbs : RepresentedC3UnitCompat B S hS (d.spaceSource Px hP))
  (hm : d.TransitionUnitCompat Px hP κ ν)

/-- `AlgebraicGeometry.Space.presentationDescendedUnit` on the presentation `P = P_U/P_R`, with
its data spelled through the base changes `U ×_X P`, `R ×_X P`. -/
def spacePresentationDescendedUnit :
    SheafOfModules.unit (structureRingSheaf B S hS ⟨P, hP⟩) ⟶
      (presentationDescendedModule (d.spacePresentation Px hP) K κ hc hu).obj :=
  presentationDescendedUnit (d.spacePresentation Px hP) κ hc hu ν hbt hbs
    (d.spacePresentation_unit_transition Px hP κ ν
      ((d.transitionUnitCompat_iff Px hP κ ν).1 hm))

/-- The inverse image along the atlas of
`AlgebraicGeometry.Space.RelativeProjPoints.spacePresentationDescendedUnit` is the attached
morphism out of the structure sheaf. -/
theorem spacePresentationDescendedUnit_spec :
    (modulePullback B S hS (presentationAtlas (d.spacePresentation Px hP))).map
        (d.spacePresentationDescendedUnit Px hP κ ν hc hu hbt hbs hm) ≫
        (presentationDescendedModuleChartIso (d.spacePresentation Px hP) K κ hc hu).hom =
      (modulePullbackUnitIso B S hS (presentationAtlas (d.spacePresentation Px hP))).hom ≫
        representedUnitChartHom B S hS ν :=
  presentationDescendedUnit_spec (d.spacePresentation Px hP) κ hc hu ν hbt hbs
    (d.spacePresentation_unit_transition Px hP κ ν hm)

include hbt hbs hm in
/-- **The descended unit on the presentation `P = P_U/P_R` is unique**: it is the only morphism
out of the structure sheaf whose inverse image along the atlas is the attached morphism. -/
theorem spacePresentationDescendedUnit_existsUnique :
    ∃! ψ : SheafOfModules.unit (structureRingSheaf B S hS ⟨P, hP⟩) ⟶
        (presentationDescendedModule (d.spacePresentation Px hP) K κ hc hu).obj,
      (modulePullback B S hS (presentationAtlas (d.spacePresentation Px hP))).map ψ ≫
          (presentationDescendedModuleChartIso (d.spacePresentation Px hP) K κ hc hu).hom =
        (modulePullbackUnitIso B S hS (presentationAtlas (d.spacePresentation Px hP))).hom ≫
          representedUnitChartHom B S hS ν :=
  ⟨d.spacePresentationDescendedUnit Px hP κ ν hc hu hbt hbs hm,
    d.spacePresentationDescendedUnit_spec Px hP κ ν hc hu hbt hbs hm,
    fun ψ hψ => presentationDescendedUnit_unique (d.spacePresentation Px hP) κ hc hu ν hbt hbs
      (d.spacePresentation_unit_transition Px hP κ ν hm) ψ hψ⟩

end Descent

end RelativeProjPoints

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-- **The unit of the twists on the scheme of a base change**: for an object `V` of the site and
`v : V ⟶ X`, the unit `𝒪 ⟶ 𝒪(0)` of Tag 01NR's `⨁_n 𝒪(n)` on `Proj_V(v^*𝒜)`, read on the scheme
of `V ×_X P` through `AlgebraicGeometry.Space.RelativeProjSituation.toRelativeProj`, as a
morphism of quasi-coherent modules. -/
def twistPieceUnit (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) :
    quasicoherentUnitObj s.site s.base s.containsBase (s.relativeProjPoints.fibre V v) ⟶
      s.twistPieceQcoh V v 0 :=
  ObjectProperty.homMk (SheafOfModules.GradedAlgebra.oneHom
    (pbAlgS (s.toRelativeProj V v) (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra V v))))

/-- **The comparisons of the twists carry the unit to the unit.**  Along a morphism
`y : V ×_X P ⟶ U ×_X P` lying over `k : V ⟶ U`, the comparison `y^*𝒪(0) ≅ 𝒪(0)` carries the
unit of the twists of `U ×_X P`, pulled back along `y` and read through Stacks 03LU, to the unit
of the twists of `V ×_X P`. -/
theorem twistPieceComparison_unit {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v)
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : s.relativeProjPoints.LiesOver y k) :
    (quasicoherentPullbackUnitIso s.site s.base s.containsBase y).inv ≫
        quasicoherentPullbackMap s.site s.base s.containsBase y (s.twistPieceUnit U u) ≫
        (s.twistPieceComparison k hv y hy 0).hom =
      s.twistPieceUnit V v := by
  refine ObjectProperty.hom_ext _ ?_
  refine Eq.trans ?_ (pullbackIsoOfSquare_hom_one
    (X := (relativeProj (s.shrink.pointAlgebra U u)).scheme)
    (Y := (relativeProj (s.shrink.pointAlgebra V v)).scheme)
    (s.toRelativeProj U u) (s.toRelativeProj V v)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y) (s.map_comp_toRelativeProj y)
    (s.pointTwistComparison k u v hv ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
      (s.toScheme_map_eq_of_liesOver hv hy)))
  exact congrArg (fun t => (Scheme.Modules.pullbackUnitIso
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)).inv ≫
    (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)).map
      (s.twistPieceUnit U u).hom ≫ t)
    ((s.twistPieceComparison_hom_hom k hv y hy 0).trans (pullbackSheafIsoOfSquare_hom _ _ _ _ _ _))

section Presentation

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **The transition of `𝒪(0)` carries the unit to the unit**: it carries the unit of the twists,
pulled back along the target projection and read through Stacks 03LU, to the unit pulled back
along the source projection. -/
theorem twistTransition_unit :
    (quasicoherentPullbackUnitIso s.site s.base s.containsBase
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)).inv ≫
      quasicoherentPullbackMap s.site s.base s.containsBase
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceUnit Px.U Px.toSpace) ≫ s.twistTransition Px 0 =
    (quasicoherentPullbackUnitIso s.site s.base s.containsBase
        (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)).inv ≫
      quasicoherentPullbackMap s.site s.base s.containsBase
        (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceUnit Px.U Px.toSpace) :=
  (transition_unit_of_comparisons _ _ _ _ _ _ _ _ (Iso.refl _)
    (s.twistPieceComparison_unit (u := Px.toSpace) (v := RelativeProjPoints.relationPoint Px)
      Px.target rfl (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor))
    (s.twistPieceComparison_unit (u := Px.toSpace) (v := RelativeProjPoints.relationPoint Px)
      Px.source (s.map_source_comp_toSpace Px)
      (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceSource Px s.isAlgebraicSpace_relativeProjFunctor))
    (Category.id_comp _)).trans (Category.id_comp _)

/-- `AlgebraicGeometry.Space.RelativeProjSituation.twistTransition_unit` as the named
proposition `AlgebraicGeometry.Space.RelativeProjPoints.TransitionUnitCompat`. -/
theorem transitionUnitCompat_twistTransition :
    s.relativeProjPoints.TransitionUnitCompat Px s.isAlgebraicSpace_relativeProjFunctor
      (s.twistTransition Px 0) (s.twistPieceUnit Px.U Px.toSpace) :=
  (s.relativeProjPoints.transitionUnitCompat_iff Px s.isAlgebraicSpace_relativeProjFunctor
    (s.twistTransition Px 0) (s.twistPieceUnit Px.U Px.toSpace)).2 (s.twistTransition_unit Px)

/-- **The unit of the twists of the relative Proj exists and is unique** (Stacks 084D): there is
exactly one morphism `𝒪_P ⟶ 𝒪_P(0)` whose inverse image along the atlas of the presentation
`P = P_U/P_R` is the unit of the twists of Stacks 01NR on the scheme of `P_U`, through
Stacks 03LU and the chart identification of `𝒪_P(0)`.  Its hypothesis is the compatibility of the
identification of Stacks 03DX (2) of the structure sheaf with inverse images along morphisms of
the site. -/
theorem existsUnique_twistModuleUnit
    (hbu : ∀ {V U : BigFppfOver s.site s.base s.containsBase} (g : V ⟶ U),
      RepresentedC3UnitCompat s.site s.base s.containsBase g) :
    type_of% (s.relativeProjPoints.spacePresentationDescendedUnit_existsUnique Px
      s.isAlgebraicSpace_relativeProjFunctor (s.twistTransition Px 0)
      (s.twistPieceUnit Px.U Px.toSpace)
      (s.presentationSchemeCocycle_twistTransition Px 0)
      (s.presentationSchemeUnit_twistTransition Px 0)
      (hbu _) (hbu _) (s.transitionUnitCompat_twistTransition Px)) :=
  s.relativeProjPoints.spacePresentationDescendedUnit_existsUnique Px
    s.isAlgebraicSpace_relativeProjFunctor (s.twistTransition Px 0)
    (s.twistPieceUnit Px.U Px.toSpace)
    (s.presentationSchemeCocycle_twistTransition Px 0)
    (s.presentationSchemeUnit_twistTransition Px 0)
    (hbu _) (hbu _) (s.transitionUnitCompat_twistTransition Px)

/-- **The unit of the twists of the relative Proj** (Stacks 084D): `𝒪_P ⟶ 𝒪_P(0)`, the descent
along the presentation `P = P_U/P_R` of the unit of the twists of Stacks 01NR on the scheme of
`P_U` (`AlgebraicGeometry.Space.RelativeProjPoints.spacePresentationDescendedUnit`).  Its
hypothesis is the compatibility of the identification of Stacks 03DX (2) of the structure sheaf
with inverse images along morphisms of the site. -/
def twistModuleUnit
    (hbu : ∀ {V U : BigFppfOver s.site s.base s.containsBase} (g : V ⟶ U),
      RepresentedC3UnitCompat s.site s.base s.containsBase g) :
    SheafOfModules.unit (structureRingSheaf s.site s.base s.containsBase
        ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩) ⟶
      (s.twistModule Px 0).obj :=
  s.relativeProjPoints.spacePresentationDescendedUnit Px s.isAlgebraicSpace_relativeProjFunctor
    (s.twistTransition Px 0) (s.twistPieceUnit Px.U Px.toSpace)
    (s.presentationSchemeCocycle_twistTransition Px 0)
    (s.presentationSchemeUnit_twistTransition Px 0)
    (hbu _) (hbu _) (s.transitionUnitCompat_twistTransition Px)

/-- **The inverse image along the atlas of the unit of the twists is the unit of the twists of
Stacks 01NR on the scheme of `P_U`**, through Stacks 03LU and the chart identification of
`𝒪_P(0)`.  The twist is spelled as the descended module it is by definition. -/
theorem twistModuleUnit_spec
    (hbu : ∀ {V U : BigFppfOver s.site s.base s.containsBase} (g : V ⟶ U),
      RepresentedC3UnitCompat s.site s.base s.containsBase g) :
    (modulePullback s.site s.base s.containsBase (presentationAtlas
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))).map
        (s.twistModuleUnit Px hbu) ≫
        (presentationDescendedModuleChartIso
          (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
          (s.twistPieceQcoh Px.U Px.toSpace 0) (s.twistTransition Px 0)
          (s.presentationSchemeCocycle_twistTransition Px 0)
          (s.presentationSchemeUnit_twistTransition Px 0)).hom =
      (modulePullbackUnitIso s.site s.base s.containsBase (presentationAtlas
          (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))).hom ≫
        representedUnitChartHom s.site s.base s.containsBase
          (s.twistPieceUnit Px.U Px.toSpace) :=
  s.relativeProjPoints.spacePresentationDescendedUnit_spec Px
    s.isAlgebraicSpace_relativeProjFunctor (s.twistTransition Px 0)
    (s.twistPieceUnit Px.U Px.toSpace)
    (s.presentationSchemeCocycle_twistTransition Px 0)
    (s.presentationSchemeUnit_twistTransition Px 0)
    (hbu _) (hbu _) (s.transitionUnitCompat_twistTransition Px)

end Presentation

end RelativeProjSituation

end AlgebraicGeometry.Space

end
