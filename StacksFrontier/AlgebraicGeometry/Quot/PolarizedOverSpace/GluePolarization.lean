module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.GlueModuleReading
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.RepresentedPolarizedThetaFull
public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.InvertibleDescent
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistedCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange

/-!
# The descended module of Stacks 0E94 is a polarization

Let `G` be a functor over the site from the points of `T` to
`AlgebraicGeometry.PolarizedOverSpace.RepresentedPolarized`, `X ⟶ T` the algebraic space glued
from its families (Stacks 0E93) and `L` the module on `X` descended from the module of `G` at the
atlas of `T` (`AlgebraicGeometry.PolarizedOverSpace.glueModule`, Stacks 04W8). Then `L` is a
polarization of `X/T`:

* `L` is invertible: its inverse image along the étale covering `Z₀ ⟶ X` is the module `M₀` of
  `G` at the atlas, which is invertible on the small étale site of `Z₀` because its restriction
  to the Zariski site is (it is the associated module of that restriction, `M₀` being
  quasi-coherent), and invertibility descends along fpqc coverings
  (`AlgebraicGeometry.Space.isInvertibleModule_of_pullback_isFpqcCovering`).
* `L` is ample on `X/T` (Stacks 0D31): `X ⟶ T` is representable, its base change along a point
  `(U, t)` of `T` being the family `Z_{(U,t)}` of `G`; a cartesian square of a scheme `U'` over
  `X` and `U` identifies `U'` with `Z_{(U,t)}`, and along this isomorphism the restriction of `L`
  to `U'` is the restriction of the module `M_{(U,t)}` of `G`, by `σ : M_{(U,t)} ≅ s^* L`
  (`AlgebraicGeometry.PolarizedOverSpace.glueSigma`), which is invertible and ample on
  `Z_{(U,t)} / U` because `G(U,t)` is polarized; ampleness is carried along the isomorphism by
  Stacks 0893. This is the descent of relative ampleness the hint of Stacks 0E94 refers to
  (Stacks 0D3C), read directly on the definition of relative ampleness.

## Main results

* `AlgebraicGeometry.PolarizedOverSpace.isInvertibleModule_glueModule`: `L` is invertible.
* `AlgebraicGeometry.PolarizedOverSpace.isRelativelyAmple_glueModule`: `L` is ample on `X/T`.
* `AlgebraicGeometry.PolarizedOverSpace.gluePolarized`: `(X ⟶ T, L)` as an object of the
  left-hand side of Stacks 0E94.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.PolarizedOverSpace

attribute [local implicit_reducible] Stack.fibredCategory BasedCategory.ofFunctor schemeSpace
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete typeToGrpd Grpd.forgetToCat
  MorphismProperty

attribute [local irreducible] Space.modulePullback Space.modulePullbackCompIso
  Scheme.Modules.pullback Space.representedSmallEtaleModuleEquivalence SmallEtale.restrictModule

variable {B : BigFppfSite.{u}}

/-- **A quasi-coherent module on the small étale site of a scheme whose restriction to the
Zariski site is invertible is invertible**: it is the module associated with that restriction. -/
theorem isInvertibleModule_of_isRepresentedPolarized (X : RepresentedPolarizedObj B) :
    Space.IsInvertibleModule (schemeSpace X.obj.base.left : AlgebraicSpaces B integerBase (hZ B))
      X.obj.fiber := by
  have hR := Space.isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule
    B integerBase (hZ B) X.obj.base.left (zariskiPolarization B X.obj)
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ X.property.invertible)
  have := isIso_zariskiCounit (A := X.obj.base) X.obj.fiber X.property.quasicoherent
  exact Space.isInvertibleModule_of_iso
    ((Space.representedSmallEtaleModuleEquivalence B integerBase (hZ B)
        X.obj.base.left).functor.mapIso
      (asIso ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B integerBase (hZ B)).obj X.obj.base.left)
        X.obj.base.left.left.property).counit.app ((etaleInverse X.obj.base).obj X.obj.fiber))) ≪≫
      (Space.representedSmallEtaleModuleEquivalence B integerBase (hZ B)
        X.obj.base.left).counitIso.app X.obj.fiber) hR

variable {T : AlgebraicSpaces B integerBase (hZ B)}
  (G : Points T ⥤ᵇ BasedCategory.ofFunctor (representedPolarizedProjection B))

/-- **The descended module is invertible**: its inverse image along the étale covering `Z₀ ⟶ X`
is the invertible module of `G` at the atlas (Stacks 04W8 with invertibility, as in Stacks
04WN). -/
theorem isInvertibleModule_glueModule : Space.IsInvertibleModule (glueTotal G) (glueModule G) :=
  Space.isInvertibleModule_of_pullback_isFpqcCovering B integerBase (hZ B)
    (fun _ : Unit => chartMap G (atlasPoint T))
    (Space.isFpqcCovering_of_isEtaleCovering B integerBase (hZ B) _ _
      (isEtaleCovering_famToGlue_atlasPoint (glueFamilies G)))
    (glueModule G) (isQuasicoherentOnSite_glueModule G)
    (fun _ => Space.isInvertibleModule_of_iso (glueModuleIso G)
      (isInvertibleModule_of_isRepresentedPolarized (G.obj (atlasPoint T)).obj))

/-- **The projection of the glued space to `T` is representable**: its base change along a point
`(U, t)` of `T` is the family of `G` at that point (Stacks 0E93). -/
theorem relativelyRepresentable_glueToBase :
    yoneda.relativelyRepresentable (SpacesOverSpace.glueSpaceMap (glueFamilies G)).hom := by
  intro U g
  refine ⟨(G.obj (SpacesOverSpace.pt U (yonedaEquiv g))).obj.obj.base.left,
    (G.obj (SpacesOverSpace.pt U (yonedaEquiv g))).obj.obj.base.hom ≫
      eqToHom (SpacesOverSpace.fam_right (glueFamilies G) (SpacesOverSpace.pt U (yonedaEquiv g))),
    SpacesOverSpace.famToGlue (glueFamilies G) (SpacesOverSpace.pt U (yonedaEquiv g)), ?_⟩
  rw [Functor.map_comp]
  exact (SpacesOverSpace.isPullback_famToGlue_yoneda (glueFamilies G) g).flip

/-- **The restriction of `L` to a scheme `U'` cartesian over a point `(U, t)` of `T` is invertible
and ample on `U' / U`**: `U'` is the family `Z` of `G` at `(U, t)`, and the restriction of `L` is
the restriction of the module of `G` there (by `σ`), carried along the isomorphism `U' ≅ Z`
(Stacks 0893). -/
theorem isRelativelyAmple_baseChange_glueModule (U U' : Site B) (g : yoneda.obj U ⟶ T.1)
    (p : yoneda.obj U' ⟶ (glueTotal G).1) (q : U' ⟶ U)
    (hsq : IsPullback p (yoneda.map q) (SpacesOverSpace.glueSpaceMap (glueFamilies G)).hom g) :
    ∃ hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B integerBase (hZ B)).obj U')
        (Space.baseChangeModule B integerBase (hZ B) (glueModule G) U' p),
      @Stacks.RelativeAmple.IsRelativelyAmple _ _ (sch B q)
        (Space.baseChangeModule B integerBase (hZ B) (glueModule G) U' p) hL := by
  let a := SpacesOverSpace.pt U (yonedaEquiv g)
  have hV : (G.obj a).obj.obj.base.right = U := SpacesOverSpace.fam_right (glueFamilies G) a
  have hV' : U = (G.obj a).obj.obj.base.right := hV.symm
  have sq := (SpacesOverSpace.isPullback_famToGlue_yoneda (glueFamilies G) g).flip
  let e := hsq.isoIsPullback _ _ sq
  have he₁ : e.hom ≫ SpacesOverSpace.famToGlue (glueFamilies G) a = p :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  have he₂ : e.hom ≫ SpacesOverSpace.famHom (glueFamilies G) a = yoneda.map q :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  let eU : U' ≅ (G.obj a).obj.obj.base.left := yoneda.preimageIso e
  have hy : yoneda.map eU.hom = e.hom := yoneda.map_preimage _
  have cancel : ∀ {V W : Site B} (h : V = W) {A : (Site B)ᵒᵖ ⥤ Type u} (f : A ⟶ yoneda.obj V),
      (f ≫ yoneda.map (eqToHom h)) ≫ yoneda.map (eqToHom h.symm) = f := by
    intro V W h A f
    subst h
    simp
  have hq : q ≫ eqToHom hV' = eU.hom ≫ (G.obj a).obj.obj.base.hom := by
    apply yoneda.map_injective
    refine ((yoneda.map_comp _ _).trans ((congrArg (· ≫ yoneda.map (eqToHom hV')) he₂.symm).trans
      ((Category.assoc _ _ _).trans (congrArg (e.hom ≫ ·) (cancel hV _))))).trans ?_
    exact (congrArg (· ≫ yoneda.map (G.obj a).obj.obj.base.hom) hy.symm).trans
      (yoneda.map_comp _ _).symm
  have hsch : IsPullback (sch B eU.hom) (sch B q) (sch B (G.obj a).obj.obj.base.hom)
      (sch B (eqToHom hV')) :=
    IsPullback.of_horiz_isIso ⟨by rw [← Functor.map_comp, ← Functor.map_comp, hq]⟩
  have hP := (G.obj a).obj.property
  have hI := hP.invertible
  have hamp := Stacks.AmpleBridge.relativelyAmpleBaseChange hsch
    (zariskiPolarization B (G.obj a).obj.obj) hP.relativelyAmple
  have hk : Space.representedSpaceMap B integerBase (hZ B) eU.hom ≫ chartMap G a =
      (ObjectProperty.homMk p : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B integerBase (hZ B) U'⟩ :
        AlgebraicSpaces B integerBase (hZ B)) ⟶ glueTotal G) :=
    ObjectProperty.hom_ext _
      ((congrArg (· ≫ SpacesOverSpace.famToGlue (glueFamilies G) a) hy).trans he₁)
  let ι : (Scheme.Modules.pullback (sch B eU.hom)).obj (zariskiPolarization B (G.obj a).obj.obj) ≅
      Space.baseChangeModule B integerBase (hZ B) (glueModule G) U' p :=
    Space.representedZariskiModulePullbackIso B integerBase (hZ B) eU.hom
        (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) eU.hom)
        (chartModule G a) hP.quasicoherent ≪≫
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B integerBase (hZ B)).obj U') U'.left.property).mapIso
        ((Space.representedSmallEtaleModuleEquivalence B integerBase (hZ B) U').inverse.mapIso
          ((Space.modulePullback B integerBase (hZ B)
              (Space.representedSpaceMap B integerBase (hZ B) eU.hom)).mapIso (glueSigma G a) ≪≫
            (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) _ _ _ hk
              (glueModule G)).symm)) ≪≫
      (Space.restrictToChartSchemeIdEtaleChartIso B integerBase (hZ B) U' _).symm
  have hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B integerBase (hZ B)).obj U')
      (Space.baseChangeModule B integerBase (hZ B) (glueModule G) U' p) :=
    Stacks.Picard.isInvertible_of_iso ι inferInstance
  exact ⟨hL, (Stacks.RelativeVeryAmple.isRelativelyAmple_congr (sch B q) _ _ ι).mp hamp⟩

/-- **The descended module is ample on `X/T`** (Stacks 0D31, descended as in Stacks 0D3C). -/
theorem isRelativelyAmple_glueModule :
    Space.IsRelativelyAmple B integerBase (hZ B) (SpacesOverSpace.glueSpaceMap (glueFamilies G))
      (glueModule G) :=
  ⟨relativelyRepresentable_glueToBase G, isRelativelyAmple_baseChange_glueModule G⟩

/-- **The descended module is a polarization of the glued space over `T`.** -/
theorem isPolarization_glueModule :
    IsPolarization B T (SpacesOverSpace.glueSpaceMap (glueFamilies G)) (glueModule G) :=
  ⟨isInvertibleModule_glueModule G, isRelativelyAmple_glueModule G⟩

/-- **The polarized family `(X ⟶ T, L)` glued from `G`**, an object of the left-hand side of
Stacks 0E94. -/
def gluePolarized : PolarizedSpacesOver B T :=
  ⟨⟨⟨SpacesOverSpace.glueObject (glueFamilies G), glueModule G⟩, isPolarization_glueModule G⟩⟩

end AlgebraicGeometry.PolarizedOverSpace

end
