module

public import StacksFrontier.Deformation.RingedSpaceThickening.CompatibleThickeningMorphism
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentPullbackMap

/-!
# The presentation along a compatible morphism of thickenings

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be morphisms of ringed spaces, let
`𝒪_{X'}` be a square-zero extension of `f⁻¹𝒪_S`-algebras of `𝒪_X` by `ℱ`, let `𝒪_{Y'}` be one of
`(g ∘ f)⁻¹𝒪_S`-algebras of `𝒪_Y` by `𝒢`, and let `c : ℱ ⟶ g_*𝒢` be a `g`-map. Present `𝒪_X` by
the sheaf of sets underlying `𝒪_{X'}` and `𝒪_Y` by the one underlying `𝒪_{Y'}`, as in Stacks
0GQ0. An `S`-morphism `Y' ⟶ X'` compatible with `g` and `c`, given by its comorphism
`h : 𝒪_{X'} ⟶ g_*𝒪_{Y'}`, is a morphism of families of generators along `g`, and so induces a
chain map `𝖭𝖫(α_X) ⟶ g_*𝖭𝖫(α_Y)`. This chain map lies over the canonical map
`𝖭𝖫_{X/S} ⟶ g_*𝖭𝖫_{Y/S}`, and it carries the homomorphism `𝒥_Y/𝒥_Y² ⟶ 𝒢` of `𝒪_{Y'}` to `c`
composed with the homomorphism `𝒥_X/𝒥_X² ⟶ ℱ` of `𝒪_{X'}`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.CompatibleMorphism.presentationPushMap`: the chain map
  `𝖭𝖫(α_X) ⟶ g_*𝖭𝖫(α_Y)` of a compatible morphism.

## Main results

* `CompatibleMorphism.presentationPushMap_comp_comparison`: it lies over
  `naiveCotangentPushMap g f`.
* `CompatibleMorphism.conormalPushMap_comp_conormalToIdeal`: the homomorphism of `𝒪_{Y'}` pulled
  back along it is `c` after the homomorphism of `𝒪_{X'}`.

## References

* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1)
* [Stacks Project, Tag 0GQ0](https://stacks.math.columbia.edu/tag/0GQ0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf freeAlgebraSheafDesc
  freeAlgebraSheafVariable freeAlgebraSheafCoefficientMap)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S Y : RingedSpace.{u, u}} {f : X ⟶ S} {g : Y ⟶ X}
  {F : SheafOfModules.{u} (structureSheafRing X)} {G : SheafOfModules.{u} (structureSheafRing Y)}
  {P : SquareZeroAlgebraExtension f F} {Q : SquareZeroAlgebraExtension (g ≫ f) G}
  {c : F ⟶ (modulePushforward g).obj G}

namespace CompatibleMorphism

/-- The presentation of `𝒪_X` by the sheaf of sets underlying `𝒪_{X'}` is locally surjective. -/
instance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (Stacks.SheafOfModules.presentation (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) X.sheaf (structureRingMap f) P.generators P.generatorsMap).hom :=
  P.toAlgebraSquareZeroExtension.presentation_isLocallySurjective

/-- The presentation of `𝒪_Y` by the sheaf of sets underlying `𝒪_{Y'}` is locally surjective. -/
instance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y.carrier)
    (Stacks.SheafOfModules.presentation (Opens.grothendieckTopology Y.carrier)
      (inverseImageBaseRing (g ≫ f)) Y.sheaf (structureRingMap (g ≫ f)) Q.generators
      Q.generatorsMap).hom :=
  Q.toAlgebraSquareZeroExtension.presentation_isLocallySurjective

variable (h : CompatibleMorphism P Q c)

/-- The comorphism of a compatible morphism, read on the sheaves of sets underlying `𝒪_{X'}` and
`𝒪_{Y'}`. -/
abbrev generatorsMap : P.generators ⟶ (Opens.map g.hom.base).op ⋙ Q.generators :=
  Functor.whiskerRight h.hom.hom (forget CommRingCat.{u})

/-- The comorphism lies over `g^♯` on generators. -/
theorem generatorsMap_comp :
    h.generatorsMap ≫ Functor.whiskerLeft (Opens.map g.hom.base).op Q.generatorsMap =
      P.generatorsMap ≫ Functor.whiskerRight (structureComorphism g).hom
        (forget CommRingCat.{u}) :=
  (Functor.whiskerRight_comp h.hom.hom ((TopCat.Sheaf.pushforward CommRingCat.{u}
      g.hom.base).map Q.reduction).hom (forget CommRingCat.{u})).symm.trans
    ((congrArg (fun t : P.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj
        Y.sheaf ↦ Functor.whiskerRight t.hom (forget CommRingCat.{u})) h.reduction_comm).trans
      (Functor.whiskerRight_comp _ _ _))

/-- **The chain map `𝖭𝖫(α_X) ⟶ g_*𝖭𝖫(α_Y)` of a compatible morphism.** -/
def presentationPushMap :
    PresentedSquareZeroExtension.presentationComplex f P.generators P.generatorsMap ⟶
      ((SheafOfModules.pushforward.{u} (Stacks.Sites.Conormal.pushforwardRingHom g.hom.base
        (structureComorphism g))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (PresentedSquareZeroExtension.presentationComplex (g ≫ f) Q.generators
            Q.generatorsMap) :=
  Stacks.SheafOfModules.presentationNaiveCotangentPushMap g.hom.base
    (structureRingMap_comp_structureComorphism g f) h.generatorsMap_comp

omit h in
variable (P) in
/-- The comparison `𝖭𝖫(α_X) ⟶ 𝖭𝖫_{X/S}` of the presentation of `𝒪_X` by `𝒪_{X'}`
(Stacks 08TL). -/
abbrev comparisonX :
    PresentedSquareZeroExtension.presentationComplex f P.generators P.generatorsMap ⟶
      PresentedSquareZeroExtension.relativeComplex f :=
  Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
    (structureRingMap f) P.generators P.generatorsMap

omit h in
variable (Q) in
/-- The comparison `𝖭𝖫(α_Y) ⟶ 𝖭𝖫_{Y/S}` of the presentation of `𝒪_Y` by `𝒪_{Y'}`. -/
abbrev comparisonY :
    PresentedSquareZeroExtension.presentationComplex (g ≫ f) Q.generators Q.generatorsMap ⟶
      PresentedSquareZeroExtension.relativeComplex (g ≫ f) :=
  Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
    (structureRingMap (g ≫ f)) Q.generators Q.generatorsMap

/-- **The chain map of a compatible morphism lies over the canonical map**
`𝖭𝖫_{X/S} ⟶ g_*𝖭𝖫_{Y/S}`. -/
theorem presentationPushMap_comp_comparison :
    h.presentationPushMap ≫ ((SheafOfModules.pushforward.{u}
        (Stacks.Sites.Conormal.pushforwardRingHom g.hom.base
          (structureComorphism g))).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (comparisonY Q) = comparisonX P ≫ naiveCotangentPushMap g f :=
  let : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (Stacks.SheafOfModules.presentation (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing f) X.sheaf (structureRingMap f) (X.sheaf.obj ⋙ forget CommRingCat)
        (𝟙 _)).hom :=
    Stacks.SheafOfModules.presentation_id_isLocallySurjective _ _ _ _
  let : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y.carrier)
      (Stacks.SheafOfModules.presentation (Opens.grothendieckTopology Y.carrier)
        (inverseImageBaseRing (g ≫ f)) Y.sheaf (structureRingMap (g ≫ f))
        (Y.sheaf.obj ⋙ forget CommRingCat) (𝟙 _)).hom :=
    Stacks.SheafOfModules.presentation_id_isLocallySurjective _ _ _ _
  Stacks.SheafOfModules.presentationNaiveCotangentPushMap_naturality g.hom.base P.generatorsMap
    Q.generatorsMap h.generatorsMap_comp (Category.comp_id _) (Category.comp_id _)
    (structureRingMap_comp_structureComorphism g f) h.generatorsMap_comp
    (underlyingPresheafMap_comp g)

/-- **The comorphism is a morphism of algebras over the bases**: `f⁻¹𝒪_S ⟶ 𝒪_{X'} ⟶ g_*𝒪_{Y'}`
is `f⁻¹𝒪_S ⟶ g_*(g ∘ f)⁻¹𝒪_S ⟶ g_*𝒪_{Y'}`. -/
theorem base_comp_hom :
    P.base ≫ h.hom = baseRingPushMap g f ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map Q.base := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv _
    _).injective
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    f.hom.base).homEquiv_naturality_right _ _).trans ?_
  refine h.base_comm.trans ?_
  refine Eq.trans ?_ ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    f.hom.base).homEquiv_naturality_right _ _).symm
  refine Eq.trans ?_ (congrArg (· ≫ _) (homEquiv_baseRingPushMap g f).symm)
  exact (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (g ≫ f).hom.base).homEquiv_unit _ _ _

/-- **The morphism of presentations followed by the lift of `𝒪_{Y'}` is the lift of `𝒪_{X'}`
followed by the comorphism.** -/
theorem freeAlgebraPushMap_comp_lift :
    Stacks.SheafOfModules.freeAlgebraPushMap g.hom.base (inverseImageBaseRing f) P.generators
        (inverseImageBaseRing (g ≫ f)) Q.generators (baseRingPushMap g f) h.generatorsMap ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map Q.lift =
    P.lift ≫ h.hom := by
  refine Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext _ _ _ _ ?_ ?_
  · refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _)
      (Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraPushMap
        g.hom.base _ _ _ _ _ _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (baseRingPushMap g f ≫ ·) ((Functor.map_comp _ _ _).symm.trans
      (congrArg _ (Stacks.Sites.FreeAlgebra.canonicalPresentation_comp_coefficientMap
        (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Q.sheaf
        Q.base)))).trans ?_
    refine (h.base_comp_hom).symm.trans ?_
    refine (congrArg (· ≫ h.hom) (Stacks.Sites.FreeAlgebra.canonicalPresentation_comp_coefficientMap
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) P.sheaf P.base).symm).trans ?_
    exact Category.assoc _ _ _
  · have h1 : Functor.whiskerRight ((sheafToPresheaf (Opens.grothendieckTopology X.carrier)
          CommRingCat.{u}).map (Stacks.SheafOfModules.freeAlgebraPushMap g.hom.base
            (inverseImageBaseRing f) P.generators (inverseImageBaseRing (g ≫ f)) Q.generators
            (baseRingPushMap g f) h.generatorsMap ≫
          (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map Q.lift))
          (forget CommRingCat.{u}) =
        Functor.whiskerRight ((sheafToPresheaf (Opens.grothendieckTopology X.carrier)
          CommRingCat.{u}).map (Stacks.SheafOfModules.freeAlgebraPushMap g.hom.base
            (inverseImageBaseRing f) P.generators (inverseImageBaseRing (g ≫ f)) Q.generators
            (baseRingPushMap g f) h.generatorsMap)) (forget CommRingCat.{u}) ≫
        Functor.whiskerLeft (Opens.map g.hom.base).op (Functor.whiskerRight
          ((sheafToPresheaf (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}).map Q.lift)
          (forget CommRingCat.{u})) := rfl
    have h2 : Functor.whiskerRight ((sheafToPresheaf (Opens.grothendieckTopology X.carrier)
          CommRingCat.{u}).map (P.lift ≫ h.hom)) (forget CommRingCat.{u}) =
        Functor.whiskerRight ((sheafToPresheaf (Opens.grothendieckTopology X.carrier)
          CommRingCat.{u}).map P.lift) (forget CommRingCat.{u}) ≫ h.generatorsMap := rfl
    rw [h1, h2]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) (Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraPushMap
      g.hom.base _ _ _ _ _ _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (h.generatorsMap ≫ ·) ((Functor.whiskerLeft_comp _ _ _).symm.trans
      (congrArg _ (Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_canonicalPresentation
        (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Q.sheaf
        Q.base)))).trans ?_
    refine (Category.comp_id _).trans ?_
    refine (Category.id_comp _).symm.trans ?_
    exact congrArg (· ≫ h.generatorsMap)
      (Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_canonicalPresentation
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) P.sheaf P.base).symm

/-- **The homomorphism of `𝒪_{Y'}` pulled back along a compatible morphism is `c` after the
homomorphism of `𝒪_{X'}`**: on `𝒥_X/𝒥_X²` the map of conormal sheaves followed by
`𝒥_Y/𝒥_Y² ⟶ 𝒢` is `𝒥_X/𝒥_X² ⟶ ℱ` followed by `c`. -/
theorem conormalPushMap_comp_conormalToIdeal :
    Stacks.SheafOfModules.presentationConormalPushMap g.hom.base
        (structureRingMap_comp_structureComorphism g f) h.generatorsMap_comp ≫
      (SheafOfModules.pushforward.{u} (Stacks.Sites.Conormal.pushforwardRingHom g.hom.base
        (structureComorphism g))).map Q.conormalToIdeal =
    P.conormalToIdeal ≫ c := by
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y.carrier)
      Q.presentation.hom := Q.toAlgebraSquareZeroExtension.presentation_isLocallySurjective
  refine Stacks.Sites.Conormal.conormal_hom_ext.{u, u, u, u} P.presentation _ (fun U x ↦ ?_)
  refine (congrArg (((SheafOfModules.pushforward.{u} (Stacks.Sites.Conormal.pushforwardRingHom
      g.hom.base (structureComorphism g))).map Q.conormalToIdeal).val.app U)
    (Stacks.Sites.Conormal.conormalSheafMapPush_toAssociatedModule g.hom.base _ _ _ _ _ _ _ U
      _)).trans ?_
  refine (Stacks.Sites.Conormal.conormalDesc_toAssociatedModule.{u, u, u, u} Q.presentation G
    Q.idealRestriction _ _).trans ?_
  refine Eq.trans ?_ (congrArg (c.val.app U)
    (Stacks.Sites.Conormal.conormalDesc_toAssociatedModule.{u, u, u, u} P.presentation F
      P.idealRestriction U x)).symm
  refine (Q.idealRestriction_app _ _).trans ?_
  refine Eq.trans ?_ (congrArg (c.val.app U) (P.idealRestriction_app U x)).symm
  have hx := congrArg (fun t : _ ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj
      Q.sheaf ↦ (t.hom.app U).hom x.1) h.freeAlgebraPushMap_comp_lift
  have hP := P.incl_ideal U ⟨(P.lift.hom.app U).hom x.1, P.lift_mem_kernelIdeal U x⟩
  have key := (congrArg (h.hom.hom.app U).hom hP.symm).trans
    (h.ideal_comm U.unop (P.ideal.app U ⟨(P.lift.hom.app U).hom x.1,
      P.lift_mem_kernelIdeal U x⟩))
  refine (congrArg (Q.ideal.app ((Opens.map g.hom.base).op.obj U))
    (Subtype.ext (hx.trans key))).trans ?_
  exact Q.ideal_incl _ _

/-- Transposing along an adjunction turns a commuting square of right adjoints into one of left
adjoints. -/
private theorem transpose_comp_eq_of_comp_eq {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {A A' : C} {B B' : D} (u : A ⟶ R.obj B) (a : A ⟶ A')
    (w : A' ⟶ R.obj B') (v : B ⟶ B') (H : u ≫ R.map v = a ≫ w) :
    (adj.homEquiv _ _).symm u ≫ v = L.map a ≫ (adj.homEquiv _ _).symm w := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_left, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  exact H

/-- **The transposed chain map `g^*𝖭𝖫(α_X) ⟶ 𝖭𝖫(α_Y)` of a compatible morphism.** -/
def pullbackPresentationMap :
    ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (show CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ from
          PresentedSquareZeroExtension.presentationComplex f P.generators P.generatorsMap) ⟶
      (show CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ from
          PresentedSquareZeroExtension.presentationComplex (g ≫ f) Q.generators
            Q.generatorsMap) :=
  ((Adjunction.mapHomologicalComplex (modulePullbackPushforwardAdjunction g)
    (ComplexShape.up ℤ)).homEquiv _ _).symm h.presentationPushMap

/-- **The transposed chain map lies over the canonical map** `g^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}`. -/
theorem pullbackPresentationMap_comp_comparison :
    h.pullbackPresentationMap ≫ comparisonY Q =
      ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map (comparisonX P) ≫
        pullbackNaiveCotangentMap g f := by
  exact transpose_comp_eq_of_comp_eq (Adjunction.mapHomologicalComplex
    (modulePullbackPushforwardAdjunction g) (ComplexShape.up ℤ)) _ _ _ _
    h.presentationPushMap_comp_comparison

/-- The transposed map of conormal sheaves `g^*(𝒥_X/𝒥_X²) ⟶ 𝒥_Y/𝒥_Y²` of a compatible
morphism. -/
def pullbackConormalMap :
    (modulePullback g).obj (show SheafOfModules.{u} (structureSheafRing X) from
      (Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf
        (structureRingMap f) P.generators P.generatorsMap).X₁) ⟶
      (show SheafOfModules.{u} (structureSheafRing Y) from
        (Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u}
          (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
          (structureRingMap (g ≫ f)) Q.generators Q.generatorsMap).X₁) :=
  ((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm
    (Stacks.SheafOfModules.presentationConormalPushMap g.hom.base
      (structureRingMap_comp_structureComorphism g f) h.generatorsMap_comp)

/-- **The transposed homomorphism of `𝒪_{Y'}` is `c` after the pulled back homomorphism of
`𝒪_{X'}`**: `g^*(𝒥_X/𝒥_X²) ⟶ 𝒥_Y/𝒥_Y² ⟶ 𝒢` is `g^*(𝒥_X/𝒥_X²) ⟶ g^*ℱ ⟶ 𝒢`, the last map the
adjoint transpose of `c`. -/
theorem pullbackConormalMap_comp_conormalToIdeal :
    h.pullbackConormalMap ≫ Q.conormalToIdeal =
      (modulePullback g).map P.conormalToIdeal ≫
        ((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm c := by
  exact transpose_comp_eq_of_comp_eq (modulePullbackPushforwardAdjunction g) _ _ _ _
    h.conormalPushMap_comp_conormalToIdeal

end CompatibleMorphism

end AlgebraicGeometry.RingedSpaceThickening

end
