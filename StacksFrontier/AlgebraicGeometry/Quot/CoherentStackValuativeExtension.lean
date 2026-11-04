module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackValuativeExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMonomorphismModuleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeFilteredColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionStep
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsDirected

/-!
# Extending a coherent sheaf over a valuation ring (Stacks 0DM0)

Let `f : X ⟶ Y` be proper and of finite presentation, `T` a test scheme over `Y` whose scheme is
the spectrum of a valuation ring `R`, and `T' ⟶ T` the generic point.  The proof of Stacks 0DM0
extends a coherent module on `X_{T'}` to `X_T` by taking a finite type quasi-coherent submodule
of the direct image along the inclusion `j : X_{T'} ⟶ X_T` of the generic fibre.  This file
collects the facts about the geometry of that situation which the construction uses.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isFinitePresentation_projection`: the base change
  `X_T ⟶ T` is of finite presentation.
* `AlgebraicGeometry.Space.CoherentSituation.qcqs_space`: over an affine test scheme, `X_T` is
  quasi-compact and quasi-separated (Stacks 06G5).
* `AlgebraicGeometry.Space.isFlat_baseChangeMap_of_isHomLift`: the inclusion of the generic fibre
  is flat.
* `AlgebraicGeometry.Space.exists_subobject_isIso_modulePullback_comp_counit`: a direct image
  `j_*F'` which is the colimit of its finite type quasi-coherent submodules has one whose inverse
  image is `F'`, when `F'` is of finite type on a quasi-compact space.

## References

* [Stacks Project, Tag 0DM0](https://stacks.math.columbia.edu/tag/0DM0)
* [Stacks Project, Tag 06G5](https://stacks.math.columbia.edu/tag/06G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The base change `X_T ⟶ T` of the standing morphism is the second projection of a cartesian
square over it. -/
theorem CoherentSituation.isPullback_projection (D : CoherentSituation B S hS)
    (T : SchemesOver D.Y) :
    IsPullback (baseChangeProjection D.f T) (D.projection T) D.f T.hom :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom

/-- The projection `X_T ⟶ T` is of finite presentation (Stacks 03XR). -/
theorem CoherentSituation.isFinitePresentation_projection (D : CoherentSituation B S hS)
    (T : SchemesOver D.Y) :
    IsFinitePresentation B S hS (D.projection T).hom :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsFinitePresentation B S hS f.hom)
    (D.isPullback_projection T) D.finitePresentation

/-- **Over an affine test scheme the base change is quasi-compact and quasi-separated**
(Stacks 06G5): it is of finite presentation over an affine scheme. -/
theorem CoherentSituation.qcqs_space (D : CoherentSituation B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) (T : SchemesOver D.Y)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left)) :
    IsQuasiCompactSpace B S hS (D.space T).1 ∧
      IsAbsolutelyQuasiSeparated B S hS hZ (D.space T).1 :=
  qcqs_of_isFinitePresentation B S hS hZ (D.space T).2 (isAlgebraicSpace_yoneda B S hS T.left)
    (isQuasiCompactSpace_yoneda_of_isAffine B S hS T.left hT)
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ ⟨T.left, hT, ⟨Iso.refl _⟩⟩)
    (D.isFinitePresentation_projection T)

/-- **The inclusion of the generic fibre is flat.**  For a flat ring map `R ⟶ A` and a morphism
`h : U ⟶ T` of test schemes over `Y` lying over `Spec A ⟶ Spec R`, the morphism
`X_h : X_U ⟶ X_T` of base changes is flat, as a base change of the flat morphism
`Spec A ⟶ Spec R`. -/
theorem isFlat_baseChangeMap_of_isHomLift {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    {hR : B.Contains (Spec (.of R))} {hA : B.Contains (Spec (.of A))} {b : Spec (.of R) ⟶ S}
    {U T : SchemesOver Y} (h : U ⟶ T)
    (hh : (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).IsHomLift
      (Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
        siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) ⟶
          siteObject B S hS hR b) h) :
    IsFlat B S hS (baseChangeMap f h).hom := by
  let φ : siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) ⟶
      siteObject B S hS hR b :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))))
  have hflat : Flat ((BigFppfOver.toScheme B S hS).map h.left) := by
    have hfac := IsHomLift.fac' (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y) φ h
    show Flat ((BigFppfOver.toScheme B S hS).map
      ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).map h))
    rw [hfac, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.mpr inferInstance
    exact inferInstanceAs (Flat (_ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ _))
  have := isFlat_isStableUnderBaseChange B S hS
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) ↦ IsFlat B S hS k.hom)
    (isPullback_baseChangeMap f h).flip (isFlat_yoneda_map B S hS h.left hflat)

/-- The category of modules on an algebraic space is abelian. -/
private noncomputable instance abelian_modules (Z : AlgebraicSpaces B S hS) :
    Abelian (Modules.{u, u} B S hS Z.1 Z.2) :=
  SheafOfModules.instAbelian.{u, u, u, u + 1}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))

/-- The category of modules on an algebraic space is Grothendieck abelian. -/
private theorem isGrothendieckAbelian_modules (Z : AlgebraicSpaces B S hS) :
    IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS Z.1 Z.2) :=
  have : EssentiallySmall.{u} (smallEtaleRingedSite B S hS Z.1 Z.2).C :=
    inferInstanceAs (EssentiallySmall.{u} (SmallEtale B S hS Z.1))
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _

/-- **A finite type submodule of a direct image whose inverse image is everything.**  Let
`j : X' ⟶ X` be a morphism of algebraic spaces with `X'` quasi-compact and `j^*` preserving
monomorphisms, let `F'` be an `𝒪_{X'}`-module of finite type, and suppose that the counit
`j^*j_*F' ⟶ F'` is an isomorphism and that `j_*F'` is the colimit of its finite type
quasi-coherent submodules, `j_*F'` being quasi-coherent.  Then some finite type quasi-coherent
submodule `G ⊆ j_*F'` has `j^*G ⟶ j^*j_*F' ⟶ F'` an isomorphism.

The inverse images of the finite type quasi-coherent submodules form a filtered system of
submodules of `j^*j_*F' ≅ F'` with colimit `F'`, the inverse image being a left adjoint; since
`F'` is of finite type over a quasi-compact space, one stage is already everything. -/
theorem exists_subobject_isIso_modulePullback_comp_counit {X' X : AlgebraicSpaces B S hS}
    (j : X' ⟶ X) (hX'qc : IsQuasiCompactSpace B S hS X'.1)
    (hmono : (modulePullback B S hS j).PreservesMonomorphisms)
    (F' : Modules.{u, u} B S hS X'.1 X'.2) (hF' : F'.IsFiniteType)
    (hcounit : IsIso ((modulePullbackAdjunction B S hS j).counit.app F'))
    (hH : ((modulePushforward B S hS j).obj F').IsQuasicoherentOnSite)
    (hcol : Nonempty (IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS X.1 X.2
      ((modulePushforward B S hS j).obj F')))) :
    ∃ G : Subobject ((modulePushforward B S hS j).obj F'),
      (G : Modules.{u, u} B S hS X.1 X.2).IsQuasicoherentOnSite ∧
      (G : Modules.{u, u} B S hS X.1 X.2).IsFiniteType ∧
      IsIso ((modulePullback B S hS j).map G.arrow ≫
        (modulePullbackAdjunction B S hS j).counit.app F') := by
  classical
  have := isGrothendieckAbelian_modules (B := B) (S := S) (hS := hS) X
  have := isGrothendieckAbelian_modules (B := B) (S := S) (hS := hS) X'
  set H := (modulePushforward B S hS j).obj F'
  set L := modulePullback B S hS j
  have hLcol : PreservesColimitsOfSize.{u, u} L :=
    (modulePullbackAdjunction B S hS j).leftAdjoint_preservesColimits
  have hsmall : Small.{u} (FiniteTypeQuasicoherentSubobject B S hS X.1 X.2 H) :=
    small_of_injective (f := fun T => T.obj)
      (fun a b h => by cases a; cases b; subst h; rfl)
  set eqv := (equivSmallModel.{u} (FiniteTypeQuasicoherentSubobject B S hS X.1 X.2 H)).symm
  have hfil : IsFiltered (FiniteTypeQuasicoherentSubobject B S hS X.1 X.2 H) :=
    have := hH
    isFiltered_finiteTypeQuasicoherentSubobject B S hS X.1 X.2 H
  have hfil' : IsFiltered (SmallModel.{u} (FiniteTypeQuasicoherentSubobject B S hS X.1 X.2 H)) :=
    IsFiltered.of_equivalence
      (equivSmallModel.{u} (FiniteTypeQuasicoherentSubobject B S hS X.1 X.2 H))
  set D' := eqv.functor ⋙ finiteTypeQuasicoherentSubobjectFunctor B S hS X.1 X.2 H
  set c' := (finiteTypeQuasicoherentSubobjectCocone B S hS X.1 X.2 H).whisker eqv.functor
  have hc'col : IsColimit c' := hcol.some.whiskerEquivalence eqv
  have hιmono : ∀ i, Mono (c'.ι.app i) := fun i =>
    inferInstanceAs (Mono (eqv.functor.obj i).obj.arrow)
  have hLDmono : ∀ {i i' : SmallModel.{u} (FiniteTypeQuasicoherentSubobject B S hS X.1 X.2 H)}
      (f : i ⟶ i'), Mono ((D' ⋙ L).map f) := by
    intro i i' f
    have := hιmono i
    have : Mono (D'.map f) := mono_of_mono_fac (c'.w f)
    exact hmono.preserves (D'.map f)
  have hLHft : (L.obj H).IsFiniteType :=
    isFiniteType_of_iso' B S hS
      (asIso ((modulePullbackAdjunction B S hS j).counit.app F')).symm hF'
  obtain ⟨i, hi⟩ := exists_isIso_ι_of_isFiniteType_of_isQuasiCompactSpace B S hS
    (U := X') hX'qc (D' ⋙ L) (L.mapCocone c') (isColimitOfPreserves L hc'col) hLDmono hLHft
  refine ⟨(eqv.functor.obj i).obj, (eqv.functor.obj i).property.1,
    (eqv.functor.obj i).property.2, ?_⟩
  have hi' : IsIso (L.map (eqv.functor.obj i).obj.arrow) := hi
  infer_instance

end AlgebraicGeometry.Space

end
