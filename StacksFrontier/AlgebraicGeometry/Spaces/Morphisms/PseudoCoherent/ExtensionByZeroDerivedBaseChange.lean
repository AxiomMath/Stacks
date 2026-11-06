module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroHomotopyBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroKFlatResolution
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectHomDescentReduction

/-!
# Derived extension by zero commutes with derived base change

Let

```
T' --u'--> T
|t'        |t
v          v
U  --u-->  Z
```

be a cartesian square of algebraic spaces with `u` étale. For the canonical pseudofunctoriality
datum of derived pullback, the base change map `u'_!(Lt'^*A) ⟶ Lt^*(u_!A)` is an isomorphism for
every object `A` of `D(𝒪_U)`.

Represent `A` by a K-flat complex `K` with flat terms whose extension by zero is again K-flat with
flat terms (`AlgebraicGeometry.Space.exists_quasiIso_isKFlat_extensionByZero`). The derived
pullbacks are then computed degreewise at `K` and at `u_!K` (Stacks 06YY), and read through these
computations the base change map is the degreewise one
(`AlgebraicGeometry.Space.isIso_extensionByZeroBaseChange_canonical_app`), which is invertible
(`AlgebraicGeometry.Space.isIso_extensionByZeroBaseChangeHomotopy_app`).

## Main results

* `isIso_extensionByZeroBaseChange_canonical_app_of_isPullback`: for a cartesian square with `u`
  étale, the base change map `u'_!(Lt'^*A) ⟶ Lt^*(u_!A)` is an isomorphism.
* `RelativeDescentSituation.shiftedHomDescent_canonical_of_restrict_affine`: the reduction of
  Stacks 0DKV to affine situations, for the canonical pseudofunctoriality datum, with the base
  change hypotheses discharged.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ExtensionByZeroDerivedBaseChange :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ExtensionByZeroDerivedBaseChange
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Derived extension by zero commutes with derived base change**: for a cartesian square of
algebraic spaces with `u` étale, the base change map `u'_!(Lt'^*A) ⟶ Lt^*(u_!A)` of the canonical
pseudofunctoriality datum is an isomorphism at every object `A` of `D(𝒪_U)`. -/
theorem isIso_extensionByZeroBaseChange_canonical_app_of_isPullback
    {T T' U W : AlgebraicSpaces B S hS} (u' : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ U) (u : U ⟶ W)
    (sq : IsPullback u' t' t u) (hu : IsEtale B S hS u.hom) (hu' : IsEtale B S hS u'.hom)
    (A : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS U))) :
    IsIso (((DerivedPullbackComposition.canonical B S hS).extensionByZeroBaseChange u' t t' u hu
      hu' sq.w).app A) := by
  obtain ⟨N, hN⟩ := HomotopyCategory.quotient_obj_surjective (DerivedCategory.Qh.objPreimage A)
  obtain ⟨K, g, hg, hK, hEK⟩ := exists_quasiIso_isKFlat_extensionByZero u hu N
  let M := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K
  have : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map g)) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff g).mpr hg)
  let e : DerivedCategory.Qh.obj M ≅ A :=
    asIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map g)) ≪≫
      eqToIso (congrArg DerivedCategory.Qh.obj hN) ≪≫ DerivedCategory.Qh.objObjPreimageIso A
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  have : IsIso ((smallEtaleDerivedModulePullbackComparison' t').app M) :=
    open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom in
    isIso_derivedPullbackComparison_app_isKFlat (smallEtaleRingedToposHom B S hS t') M hK
  have : IsIso ((smallEtaleDerivedModulePullbackComparison' t).app
      (((etaleExtensionByZero B S hS u hu).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) :=
    open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom in
    isIso_derivedPullbackComparison_app_isKFlat (smallEtaleRingedToposHom B S hS t) _ hEK
  have := isIso_extensionByZeroBaseChangeHomotopy_app u' t t' u sq hu hu' M
  exact isIso_extensionByZeroBaseChange_canonical_app u' t t' u hu hu' sq.w M

namespace RelativeDescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)

section Restrict

variable {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU₀ : IsAlgebraicSpace B S hS U₀) (g : U₀ ⟶ D.X₀)
  (hgflat : IsFlat B S hS g) (hgfp : IsFinitePresentation B S hS g)

/-- A stage of the situation restricted along `g` is the base change of the stage along `g`. -/
theorem isPullback_restrictStage (i : D.LaterIndex) :
    IsPullback (D.restrictStage hU₀ g hgflat hgfp i)
      ((D.restrict hU₀ g hgflat hgfp).stageToInitial i) (D.stageToInitial i)
      (D.restrictInitial hU₀ g hgflat hgfp) :=
  IsPullback.flip (IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) (by
    simp only [ObjectProperty.ι_map]
    exact (IsPullback.of_hasPullback (D.toX₀ i.1 i.2) g).flip))

/-- The limit of the situation restricted along `g` is the base change of the limit along `g`. -/
theorem isPullback_restrictLimit :
    IsPullback (D.restrictLimit hU₀ g hgflat hgfp)
      (D.restrict hU₀ g hgflat hgfp).limitToInitial D.limitToInitial
      (D.restrictInitial hU₀ g hgflat hgfp) :=
  IsPullback.flip (IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) (by
    simp only [ObjectProperty.ι_map]
    exact (IsPullback.of_hasPullback D.toInitial g).flip))

variable (hg : IsEtale B S hS g)

include hg in
/-- The base change maps for extension by zero at the stages of a restricted situation are
invertible, for the canonical pseudofunctoriality datum. -/
theorem isIso_stageExtensionByZeroBaseChange_canonical_app (i : D.LaterIndex)
    (A : (D.restrict hU₀ g hgflat hgfp).InitialDerived) :
    IsIso ((D.stageExtensionByZeroBaseChange (DerivedPullbackComposition.canonical B S hS) hU₀ g
      hgflat hgfp hg i).app A) := by
  have e : D.stageExtensionByZeroBaseChange (DerivedPullbackComposition.canonical B S hS) hU₀ g
      hgflat hgfp hg i =
      (DerivedPullbackComposition.canonical B S hS).extensionByZeroBaseChange _ _ _ _ hg
        (D.isEtale_restrictStage hU₀ g hgflat hgfp hg i)
        (D.isPullback_restrictStage hU₀ g hgflat hgfp i).w := rfl
  rw [e]
  exact isIso_extensionByZeroBaseChange_canonical_app_of_isPullback _ _ _ _
    (D.isPullback_restrictStage hU₀ g hgflat hgfp i) hg
    (D.isEtale_restrictStage hU₀ g hgflat hgfp hg i) A

include hg in
/-- The base change map for extension by zero at the limit of a restricted situation is
invertible, for the canonical pseudofunctoriality datum. -/
theorem isIso_limitExtensionByZeroBaseChange_canonical_app
    (A : (D.restrict hU₀ g hgflat hgfp).InitialDerived) :
    IsIso ((D.limitExtensionByZeroBaseChange (DerivedPullbackComposition.canonical B S hS) hU₀ g
      hgflat hgfp hg).app A) := by
  have e : D.limitExtensionByZeroBaseChange (DerivedPullbackComposition.canonical B S hS) hU₀ g
      hgflat hgfp hg =
      (DerivedPullbackComposition.canonical B S hS).extensionByZeroBaseChange _ _ _ _ hg
        (D.isEtale_restrictLimit hU₀ g hgflat hgfp hg)
        (D.isPullback_restrictLimit hU₀ g hgflat hgfp).w := rfl
  rw [e]
  exact isIso_extensionByZeroBaseChange_canonical_app_of_isPullback _ _ _ _
    (D.isPullback_restrictLimit hU₀ g hgflat hgfp) hg
    (D.isEtale_restrictLimit hU₀ g hgflat hgfp hg) A

end Restrict

/-- **The reduction of Stacks 0DKV to an affine situation, for the canonical pseudofunctoriality
datum of derived pullback.**  If for every étale `u : U₀ ⟶ X₀` with `U₀` affine whose composite
`U₀ ⟶ Y₀` factors through an étale morphism from an affine algebraic space the conclusion of the
tag holds for `(Lu^*K₀, Lu^*L₀)` in the situation restricted along `u`, at every shift, then it
holds for `(K₀, L₀)` at every shift.  The base change maps for extension by zero along the
projections of the restricted situation are invertible by
`AlgebraicGeometry.Space.isIso_extensionByZeroBaseChange_canonical_app_of_isPullback`. -/
theorem shiftedHomDescent_canonical_of_restrict_affine (K₀ L₀ : D.InitialDerived)
    (hleaf : ∀ {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU₀ : IsAffineSpace B S hS U₀)
      (g : U₀ ⟶ D.X₀) (hg : IsEtale B S hS g)
      {V : AlgebraicSpaces B S hS} (w : V ⟶ D.initialTarget) (t : U₀ ⟶ V.1),
        IsAffineSpace B S hS V.1 → IsEtale B S hS w.hom → t ≫ w.hom = g ≫ D.p₀ →
        (D.restrict hU₀.isAlgebraicSpace g (D.isFlat_of_isEtale_affine hg)
            (D.isFinitePresentation_of_isEtale_affine hU₀ hg)).ShiftedHomDescent
          (DerivedPullbackComposition.canonical B S hS)
          ((smallEtaleDerivedModulePullback B S hS (D.restrictInitial hU₀.isAlgebraicSpace g
            (D.isFlat_of_isEtale_affine hg)
            (D.isFinitePresentation_of_isEtale_affine hU₀ hg))).obj K₀)
          ((smallEtaleDerivedModulePullback B S hS (D.restrictInitial hU₀.isAlgebraicSpace g
            (D.isFlat_of_isEtale_affine hg)
            (D.isFinitePresentation_of_isEtale_affine hU₀ hg))).obj L₀)) :
    D.ShiftedHomDescent (DerivedPullbackComposition.canonical B S hS) K₀ L₀ :=
  D.shiftedHomDescent_of_restrict_affine (DerivedPullbackComposition.canonical B S hS) K₀ L₀
    fun {_} hU₀ g hg _ w t hV hw ht ↦
      ⟨fun i A ↦
        D.isIso_stageExtensionByZeroBaseChange_canonical_app hU₀.isAlgebraicSpace g _ _ hg i A,
      fun A ↦ D.isIso_limitExtensionByZeroBaseChange_canonical_app hU₀.isAlgebraicSpace g _ _ hg A,
      hleaf hU₀ g hg w t hV hw ht⟩

end RelativeDescentSituation

end AlgebraicGeometry.Space
