module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointRelocalize
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleLimitComparison

/-!
# The morphism to an affine scheme viewed over a larger base

Let `h : S ⟶ S'` be a morphism of schemes of a big fppf site, `X` an algebraic space over `S`
and `f : X ⟶ T` a morphism to a scheme `T` over `S`. The lower shriek `Λ_h` of Stacks 03I5 (2)
carries `f` to a morphism `Λ_h f : Λ_h X ⟶ Λ_h h_T ≅ h_{T/S'}`, a morphism to the scheme `T`
viewed over `S'`. This morphism pulls back the same functions to the charts as `f` does, and it is
proper, flat or of finite presentation when `f` is.

So perfectness of `Rf_*E` over `Γ(T, 𝒪_T)` for perfect `E`, for a proper, flat morphism of finite
presentation to an affine scheme, follows from pseudo-coherence of the derived direct images along
the relocalized morphism: this reduces the statement of Stacks 0CTM over an arbitrary base scheme
to the base `Spec ℤ`, where Noetherian approximation is available.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeSchemeSpaceMap`: the morphism `Λ_h X ⟶ h_{T/S'}` induced by
  `f : X ⟶ h_T`.

## Main results

* `AlgebraicGeometry.Space.chartToBaseOfMap_relocalizeSchemeSpaceMap`: on the chart of `Λ_h X`
  extended from a chart `U` of `X`, the relocalized morphism is the morphism `U ⟶ T` viewed over
  `S'`.
* `AlgebraicGeometry.Space.isProper_relocalizeSchemeSpaceMap`,
  `AlgebraicGeometry.Space.isFlat_relocalizeSchemeSpaceMap`,
  `AlgebraicGeometry.Space.isFinitePresentation_relocalizeSchemeSpaceMap`: the relocalized
  morphism keeps these properties.
* `AlgebraicGeometry.Space.isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_relocalize`:
  perfectness of `Rf_*E` on the point follows from pseudo-coherence along the relocalized morphism.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (h : B.obj hS ⟶ B.obj hS') (X : AlgebraicSpaces B S hS)
  (hX' : IsAlgebraicSpace B S' hS' ((OverShriek.relocalizePresheafFunctor h).obj X.1))
  {T : BigFppfOver B S hS}

/-- The identification `Λ_h h_T ≅ h_{T/S'}` of Stacks 03I4 (2), as an isomorphism of presheaves on
the big fppf site of `S'`. -/
def relocalizeYonedaSchemeIso (T : BigFppfOver B S hS) :
    Iso (C := (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u)
      ((OverShriek.relocalizePresheafFunctor h).obj (yoneda.obj T))
      (yoneda.obj ((Over.map h).obj T)) :=
  relocalizedYonedaIso B (B.obj hS) (B.obj hS') h T

/-- **A morphism to a scheme viewed over a larger base.** The lower shriek of `f : X ⟶ h_T`,
followed by the identification `Λ_h h_T ≅ h_{T/S'}` of Stacks 03I4 (2). -/
def relocalizeSchemeSpaceMap (f : X ⟶ schemeSpace T) :
    (⟨(OverShriek.relocalizePresheafFunctor h).obj X.1, hX'⟩ : AlgebraicSpaces B S' hS') ⟶
      schemeSpace ((Over.map h).obj T) :=
  ObjectProperty.homMk ((OverShriek.relocalizePresheafFunctor h).map f.hom ≫
    (relocalizeYonedaSchemeIso B S S' hS hS' h T).hom)

/-- On the chart of `Λ_h X` extended from a chart `U` of `X`, the relocalized morphism is the
morphism `U ⟶ T` induced by `f`, viewed over `S'`. -/
theorem chartToBaseOfMap_relocalizeSchemeSpaceMap (f : X ⟶ schemeSpace T)
    (V : SmallEtale B S hS X.1) :
    chartToBaseOfMap (relocalizeSchemeSpaceMap B S S' hS hS' h X hX' f)
        ((SmallEtale.relocalizeEquivalence B S S' hS hS' h X.1).functor.obj V) =
      (Over.map h).map (chartToBaseOfMap f V) := by
  apply yoneda.map_injective
  rw [yoneda_map_chartToBaseOfMap]
  have hid : relocalizeChart B S S' hS hS' h (𝟙 (yoneda.obj T)) =
      (relocalizedYonedaIso B (B.obj hS) (B.obj hS') h T).inv := by
    simp [relocalizeChart]
  have hc : relocalizeChart B S S' hS hS' h (yoneda.map (chartToBaseOfMap f V)) =
      yoneda.map ((Over.map h).map (chartToBaseOfMap f V)) ≫
        (relocalizedYonedaIso B (B.obj hS) (B.obj hS') h T).inv := by
    rw [← hid, relocalizeChart_naturality, Category.comp_id]
  have key : relocalizeChart B S S' hS hS' h V.obj.hom ≫
      ((OverShriek.relocalizePresheafFunctor h).map f.hom ≫
        (relocalizedYonedaIso B (B.obj hS) (B.obj hS') h T).hom) =
      yoneda.map ((Over.map h).map (chartToBaseOfMap f V)) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (relocalizedYonedaIso B (B.obj hS) (B.obj hS') h T).hom)
        ((relocalizeChart_comp B S S' hS hS' h V.obj.hom f.hom).trans
          ((congrArg (relocalizeChart B S S' hS hS' h) (yoneda_map_chartToBaseOfMap f V).symm).trans
            hc))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (yoneda.map ((Over.map h).map (chartToBaseOfMap f V)) ≫ ·)
            (Iso.inv_hom_id _)).trans (Category.comp_id _))))
  exact key

/-- The relocalized morphism pulls back the same functions of `T` to the charts as `f` does: the
compatibility under which `AlgebraicGeometry.Space.relocalizeGlobalSectionsIso` applies. -/
theorem globalFunctionsOfMap_relocalizeSchemeSpaceMap (f : X ⟶ schemeSpace T)
    (r : baseRing B S hS T) (V : SmallEtale B S hS X.1) :
    (globalFunctionsOfMap (relocalizeSchemeSpaceMap B S S' hS hS' h X hX' f) r).1
        (op ((SmallEtale.relocalizeEquivalence B S S' hS hS' h X.1).functor.obj V)) =
      (globalFunctionsOfMap f r).1 (op V) := by
  have hc := chartToBaseOfMap_relocalizeSchemeSpaceMap B S S' hS hS' h X hX' f V
  let r' : baseRing B S' hS' ((Over.map h).obj T) := r
  have key := congrArg (fun (c : ((SmallEtale.relocalizeEquivalence B S S' hS hS' h X.1).functor.obj
      V).obj.left ⟶ (Over.map h).obj T) =>
    (Scheme.Γ.map ((BigFppfOver.toScheme B S' hS').map c).op).hom r') hc
  exact key

/-- **Properness survives viewing the morphism over a larger base.** -/
theorem isProper_relocalizeSchemeSpaceMap (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom) :
    IsProper B S' hS' (relocalizeSchemeSpaceMap B S S' hS hS' h X hX' f).hom :=
  @isProper_of_arrowIso B S' hS' _ _ _ _ ((OverShriek.relocalizePresheafFunctor h).map f.hom)
    (relocalizeSchemeSpaceMap B S S' hS hS' h X hX' f).hom (𝟙 _)
    (relocalizeYonedaSchemeIso B S S' hS hS' h T).hom inferInstance (Iso.isIso_hom _)
    (Category.id_comp _)
    ((isProper_relocalize_iff B S hS S' hS' h X.2 (schemeSpace T).2 f.hom).2 hf)

/-- **Flatness survives viewing the morphism over a larger base.** -/
theorem isFlat_relocalizeSchemeSpaceMap (f : X ⟶ schemeSpace T) (hf : IsFlat B S hS f.hom) :
    IsFlat B S' hS' (relocalizeSchemeSpaceMap B S S' hS hS' h X hX' f).hom :=
  (@holdsOnEveryEtaleChart_comp_iso_iff B S' hS' _ _ _ _ _
    (relocalizeYonedaSchemeIso B S S' hS hS' h T).hom (Iso.isIso_hom _)).2
    ((holdsOnEveryEtaleChart_relocalizeMap_iff B S S' hS hS' h _ f.hom).2 hf)

/-- **Finite presentation survives viewing the morphism over a larger base.** -/
theorem isFinitePresentation_relocalizeSchemeSpaceMap (f : X ⟶ schemeSpace T)
    (hf : IsFinitePresentation B S hS f.hom) :
    IsFinitePresentation B S' hS' (relocalizeSchemeSpaceMap B S S' hS hS' h X hX' f).hom :=
  @isFinitePresentation_of_arrowIso B S' hS' _ _ _ _
    ((OverShriek.relocalizePresheafFunctor h).map f.hom)
    (relocalizeSchemeSpaceMap B S S' hS hS' h X hX' f).hom (𝟙 _)
    (relocalizeYonedaSchemeIso B S S' hS hS' h T).hom inferInstance (Iso.isIso_hom _)
    (Category.id_comp _)
    ⟨(holdsOnEveryEtaleChart_relocalizeMap_iff B S S' hS hS' h _ f.hom).2 hf.1,
      (isQuasiCompact_relocalize_iff B S hS S' hS' h f.hom).2 hf.2.1,
      (isQuasiSeparated_relocalize_iff B S hS S' hS' h f.hom).2 hf.2.2⟩

section Perfect

attribute [local instance] HasDerivedCategory.standard

/-- **Perfectness of `RΓ` on the point reduces to a larger base.** Let `f : X ⟶ T` be flat and of
finite presentation over an affine `T`. If, along the relocalized morphism
`Λ_h X ⟶ h_{T/S'}`, the derived direct image of every perfect object is pseudo-coherent over
`Γ(T, 𝒪_T)`, then the derived direct image along `f` of every perfect object is perfect on the
point `(pt, Γ(T, 𝒪_T))`. -/
theorem isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_relocalize
    (hZ : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (H : ∀ E' : DerivedCategory (spacesEtaleModelRingedTopos B S' hS'
        (⟨(OverShriek.relocalizePresheafFunctor h).obj X.1, hX'⟩ :
          AlgebraicSpaces B S' hS')).Modules,
      (spacesEtaleModelRingedTopos B S' hS' _).toRingedSite.IsPerfect E' →
      StacksDraft.PseudoCoherence.IsPseudoCoherent
        ((pointDerivedEquiv (R := baseRing B S hS T)).functor.obj
          ((derivedPushforward (spacesEtaleModelToBaseRing B S' hS' _
            (baseRingHomOfMap (relocalizeSchemeSpaceMap B S S' hS hS' h X hX' f)))).obj E')))
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hE : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect E) :
    (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).toRingedSite.IsPerfect
      ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj E) := by
  have hqcqs := qcqs_of_isFinitePresentation_schemeSpace hZ f hT hfp
  exact isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_isPseudoCoherent B S hS hZ
    hqcqs.1 hqcqs.2 f hflat hT E hE
    (isPseudoCoherent_pointDerivedEquiv_derivedPushforward_of_relocalize B S S' hS hS' h X hX'
      (globalFunctionsOfMap_relocalizeSchemeSpaceMap B S S' hS hS' h X hX' f) H E hE)

omit hX' in
/-- **The point form of Stacks 0CTM reduces to the base `Spec ℤ`.** Suppose that over the terminal
scheme, for every proper and flat morphism of finite presentation `f' : X' ⟶ T'` to an affine
scheme, the derived direct image `Rf'_*E'` of every perfect `E'` is pseudo-coherent over
`Γ(T', 𝒪_{T'})`. Then over any base scheme `S`, for `f : X ⟶ T` proper, flat and of finite
presentation with `T` affine, `Rf_*E` is perfect on the point `(pt, Γ(T, 𝒪_T))` for every perfect
`E`. The morphism over `Spec ℤ` is `Λ f : Λ X ⟶ h_{T/ℤ}`, the lower shriek along `S ⟶ Spec ℤ`. -/
theorem isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_integers
    (hZ : B.Contains (⊤_ Scheme.{u})) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (hflat : IsFlat B S hS f.hom)
    (Hℤ : ∀ (X' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ) (T' : BigFppfOver B (⊤_ Scheme.{u}) hZ)
      (f' : X' ⟶ schemeSpace T'), IsAffine ((BigFppfOver.toScheme B _ hZ).obj T') →
      IsProper B _ hZ f'.hom → IsFlat B _ hZ f'.hom → IsFinitePresentation B _ hZ f'.hom →
      ∀ E' : DerivedCategory (spacesEtaleModelRingedTopos B _ hZ X').Modules,
        (spacesEtaleModelRingedTopos B _ hZ X').toRingedSite.IsPerfect E' →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((pointDerivedEquiv (R := baseRing B _ hZ T')).functor.obj
            ((derivedPushforward (spacesEtaleModelToBaseRing B _ hZ X'
              (baseRingHomOfMap f'))).obj E')))
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hE : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect E) :
    (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).toRingedSite.IsPerfect
      ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj E) := by
  let h : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  have hX' := isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ h X.1 X.2
  exact isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_relocalize B S (⊤_ Scheme.{u})
    hS hZ h X hX' hZ f hflat hfp hT
    (Hℤ _ _ (relocalizeSchemeSpaceMap B S (⊤_ Scheme.{u}) hS hZ h X hX' f) hT
      (isProper_relocalizeSchemeSpaceMap B S (⊤_ Scheme.{u}) hS hZ h X hX' f hf)
      (isFlat_relocalizeSchemeSpaceMap B S (⊤_ Scheme.{u}) hS hZ h X hX' f hflat)
      (isFinitePresentation_relocalizeSchemeSpaceMap B S (⊤_ Scheme.{u}) hS hZ h X hX' f hfp))
    E hE

end Perfect

end AlgebraicGeometry.Space

end
