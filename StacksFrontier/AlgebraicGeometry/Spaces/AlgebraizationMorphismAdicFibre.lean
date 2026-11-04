module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraizationMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# Algebraization of morphisms in terms of the adic fibres

Over the site of `Spec A`, the adic fibres `AlgebraicGeometry.Space.adicFibre` of an algebraic
space over `Spec A` are its base changes along the thickenings `Spec (A / Iⁿ⁺¹)`, and a morphism
over `Spec A` induces the morphisms `AlgebraicGeometry.Space.adicFibreMap` between them. This file
identifies the adic fibres with the infinitesimal fibres `AlgebraicGeometry.Space.fibreSpace` for
the ideal `I` transported to `Γ(Spec A, 𝒪)`, and states Stacks 0A4Z in terms of adic fibres,
assuming Stacks 08BG.

## Main results

* `AlgebraicGeometry.Space.adicThickeningIsoQuotient`: the two models of `Spec (A / Iⁿ⁺¹)`.
* `AlgebraicGeometry.Space.fibreSpaceIsoAdicFibre`: the infinitesimal fibres are the adic
  fibres, compatibly with the transitions
  (`AlgebraicGeometry.Space.fibreTransition_comp_fibreSpaceIsoAdicFibre`).
* `Space.existsUnique_algebraization_of_adicFibre_of_closedSubspaceTowerAlgebraizes`:
  Stacks 0A4Z in terms of adic fibres, assuming Stacks 08BG.

## References

* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of A))) (hSn : ∀ n, B.Contains (adicThickening A I n))

/-- The scheme underlying the base object `Spec A` is affine. -/
theorem isAffine_toScheme_baseObject :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hS).obj (baseObject A B hS)) :=
  inferInstanceAs (IsAffine (Spec (.of A)))

attribute [local instance] isAffine_toScheme_baseObject

/-- The ring isomorphism `A ≃ Γ(Spec A, 𝒪)`. -/
abbrev baseRingEquiv :
    A ≃+* Γ((BigFppfOver.toScheme B (Spec (.of A)) hS).obj (baseObject A B hS), ⊤) :=
  (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv

/-- The ideal `I`, transported to the global sections of `Spec A`. -/
abbrev adicBaseIdeal :
    Ideal Γ((BigFppfOver.toScheme B (Spec (.of A)) hS).obj (baseObject A B hS), ⊤) :=
  I.map (baseRingEquiv A B hS)

/-- The `n`-th power of the transported ideal is the transport of `Iⁿ`. -/
theorem adicBaseIdeal_pow (n : ℕ) :
    adicBaseIdeal A I B hS ^ n = (I ^ n).map (baseRingEquiv A B hS) := by
  rw [adicBaseIdeal, Ideal.map_pow]

/-- `A / Iⁿ ≃ Γ(Spec A) / Iⁿ`. -/
abbrev adicBaseQuotientEquiv (n : ℕ) :
    A ⧸ I ^ n ≃+* Γ((BigFppfOver.toScheme B (Spec (.of A)) hS).obj (baseObject A B hS), ⊤) ⧸
      adicBaseIdeal A I B hS ^ n :=
  Ideal.quotientEquiv (I ^ n) (adicBaseIdeal A I B hS ^ n) (baseRingEquiv A B hS)
    (adicBaseIdeal_pow A I B hS n)

/-- The map `Spec (A / Iⁿ⁺¹) ⟶ Spec (Γ / Iⁿ⁺¹) ⟶ Spec A` induced by `adicBaseQuotientEquiv` is
`adicThickeningι`. -/
theorem specMap_adicBaseQuotientEquiv_symm_comp (n : ℕ) :
    Spec.map (CommRingCat.ofHom (adicBaseQuotientEquiv A I B hS (n + 1)).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (adicBaseIdeal A I B hS ^ (n + 1)))) ≫
          (Spec (.of A)).isoSpec.inv = adicThickeningι A I n := by
  rw [Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp, adicThickeningι]
  congr 1
  ext a
  change Ideal.Quotient.mk _ ((baseRingEquiv A B hS).symm (baseRingEquiv A B hS a)) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

/-- The map `Spec (Γ / Iⁿ⁺¹) ⟶ Spec (A / Iⁿ⁺¹) ⟶ Spec A` induced by `adicBaseQuotientEquiv` is
the closed immersion `Spec (Γ / Iⁿ⁺¹) ⟶ Spec A`. -/
theorem specMap_adicBaseQuotientEquiv_comp (n : ℕ) :
    Spec.map (CommRingCat.ofHom (adicBaseQuotientEquiv A I B hS (n + 1)).toRingHom) ≫
        adicThickeningι A I n =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (adicBaseIdeal A I B hS ^ (n + 1)))) ≫
          (Spec (.of A)).isoSpec.inv := by
  rw [Scheme.isoSpec_Spec_inv, adicThickeningι, ← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- The structure morphism of `adicCompletionQuotientObj` over `Spec A` is the closed immersion
`Spec (Γ / Iⁿ) ⟶ Spec A`. -/
theorem hom_hom_adicCompletionQuotientObj_baseObject (n : ℕ) :
    (adicCompletionQuotientObj B (Spec (.of A)) hS (baseObject A B hS) (adicBaseIdeal A I B hS)
        n).hom.hom =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (adicBaseIdeal A I B hS ^ n))) ≫
        (Spec (.of A)).isoSpec.inv := by
  simp only [adicCompletionQuotientObj, BigFppfOver.mk, Over.mk_hom,
    ObjectProperty.homMk_hom, Over.mk_left]
  rfl

/-- The adic thickening `Spec (A / Iⁿ⁺¹)` maps to `Spec (Γ / Iⁿ⁺¹)` over `Spec A`. -/
def adicThickeningToQuotient (n : ℕ) :
    adicThickeningObject A I B hS hSn n ⟶
      adicCompletionQuotientObj B (Spec (.of A)) hS (baseObject A B hS) (adicBaseIdeal A I B hS)
        (n + 1) :=
  Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (adicBaseQuotientEquiv A I B hS (n + 1)).symm.toRingHom)))
    (by
      apply ObjectProperty.hom_ext
      rw [ObjectProperty.FullSubcategory.comp_hom, hom_hom_adicCompletionQuotientObj_baseObject]
      exact specMap_adicBaseQuotientEquiv_symm_comp A I B hS n)

/-- `adicThickeningToQuotient` followed by the inclusion of `Spec (Γ / Iⁿ⁺¹)` is
`adicThickeningMap`. -/
theorem adicThickeningToQuotient_comp (n : ℕ) :
    adicThickeningToQuotient A I B hS hSn n ≫
        adicCompletionQuotientObjHom B (Spec (.of A)) hS (baseObject A B hS)
          (adicBaseIdeal A I B hS) (n + 1) =
      adicThickeningMap A I B hS hSn n :=
  (BigFppfOver.toScheme B (Spec (.of A)) hS).map_injective
    ((Functor.map_comp _ _ _).trans (specMap_adicBaseQuotientEquiv_symm_comp A I B hS n))

/-- `Spec (Γ / Iⁿ⁺¹)` maps to the adic thickening `Spec (A / Iⁿ⁺¹)` over `Spec A`. -/
def adicQuotientToThickening (n : ℕ) :
    adicCompletionQuotientObj B (Spec (.of A)) hS (baseObject A B hS) (adicBaseIdeal A I B hS)
        (n + 1) ⟶ adicThickeningObject A I B hS hSn n :=
  Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (adicBaseQuotientEquiv A I B hS (n + 1)).toRingHom)))
    (by
      apply ObjectProperty.hom_ext
      refine (specMap_adicBaseQuotientEquiv_comp A I B hS n).trans ?_
      rw [hom_hom_adicCompletionQuotientObj_baseObject])

/-- `adicQuotientToThickening` followed by `adicThickeningMap` is the inclusion of
`Spec (Γ / Iⁿ⁺¹)`. -/
theorem adicQuotientToThickening_comp (n : ℕ) :
    adicQuotientToThickening A I B hS hSn n ≫ adicThickeningMap A I B hS hSn n =
      adicCompletionQuotientObjHom B (Spec (.of A)) hS (baseObject A B hS)
        (adicBaseIdeal A I B hS) (n + 1) :=
  (BigFppfOver.toScheme B (Spec (.of A)) hS).map_injective
    ((Functor.map_comp _ _ _).trans (specMap_adicBaseQuotientEquiv_comp A I B hS n))

/-- The inclusion `adicThickeningMap` of the adic thickening is a monomorphism. -/
theorem mono_adicThickeningMap (n : ℕ) : Mono (adicThickeningMap A I B hS hSn n) :=
  have : _root_.AlgebraicGeometry.IsClosedImmersion (adicThickeningι A I n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  (BigFppfOver.toScheme B (Spec (.of A)) hS).mono_of_mono_map
    (inferInstanceAs (Mono (adicThickeningι A I n)))

attribute [local instance] mono_adicThickeningMap

/-- The two models of `Spec (A / Iⁿ⁺¹)` over `Spec A` are isomorphic. -/
def adicThickeningIsoQuotient (n : ℕ) :
    adicThickeningObject A I B hS hSn n ≅
      adicCompletionQuotientObj B (Spec (.of A)) hS (baseObject A B hS) (adicBaseIdeal A I B hS)
        (n + 1) where
  hom := adicThickeningToQuotient A I B hS hSn n
  inv := adicQuotientToThickening A I B hS hSn n
  hom_inv_id := by
    rw [← cancel_mono (adicThickeningMap A I B hS hSn n), Category.assoc,
      adicQuotientToThickening_comp, adicThickeningToQuotient_comp, Category.id_comp]
  inv_hom_id := by
    have : Mono (adicCompletionQuotientObjHom B (Spec (.of A)) hS (baseObject A B hS)
        (adicBaseIdeal A I B hS) (n + 1)) :=
      (BigFppfOver.toScheme B (Spec (.of A)) hS).mono_of_mono_map inferInstance
    rw [← cancel_mono (adicCompletionQuotientObjHom B (Spec (.of A)) hS (baseObject A B hS)
      (adicBaseIdeal A I B hS) (n + 1)), Category.assoc, adicThickeningToQuotient_comp,
      adicQuotientToThickening_comp, Category.id_comp]

/-- **The infinitesimal fibre `X ×_V Spec (A / Iⁿ⁺¹)` is the adic fibre.** -/
theorem isPullback_fibreInclusion_adicThickeningMap
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hS X) (fX : X ⟶ yoneda.obj (baseObject A B hS))
    (n : ℕ) :
    IsPullback (fibreInclusion (baseObject A B hS) (adicBaseIdeal A I B hS)
        (ObjectProperty.homMk fX : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
          schemeSpace (baseObject A B hS)) (n + 1)).hom
      (((adicQuotientSubspace (baseObject A B hS) (adicBaseIdeal A I B hS) (n + 1)).1.fromPreimage
          fX ≫ (adicQuotientSubspaceIso (baseObject A B hS) (adicBaseIdeal A I B hS) (n + 1)).hom) ≫
        yoneda.map (adicThickeningIsoQuotient A I B hS hSn n).inv)
      fX (yoneda.map (adicThickeningMap A I B hS hSn n)) := by
  refine (isPullback_fibreInclusion_of_hom (I := adicBaseIdeal A I B hS) hX fX (n + 1)).of_iso
    (Iso.refl _) (Iso.refl _) (yoneda.mapIso (adicThickeningIsoQuotient A I B hS hSn n).symm)
    (Iso.refl _) (by simp) (by simp) (by simp) ?_
  simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, Iso.symm_hom, ← Functor.map_comp]
  congr 1
  exact (adicQuotientToThickening_comp A I B hS hSn n).symm

/-- The infinitesimal fibre `X ×_V Spec (A / Iⁿ⁺¹)`, identified with the adic fibre. -/
def fibreSpaceIsoAdicFibre {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hS X) (fX : X ⟶ yoneda.obj (baseObject A B hS))
    (n : ℕ) :
    (fibreSpace (baseObject A B hS) (adicBaseIdeal A I B hS)
        (ObjectProperty.homMk fX : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
          schemeSpace (baseObject A B hS)) (n + 1)).1 ≅ adicFibre A I B hS hSn fX n :=
  (isPullback_fibreInclusion_adicThickeningMap A I B hS hSn hX fX n).isoPullback

/-- `fibreSpaceIsoAdicFibre` followed by the first projection is the fibre inclusion. -/
@[reassoc (attr := simp)]
theorem fibreSpaceIsoAdicFibre_hom_fst {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hS X) (fX : X ⟶ yoneda.obj (baseObject A B hS))
    (n : ℕ) :
    (fibreSpaceIsoAdicFibre A I B hS hSn hX fX n).hom ≫ pullback.fst _ _ =
      (fibreInclusion (baseObject A B hS) (adicBaseIdeal A I B hS)
        (ObjectProperty.homMk fX : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
          schemeSpace (baseObject A B hS)) (n + 1)).hom :=
  IsPullback.isoPullback_hom_fst _

/-- The inverse of `fibreSpaceIsoAdicFibre` followed by the fibre inclusion is the first
projection. -/
@[reassoc (attr := simp)]
theorem fibreSpaceIsoAdicFibre_inv_fibreInclusion
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hS X) (fX : X ⟶ yoneda.obj (baseObject A B hS))
    (n : ℕ) :
    (fibreSpaceIsoAdicFibre A I B hS hSn hX fX n).inv ≫
      (fibreInclusion (baseObject A B hS) (adicBaseIdeal A I B hS)
        (ObjectProperty.homMk fX : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
          schemeSpace (baseObject A B hS)) (n + 1)).hom = pullback.fst _ _ := by
  rw [Iso.inv_comp_eq, fibreSpaceIsoAdicFibre_hom_fst]

/-- The transition between infinitesimal fibres commutes with their inclusions, on underlying
morphisms of functors. -/
private theorem hom_fibreTransition_comp_hom_fibreInclusion
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hS X) (fX : X ⟶ yoneda.obj (baseObject A B hS))
    (n : ℕ) :
    (fibreTransition (baseObject A B hS) (adicBaseIdeal A I B hS)
        (ObjectProperty.homMk fX : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
          schemeSpace (baseObject A B hS)) (Nat.le_succ (n + 1))).hom ≫
      (fibreInclusion (baseObject A B hS) (adicBaseIdeal A I B hS)
        (ObjectProperty.homMk fX : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
          schemeSpace (baseObject A B hS)) (n + 1 + 1)).hom =
      (fibreInclusion (baseObject A B hS) (adicBaseIdeal A I B hS)
        (ObjectProperty.homMk fX : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
          schemeSpace (baseObject A B hS)) (n + 1)).hom :=
  congrArg (fun k => k.hom) (fibreTransition_comp (baseObject A B hS) (adicBaseIdeal A I B hS)
    (ObjectProperty.homMk fX : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
      schemeSpace (baseObject A B hS)) (Nat.le_succ (n + 1)))

/-- The identifications with the adic fibres are compatible with the transitions. -/
theorem fibreTransition_comp_fibreSpaceIsoAdicFibre
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hS X) (fX : X ⟶ yoneda.obj (baseObject A B hS))
    (n : ℕ) :
    (fibreTransition (baseObject A B hS) (adicBaseIdeal A I B hS)
        (ObjectProperty.homMk fX : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
          schemeSpace (baseObject A B hS)) (Nat.le_succ (n + 1))).hom ≫
        (fibreSpaceIsoAdicFibre A I B hS hSn hX fX (n + 1)).hom =
      (fibreSpaceIsoAdicFibre A I B hS hSn hX fX n).hom ≫ adicFibreSucc A I B hS hSn fX n := by
  have htr := hom_fibreTransition_comp_hom_fibreInclusion A I B hS hX fX n
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, fibreSpaceIsoAdicFibre_hom_fst, Category.assoc, adicFibreSucc_fst,
      fibreSpaceIsoAdicFibre_hom_fst]
    exact htr
  · rw [← cancel_mono (yoneda.map (adicThickeningMap A I B hS hSn (n + 1))), Category.assoc,
      Category.assoc, ← pullback.condition, fibreSpaceIsoAdicFibre_hom_fst_assoc,
      Category.assoc, Category.assoc, adicFibreSucc_snd_assoc, ← Functor.map_comp,
      adicThickeningSuccMap_adicThickeningMap, ← pullback.condition,
      fibreSpaceIsoAdicFibre_hom_fst_assoc, ← Category.assoc, htr]

section FibreMap

variable {X Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B (Spec (.of A)) hS X) (hY : IsAlgebraicSpace B (Spec (.of A)) hS Y)
  (fX : X ⟶ yoneda.obj (baseObject A B hS)) (fY : Y ⟶ yoneda.obj (baseObject A B hS))

/-- A morphism of adic fibres, viewed as a morphism of infinitesimal fibres. -/
def fibreMapOfAdicFibre (n : ℕ) (g : adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fY n) :
    fibreSpace (baseObject A B hS) (adicBaseIdeal A I B hS)
        (ObjectProperty.homMk fX : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
          schemeSpace (baseObject A B hS)) (n + 1) ⟶
      fibreSpace (baseObject A B hS) (adicBaseIdeal A I B hS)
        (ObjectProperty.homMk fY : (⟨Y, hY⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
          schemeSpace (baseObject A B hS)) (n + 1) :=
  ObjectProperty.homMk ((fibreSpaceIsoAdicFibre A I B hS hSn hX fX n).hom ≫ g ≫
    (fibreSpaceIsoAdicFibre A I B hS hSn hY fY n).inv)

/-- `fibreMapOfAdicFibre` followed by the fibre inclusion is `g` followed by the projection. -/
theorem fibreMapOfAdicFibre_hom_fibreInclusion (n : ℕ)
    (g : adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fY n) :
    (fibreMapOfAdicFibre A I B hS hSn hX hY fX fY n g).hom ≫
        (fibreInclusion (baseObject A B hS) (adicBaseIdeal A I B hS)
          (ObjectProperty.homMk fY : (⟨Y, hY⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
            schemeSpace (baseObject A B hS)) (n + 1)).hom =
      (fibreSpaceIsoAdicFibre A I B hS hSn hX fX n).hom ≫ g ≫ pullback.fst _ _ := by
  change ((fibreSpaceIsoAdicFibre A I B hS hSn hX fX n).hom ≫ g ≫
    (fibreSpaceIsoAdicFibre A I B hS hSn hY fY n).inv) ≫ _ = _
  rw [Category.assoc, Category.assoc, fibreSpaceIsoAdicFibre_inv_fibreInclusion]

/-- If `g` commutes with the projections to the thickening, then `fibreMapOfAdicFibre g` commutes
with the maps to `Spec A`. -/
theorem fibreMapOfAdicFibre_over (n : ℕ)
    (g : adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fY n)
    (hg : g ≫ pullback.snd fY (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n))) :
    fibreMapOfAdicFibre A I B hS hSn hX hY fX fY n g ≫
        fibreInclusion (baseObject A B hS) (adicBaseIdeal A I B hS)
          (ObjectProperty.homMk fY : (⟨Y, hY⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
            schemeSpace (baseObject A B hS)) (n + 1) ≫
          (ObjectProperty.homMk fY : (⟨Y, hY⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
            schemeSpace (baseObject A B hS)) =
      fibreInclusion (baseObject A B hS) (adicBaseIdeal A I B hS)
          (ObjectProperty.homMk fX : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
            schemeSpace (baseObject A B hS)) (n + 1) ≫
          (ObjectProperty.homMk fX : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
            schemeSpace (baseObject A B hS)) := by
  refine ObjectProperty.hom_ext _ ?_
  change (fibreMapOfAdicFibre A I B hS hSn hX hY fX fY n g).hom ≫
      (fibreInclusion _ _ (ObjectProperty.homMk fY : (⟨Y, hY⟩ : AlgebraicSpaces B (Spec (.of A)) hS)
        ⟶ schemeSpace (baseObject A B hS)) (n + 1)).hom ≫ fY =
    (fibreInclusion _ _ (ObjectProperty.homMk fX : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hS)
        ⟶ schemeSpace (baseObject A B hS)) (n + 1)).hom ≫ fX
  rw [← Category.assoc, fibreMapOfAdicFibre_hom_fibreInclusion, Category.assoc, Category.assoc,
    pullback.condition, ← Category.assoc g, hg, ← pullback.condition, ← Category.assoc,
    fibreSpaceIsoAdicFibre_hom_fst]

/-- `fibreMapOfAdicFibre` is compatible with the transitions when the adic fibre maps are. -/
theorem fibreTransition_comp_fibreMapOfAdicFibre (n : ℕ)
    (g₀ : adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fY n)
    (g₁ : adicFibre A I B hS hSn fX (n + 1) ⟶ adicFibre A I B hS hSn fY (n + 1))
    (hg : adicFibreSucc A I B hS hSn fX n ≫ g₁ = g₀ ≫ adicFibreSucc A I B hS hSn fY n) :
    fibreTransition (baseObject A B hS) (adicBaseIdeal A I B hS)
          (ObjectProperty.homMk fX : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
            schemeSpace (baseObject A B hS)) (Nat.le_succ (n + 1)) ≫
        fibreMapOfAdicFibre A I B hS hSn hX hY fX fY (n + 1) g₁ =
      fibreMapOfAdicFibre A I B hS hSn hX hY fX fY n g₀ ≫
        fibreTransition (baseObject A B hS) (adicBaseIdeal A I B hS)
          (ObjectProperty.homMk fY : (⟨Y, hY⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
            schemeSpace (baseObject A B hS)) (Nat.le_succ (n + 1)) := by
  have : Mono (fibreInclusion (baseObject A B hS) (adicBaseIdeal A I B hS)
      (ObjectProperty.homMk fY : (⟨Y, hY⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
        schemeSpace (baseObject A B hS)) (n + 1 + 1)).hom :=
    inferInstanceAs (Mono (Subfunctor.ι _))
  refine ObjectProperty.hom_ext _ ((cancel_mono (fibreInclusion (baseObject A B hS)
    (adicBaseIdeal A I B hS)
    (ObjectProperty.homMk fY : (⟨Y, hY⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
      schemeSpace (baseObject A B hS)) (n + 1 + 1)).hom).1 ?_)
  have htr := hom_fibreTransition_comp_hom_fibreInclusion A I B hS hY fY n
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [Category.assoc, fibreMapOfAdicFibre_hom_fibreInclusion, Category.assoc, htr,
    fibreMapOfAdicFibre_hom_fibreInclusion, ← Category.assoc,
    fibreTransition_comp_fibreSpaceIsoAdicFibre, Category.assoc, reassoc_of% hg,
    adicFibreSucc_fst]

/-- The `n`-th adic fibre map of `h` is `g` iff `h` restricts to `fibreMapOfAdicFibre g` on the
infinitesimal fibres. -/
theorem adicFibreMap_eq_iff_fibreInclusion_comp (n : ℕ)
    (g : adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fY n)
    (hg : g ≫ pullback.snd fY (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)))
    (h : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶ ⟨Y, hY⟩) (hh : h.hom ≫ fY = fX) :
    adicFibreMap A I B hS hSn h.hom hh n = g ↔
      fibreInclusion (baseObject A B hS) (adicBaseIdeal A I B hS)
          (ObjectProperty.homMk fX : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
            schemeSpace (baseObject A B hS)) (n + 1) ≫ h =
        fibreMapOfAdicFibre A I B hS hSn hX hY fX fY n g ≫
          fibreInclusion (baseObject A B hS) (adicBaseIdeal A I B hS)
            (ObjectProperty.homMk fY : (⟨Y, hY⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
              schemeSpace (baseObject A B hS)) (n + 1) := by
  refine ⟨fun he => ObjectProperty.hom_ext _ ?_, fun he => pullback.hom_ext ?_ ?_⟩
  · simp only [ObjectProperty.FullSubcategory.comp_hom]
    rw [fibreMapOfAdicFibre_hom_fibreInclusion, ← he, adicFibreMap_fst, ← Category.assoc,
      fibreSpaceIsoAdicFibre_hom_fst]
  · have he' := congrArg (fun k => k.hom) he
    simp only [ObjectProperty.FullSubcategory.comp_hom] at he'
    rw [adicFibreMap_fst, ← fibreSpaceIsoAdicFibre_inv_fibreInclusion A I B hS hSn hX fX n,
      Category.assoc, he', fibreMapOfAdicFibre_hom_fibreInclusion, Iso.inv_hom_id_assoc]
  · rw [adicFibreMap_snd, hg]

end FibreMap

/-- Let `A` be Noetherian and `I`-adically complete, `X` proper and `Y` separated of finite type
over `Spec A`, and assume `h08BG`, the statement of Stacks 08BG. A system of morphisms between
the adic fibres over `Spec (A / Iⁿ⁺¹)`, over the thickenings and compatible with the transitions,
is the system of adic fibres of a unique morphism `X ⟶ Y` over `Spec A`. -/
theorem existsUnique_algebraization_of_adicFibre_of_closedSubspaceTowerAlgebraizes
    [IsNoetherianRing A] (hcomplete : IsAdicComplete I A)
    (h08BG : ∀ [_root_.AlgebraicGeometry.IsLocallyNoetherian
        ((BigFppfOver.toScheme B (Spec (.of A)) hS).obj (baseObject A B hS))]
      (W : AlgebraicSpaces B (Spec (.of A)) hS) (f : W ⟶ schemeSpace (baseObject A B hS)),
      ClosedSubspaceTowerAlgebraizes (baseObject A B hS) (adicBaseIdeal A I B hS) f)
    {X Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hS X) (hY : IsAlgebraicSpace B (Spec (.of A)) hS Y)
    (fX : X ⟶ yoneda.obj (baseObject A B hS)) (fY : Y ⟶ yoneda.obj (baseObject A B hS))
    (hproper : IsProper B (Spec (.of A)) hS fX)
    (hseparated : IsSeparated B (Spec (.of A)) hS fY)
    (hfinite : IsFiniteType B (Spec (.of A)) hS fY)
    (g : ∀ n, adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fY n)
    (g_over : ∀ n, g n ≫ pullback.snd fY (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)))
    (g_compatible : ∀ n,
      adicFibreSucc A I B hS hSn fX n ≫ g (n + 1) = g n ≫ adicFibreSucc A I B hS hSn fY n) :
    ∃! algebraization : {f : X ⟶ Y // f ≫ fY = fX},
      ∀ n, adicFibreMap A I B hS hSn algebraization.1 algebraization.2 n = g n := by
  have : IsNoetherianRing
      Γ((BigFppfOver.toScheme B (Spec (.of A)) hS).obj (baseObject A B hS), ⊤) :=
    isNoetherianRing_of_ringEquiv A (baseRingEquiv A B hS)
  have : IsAdicComplete (adicBaseIdeal A I B hS)
      Γ((BigFppfOver.toScheme B (Spec (.of A)) hS).obj (baseObject A B hS), ⊤) :=
    (IsAdicComplete.congr_ringEquiv I (baseRingEquiv A B hS)).2 hcomplete
  obtain ⟨g', ⟨hq, hn⟩, huniq⟩ :=
    existsUnique_algebraization_fibreMaps_of_closedSubspaceTowerAlgebraizes (baseObject A B hS)
      (adicBaseIdeal A I B hS) h08BG
      (ObjectProperty.homMk fX : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
        schemeSpace (baseObject A B hS))
      (ObjectProperty.homMk fY : (⟨Y, hY⟩ : AlgebraicSpaces B (Spec (.of A)) hS) ⟶
        schemeSpace (baseObject A B hS))
      hproper hseparated hfinite (fun n => fibreMapOfAdicFibre A I B hS hSn hX hY fX fY n (g n))
      (fun n => fibreMapOfAdicFibre_over A I B hS hSn hX hY fX fY n (g n) (g_over n))
      (fun n => fibreTransition_comp_fibreMapOfAdicFibre A I B hS hSn hX hY fX fY n _ _
        (g_compatible n))
  refine ⟨⟨g'.hom, congrArg (fun k => k.hom) hq⟩, fun n =>
    (adicFibreMap_eq_iff_fibreInclusion_comp A I B hS hSn hX hY fX fY n _ (g_over n) g' _).2
      (hn n), ?_⟩
  rintro ⟨h', hh'⟩ hh''
  exact Subtype.ext (congrArg (fun k => k.hom) (huniq (ObjectProperty.homMk h')
    ⟨ObjectProperty.hom_ext _ hh', fun n => (adicFibreMap_eq_iff_fibreInclusion_comp A I B hS hSn
      hX hY fX fY n _ (g_over n) (ObjectProperty.homMk h') hh').1 (hh'' n)⟩))

end AlgebraicGeometry.Space
