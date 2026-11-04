module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsFlatBaseChange
public import StacksFrontier.RingTheory.IntegrallyClosed.FlatEqualizerNormal

/-!
# Normality of the global functions of a base change of a separated algebraic space

Let `A` be a ring, `T` an `A`-algebra, `X` a quasi-compact separated algebraic space over
`Spec A` and `X' = X ×_{Spec A} Spec T`. If the étale charts of `X'` are normal and locally
Noetherian and `Γ(X', 𝒪_{X'})` is a Noetherian ring, then `Γ(X', 𝒪_{X'})` is a normal ring.

The proof presents the global functions as an equalizer. An affine surjective étale chart `U`
of `X` has an affine kernel pair `V = U ×_X U`, `X` being separated (Stacks 08GB); their base
changes `U'` and `V'` to `Spec T` are an affine surjective étale chart of `X'` and its kernel
pair, so `Γ(X', 𝒪)` is the equalizer of the two restriction maps `Γ(U', 𝒪) ⇉ Γ(V', 𝒪)`
(Stacks 0792). Those maps are flat, `V' ⟶ U'` being étale, and `Γ(U', 𝒪)` is a Noetherian normal
ring, so `IsNormalRing.eqLocus_of_flat` applies.

No irreducible-component theory of algebraic spaces is used: the components of `X'` enter only
through those of the affine scheme `U'`.

## Main results

* `AlgebraicGeometry.Space.isNormalRing_globalFunctions_of_isPullback`: the global functions of
  the base change are a normal ring.

## References

* [Stacks Project, Tag 0792](https://stacks.math.columbia.edu/tag/0792)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
* [Stacks Project, Tag 030C](https://stacks.math.columbia.edu/tag/030C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (A T : Type u) [CommRing A] [CommRing T] [Algebra A T]
    {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))} (hT : B.Contains (Spec (.of T)))

attribute [local instance] siteObjSectionsAlgebra

variable {X X' : AlgebraicSpaces B (Spec (.of A)) hA}
    (f : X.obj ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    {q : X'.obj ⟶ X.obj} {r : X'.obj ⟶ yoneda.obj (specAlgebraObj A T B hA hT)}
    (hX' : IsPullback q r f (yoneda.map (siteTerminalHom B (Spec (.of A)) hA
      (specAlgebraObj A T B hA hT))))

/-- The base change to `Spec T` of an object of the site over `Spec A` with affine underlying
scheme has affine underlying scheme. -/
theorem isAffine_toScheme_siteBaseChange (U : BigFppfOver B (Spec (.of A)) hA)
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U)] :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj
      (pullback (siteTerminalHom B (Spec (.of A)) hA U)
        (siteTerminalHom B (Spec (.of A)) hA (specAlgebraObj A T B hA hT)))) := by
  have _ : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj
      (specAlgebraObj A T B hA hT)) := inferInstanceAs (IsAffine (Spec (.of T)))
  have _ : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj
      (Over.mk (𝟙 (B.obj hA)))) := inferInstanceAs (IsAffine (Spec (.of A)))
  exact IsAffine.of_isIso (isPullback_toScheme_siteBaseChangeObj B (Spec (.of A)) hA U
    (specAlgebraObj A T B hA hT)).isoPullback.hom

include hX' in
/-- **The global functions of the base change of a quasi-compact separated algebraic space with
normal Noetherian charts are a normal ring.** Let `X` be a quasi-compact separated algebraic
space over `Spec A`, `T` an `A`-algebra and `X' = X ×_{Spec A} Spec T`. If every étale chart of
`X'` is normal and locally Noetherian and `Γ(X', 𝒪_{X'})` is Noetherian, then `Γ(X', 𝒪_{X'})`
is a normal ring. -/
theorem isNormalRing_globalFunctions_of_isPullback (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompactSpace B (Spec (.of A)) hA X.obj)
    (hsep : IsAbsolutelySeparated B (Spec (.of A)) hA hZ X.obj)
    (hnorm : HasEtaleLocalProperty B (Spec (.of A)) hA X'.obj
      (fun Z : Scheme.{u} => IsNormal Z))
    (hlnoeth : HasEtaleLocalProperty B (Spec (.of A)) hA X'.obj
      (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (hnoeth : IsNoetherianRing (globalFunctions B (Spec (.of A)) hA X'.obj)) :
    IsNormalRing (globalFunctions B (Spec (.of A)) hA X'.obj) := by
  classical
  -- An affine surjective étale chart of `X`, with affine kernel pair.
  obtain ⟨U, a, hUaff, hasurj, haet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B (Spec (.of A)) hA X.obj
      X.property).mp hqc
  have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf (yoneda.map (𝟙 U)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B (Spec (.of A)) hA
      (@Etale.{u} : MorphismProperty Scheme.{u}) (𝟙 U)).2
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  have haet' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf a := by
    have h := haet U (yoneda.map (𝟙 U)) hid
    rwa [CategoryTheory.Functor.map_id, Category.id_comp] at h
  obtain ⟨W, p, qq, hsq⟩ := isAffineHom_of_affine_source_of_isAbsolutelySeparated
    B (Spec (.of A)) hA hZ ⟨U, hUaff⟩ a hsep ⟨U, hUaff⟩ a
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : (BigAffineFppf.inclusion B (Spec (.of A)) hA).obj W ⟶ U,
      yoneda.map p₀ = p := ⟨yoneda.preimage p, yoneda.map_preimage p⟩
  rw [← hp₀] at hsq
  have hp₀et : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)) p₀ :=
    haet'.property a (yoneda.map qq) p₀ hsq.flip
  let Uc : SmallEtale B (Spec (.of A)) hA X.obj := ⟨CostructuredArrow.mk a, haet'⟩
  let Vc : SmallEtale B (Spec (.of A)) hA X.obj :=
    ⟨CostructuredArrow.mk (yoneda.map p₀ ≫ a),
      chart_preimage_etale B (Spec (.of A)) hA X a haet' p₀ hp₀et⟩
  have : IsAffine (chartScheme Uc) := hUaff
  have : IsAffine (chartScheme Vc) := W.property
  let α : Vc ⟶ Uc := ObjectProperty.homMk (CostructuredArrow.homMk p₀ rfl)
  let β : Vc ⟶ Uc := ObjectProperty.homMk (CostructuredArrow.homMk qq hsq.w.symm)
  -- Their base changes: an affine surjective étale chart of `X'` and its kernel pair.
  let U' := siteBaseChangeEtaleChart A T hT f hX' Uc
  let V' := siteBaseChangeEtaleChart A T hT f hX' Vc
  let α' : V' ⟶ U' := siteBaseChangeEtaleChartHom A T hT f hX' α
  let β' : V' ⟶ U' := siteBaseChangeEtaleChartHom A T hT f hX' β
  have hcov' := coversTop_siteBaseChangeEtaleChart A T hT f hX' Uc hasurj
  have hsq' := isPullback_kernelPair_siteBaseChangeChartMap B (Spec (.of A)) hA f hX'
    ((SmallEtale.toOver B (Spec (.of A)) hA X.obj).map α)
    ((SmallEtale.toOver B (Spec (.of A)) hA X.obj).map β) hsq
  have hU'aff : IsAffine (chartScheme U') :=
    isAffine_toScheme_siteBaseChange A T hT ((SmallEtale.toOver B (Spec (.of A)) hA X.obj).obj Uc)
  have hV'aff : IsAffine (chartScheme V') :=
    isAffine_toScheme_siteBaseChange A T hT ((SmallEtale.toOver B (Spec (.of A)) hA X.obj).obj Vc)
  -- The two restriction maps are étale, hence flat on global sections.
  have hfl : ∀ g : V' ⟶ U', Etale ((BigFppfOver.toScheme B (Spec (.of A)) hA).map
      ((SmallEtale.toOver B (Spec (.of A)) hA X'.obj).map g)) →
      RingHom.Flat ((BigFppfOver.toScheme B (Spec (.of A)) hA).map
        ((SmallEtale.toOver B (Spec (.of A)) hA X'.obj).map g)).appTop.hom := fun g hg =>
    HasRingHomProperty.appTop @Flat _ (inferInstance : Flat _)
  have hαfl := hfl α' (U'.property.property U'.obj.hom _ _ hsq'.flip)
  have hβfl := hfl β' (U'.property.property U'.obj.hom _ _ hsq')
  -- The chart `U'` is a normal Noetherian affine scheme.
  have : IsNormal (chartScheme U') := (exists_atlas_iff_forall_etale B (Spec (.of A)) hA
    X'.obj (fun Z : Scheme.{u} => IsNormal Z) X'.property).mp hnorm
    U'.obj.left U'.obj.hom U'.property
  have : IsLocallyNoetherian (chartScheme U') := (exists_atlas_iff_forall_etale B
    (Spec (.of A)) hA X'.obj (fun Z : Scheme.{u} => IsLocallyNoetherian Z) X'.property).mp
    hlnoeth U'.obj.left U'.obj.hom U'.property
  have hPnorm : IsNormalRing Γ(chartScheme U', ⊤) := isNormalRing_appTop_of_isNormal _
  have hPnoeth : IsNoetherianRing Γ(chartScheme U', ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  -- The global functions of `X'` are the equalizer.
  let e : globalFunctions B (Spec (.of A)) hA X'.obj ≃+*
      RingHom.eqLocus
        ((BigFppfOver.toScheme B (Spec (.of A)) hA).map
          ((SmallEtale.toOver B (Spec (.of A)) hA X'.obj).map α')).appTop.hom
        ((BigFppfOver.toScheme B (Spec (.of A)) hA).map
          ((SmallEtale.toOver B (Spec (.of A)) hA X'.obj).map β')).appTop.hom :=
    (globalFunctionsEqualizerAlgEquiv A X' α' β' hcov' hsq').toRingEquiv.trans
      (eqLocusRingEquivEqualizer _ _ _ _ (fun _ => rfl) (fun _ => rfl)).symm
  have hEnoeth := isNoetherianRing_of_ringEquiv _ e
  exact IsNormalRing.congr e.symm
    (IsNormalRing.eqLocus_of_flat _ _ hαfl hβfl hPnorm
      (minimalPrimes.finite_of_isNoetherianRing _) (minimalPrimes.finite_of_isNoetherianRing _))

end AlgebraicGeometry.Space

end
