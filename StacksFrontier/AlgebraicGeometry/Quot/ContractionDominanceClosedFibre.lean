module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessLocal
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessComplete
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FibrewiseFiber

/-!
# Scheme-theoretic dominance of a contraction over a Noetherian local ring, from the closed fibre

Let `Λ` be a Noetherian local ring with residue field `κ`, and let `γ : X ⟶ Y` be a morphism of
schemes proper over `Spec Λ`, with `X` flat over `Spec Λ`. Write `γ_s : X ×_Λ κ ⟶ Y ×_Λ κ` for its
base change along the closed point `Spec κ ⟶ Spec Λ`. If the fibres of `γ_s` have dimension at
most one, `𝒪 ≅ γ_{s,*}𝒪` and `R¹γ_{s,*}𝒪 = 0`, then `γ` is scheme-theoretically dominant.

This is `AlgebraicGeometry.isSchemeTheoreticallyDominant_of_specialFibre_of_isLocalRing`, whose
special fibre is the scheme-theoretic fibre over the point `𝔪 ∈ Spec Λ`, that is the base change
along `Spec κ(𝔪) ⟶ Spec Λ`, read on the base change along `Spec κ ⟶ Spec Λ`: the two residue
fields are identified, and the hypotheses pass along the resulting isomorphisms of fibres.

## Main results

* `AlgebraicGeometry.isSchemeTheoreticallyDominant_of_closedFibre`: the statement above.

## References

* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
* [Stacks Project, Tag 0E7L](https://stacks.math.columbia.edu/tag/0E7L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

namespace AlgebraicGeometry

open ContractionUniquenessComplete

variable (A : CommRingCat.{u}) [IsLocalRing A]

/-- The stalk of `Spec A` at the closed point is a local ring. -/
instance isLocalRing_stalk_spec_closedPoint :
    IsLocalRing ((Spec A).presheaf.stalk (IsLocalRing.closedPoint A)) :=
  let x : Spec A := IsLocalRing.closedPoint A
  inferInstanceAs (IsLocalRing ((Spec A).presheaf.stalk x))

/-- The residue field of a local ring `A` and the residue field of `Spec A` at its closed point,
as an isomorphism of spectra over `Spec A`. -/
def closedPointResidueFieldIso :
    Spec (.of (ResidueField A)) ≅ Spec ((Spec A).residueField (IsLocalRing.closedPoint A)) :=
  Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    (ResidueField.mapEquiv (stalkClosedPointIso A).commRingCatIsoToRingEquiv)).op

/-- The isomorphism `closedPointResidueFieldIso A` followed by the morphism from the spectrum of
the residue field of `Spec A` at its closed point is `Spec` of the residue map `A → κ(A)`. -/
theorem closedPointResidueFieldIso_hom_fromSpecResidueField :
    (closedPointResidueFieldIso A).hom ≫
        (Spec A).fromSpecResidueField (IsLocalRing.closedPoint A) =
      Spec.map (CommRingCat.ofHom (residue A)) := by
  change Spec.map _ ≫ _ = _
  dsimp only [Scheme.fromSpecResidueField]
  rw [← Spec_stalkClosedPointIso]
  have h : CommRingCat.ofHom (residue (A : Type u)) =
      (stalkClosedPointIso A).inv ≫ (Spec A).residue (IsLocalRing.closedPoint A) ≫
        CommRingCat.ofHom
          (ResidueField.mapEquiv
            (stalkClosedPointIso A).commRingCatIsoToRingEquiv).toRingHom := by
    ext a
    change residue (A : Type u) a =
      (ResidueField.mapEquiv (stalkClosedPointIso A).commRingCatIsoToRingEquiv)
        (residue _ ((stalkClosedPointIso A).inv a))
    rw [ResidueField.mapEquiv_apply, ResidueField.map_residue]
    exact congrArg (residue (A : Type u))
      (ConcreteCategory.congr_hom (stalkClosedPointIso A).inv_hom_id a).symm
  rw [h, Spec.map_comp ((stalkClosedPointIso A).inv)
      ((Spec A).residue (IsLocalRing.closedPoint (A : Type u)) ≫
        CommRingCat.ofHom
          (ResidueField.mapEquiv
            (stalkClosedPointIso A).commRingCatIsoToRingEquiv).toRingHom),
    Spec.map_comp ((Spec A).residue (IsLocalRing.closedPoint (A : Type u)))
      (CommRingCat.ofHom
        (ResidueField.mapEquiv
          (stalkClosedPointIso A).commRingCatIsoToRingEquiv).toRingHom),
    Category.assoc]
  rfl

variable {Λ : Type u} [CommRing Λ] [IsLocalRing Λ]

/-- **A contraction over a Noetherian local ring is scheme-theoretically dominant, from the
closed fibre.** Let `γ : X ⟶ Y` be a morphism over `Spec Λ` of schemes proper over `Spec Λ`, with
`X` flat over `Spec Λ`. If its base change `γ_s` along the closed point `Spec κ ⟶ Spec Λ` has
fibres of dimension at most one, `𝒪 ≅ γ_{s,*}𝒪` and `R¹γ_{s,*}𝒪 = 0`, then `γ` is
scheme-theoretically dominant. -/
theorem isSchemeTheoreticallyDominant_of_closedFibre [IsNoetherianRing Λ] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (.of Λ)) (fY : Y ⟶ Spec (.of Λ)) [IsProper fX] [Flat fX] [IsProper fY]
    (γ : X ⟶ Y) (hγ : γ ≫ fY = fX)
    (hdim : ∀ y, topologicalKrullDim ((specialMap fX fY γ hγ).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit (specialMap fX fY γ hγ)))
    (hR : IsZero (firstDirectImageStructureSheaf (specialMap fX fY γ hγ))) :
    IsSchemeTheoreticallyDominant γ := by
  obtain ⟨s₀, hs₀⟩ : ∃ s : Spec (.of Λ), s = IsLocalRing.closedPoint Λ := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Spec (.of (ResidueField Λ)) ≅ Spec ((Spec (.of Λ)).residueField s₀),
      ρ.hom ≫ (Spec (.of Λ)).fromSpecResidueField s₀ =
        ContractionUniquenessComplete.closedPoint Λ := by
    subst hs₀
    exact ⟨_, closedPointResidueFieldIso_hom_fromSpecResidueField (CommRingCat.of Λ)⟩
  have : IsProper (γ ≫ fY) := hγ ▸ inferInstance
  have : LocallyOfFinitePresentation (γ ≫ fY) := hγ ▸ inferInstance
  have : Flat (γ ≫ fY) := hγ ▸ inferInstance
  have : IsProper γ := IsProper.of_comp _ fY
  set sm := specialMap fX fY γ hγ
  have : IsProper sm := by
    have : IsProper (sm ≫ pullback.snd fY (ContractionUniquenessComplete.closedPoint Λ)) := by
      rw [specialMap_snd]
      infer_instance
    exact IsProper.of_comp _ (pullback.snd fY (ContractionUniquenessComplete.closedPoint Λ))
  have hP : IsPullback (pullback.fst fY (ContractionUniquenessComplete.closedPoint Λ))
      (pullback.snd fY (ContractionUniquenessComplete.closedPoint Λ) ≫ ρ.hom)
      fY ((Spec (.of Λ)).fromSpecResidueField s₀) :=
    IsPullback.of_iso (IsPullback.of_hasPullback fY (ContractionUniquenessComplete.closedPoint Λ))
      (Iso.refl _) (Iso.refl _) ρ (Iso.refl _) (by simp) (by simp) (by simp) (by simp [hρ])
  let τ : pullback fY (ContractionUniquenessComplete.closedPoint Λ) ≅ fY.fiber s₀ :=
    hP.isoPullback
  have hτ : τ.inv ≫ pullback.fst fY (ContractionUniquenessComplete.closedPoint Λ) =
      fY.fiberι s₀ := hP.isoPullback_inv_fst
  have hA : IsPullback (pullback.fst fX (ContractionUniquenessComplete.closedPoint Λ)) sm γ
      (pullback.fst fY (ContractionUniquenessComplete.closedPoint Λ)) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback fY _)
    rw [specialMap_snd, hγ]
    exact IsPullback.of_hasPullback fX (ContractionUniquenessComplete.closedPoint Λ)
  have key : ∀ {P : Scheme.{u}} {a : P ⟶ X} {f' : P ⟶ fY.fiber s₀},
      IsPullback a f' γ (fY.fiberι s₀) → ∃ g', IsPullback g' f' sm τ.inv := by
    intro P a f' h
    refine ⟨hA.lift a (f' ≫ τ.inv) (by rw [h.w, Category.assoc, hτ]), ?_⟩
    refine IsPullback.of_right ?_ (hA.lift_snd _ _ _) hA
    rw [hA.lift_fst, hτ]
    exact h
  obtain ⟨g₁', H₁⟩ := key (IsPullback.of_hasPullback γ (fY.fiberι s₀))
  obtain ⟨g₂', H₂⟩ := key (Stacks.Flatness.isPullback_fiberHom γ fY s₀).flip
  obtain ⟨hR', h0'⟩ := isZero_and_isIso_of_isPullback H₁ hdim hR h0
  have hflat : ∀ x : X, (γ ≫ fY) x = s₀ → IsFlatAt (γ ≫ fY).toLRSHom.toShHom x :=
    fun x _ => Flat.stalkMap (γ ≫ fY) x
  have : IsIso g₂' := H₂.isIso_fst_of_isIso
  have H₂' : IsPullback (inv g₂') sm (Stacks.Flatness.fiberHom γ fY s₀) τ.hom :=
    IsPullback.of_horiz_isIso ⟨by rw [IsIso.inv_comp_eq, reassoc_of% H₂.w,
      Iso.inv_hom_id, Category.comp_id]⟩
  have : LocallyOfFiniteType (Stacks.Flatness.fiberHom γ fY s₀) :=
    MorphismProperty.of_isPullback (Stacks.Flatness.isPullback_fiberHom γ fY s₀).flip
      (inferInstance : LocallyOfFiniteType γ)
  have hdim' : ∀ y : fY.fiber s₀, topologicalKrullDim
      ((Stacks.Flatness.fiberHom γ fY s₀).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    intro y
    have h := topologicalKrullDim_fiber_le_of_isPullback' H₂' 1 (τ.inv y) (hdim _)
    have e : τ.hom (τ.inv y) = y := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    rwa [e] at h
  subst hs₀
  exact isSchemeTheoreticallyDominant_of_specialFibre_of_isLocalRing γ fY hflat hdim' hR' h0'

end AlgebraicGeometry

end
