module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreDataTransport
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessLocal
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing

/-!
# Uniqueness of contractions over a Noetherian local ring

Let `Λ` be a Noetherian local ring with residue field `κ`, let `X`, `Y₁`, `Y₂` be proper flat
schemes of finite presentation over `Spec Λ` and let `cᵢ : X ⟶ Yᵢ` be morphisms over `Spec Λ`.
Suppose the special fibres `Y₁,ₛ` and `Y₂,ₛ` are identified by an isomorphism `φ` over `κ`
compatible with `c₁,ₛ` and `c₂,ₛ`, that the fibres of `c₁,ₛ` have dimension at most one, and that
`𝒪_{Y₁,ₛ} ≅ c₁,ₛ,* 𝒪_{Xₛ}` and `R¹c₁,ₛ,* 𝒪_{Xₛ} = 0`. Then there is an isomorphism `Y₁ ≅ Y₂`
over `Spec Λ` compatible with `c₁` and `c₂`.

This is the case of a Noetherian local base in the proof of [Stacks, Tag 0E89], and it is proved
as the source proves it: over the completion `Λ^∧` the complete case
(`AlgebraicGeometry.exists_iso_comp_eq_of_specialFibre_of_isAdicComplete_holds`) gives an
isomorphism of the base changes, and it descends along the faithfully flat `Spec Λ^∧ ⟶ Spec Λ`
because `c₁` is scheme-theoretically dominant
(`AlgebraicGeometry.exists_iso_desc_of_isSchemeTheoreticallyDominant`,
`AlgebraicGeometry.isSchemeTheoreticallyDominant_of_specialFibre_of_isLocalRing`). The source
phrases the descent through the scheme-theoretic image of `(c₁, c₂)` and its compatibility with
flat base change; the dominance of `c₁` is the same input.

## Main results

* `AlgebraicGeometry.C1590Private.isSchemeTheoreticallyDominant_of_fibre_closedPoint`: the
  dominance of `c₁`, from the conditions on the fibre at the closed point.
* `AlgebraicGeometry.C1590Private.exists_iso_comp_eq_of_specialFibre_of_isNoetherianLocal`: the
  statement above.

## References

* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
* [Stacks Project, Tag 0A42](https://stacks.math.columbia.edu/tag/0A42)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.C1590Private

open ContractionUniquenessComplete Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-! ### Isomorphisms of base changes -/

/-- An isomorphism `A₁ ≅ A₂` over `T` induces one of their base changes along `τ : T' ⟶ T`,
presented by any two cartesian squares. -/
def isoOfIsPullback {A₁ A₂ A₁' A₂' T T' : Scheme.{u}} {u₁ : A₁ ⟶ T} {u₂ : A₂ ⟶ T}
    {τ : T' ⟶ T} {a₁ : A₁' ⟶ A₁} {b₁ : A₁' ⟶ T'} {a₂ : A₂' ⟶ A₂} {b₂ : A₂' ⟶ T'}
    (P₁ : IsPullback a₁ b₁ u₁ τ) (P₂ : IsPullback a₂ b₂ u₂ τ) (φ : A₁ ≅ A₂)
    (hφ : φ.hom ≫ u₂ = u₁) : A₁' ≅ A₂' where
  hom := P₂.lift (a₁ ≫ φ.hom) b₁ (by rw [Category.assoc, hφ, P₁.w])
  inv := P₁.lift (a₂ ≫ φ.inv) b₂ (by rw [Category.assoc, ← hφ, φ.inv_hom_id_assoc, P₂.w])
  hom_inv_id := P₁.hom_ext (by simp) (by simp)
  inv_hom_id := P₂.hom_ext (by simp) (by simp)

/-- The isomorphism `isoOfIsPullback P₁ P₂ φ hφ` of base changes lies over `φ`. -/
@[reassoc (attr := simp)]
theorem isoOfIsPullback_hom_fst {A₁ A₂ A₁' A₂' T T' : Scheme.{u}} {u₁ : A₁ ⟶ T} {u₂ : A₂ ⟶ T}
    {τ : T' ⟶ T} {a₁ : A₁' ⟶ A₁} {b₁ : A₁' ⟶ T'} {a₂ : A₂' ⟶ A₂} {b₂ : A₂' ⟶ T'}
    (P₁ : IsPullback a₁ b₁ u₁ τ) (P₂ : IsPullback a₂ b₂ u₂ τ) (φ : A₁ ≅ A₂)
    (hφ : φ.hom ≫ u₂ = u₁) : (isoOfIsPullback P₁ P₂ φ hφ).hom ≫ a₂ = a₁ ≫ φ.hom :=
  P₂.lift_fst _ _ _

/-- The isomorphism `isoOfIsPullback P₁ P₂ φ hφ` of base changes lies over `T'`. -/
@[reassoc (attr := simp)]
theorem isoOfIsPullback_hom_snd {A₁ A₂ A₁' A₂' T T' : Scheme.{u}} {u₁ : A₁ ⟶ T} {u₂ : A₂ ⟶ T}
    {τ : T' ⟶ T} {a₁ : A₁' ⟶ A₁} {b₁ : A₁' ⟶ T'} {a₂ : A₂' ⟶ A₂} {b₂ : A₂' ⟶ T'}
    (P₁ : IsPullback a₁ b₁ u₁ τ) (P₂ : IsPullback a₂ b₂ u₂ τ) (φ : A₁ ≅ A₂)
    (hφ : φ.hom ≫ u₂ = u₁) : (isoOfIsPullback P₁ P₂ φ hφ).hom ≫ b₂ = b₁ :=
  P₂.lift_snd _ _ _

/-! ### Field-valued points through residue fields -/

/-- A morphism from the spectrum of a field to `S` hitting `x` factors through the residue field
of `x`, by a morphism which is the spectrum of a field extension. -/
theorem exists_comp_fromSpecResidueField {K : Type u} [Field K] {S : Scheme.{u}}
    (t : Spec (.of K) ⟶ S) (x : S) (hx : t (IsLocalRing.closedPoint K) = x) :
    ∃ φ : CommRingCat.of (S.residueField x) ⟶ CommRingCat.of K,
      Spec.map φ ≫ S.fromSpecResidueField x = t := by
  subst hx
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S t⟩

/-! ### Dominance of `c₁` from its fibre at the closed point -/

section Dominance

variable {Λ : Type u} [CommRing Λ] [IsLocalRing Λ]

/-- **The contraction is scheme-theoretically dominant.** Let `c : X ⟶ Y` be a morphism of schemes
over `Spec Λ`, `Λ` local, with `X` flat and both locally of finite presentation, `X` proper and `Y`
separated. If the fibres of `c` over the closed point `Spec κ ⟶ Spec Λ` have dimension at most one,
`𝒪_{Yₛ} ≅ cₛ,*𝒪_{Xₛ}` and `R¹cₛ,*𝒪_{Xₛ} = 0`, then `c` is scheme-theoretically dominant.

This is `AlgebraicGeometry.isSchemeTheoreticallyDominant_of_specialFibre_of_isLocalRing`, whose
hypotheses are stated at the residue field of the closed point of the scheme `Spec Λ` and for the
base change of `c` along `Yₛ ⟶ Y`; they are moved there from `Spec κ`. -/
theorem isSchemeTheoreticallyDominant_of_fibre_closedPoint {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (.of Λ)) (fY : Y ⟶ Spec (.of Λ)) [IsProper fX] [Flat fX]
    [LocallyOfFinitePresentation fX] [IsProper fY] [LocallyOfFinitePresentation fY]
    (c : X ⟶ Y) (hc : c ≫ fY = fX)
    (hdim : ∀ y, topologicalKrullDim
        ((fibreHom (ContractionUniquenessComplete.closedPoint Λ) fX fY c hc).fiber y) ≤
      ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit
      (fibreHom (ContractionUniquenessComplete.closedPoint Λ) fX fY c hc)))
    (hR : IsZero (((Scheme.Modules.pushforward
        (fibreHom (ContractionUniquenessComplete.closedPoint Λ) fX fY c hc)).rightDerived 1).obj
      (SheafOfModules.unit
        (pullback fX (ContractionUniquenessComplete.closedPoint Λ)).ringCatSheaf))) :
    IsSchemeTheoreticallyDominant c := by
  subst hc
  have : IsProper c := IsProper.of_comp c fY
  set s : Spec (.of Λ) := IsLocalRing.closedPoint Λ
  have : IsLocalHom (CommRingCat.ofHom (residue Λ)).hom :=
    inferInstanceAs (IsLocalHom (residue Λ))
  obtain ⟨φ, hφ⟩ := exists_comp_fromSpecResidueField (ContractionUniquenessComplete.closedPoint Λ)
    s Spec_closedPoint
  set t'' := (Spec (.of Λ)).fromSpecResidueField s
  have hst : ContractionUniquenessComplete.closedPoint Λ ≫ 𝟙 _ = Spec.map φ ≫ t'' := by
    rw [Category.comp_id, hφ]
  -- the fibre at `Spec κ` is the base change of the fibre at `Spec κ(s)`
  have H := isPullback_fibreHom hst (c ≫ fY) fY (c ≫ fY) fY (𝟙 X) (𝟙 Y) (by simp) (by simp)
    c rfl c rfl (by simp) (IsPullback.of_horiz_isIso ⟨rfl⟩)
  have hτ := flat_and_surjective_specMap_of_field φ
  have : Flat (Spec.map φ) := hτ.1
  have : Surjective (Spec.map φ) := hτ.2
  have hpY : fY ≫ 𝟙 _ = 𝟙 Y ≫ fY := by simp
  have hYsq := isPullback_fibreMap hst fY fY (𝟙 Y) hpY (IsPullback.of_horiz_isIso ⟨rfl⟩)
  have : Flat (fibreMap hst fY fY (𝟙 Y) hpY) :=
    MorphismProperty.of_isPullback hYsq.flip inferInstance
  have : Surjective (fibreMap hst fY fY (𝟙 Y) hpY) :=
    MorphismProperty.of_isPullback hYsq.flip inferInstance
  have : IsProper (fibreHom t'' (c ≫ fY) fY c rfl) :=
    MorphismProperty.of_isPullback (isPullback_fibreHom_fst t'' (c ≫ fY) fY c rfl)
      inferInstance
  have hdim'' : ∀ y, topologicalKrullDim ((fibreHom t'' (c ≫ fY) fY c rfl).fiber y) ≤
      ((1 : ℕ) : WithBot ℕ∞) := by
    intro y
    obtain ⟨y', rfl⟩ := (fibreMap hst fY fY (𝟙 Y) hpY).surjective y
    exact topologicalKrullDim_fiber_le_of_isPullback' H 1 y' (hdim y')
  obtain ⟨h0'', hR''⟩ := fibreConditions_of_isPullback_of_surjective H hdim'' h0 hR
  -- the fibre at `Spec κ(s)` is `X ×_Y Yₛ`
  have P₁ := isPullback_fibreHom_fst t'' (c ≫ fY) fY c rfl
  let k : pullback c (fY.fiberι s) ⟶ pullback fY t'' := pullback.snd c (fY.fiberι s)
  have w : pullback.fst c (fY.fiberι s) ≫ c = k ≫ pullback.fst fY t'' := pullback.condition
  have hsq : IsPullback (P₁.lift (pullback.fst c (fY.fiberι s)) k w) k
      (fibreHom t'' (c ≫ fY) fY c rfl) (𝟙 _) := by
    refine IsPullback.of_right ?_
      ((P₁.lift_snd (pullback.fst c (fY.fiberι s)) k w).trans (Category.comp_id _).symm) P₁
    rw [P₁.lift_fst (pullback.fst c (fY.fiberι s)) k w, Category.id_comp]
    exact IsPullback.of_hasPullback c (fY.fiberι s)
  obtain ⟨h0', hR'⟩ := fibreConditions_of_isPullback hsq hdim'' h0'' hR''
  have hfib : Stacks.Flatness.fiberHom c fY s = fibreHom t'' (c ≫ fY) fY c rfl :=
    pullback.hom_ext
      ((Stacks.Flatness.fiberHom_fiberι c fY s).trans (fibreHom_fst t'' _ fY c rfl).symm)
      ((Stacks.Flatness.fiberHom_fiberToSpecResidueField c fY s).trans
        (fibreHom_snd t'' _ fY c rfl).symm)
  refine isSchemeTheoreticallyDominant_of_specialFibre_of_isLocalRing c fY
    (fun x _ => Flat.stalkMap (c ≫ fY) x) (fun y => ?_) ((isZero_rightDerived_one_iff _).1 hR') h0'
  rw [hfib]
  exact hdim'' y

end Dominance

/-! ### The base change of a morphism over `S` -/

/-- The base change `X ×_S T ⟶ Y ×_S T` of a morphism `c : X ⟶ Y` over `S` is cartesian over
`c`. -/
theorem isPullback_pullbackMap_fst {S T X Y : Scheme.{u}} (π : T ⟶ S) {fX : X ⟶ S} {fY : Y ⟶ S}
    (c : X ⟶ Y) (hc : c ≫ fY = fX) :
    IsPullback (pullback.fst fX π)
      (pullback.map fX π fY π c (𝟙 T) (𝟙 S) (by simp [hc]) (by simp)) c (pullback.fst fY π) := by
  refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback fY π)
  rw [pullback.lift_snd, Category.comp_id, hc]
  exact IsPullback.of_hasPullback fX π

/-! ### The completion of a Noetherian local ring -/

section Completion

variable (Λ : Type u) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]

/-- The morphism `Spec Λ^∧ ⟶ Spec Λ` to the spectrum of a Noetherian local ring from that of its
completion. -/
abbrev completionMap : Spec (.of (AdicCompletion (maximalIdeal Λ) Λ)) ⟶ Spec (.of Λ) :=
  Spec.map (CommRingCat.ofHom (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ)))

/-- `Spec Λ^∧ ⟶ Spec Λ` is flat and surjective: `Λ^∧` is faithfully flat over `Λ`. -/
theorem flat_and_surjective_completionMap :
    Flat (completionMap Λ) ∧ Surjective (completionMap Λ) := by
  rw [flat_and_surjective_SpecMap_iff]
  change (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ)).FaithfullyFlat
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  exact AdicCompletion.faithfullyFlat_of_le_ringJacobson (maximalIdeal Λ) (by
    rw [← Ideal.jacobson_bot]
    exact IsLocalRing.maximalIdeal_le_jacobson ⊥)

/-- The closed point of `Spec Λ^∧` lies over the closed point of `Spec Λ`, through the map of
residue fields. -/
theorem closedPoint_comp_completionMap :
    ContractionUniquenessComplete.closedPoint (AdicCompletion (maximalIdeal Λ) Λ) ≫
        completionMap Λ =
      Spec.map (CommRingCat.ofHom (ResidueField.map
        (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ)))) ≫
          ContractionUniquenessComplete.closedPoint Λ := by
  simp only [ContractionUniquenessComplete.closedPoint, completionMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2

end Completion

/-! ### The Noetherian local case -/

section NoetherianLocal

variable {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]

/-- **Uniqueness of contractions over a Noetherian local ring** (the Noetherian local case of
[Stacks, Tag 0E89]). Let `Λ` be a Noetherian local ring with closed point `s : Spec κ ⟶ Spec Λ`,
let `X`, `Y₁`, `Y₂` be proper flat schemes over `Spec Λ`, `X` and `Y₁` of finite presentation, and
let `cᵢ : X ⟶ Yᵢ` be morphisms over `Spec Λ`. Let `φ : Y₁,ₛ ≅ Y₂,ₛ` be an isomorphism of special
fibres over `κ` with `c₁,ₛ ≫ φ = c₂,ₛ`. If the fibres of `c₁,ₛ` have dimension at most one,
`𝒪_{Y₁,ₛ} ≅ c₁,ₛ,*𝒪_{Xₛ}` and `R¹c₁,ₛ,*𝒪_{Xₛ} = 0`, there is an isomorphism `ψ : Y₁ ≅ Y₂` over
`Spec Λ` with `c₁ ≫ ψ = c₂`.

Over the completion `Λ^∧` the complete case gives such an isomorphism of the base changes; it
descends along the faithfully flat `Spec Λ^∧ ⟶ Spec Λ` because `c₁` is scheme-theoretically
dominant. -/
theorem exists_iso_comp_eq_of_specialFibre_of_isNoetherianLocal {X Y₁ Y₂ : Scheme.{u}}
    (fX : X ⟶ Spec (.of Λ)) (fY₁ : Y₁ ⟶ Spec (.of Λ)) (fY₂ : Y₂ ⟶ Spec (.of Λ))
    [IsProper fX] [Flat fX] [LocallyOfFinitePresentation fX] [IsProper fY₁] [Flat fY₁]
    [LocallyOfFinitePresentation fY₁] [IsProper fY₂] [Flat fY₂]
    (c₁ : X ⟶ Y₁) (hc₁ : c₁ ≫ fY₁ = fX) (c₂ : X ⟶ Y₂) (hc₂ : c₂ ≫ fY₂ = fX)
    (φ : pullback fY₁ (ContractionUniquenessComplete.closedPoint Λ) ≅
      pullback fY₂ (ContractionUniquenessComplete.closedPoint Λ))
    (hφ : φ.hom ≫ pullback.snd _ _ = pullback.snd _ _)
    (hφc : fibreHom (ContractionUniquenessComplete.closedPoint Λ) fX fY₁ c₁ hc₁ ≫ φ.hom =
      fibreHom (ContractionUniquenessComplete.closedPoint Λ) fX fY₂ c₂ hc₂)
    (hdim : ∀ y, topologicalKrullDim
        ((fibreHom (ContractionUniquenessComplete.closedPoint Λ) fX fY₁ c₁ hc₁).fiber y) ≤
      ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit
      (fibreHom (ContractionUniquenessComplete.closedPoint Λ) fX fY₁ c₁ hc₁)))
    (hR : IsZero (((Scheme.Modules.pushforward
        (fibreHom (ContractionUniquenessComplete.closedPoint Λ) fX fY₁ c₁ hc₁)).rightDerived 1).obj
      (SheafOfModules.unit
        (pullback fX (ContractionUniquenessComplete.closedPoint Λ)).ringCatSheaf))) :
    ∃ ψ : Y₁ ≅ Y₂, ψ.hom ≫ fY₂ = fY₁ ∧ c₁ ≫ ψ.hom = c₂ := by
  have := Stacks.AdicCompletion.NoetherianRing.solution (maximalIdeal Λ)
  set π := completionMap Λ
  obtain ⟨hfl, hsu⟩ := flat_and_surjective_completionMap Λ
  have : Flat π := hfl
  have : Surjective π := hsu
  have : IsProper c₁ := by
    subst hc₁
    exact IsProper.of_comp c₁ fY₁
  -- the base change to the completion
  set fX' := pullback.snd fX π
  set fY₁' := pullback.snd fY₁ π
  set fY₂' := pullback.snd fY₂ π
  set c₁' := pullback.map fX π fY₁ π c₁ (𝟙 _) (𝟙 _) (by simp [hc₁]) (by simp)
  set c₂' := pullback.map fX π fY₂ π c₂ (𝟙 _) (𝟙 _) (by simp [hc₂]) (by simp)
  have hc₁' : c₁' ≫ fY₁' = fX' := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hc₂' : c₂' ≫ fY₂' = fX' := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  -- the closed points
  have hst := closedPoint_comp_completionMap Λ
  have : Flat (Spec.map (CommRingCat.ofHom (ResidueField.map
      (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ))))) :=
    (flat_and_surjective_specMap_of_field _).1
  -- the special fibres of the base change are base changes of the special fibres
  have PY₁ := isPullback_fibreMap hst fY₁ fY₁' (pullback.fst fY₁ π) pullback.condition.symm
    (IsPullback.of_hasPullback fY₁ π)
  have PY₂ := isPullback_fibreMap hst fY₂ fY₂' (pullback.fst fY₂ π) pullback.condition.symm
    (IsPullback.of_hasPullback fY₂ π)
  have H₁ := isPullback_fibreHom hst fX fY₁ fX' fY₁' (pullback.fst fX π) (pullback.fst fY₁ π)
    pullback.condition.symm pullback.condition.symm c₁ hc₁ c₁' hc₁' (pullback.lift_fst _ _ _)
    (isPullback_pullbackMap_fst π c₁ hc₁)
  have H₂ := isPullback_fibreHom hst fX fY₂ fX' fY₂' (pullback.fst fX π) (pullback.fst fY₂ π)
    pullback.condition.symm pullback.condition.symm c₂ hc₂ c₂' hc₂' (pullback.lift_fst _ _ _)
    (isPullback_pullbackMap_fst π c₂ hc₂)
  -- the identification of special fibres over the completion
  set φ' := isoOfIsPullback PY₁ PY₂ φ hφ
  have hφ' : φ'.hom ≫ pullback.snd fY₂' (ContractionUniquenessComplete.closedPoint _) =
      pullback.snd fY₁' (ContractionUniquenessComplete.closedPoint _) :=
    isoOfIsPullback_hom_snd PY₁ PY₂ φ hφ
  have hφc' : fibreHom (ContractionUniquenessComplete.closedPoint _) fX' fY₁' c₁' hc₁' ≫ φ'.hom =
      fibreHom (ContractionUniquenessComplete.closedPoint _) fX' fY₂' c₂' hc₂' := by
    refine PY₂.hom_ext ?_ ?_
    · rw [Category.assoc, isoOfIsPullback_hom_fst, ← reassoc_of% H₁.w, hφc, H₂.w]
    · rw [Category.assoc, hφ', fibreHom_snd, fibreHom_snd]
  -- the two conditions over the completion
  have : Flat (fibreMap hst fY₁ fY₁' (pullback.fst fY₁ π) pullback.condition.symm) :=
    MorphismProperty.of_isPullback PY₁.flip inferInstance
  have : IsProper (fibreHom (ContractionUniquenessComplete.closedPoint Λ) fX fY₁ c₁ hc₁) :=
    MorphismProperty.of_isPullback (isPullback_fibreHom_fst _ fX fY₁ c₁ hc₁) inferInstance
  obtain ⟨h0', hR'⟩ := fibreConditions_of_isPullback H₁ hdim h0 hR
  -- the complete case, and descent along the completion
  obtain ⟨ψ₀, hψ₀, hcψ₀, -⟩ := exists_iso_comp_eq_of_specialFibre_of_isAdicComplete_holds
    inferInstance fX' fY₁' fY₂' c₁' hc₁' c₂' hc₂' φ' hφ' hφc' h0' hR'
  have := isSchemeTheoreticallyDominant_of_fibre_closedPoint fX fY₁ c₁ hc₁ hdim h0 hR
  exact (exists_iso_desc_of_isSchemeTheoreticallyDominant π c₁ hc₁ c₂ hc₂ ψ₀ hψ₀ hcψ₀).imp
    fun _ h => ⟨h.1, h.2.2⟩

end NoetherianLocal

end AlgebraicGeometry.C1590Private

end
