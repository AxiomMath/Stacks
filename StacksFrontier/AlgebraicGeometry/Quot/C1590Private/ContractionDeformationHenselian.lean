module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ContractionDeformationComplete
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ApproximationSection
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.NoetherianModelContraction
public import StacksFrontier.AlgebraicGeometry.Limits.AdjoinFinsetSystem

/-!
# Deforming a contraction over a henselian G-ring (a step of Stacks 0E7C)

Let `Λ` be a Noetherian henselian local G-ring with residue field `κ`, let `X` be a proper flat
scheme over `Spec Λ` and let `h₀ : Xₛ ⟶ Y₀` be a morphism from its special fibre to a proper scheme
of dimension at most one over `κ` with `𝒪_{Y₀} ≅ h₀,*𝒪_{Xₛ}` and `R¹h₀,*𝒪_{Xₛ} = 0`. Then there
are a proper flat `Y ⟶ Spec Λ` and a morphism `h : X ⟶ Y` over `Spec Λ` whose special fibre is
`h₀`.

This is the step "Assume `S = Spec(Λ)` where `Λ` is a henselian G-ring" of the proof of
[Stacks, Tag 0E7C], proved as the source proves it: the complete case over the completion `Λ^∧`
(`AlgebraicGeometry.C1590Private.ContractionDeformation.exists_contraction_of_isAdicComplete`)
gives `Y'` and `h'`; they descend to a finitely generated `Λ`-subalgebra `A ⊆ Λ^∧`, and the
approximation property ([Stacks, Tag 07QY],
`AlgebraicGeometry.C1590Private.exists_approximationSection`) gives `σ : A ⟶ Λ` inducing the same
map `A ⟶ κ` as the inclusion; the base change of the model along `σ` is the required `(Y, h)`.

The special fibres are handled through cartesian presentations: the fibre of `X` over a point
`t : T ⟶ Spec Λ` is any cartesian square `V ⟶ X` over `t`, and the conclusion identifies `Y₀` with
the fibre of `Y` by a cartesian square `Y₀ ⟶ Y` over `t` carrying `h₀` to `h`.

## Main results

* `exists_contraction_of_isAdicComplete_of_isPullback`:
  the complete case, with the fibres read on cartesian presentations.
* `exists_contraction_of_henselian_isGRing`:
  the statement above.

## References

* [Stacks Project, Tag 0E7C](https://stacks.math.columbia.edu/tag/0E7C)
* [Stacks Project, Tag 07QY](https://stacks.math.columbia.edu/tag/07QY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.C1590Private

namespace ContractionDeformation

/-! ### Cartesian squares along isomorphisms -/

/-- A cartesian square over `e ≫ t` with `e` an isomorphism is a cartesian square over `t`. -/
theorem isPullback_comp_iso_iff {V X T T' S : Scheme.{u}} (q : V ⟶ X) (v : V ⟶ T) (f : X ⟶ S)
    (e : T ⟶ T') [IsIso e] (t : T' ⟶ S) :
    IsPullback q v f (e ≫ t) ↔ IsPullback q (v ≫ e) f t := by
  have key : ∀ {T T' : Scheme.{u}} (v : V ⟶ T) (e : T ⟶ T') [IsIso e] (t : T' ⟶ S),
      IsPullback q (v ≫ e) f t → IsPullback q v f (e ≫ t) := fun v e _ t h => by
    have hl : IsPullback (𝟙 V) v (v ≫ e) e := IsPullback.of_horiz_isIso ⟨by simp⟩
    simpa using hl.paste_horiz h
  refine ⟨fun h => ?_, key v e t⟩
  have h' : IsPullback q ((v ≫ e) ≫ inv e) f (e ≫ t) := by simpa using h
  simpa using key (v ≫ e) (inv e) (e ≫ t) h'

/-! ### The complete case on cartesian presentations -/

variable {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]

/-- **The fibre conditions of a morphism out of a curve.** If `dim V ≤ 1`, every fibre of a
morphism out of `V` has dimension at most one. -/
theorem topologicalKrullDim_fiber_le_of_le {V Y : Scheme.{u}} (h : V ⟶ Y)
    (hdim : topologicalKrullDim V ≤ ((1 : ℕ) : WithBot ℕ∞)) (y : Y) :
    topologicalKrullDim (h.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
  (Topology.IsInducing.topologicalKrullDim_le (h.fiberι y).isEmbedding.isInducing).trans hdim

/-- **Deforming a contraction over a complete local ring, on cartesian presentations.** Let `Λ`
be a complete Noetherian local ring, `X` proper and flat over `Spec Λ`, and let `t = e ≫ s` be
the closed point `s : Spec κ ⟶ Spec Λ` precomposed with an isomorphism `e : T ⟶ Spec κ`. Let
`V ⟶ X` be a cartesian presentation of the fibre over `t`, of dimension at most one, and
`h₀ : V ⟶ Y₀` a morphism over `T` to a proper scheme of dimension at most one with
`𝒪_{Y₀} ≅ h₀,*𝒪_V` and `R¹h₀,*𝒪_V = 0`. Then there are a proper flat `Y ⟶ Spec Λ`, a morphism
`h : X ⟶ Y` over `Spec Λ`, and a cartesian presentation `Y₀ ⟶ Y` of the fibre over `t` carrying
`h₀` to `h`. -/
theorem exists_contraction_of_isAdicComplete_of_isPullback
    (hc : IsAdicComplete (maximalIdeal Λ) Λ) {X : Scheme.{u}} (fX : X ⟶ Spec (.of Λ))
    [IsProper fX] [Flat fX] {T V Y₀ : Scheme.{u}} (e : T ⟶ Spec (.of (ResidueField Λ)))
    [IsIso e] (qV : V ⟶ X) (v : V ⟶ T)
    (hV : IsPullback qV v fX (e ≫ ContractionUniquenessComplete.closedPoint Λ))
    (gY₀ : Y₀ ⟶ T) [IsProper gY₀] (h₀ : V ⟶ Y₀) (hh₀ : h₀ ≫ gY₀ = v)
    (hdimV : topologicalKrullDim V ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit V.ringCatSheaf)))
    (hdimY : topologicalKrullDim Y₀ ≤ ((1 : ℕ) : WithBot ℕ∞)) :
    ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of Λ)) (h : X ⟶ Y), h ≫ fY = fX ∧ IsProper fY ∧
      Flat fY ∧ ∃ iY : Y₀ ⟶ Y,
        IsPullback iY gY₀ fY (e ≫ ContractionUniquenessComplete.closedPoint Λ) ∧
          h₀ ≫ iY = qV ≫ h := by
  have hV' := (isPullback_comp_iso_iff qV v fX e (ContractionUniquenessComplete.closedPoint Λ)).1 hV
  have : IsProper v := MorphismProperty.of_isPullback hV inferInstance
  have : IsProper (h₀ ≫ gY₀) := by rw [hh₀]; infer_instance
  have : IsProper h₀ := IsProper.of_comp h₀ gY₀
  set j := hV'.isoPullback
  set h₀' : pullback fX (ContractionUniquenessComplete.closedPoint Λ) ⟶ Y₀ := j.inv ≫ h₀
  have hh₀' : h₀' ≫ gY₀ ≫ e = pullback.snd fX (ContractionUniquenessComplete.closedPoint Λ) := by
    rw [Category.assoc, reassoc_of% hh₀, IsPullback.isoPullback_inv_snd]
  have H : IsPullback j.inv h₀' h₀ (𝟙 Y₀) := IsPullback.of_horiz_isIso ⟨by simp [h₀']⟩
  obtain ⟨h0', hR'⟩ := fibreConditions_of_isPullback H
    (topologicalKrullDim_fiber_le_of_le h₀ hdimV) h0 hR
  have : IsProper (gY₀ ≫ e) := inferInstance
  obtain ⟨Y, fY, h, hh, -, hpr, hfl, ι, hι, hιh⟩ :=
    exists_contraction_of_isAdicComplete hc fX (gY₀ ≫ e) h₀' hh₀' h0' hR' hdimY
  refine ⟨Y, fY, h, hh, hpr, hfl,
    ι.hom ≫ pullback.fst fY (ContractionUniquenessComplete.closedPoint Λ), ?_, ?_⟩
  · rw [isPullback_comp_iso_iff, ← hι]
    exact IsPullback.of_iso_pullback ⟨by rw [Category.assoc, Category.assoc, pullback.condition]⟩ ι
      (by simp) (by simp)
  · have := congrArg (j.hom ≫ · ≫ pullback.fst fY (ContractionUniquenessComplete.closedPoint Λ)) hιh
    simp only [h₀', Category.assoc, Iso.hom_inv_id_assoc, fibreHom_fst] at this
    rw [this, ← Category.assoc, IsPullback.isoPullback_hom_fst]

/-! ### The henselian G-ring case -/

section Henselian

variable {Λ : Type u} [CommRing Λ] [HenselianLocalRing Λ]

/-- The residue field of `Λ` is that of its completion. -/
theorem isIso_residueSpecMap_completion [IsNoetherianRing Λ] :
    IsIso (Spec.map (CommRingCat.ofHom (ResidueField.map
      (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ))))) := by
  have hb := AdicCompletion.residueField_map_bijective_of_fg
    (maximalIdeal Λ).fg_of_isNoetherianRing
  have : IsIso (CommRingCat.ofHom (ResidueField.map
      (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ)))) :=
    inferInstanceAs (IsIso (RingEquiv.ofBijective _ hb).toCommRingCatIso.hom)
  infer_instance

/-- An approximate section `σ : A ⟶ Λ` of `A ⊆ Λ^∧` induces the same map `A ⟶ κ` as the inclusion:
the closed points of `Spec Λ` and `Spec Λ^∧` have the same image in `Spec A`. -/
theorem closedPoint_comp_specMap_section [IsNoetherianRing Λ]
    (A : Subalgebra Λ (AdicCompletion (maximalIdeal Λ) Λ)) (σ : A →ₐ[Λ] Λ)
    (hσ : ∀ a : A, (a : AdicCompletion (maximalIdeal Λ) Λ) -
      algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ) (σ a) ∈
        (maximalIdeal Λ).map (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ))) :
    Spec.map (CommRingCat.ofHom (ResidueField.map
        (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ)))) ≫
      ContractionUniquenessComplete.closedPoint Λ ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) =
    ContractionUniquenessComplete.closedPoint (AdicCompletion (maximalIdeal Λ) Λ) ≫
      Spec.map (CommRingCat.ofHom A.val.toRingHom) := by
  simp only [ContractionUniquenessComplete.closedPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, ResidueField.map_residue]
  refine (sub_eq_zero.1 ?_).symm
  rw [← map_sub, residue_eq_zero_iff, AdicCompletion.maximalIdeal_eq_map]
  exact hσ a

/-- **Deforming a contraction over a henselian G-ring** (a step of [Stacks, Tag 0E7C]). Let `Λ` be
a Noetherian henselian local G-ring, `X` proper and flat over `Spec Λ`, and let `t = e ≫ s` be the
closed point `s : Spec κ ⟶ Spec Λ` precomposed with an isomorphism `e : T ⟶ Spec κ`. Let `V ⟶ X` be
a cartesian presentation of the fibre over `t`, of dimension at most one, and `h₀ : V ⟶ Y₀` a
morphism over `T` to a proper scheme of dimension at most one with `𝒪_{Y₀} ≅ h₀,*𝒪_V` and
`R¹h₀,*𝒪_V = 0`. Then there are a proper flat `Y ⟶ Spec Λ`, a morphism `h : X ⟶ Y` over `Spec Λ`,
and a cartesian presentation `Y₀ ⟶ Y` of the fibre over `t` carrying `h₀` to `h`. -/
theorem exists_contraction_of_henselian_isGRing (hG : IsGRing Λ) {X : Scheme.{u}}
    (fX : X ⟶ Spec (.of Λ)) [IsProper fX] [Flat fX] {T V Y₀ : Scheme.{u}}
    (e₀ : T ⟶ Spec (.of (ResidueField Λ))) [IsIso e₀] (qV : V ⟶ X) (v : V ⟶ T)
    (hV : IsPullback qV v fX (e₀ ≫ ContractionUniquenessComplete.closedPoint Λ))
    (gY₀ : Y₀ ⟶ T) [IsProper gY₀] (h₀ : V ⟶ Y₀) (hh₀ : h₀ ≫ gY₀ = v)
    (hdimV : topologicalKrullDim V ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit V.ringCatSheaf)))
    (hdimY : topologicalKrullDim Y₀ ≤ ((1 : ℕ) : WithBot ℕ∞)) :
    ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of Λ)) (h : X ⟶ Y), h ≫ fY = fX ∧ IsProper fY ∧
      Flat fY ∧ ∃ iY : Y₀ ⟶ Y,
        IsPullback iY gY₀ fY (e₀ ≫ ContractionUniquenessComplete.closedPoint Λ) ∧
          h₀ ≫ iY = qV ≫ h := by
  have : IsNoetherianRing Λ := hG.1
  have := Stacks.AdicCompletion.NoetherianRing.solution (maximalIdeal Λ)
  let π := completionMap Λ
  have : Flat π := (flat_and_surjective_completionMap Λ).1
  let τ := Spec.map (CommRingCat.ofHom
    (ResidueField.map (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ))))
  have : IsIso τ := isIso_residueSpecMap_completion
  have hτ : ContractionUniquenessComplete.closedPoint (AdicCompletion (maximalIdeal Λ) Λ) ≫ π =
      τ ≫ ContractionUniquenessComplete.closedPoint Λ := closedPoint_comp_completionMap Λ
  let e := e₀ ≫ inv τ
  have he : (e ≫ ContractionUniquenessComplete.closedPoint (AdicCompletion (maximalIdeal Λ) Λ)) ≫
      π = e₀ ≫ ContractionUniquenessComplete.closedPoint Λ := by
    simp only [e, Category.assoc, hτ, IsIso.inv_hom_id_assoc]
  let fX' := pullback.snd fX π
  have : IsProper fX' := MorphismProperty.of_isPullback (IsPullback.of_hasPullback fX π)
    inferInstance
  have sqX' : IsPullback (pullback.fst fX π) fX' fX π := IsPullback.of_hasPullback fX π
  let qV' : V ⟶ pullback fX π :=
    sqX'.lift qV
      (v ≫ e ≫ ContractionUniquenessComplete.closedPoint (AdicCompletion (maximalIdeal Λ) Λ))
      (by rw [hV.w, Category.assoc, Category.assoc, ← Category.assoc e, he])
  have hqV'₁ : qV' ≫ pullback.fst fX π = qV := sqX'.lift_fst _ _ _
  have hqV'₂ : qV' ≫ fX' =
      v ≫ e ≫ ContractionUniquenessComplete.closedPoint (AdicCompletion (maximalIdeal Λ) Λ) :=
    sqX'.lift_snd _ _ _
  have hV' : IsPullback qV' v fX'
      (e ≫ ContractionUniquenessComplete.closedPoint (AdicCompletion (maximalIdeal Λ) Λ)) :=
    IsPullback.of_right' (by rw [he]; exact hV) sqX'
  obtain ⟨Y', fY', h', hh', hpr', hfl', iY', hiY', hiYh'⟩ :=
    exists_contraction_of_isAdicComplete_of_isPullback (inferInstance : IsAdicComplete
      (maximalIdeal (AdicCompletion (maximalIdeal Λ) Λ)) (AdicCompletion (maximalIdeal Λ) Λ))
      fX' e qV' v hV' gY₀ h₀ hh₀ hdimV h0 hR hdimY
  have : LocallyOfFinitePresentation fY' := inferInstance
  let E := AdjoinFinset.specDiagram Λ (AdicCompletion (maximalIdeal Λ) Λ)
  let c₀ := AdjoinFinset.specCone Λ (AdicCompletion (maximalIdeal Λ) Λ)
  let c : Cone E :=
    { pt := Spec (.of (AdicCompletion (maximalIdeal Λ) Λ))
      π := { app := fun i => c₀.π.app i, naturality := fun _ _ a => c₀.π.naturality a } }
  have hc : IsLimit c := AdjoinFinset.isLimitSpecCone Λ (AdicCompletion (maximalIdeal Λ) Λ)
  have : ∀ {i j : (Finset (AdicCompletion (maximalIdeal Λ) Λ))ᵒᵖ} (a : i ⟶ j),
      IsAffineHom (E.map a) := fun a => by
    dsimp [E, AdjoinFinset.specDiagram]
    infer_instance
  have : ∀ i : (Finset (AdicCompletion (maximalIdeal Λ) Λ))ᵒᵖ, IsAffine (E.obj i) := fun i =>
    inferInstanceAs (IsAffine (Spec _))
  have : ∀ i : (Finset (AdicCompletion (maximalIdeal Λ) Λ))ᵒᵖ, CompactSpace (E.obj i) :=
    fun i => inferInstance
  have : ∀ i : (Finset (AdicCompletion (maximalIdeal Λ) Λ))ᵒᵖ,
      QuasiSeparatedSpace (E.obj i) := fun i => quasiSeparatedSpace_of_isAffine _
  let ρ := AdjoinFinset.specToBase Λ (AdicCompletion (maximalIdeal Λ) Λ)
  have hρπ : ∀ i, c.π.app i ≫ ρ.app i = π := fun i =>
    AdjoinFinset.specCone_π_comp Λ (AdicCompletion (maximalIdeal Λ) Λ) i
  have hρ : ∀ {i j : (Finset (AdicCompletion (maximalIdeal Λ) Λ))ᵒᵖ} (a : j ⟶ i),
      E.map a ≫ ρ.app i = ρ.app j := fun a => by simp
  obtain ⟨i, Y₁, fY₁, gY, hY₁p, hY₁f, hY₁l, sqY⟩ :=
    exists_properFlat_stageModel E c hc fY'
  let fX₁ := pullback.snd fX (ρ.app i)
  have sqX₁ : IsPullback (pullback.fst fX (ρ.app i)) fX₁ fX (ρ.app i) :=
    IsPullback.of_hasPullback fX (ρ.app i)
  have : IsProper fX₁ := MorphismProperty.of_isPullback sqX₁ inferInstance
  let gX : pullback fX π ⟶ pullback fX (ρ.app i) := sqX₁.lift (pullback.fst fX π)
    (fX' ≫ c.π.app i) (by rw [pullback.condition, Category.assoc, hρπ])
  have sqX : IsPullback gX fX' fX₁ (c.π.app i) :=
    IsPullback.of_right' (by rw [hρπ]; exact sqX') sqX₁
  obtain ⟨j, a, h₂, hh₂, hh₂c⟩ := exists_stageModel_hom E c hc sqX sqY h' hh'
  let fX₂ := pullback.fst (E.map a) fX₁
  let fY₂ := pullback.fst (E.map a) fY₁
  have sqX₂ := isPullback_stageLift (E := E) (c := c) sqX a
  have sqY₂ := isPullback_stageLift (E := E) (c := c) sqY a
  have : IsProper fY₂ := prop_fst_stage @IsProper a hY₁p
  have : Flat fY₂ := prop_fst_stage @Flat a hY₁f
  let pX₂ : pullback (E.map a) fX₁ ⟶ X := pullback.snd (E.map a) fX₁ ≫ pullback.fst fX (ρ.app i)
  have hX₂ : IsPullback pX₂ fX₂ fX (ρ.app j) := by
    have := (IsPullback.of_hasPullback (E.map a) fX₁).flip.paste_horiz sqX₁
    rwa [hρ a] at this
  let A := Algebra.adjoin Λ ((Opposite.unop j : Finset (AdicCompletion (maximalIdeal Λ) Λ)) :
    Set (AdicCompletion (maximalIdeal Λ) Λ))
  have : Algebra.FiniteType Λ A := Algebra.FiniteType.adjoin_of_finite (Finset.finite_toSet _)
  obtain ⟨σ, hσ⟩ := exists_approximationSection hG A.val
  let ψ : Spec (.of Λ) ⟶ E.obj j := Spec.map (CommRingCat.ofHom σ.toRingHom)
  have hring : CommRingCat.ofHom (algebraMap Λ A) ≫ CommRingCat.ofHom σ.toRingHom = 𝟙 _ :=
    CommRingCat.hom_ext (RingHom.ext fun x => σ.commutes x)
  have hψρ : ψ ≫ ρ.app j = 𝟙 _ :=
    (Spec.map_comp (CommRingCat.ofHom (algebraMap Λ A)) (CommRingCat.ofHom σ.toRingHom)).symm.trans
      ((congrArg Spec.map hring).trans (Spec.map_id _))
  have hψ0 : τ ≫ ContractionUniquenessComplete.closedPoint Λ ≫ ψ =
      ContractionUniquenessComplete.closedPoint (AdicCompletion (maximalIdeal Λ) Λ) ≫ c.π.app j :=
    closedPoint_comp_specMap_section A σ hσ
  have hψ : (e₀ ≫ ContractionUniquenessComplete.closedPoint Λ) ≫ ψ =
      (e ≫ ContractionUniquenessComplete.closedPoint (AdicCompletion (maximalIdeal Λ) Λ)) ≫
        c.π.app j := by
    simp only [e, Category.assoc]
    rw [← hψ0, IsIso.inv_hom_id_assoc]
  let fY := pullback.snd fY₂ ψ
  have sqY₃ : IsPullback (pullback.fst fY₂ ψ) fY fY₂ ψ := IsPullback.of_hasPullback fY₂ ψ
  have : IsProper fY := MorphismProperty.of_isPullback sqY₃ inferInstance
  have : Flat fY := MorphismProperty.of_isPullback sqY₃ inferInstance
  let jX : X ⟶ pullback (E.map a) fX₁ := hX₂.lift (𝟙 X) (fX ≫ ψ) (by
    rw [Category.id_comp, Category.assoc, hψρ, Category.comp_id])
  have hjX₁ : jX ≫ pX₂ = 𝟙 X := hX₂.lift_fst _ _ _
  have hjX₂ : jX ≫ fX₂ = fX ≫ ψ := hX₂.lift_snd _ _ _
  let h : X ⟶ pullback fY₂ ψ := sqY₃.lift (jX ≫ h₂) fX (by rw [Category.assoc, hh₂, hjX₂])
  have hh : h ≫ fY = fX := sqY₃.lift_snd _ _ _
  have hhf : h ≫ pullback.fst fY₂ ψ = jX ≫ h₂ := sqY₃.lift_fst _ _ _
  have key : qV' ≫ stageLift (E := E) (c := c) sqX a = qV ≫ jX := by
    refine hX₂.hom_ext ?_ ?_
    · have e1 : stageLift (E := E) (c := c) sqX a ≫ pX₂ = pullback.fst fX π := by
        simp only [pX₂]
        rw [stageLift_snd_assoc]
        exact sqX₁.lift_fst _ _ _
      rw [Category.assoc, e1, hqV'₁, Category.assoc, hjX₁, Category.comp_id]
    · rw [Category.assoc qV, hjX₂, reassoc_of% hV.w, Category.assoc, stageLift_fst,
        reassoc_of% hqV'₂]
      simp only [e, Category.assoc, ← hψ0, IsIso.inv_hom_id_assoc]
  have hiY : IsPullback (iY' ≫ stageLift (E := E) (c := c) sqY a) gY₀ fY₂
      ((e₀ ≫ ContractionUniquenessComplete.closedPoint Λ) ≫ ψ) := by
    rw [hψ]
    exact hiY'.paste_horiz sqY₂
  refine ⟨pullback fY₂ ψ, fY, h, hh, inferInstance, inferInstance, _,
    IsPullback.of_right' hiY sqY₃, ?_⟩
  · refine sqY₃.hom_ext ?_ ?_
    · rw [Category.assoc, sqY₃.lift_fst, Category.assoc, hhf, reassoc_of% hiYh', ← hh₂c,
        reassoc_of% key]
    · rw [Category.assoc, sqY₃.lift_snd, Category.assoc, hh, reassoc_of% hh₀, hV.w]

end Henselian

end ContractionDeformation

end AlgebraicGeometry.C1590Private

end
