module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeMorphism
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicFiniteAlgebraizationTags
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSourceEquivalence
public import StacksFrontier.Deformation.FormalObject.Basic

/-!
# Uniqueness of contractions over a complete Noetherian local ring

Let `Λ` be a complete Noetherian local ring with residue field `κ`, let `X`, `Y₁`, `Y₂` be
proper flat schemes over `Spec Λ` and let `cᵢ : X ⟶ Yᵢ` be morphisms over `Spec Λ`. Suppose the
special fibres `Y₁,ₛ` and `Y₂,ₛ` are identified by an isomorphism `φ` over `κ` compatible with
`c₁,ₛ` and `c₂,ₛ`, and suppose `c₁,ₛ` satisfies `𝒪_{Y₁,ₛ} ≅ c₁,ₛ,* 𝒪_{Xₛ}` and
`R¹c₁,ₛ,* 𝒪_{Xₛ} = 0`. Then there is an isomorphism `Y₁ ≅ Y₂` over `Spec Λ` compatible with
`c₁`, `c₂` and `φ`.

## Main results

* `AlgebraicGeometry.exists_iso_comp_eq_of_specialFibre_of_isAdicComplete`: the statement above,
  taking Grothendieck's algebraization of morphisms as the hypothesis `h0A42`.
* `AlgebraicGeometry.exists_iso_comp_eq_of_specialFibre_of_isAdicComplete_holds`: the statement
  above, with no further hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation Deformation.Examples IsLocalRing

universe u

namespace AlgebraicGeometry

namespace ContractionUniquenessComplete

variable (Λ : Type u) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]

/-- `Λ` as a complete local `Λ`-algebra with residue field the residue field of `Λ`. -/
def selfObj (hc : IsAdicComplete (maximalIdeal Λ) Λ) :
    CompleteLocalAlgCat.{u, u, u} Λ (ResidueField Λ) where
  carrier := Λ
  completeLocal := ⟨inferInstance, inferInstance, hc⟩
  residueEquiv := AlgEquiv.refl

/-- The closed point `Spec κ ⟶ Spec Λ`. -/
abbrev closedPoint : Spec (.of (ResidueField Λ)) ⟶ Spec (.of Λ) :=
  Spec.map (CommRingCat.ofHom (residue Λ))

variable {Λ} (hc : IsAdicComplete (maximalIdeal Λ) Λ)

/-- The unique morphism of `𝒞_Λ` from the `n`-th truncation of `Λ` to the residue field. -/
def toResidue (n : ℕ) :
    AdicTruncation.obj (selfObj Λ hc) n ⟶ residueFieldBase Λ (ResidueField Λ) :=
  isTerminal_residueFieldBase.from _

/-- The closed point of the `n`-th thickening. -/
abbrev levelPoint (n : ℕ) : Spec (.of (ResidueField Λ)) ⟶ adicThickening Λ (maximalIdeal Λ) n :=
  baseSpecMap (toResidue hc n)

/-- The closed point of the `n`-th thickening, composed with the closed immersion into `Spec Λ`,
is the closed point of `Spec Λ`. -/
theorem levelPoint_ι (n : ℕ) :
    levelPoint hc n ≫ adicThickeningι Λ (maximalIdeal Λ) n = closedPoint Λ := by
  have e : (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal Λ ^ (n + 1))) :
      CommRingCat.of Λ ⟶ CommRingCat.of (AdicTruncation.obj (selfObj Λ hc) n)) ≫
        CommRingCat.ofHom (Artin.residueMap (AdicTruncation.obj (selfObj Λ hc) n)) =
      CommRingCat.ofHom (residue Λ) := by
    ext r
    exact AdicTruncation.residueEquiv_residue_mk (selfObj Λ hc) n r
  calc levelPoint hc n ≫ adicThickeningι Λ (maximalIdeal Λ) n
      = residueSpecMap (AdicTruncation.obj (selfObj Λ hc) n) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal Λ ^ (n + 1))) :
            CommRingCat.of Λ ⟶ CommRingCat.of (AdicTruncation.obj (selfObj Λ hc) n)) :=
        congrArg (· ≫ _) (baseSpecMap_eq_residueSpecMap _ (toResidue hc n))
    _ = closedPoint Λ := (Spec.map_comp _ _).symm.trans (congrArg Spec.map e)

/-- The transition map of the truncations of `Λ` induces the inclusion of the `n`-th thickening
into the `(n + 1)`-st. -/
theorem baseSpecMap_transition (n : ℕ) :
    baseSpecMap (AdicTruncation.transition (selfObj Λ hc) n) =
      adicThickeningSucc Λ (maximalIdeal Λ) n :=
  rfl

/-- The closed points of the thickenings are compatible with the inclusions of thickenings. -/
theorem levelPoint_succ (n : ℕ) :
    levelPoint hc n ≫ adicThickeningSucc Λ (maximalIdeal Λ) n = levelPoint hc (n + 1) :=
  (baseSpecMap_comp (AdicTruncation.transition (selfObj Λ hc) n) (toResidue hc n)).symm.trans
    (congrArg baseSpecMap (isTerminal_residueFieldBase.hom_ext _ _))

/-! ### The special fibre inside the truncations -/

variable {X Y₁ Y : Scheme.{u}} (fX : X ⟶ Spec (.of Λ)) (fY₁ : Y₁ ⟶ Spec (.of Λ))
  (fY : Y ⟶ Spec (.of Λ))

/-- The special fibre of `Y` inside its `n`-th truncation. -/
def specialToLevel (n : ℕ) :
    pullback fY (closedPoint Λ) ⟶ adicBaseChange Λ (maximalIdeal Λ) fY n :=
  pullback.map _ _ _ _ (𝟙 _) (levelPoint hc n) (𝟙 _) (by simp)
    (by rw [Category.comp_id, levelPoint_ι])

/-- The special fibre of `Y` inside its `n`-th truncation is compatible with the projections
to `Y`. -/
@[reassoc (attr := simp)]
theorem specialToLevel_fst (n : ℕ) :
    specialToLevel hc fY n ≫ pullback.fst fY (adicThickeningι Λ (maximalIdeal Λ) n) =
      pullback.fst fY (closedPoint Λ) := by
  unfold specialToLevel pullback.map
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The special fibre of `Y` inside its `n`-th truncation lies over the closed point of the
`n`-th thickening. -/
@[reassoc (attr := simp)]
theorem specialToLevel_snd (n : ℕ) :
    specialToLevel hc fY n ≫ pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) n) =
      pullback.snd fY (closedPoint Λ) ≫ levelPoint hc n := by
  unfold specialToLevel pullback.map
  exact pullback.lift_snd _ _ _

/-- The special fibre is the fibre of the `n`-th truncation over the closed point. -/
theorem isPullback_specialToLevel (n : ℕ) :
    IsPullback (specialToLevel hc fY n) (pullback.snd fY (closedPoint Λ))
      (pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) n)) (levelPoint hc n) := by
  refine IsPullback.of_right ?_ (specialToLevel_snd hc fY n)
    (IsPullback.of_hasPullback fY (adicThickeningι Λ (maximalIdeal Λ) n))
  rw [specialToLevel_fst, levelPoint_ι]
  exact IsPullback.of_hasPullback fY (closedPoint Λ)

/-- The inclusions of the special fibre into the truncations of `Y` are compatible with the
transition maps. -/
@[reassoc]
theorem specialToLevel_succ (n : ℕ) :
    specialToLevel hc fY n ≫ adicBaseChangeSucc Λ (maximalIdeal Λ) fY n =
      specialToLevel hc fY (n + 1) := by
  apply pullback.hom_ext
  · simp only [adicBaseChangeSucc, Category.assoc, pullback.lift_fst, specialToLevel_fst]
  · simp only [adicBaseChangeSucc, Category.assoc, pullback.lift_snd, specialToLevel_snd_assoc,
      specialToLevel_snd, levelPoint_succ]

/-- The special fibre of a morphism `c : X ⟶ Y` over `Spec Λ`. -/
abbrev specialMap (c : X ⟶ Y) (h : c ≫ fY = fX) :
    pullback fX (closedPoint Λ) ⟶ pullback fY (closedPoint Λ) :=
  pullback.map _ _ _ _ c (𝟙 _) (𝟙 _) (by simp [h]) (by simp)

omit [IsNoetherianRing Λ] in
/-- The special fibre of `c` lies over `Spec κ`. -/
@[reassoc]
theorem specialMap_snd (c : X ⟶ Y) (h : c ≫ fY = fX) :
    specialMap fX fY c h ≫ pullback.snd fY (closedPoint Λ) = pullback.snd fX (closedPoint Λ) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-! ### The truncations as deformations of the special fibre -/

variable (c₁ : X ⟶ Y₁) (hc₁ : c₁ ≫ fY₁ = fX) (c : X ⟶ Y) (hcY : c ≫ fY = fX)

/-- The `n`-th truncation of `c : X ⟶ Y`, as a flat family of morphisms over `𝒞_Λ`. -/
def levelFamily [Flat fX] [Flat fY] (n : ℕ) : SchemeMorphismFamily.{u, u} Λ (ResidueField Λ) where
  base := AdicTruncation.obj (selfObj Λ hc) n
  source := adicBaseChange Λ (maximalIdeal Λ) fX n
  target := adicBaseChange Λ (maximalIdeal Λ) fY n
  morphism := adicBaseChangeMap Λ (maximalIdeal Λ) c hcY n
  sourceToBase := pullback.snd fX (adicThickeningι Λ (maximalIdeal Λ) n)
  targetToBase := pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) n)
  over_base := adicBaseChangeMap_snd ..
  source_flat := inferInstanceAs (Flat (pullback.snd fX (adicThickeningι Λ (maximalIdeal Λ) n)))
  target_flat := inferInstanceAs (Flat (pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) n)))

variable (τ : pullback fY₁ (closedPoint Λ) ≅ pullback fY (closedPoint Λ))
  (hτ : τ.hom ≫ pullback.snd fY (closedPoint Λ) = pullback.snd fY₁ (closedPoint Λ))
  (hτc : specialMap fX fY₁ c₁ hc₁ ≫ τ.hom = specialMap fX fY c hcY)

/-- The arrow from the `n`-th truncation of `c` to the special fibre of `c₁`, through the
identification `τ` of special fibres. -/
def levelHom [Flat fX] [Flat fY] (n : ℕ) :
    levelFamily hc fX fY c hcY n ⟶
      schemeMorphismFamilySpecialFiber (Λ := Λ) (specialMap fX fY₁ c₁ hc₁)
        (pullback.snd fX (closedPoint Λ)) (pullback.snd fY₁ (closedPoint Λ))
        (specialMap_snd fX fY₁ c₁ hc₁) where
  base := toResidue hc n
  source := specialToLevel hc fX n
  target := τ.hom ≫ specialToLevel hc fY n
  source_pullback := by
    have t : IsPullback (τ.hom ≫ specialToLevel hc fY n) (pullback.snd fY₁ (closedPoint Λ))
        (pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) n)) (levelPoint hc n) := by
      have h := (IsPullback.of_horiz_isIso (fst := τ.hom) (snd := pullback.snd fY₁ (closedPoint Λ))
        (f := pullback.snd fY (closedPoint Λ)) (g := 𝟙 _)
        ⟨by rw [hτ, Category.comp_id]⟩).paste_horiz
        (isPullback_specialToLevel hc fY n)
      rwa [Category.id_comp] at h
    refine (IsPullback.of_bot ?_ ?_ t).flip
    · have s : IsPullback (specialToLevel hc fX n)
          (specialMap fX fY₁ c₁ hc₁ ≫ pullback.snd fY₁ (closedPoint Λ))
          (adicBaseChangeMap Λ (maximalIdeal Λ) c hcY n ≫
            pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) n)) (levelPoint hc n) := by
        rw [specialMap_snd, adicBaseChangeMap_snd]
        exact isPullback_specialToLevel hc fX n
      exact s
    · have key : specialToLevel hc fX n ≫ adicBaseChangeMap Λ (maximalIdeal Λ) c hcY n =
          specialMap fX fY₁ c₁ hc₁ ≫ τ.hom ≫ specialToLevel hc fY n := by
        rw [reassoc_of% hτc]
        apply pullback.hom_ext
        · simp only [Category.assoc, adicBaseChangeMap_fst, specialToLevel_fst_assoc,
            specialToLevel_fst, pullback.lift_fst]
        · simp only [Category.assoc, adicBaseChangeMap_snd, specialToLevel_snd,
            specialMap_snd_assoc]
      exact key
  target_pullback := by
    have h := (IsPullback.of_horiz_isIso (fst := τ.hom) (snd := pullback.snd fY₁ (closedPoint Λ))
      (f := pullback.snd fY (closedPoint Λ)) (g := 𝟙 _) ⟨by rw [hτ, Category.comp_id]⟩).paste_horiz
      (isPullback_specialToLevel hc fY n)
    rwa [Category.id_comp] at h

/-- The `n`-th truncation of `c`, as an object of the deformation category of `c₁,ₛ`. -/
abbrev levelObj [Flat fX] [Flat fY] (n : ℕ) :
    schemeMorphismDeformationCategory (Λ := Λ) (k := ResidueField Λ) (specialMap fX fY₁ c₁ hc₁)
      (pullback.snd fX (closedPoint Λ)) (pullback.snd fY₁ (closedPoint Λ))
      (specialMap_snd fX fY₁ c₁ hc₁) :=
  Over.mk (levelHom hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n)

/-- The transition from the `(n + 1)`-st truncation of `c` to the `n`-th one. -/
def levelTransitionFamily [Flat fX] [Flat fY] (n : ℕ) :
    levelFamily hc fX fY c hcY (n + 1) ⟶ levelFamily hc fX fY c hcY n where
  base := AdicTruncation.transition (selfObj Λ hc) n
  source := adicBaseChangeSucc Λ (maximalIdeal Λ) fX n
  target := adicBaseChangeSucc Λ (maximalIdeal Λ) fY n
  source_pullback := by
    have s : IsPullback (adicBaseChangeSucc Λ (maximalIdeal Λ) fX n)
        (adicBaseChangeMap Λ (maximalIdeal Λ) c hcY n ≫
          pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) n))
        (adicBaseChangeMap Λ (maximalIdeal Λ) c hcY (n + 1) ≫
          pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) (n + 1)))
        (adicThickeningSucc Λ (maximalIdeal Λ) n) := by
      rw [adicBaseChangeMap_snd, adicBaseChangeMap_snd]
      exact isPullback_adicBaseChangeSucc Λ (maximalIdeal Λ) fX n
    exact (IsPullback.of_bot s (adicBaseChangeSucc_adicBaseChangeMap ..)
      (isPullback_adicBaseChangeSucc Λ (maximalIdeal Λ) fY n)).flip
  target_pullback := isPullback_adicBaseChangeSucc Λ (maximalIdeal Λ) fY n

/-- The transition from the `(n + 1)`-st truncation of `c` to the `n`-th one, as an arrow of the
deformation category of `c₁,ₛ`. -/
def levelTransition [Flat fX] [Flat fY] (n : ℕ) :
    levelObj hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc (n + 1) ⟶
      levelObj hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n :=
  Over.homMk (levelTransitionFamily hc fX fY c hcY n) <| by
    have ht : (τ.hom ≫ specialToLevel hc fY n) ≫ adicBaseChangeSucc Λ (maximalIdeal Λ) fY n =
        τ.hom ≫ specialToLevel hc fY (n + 1) := by
      rw [Category.assoc, specialToLevel_succ]
    exact SchemeMorphismFamily.Hom.ext (isTerminal_residueFieldBase.hom_ext _ _)
      (specialToLevel_succ hc fX n) ht

/-- The image of the `n`-th truncation of `c` in the deformation category of `Xₛ` does not
depend on `Y`, `c` or `τ`. -/
theorem forget_obj_levelObj [Flat fX] [Flat fY] [Flat fY₁] (n : ℕ) :
    (schemeMorphismSourceForgetful _ _ _ _).obj
        (levelObj hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n) =
      (schemeMorphismSourceForgetful _ _ _ _).obj
        (levelObj hc fX fY₁ fY₁ c₁ hc₁ c₁ hc₁ (Iso.refl _) (Category.id_comp _)
          (Category.comp_id _) n) :=
  rfl

/-! ### Lifting the identity of the common image -/

/-- The forgetful functor from deformations of `c₁,ₛ` to deformations of `Xₛ`. -/
abbrev forget : schemeMorphismDeformationCategory (Λ := Λ) (k := ResidueField Λ)
      (specialMap fX fY₁ c₁ hc₁) (pullback.snd fX (closedPoint Λ))
      (pullback.snd fY₁ (closedPoint Λ)) (specialMap_snd fX fY₁ c₁ hc₁) ⥤
    SchemeDeformationCategory (Λ := Λ) (k := ResidueField Λ)
      (Over.mk (pullback.snd fX (closedPoint Λ))) :=
  schemeMorphismSourceForgetful _ _ _ _

variable [Flat fX] [Flat fY] [Flat fY₁] [(forget fX fY₁ c₁ hc₁).Full]
  [(forget fX fY₁ c₁ hc₁).Faithful]

/-- The identity of the common image of the `n`-th truncations of `c` and `c₁` in the
deformation category of `Xₛ`. -/
def commonImageId (n : ℕ) :
    (forget fX fY₁ c₁ hc₁).obj (levelObj hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n) ⟶
      (forget fX fY₁ c₁ hc₁).obj (levelObj hc fX fY₁ fY₁ c₁ hc₁ c₁ hc₁ (Iso.refl _)
        (Category.id_comp _) (Category.comp_id _) n) :=
  𝟙 ((forget fX fY₁ c₁ hc₁).obj (levelObj hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n))

/-- An arrow from the `n`-th truncation of `c` to that of `c₁` over the identity of their
common image in the deformation category of `Xₛ`, by fullness. -/
def levelLift (n : ℕ) :
    levelObj hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n ⟶
      levelObj hc fX fY₁ fY₁ c₁ hc₁ c₁ hc₁ (Iso.refl _) (Category.id_comp _)
        (Category.comp_id _) n :=
  (forget fX fY₁ c₁ hc₁).preimage (commonImageId hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n)

omit [(forget fX fY₁ c₁ hc₁).Faithful] in
/-- The image of `levelLift` in the deformation category of `Xₛ` is `commonImageId`. -/
theorem forget_map_levelLift (n : ℕ) :
    (forget fX fY₁ c₁ hc₁).map (levelLift hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n) =
      commonImageId hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n :=
  (forget fX fY₁ c₁ hc₁).map_preimage _

omit [(forget fX fY₁ c₁ hc₁).Full] [(forget fX fY₁ c₁ hc₁).Faithful] in
/-- The arrow `commonImageId` lies over the identity of the `n`-th truncation of `Λ`. -/
theorem commonImageId_base (n : ℕ) :
    (commonImageId hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n).base =
      𝟙 (AdicTruncation.obj (selfObj Λ hc) n) :=
  rfl

omit [(forget fX fY₁ c₁ hc₁).Faithful] in
/-- The arrow `levelLift` lies over the identity of the `n`-th truncation of `Λ`. -/
theorem levelLift_base (n : ℕ) :
    (levelLift hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n).left.base =
      𝟙 (AdicTruncation.obj (selfObj Λ hc) n) :=
  (congrArg SchemeDeformationCategory.Hom.base
    (forget_map_levelLift hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n)).trans
    (commonImageId_base hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n)

omit [(forget fX fY₁ c₁ hc₁).Faithful] in
/-- The arrow `levelLift` lies over the identity of the `n`-th thickening. -/
theorem baseSpecMap_levelLift_base (n : ℕ) :
    baseSpecMap (levelLift hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n).left.base =
      𝟙 (baseSpec (AdicTruncation.obj (selfObj Λ hc) n)) :=
  (congrArg baseSpecMap (levelLift_base hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n)).trans
    (baseSpecMap_id _)

omit [(forget fX fY₁ c₁ hc₁).Faithful] in
/-- The arrow `levelLift` is the identity on the `n`-th truncation of `X`. -/
theorem levelLift_source (n : ℕ) :
    (levelLift hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n).left.source = 𝟙 _ :=
  congrArg SchemeDeformationCategory.Hom.map
    (forget_map_levelLift hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n)

/-- The comparison of the `n`-th truncations of `Y₁` and `Y`. -/
abbrev levelIso (n : ℕ) :
    adicBaseChange Λ (maximalIdeal Λ) fY₁ n ⟶ adicBaseChange Λ (maximalIdeal Λ) fY n :=
  (levelLift hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n).left.target

omit [(forget fX fY₁ c₁ hc₁).Faithful] in
/-- The comparison `levelIso` is a morphism over the `n`-th thickening. -/
theorem levelIso_snd (n : ℕ) :
    levelIso hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n ≫
        pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) n) =
      pullback.snd fY₁ (adicThickeningι Λ (maximalIdeal Λ) n) :=
  (levelLift hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n).left.target_pullback.w.trans
    ((congrArg (pullback.snd fY₁ (adicThickeningι Λ (maximalIdeal Λ) n) ≫ ·)
      (baseSpecMap_levelLift_base hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n)).trans
        (Category.comp_id _))

/-- The comparison `levelIso` is an isomorphism. -/
instance isIso_levelIso (n : ℕ) : IsIso (levelIso hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n) := by
  have h := (levelLift hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n).left.target_pullback
  have : IsIso (baseSpecMap (levelLift hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n).left.base) := by
    rw [baseSpecMap_levelLift_base]
    exact IsIso.id _
  exact h.isIso_fst_of_isIso

omit [(forget fX fY₁ c₁ hc₁).Faithful] in
/-- The comparison `levelIso` carries the `n`-th truncation of `c₁` to that of `c`. -/
theorem adicBaseChangeMap_levelIso (n : ℕ) :
    adicBaseChangeMap Λ (maximalIdeal Λ) c₁ hc₁ n ≫ levelIso hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n =
      adicBaseChangeMap Λ (maximalIdeal Λ) c hcY n :=
  (levelLift hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n).left.source_pullback.w.trans
    ((congrArg (· ≫ adicBaseChangeMap Λ (maximalIdeal Λ) c hcY n)
      (levelLift_source hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n)).trans
      (Category.id_comp _))

omit [(forget fX fY₁ c₁ hc₁).Faithful] in
/-- On special fibres, the comparison `levelIso` restricts to `τ`. -/
theorem specialToLevel_levelIso (n : ℕ) :
    specialToLevel hc fY₁ n ≫ levelIso hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n =
      τ.hom ≫ specialToLevel hc fY n := by
  have w : ((Iso.refl _).hom ≫ specialToLevel hc fY₁ n) ≫
      levelIso hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n = τ.hom ≫ specialToLevel hc fY n :=
    congrArg SchemeMorphismFamily.Hom.target
      (Over.w (levelLift hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n))
  rwa [Iso.refl_hom, Category.id_comp] at w

/-- The arrows `levelLift` are compatible with the transition arrows `levelTransition`. -/
theorem levelLift_comp_levelTransition (n : ℕ) :
    levelLift hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc (n + 1) ≫
        levelTransition hc fX fY₁ fY₁ c₁ hc₁ c₁ hc₁ (Iso.refl _) (Category.id_comp _)
          (Category.comp_id _) n =
      levelTransition hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n ≫
        levelLift hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n := by
  apply (forget fX fY₁ c₁ hc₁).map_injective
  simp only [Functor.map_comp, forget_map_levelLift]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The comparisons `levelIso` are compatible with the transition maps of the truncations. -/
theorem levelIso_succ (n : ℕ) :
    adicBaseChangeSucc Λ (maximalIdeal Λ) fY₁ n ≫
        levelIso hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc (n + 1) =
      levelIso hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n ≫ adicBaseChangeSucc Λ (maximalIdeal Λ) fY n :=
  congrArg (fun h : levelObj hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc (n + 1) ⟶
      levelObj hc fX fY₁ fY₁ c₁ hc₁ c₁ hc₁ (Iso.refl _) (Category.id_comp _)
        (Category.comp_id _) n => h.left.target)
    (levelLift_comp_levelTransition hc fX fY₁ fY c₁ hc₁ c hcY τ hτ hτc n)

/-- The `n`-th truncation of the identity of `Y` is the identity. -/
theorem adicBaseChangeMap_id (A : Type u) [CommRing A] (I : Ideal A) {Y : Scheme.{u}}
    (fY : Y ⟶ Spec (.of A)) (n : ℕ) :
    adicBaseChangeMap A I (𝟙 Y) (Category.id_comp fY) n = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [adicBaseChangeMap_fst, Category.comp_id, Category.id_comp]
  · rw [adicBaseChangeMap_snd, Category.id_comp]

end ContractionUniquenessComplete

open ContractionUniquenessComplete in
/-- Let `Λ` be a complete Noetherian local ring with residue field `κ`, closed point
`s : Spec κ ⟶ Spec Λ`, let `X`, `Y₁`, `Y₂` be proper flat schemes over `Spec Λ` and let
`cᵢ : X ⟶ Yᵢ` be morphisms over `Spec Λ`. Let `φ : Y₁,ₛ ≅ Y₂,ₛ` be an isomorphism of special fibres
over `κ` compatible with `c₁,ₛ` and `c₂,ₛ`. If `𝒪_{Y₁,ₛ} ⟶ c₁,ₛ,* 𝒪_{Xₛ}` is an isomorphism and
`R¹c₁,ₛ,* 𝒪_{Xₛ} = 0`, there is an isomorphism `ψ : Y₁ ≅ Y₂` over `Spec Λ` with `c₁ ≫ ψ = c₂` whose
special fibre is `φ`.

Grothendieck's algebraization of morphisms is taken as the hypothesis `h0A42`, the statement of
`AlgebraicGeometry.existsUnique_algebraization_adicBaseChangeMap` without its hypotheses `halg`
and `hrig`. -/
theorem exists_iso_comp_eq_of_specialFibre_of_isAdicComplete
    (h0A42 : ∀ (A : Type u) [CommRing A] (I : Ideal A) {X Y : Scheme.{u}} [IsNoetherianRing A]
      (_hcomplete : IsAdicComplete I A) (fX : X ⟶ Spec (.of A)) (fY : Y ⟶ Spec (.of A))
      [IsProper fX] [IsSeparated fY] [LocallyOfFiniteType fY] [QuasiCompact fY]
      (g : ∀ n, adicBaseChange A I fX n ⟶ adicBaseChange A I fY n)
      (_g_over : ∀ n, g n ≫ pullback.snd fY (adicThickeningι A I n) =
        pullback.snd fX (adicThickeningι A I n))
      (_g_compatible : ∀ n, adicBaseChangeSucc A I fX n ≫ g (n + 1) =
        g n ≫ adicBaseChangeSucc A I fY n),
      ∃! algebraization : {h : X ⟶ Y // h ≫ fY = fX},
        ∀ n, adicBaseChangeMap A I algebraization.1 algebraization.2 n = g n)
    {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
    (hc : IsAdicComplete (maximalIdeal Λ) Λ)
    {X Y₁ Y₂ : Scheme.{u}} (fX : X ⟶ Spec (.of Λ)) (fY₁ : Y₁ ⟶ Spec (.of Λ))
    (fY₂ : Y₂ ⟶ Spec (.of Λ)) [IsProper fX] [Flat fX] [IsProper fY₁] [Flat fY₁]
    [IsProper fY₂] [Flat fY₂]
    (c₁ : X ⟶ Y₁) (hc₁ : c₁ ≫ fY₁ = fX) (c₂ : X ⟶ Y₂) (hc₂ : c₂ ≫ fY₂ = fX)
    (φ : pullback fY₁ (closedPoint Λ) ≅ pullback fY₂ (closedPoint Λ))
    (hφ : φ.hom ≫ pullback.snd _ _ = pullback.snd _ _)
    (hφc : specialMap fX fY₁ c₁ hc₁ ≫ φ.hom = specialMap fX fY₂ c₂ hc₂)
    (h0 : IsIso (C := (pullback fY₁ (closedPoint Λ)).Modules)
      (Scheme.Modules.unitToPushforwardUnit (specialMap fX fY₁ c₁ hc₁)))
    (hR : IsZero (((Scheme.Modules.pushforward (specialMap fX fY₁ c₁ hc₁)).rightDerived 1).obj
      (SheafOfModules.unit (pullback fX (closedPoint Λ)).ringCatSheaf))) :
    ∃ ψ : Y₁ ≅ Y₂, ψ.hom ≫ fY₂ = fY₁ ∧ c₁ ≫ ψ.hom = c₂ ∧
      pullback.fst _ _ ≫ ψ.hom = φ.hom ≫ pullback.fst _ _ := by
  have : (forget fX fY₁ c₁ hc₁).IsEquivalence :=
    schemeMorphismSourceForgetful_isEquivalence_of_specialFibre _ _ _ _ h0 hR
  have t_over := levelIso_snd hc fX fY₁ fY₂ c₁ hc₁ c₂ hc₂ φ hφ hφc
  have t_succ := levelIso_succ hc fX fY₁ fY₂ c₁ hc₁ c₂ hc₂ φ hφ hφc
  have t_c := adicBaseChangeMap_levelIso hc fX fY₁ fY₂ c₁ hc₁ c₂ hc₂ φ hφ hφc
  have t_special := specialToLevel_levelIso hc fX fY₁ fY₂ c₁ hc₁ c₂ hc₂ φ hφ hφc
  obtain ⟨⟨ψ, hψ⟩, hψn, -⟩ := h0A42 Λ (maximalIdeal Λ) hc fY₁ fY₂ _ t_over t_succ
  obtain ⟨⟨ψ', hψ'⟩, hψ'n, -⟩ := h0A42 Λ (maximalIdeal Λ) hc fY₂ fY₁
    (fun n => inv (levelIso hc fX fY₁ fY₂ c₁ hc₁ c₂ hc₂ φ hφ hφc n))
    (fun n => by rw [IsIso.inv_comp_eq, t_over])
    (fun n => by
      rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
      exact (t_succ n).symm)
  have uniq : ∀ {Z W : Scheme.{u}} (fZ : Z ⟶ Spec (.of Λ)) (fW : W ⟶ Spec (.of Λ))
      [IsProper fZ] [IsProper fW] (a b : Z ⟶ W) (ha : a ≫ fW = fZ) (hb : b ≫ fW = fZ),
      (∀ n, adicBaseChangeMap Λ (maximalIdeal Λ) a ha n =
        adicBaseChangeMap Λ (maximalIdeal Λ) b hb n) → a = b := by
    intro Z W fZ fW _ _ a b ha hb h
    obtain ⟨_, _, huniq⟩ := h0A42 Λ (maximalIdeal Λ) hc fZ fW
      (fun n => adicBaseChangeMap Λ (maximalIdeal Λ) b hb n) (fun n => adicBaseChangeMap_snd ..)
      (fun n => adicBaseChangeSucc_adicBaseChangeMap ..)
    exact congrArg Subtype.val ((huniq ⟨a, ha⟩ h).trans (huniq ⟨b, hb⟩ fun n => rfl).symm)
  have hid₁ : ψ ≫ ψ' = 𝟙 Y₁ :=
    uniq fY₁ fY₁ _ _ (by rw [Category.assoc, hψ', hψ]) (Category.id_comp _) fun n => by
      rw [adicBaseChangeMap_comp Λ (maximalIdeal Λ) ψ hψ ψ' hψ' n, hψn, hψ'n, IsIso.hom_inv_id,
        adicBaseChangeMap_id]
  have hid₂ : ψ' ≫ ψ = 𝟙 Y₂ :=
    uniq fY₂ fY₂ _ _ (by rw [Category.assoc, hψ, hψ']) (Category.id_comp _) fun n => by
      rw [adicBaseChangeMap_comp Λ (maximalIdeal Λ) ψ' hψ' ψ hψ n, hψn, hψ'n, IsIso.inv_hom_id,
        adicBaseChangeMap_id]
  refine ⟨⟨ψ, ψ', hid₁, hid₂⟩, hψ, ?_, ?_⟩
  · exact uniq fX fY₂ _ _ (by rw [Category.assoc, hψ, hc₁]) hc₂ fun n => by
      rw [adicBaseChangeMap_comp Λ (maximalIdeal Λ) c₁ hc₁ ψ hψ n, hψn, t_c]
  · have h := congrArg (· ≫ pullback.fst fY₂ (adicThickeningι Λ (maximalIdeal Λ) 0)) (t_special 0)
    simp only [Category.assoc, specialToLevel_fst] at h
    rw [← h, ← hψn 0, adicBaseChangeMap_fst, specialToLevel_fst_assoc]

open ContractionUniquenessComplete in
/-- Let `Λ` be a complete Noetherian local ring with residue field `κ`, closed point
`s : Spec κ ⟶ Spec Λ`, let `X`, `Y₁`, `Y₂` be proper flat schemes over `Spec Λ` and let
`cᵢ : X ⟶ Yᵢ` be morphisms over `Spec Λ`. Let `φ : Y₁,ₛ ≅ Y₂,ₛ` be an isomorphism of special fibres
over `κ` compatible with `c₁,ₛ` and `c₂,ₛ`. If `𝒪_{Y₁,ₛ} ⟶ c₁,ₛ,* 𝒪_{Xₛ}` is an isomorphism and
`R¹c₁,ₛ,* 𝒪_{Xₛ} = 0`, there is an isomorphism `ψ : Y₁ ≅ Y₂` over `Spec Λ` with `c₁ ≫ ψ = c₂` whose
special fibre is `φ`. No algebraization hypothesis is taken. -/
theorem exists_iso_comp_eq_of_specialFibre_of_isAdicComplete_holds
    {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
    (hc : IsAdicComplete (maximalIdeal Λ) Λ)
    {X Y₁ Y₂ : Scheme.{u}} (fX : X ⟶ Spec (.of Λ)) (fY₁ : Y₁ ⟶ Spec (.of Λ))
    (fY₂ : Y₂ ⟶ Spec (.of Λ)) [IsProper fX] [Flat fX] [IsProper fY₁] [Flat fY₁]
    [IsProper fY₂] [Flat fY₂]
    (c₁ : X ⟶ Y₁) (hc₁ : c₁ ≫ fY₁ = fX) (c₂ : X ⟶ Y₂) (hc₂ : c₂ ≫ fY₂ = fX)
    (φ : pullback fY₁ (closedPoint Λ) ≅ pullback fY₂ (closedPoint Λ))
    (hφ : φ.hom ≫ pullback.snd _ _ = pullback.snd _ _)
    (hφc : specialMap fX fY₁ c₁ hc₁ ≫ φ.hom = specialMap fX fY₂ c₂ hc₂)
    (h0 : IsIso (C := (pullback fY₁ (closedPoint Λ)).Modules)
      (Scheme.Modules.unitToPushforwardUnit (specialMap fX fY₁ c₁ hc₁)))
    (hR : IsZero (((Scheme.Modules.pushforward (specialMap fX fY₁ c₁ hc₁)).rightDerived 1).obj
      (SheafOfModules.unit (pullback fX (closedPoint Λ)).ringCatSheaf))) :
    ∃ ψ : Y₁ ≅ Y₂, ψ.hom ≫ fY₂ = fY₁ ∧ c₁ ≫ ψ.hom = c₂ ∧
      pullback.fst _ _ ≫ ψ.hom = φ.hom ≫ pullback.fst _ _ :=
  exists_iso_comp_eq_of_specialFibre_of_isAdicComplete
    (@fun A _ I _ _ _ hcA fX fY _ _ _ _ g go gc =>
      existsUnique_algebraization_adicBaseChangeMap_holds A I hcA fX fY g go gc)
    hc fX fY₁ fY₂ c₁ hc₁ c₂ hc₂ φ hφ hφc h0 hR

end AlgebraicGeometry

end
