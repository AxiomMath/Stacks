module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.Algebraization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicFiniteAlgebraizationTags
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionExistenceFlatness
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessLocal
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# Existence of contractions over a complete Noetherian local ring

Let `Λ` be a complete Noetherian local ring with residue field `κ`, let `fX : X ⟶ Spec Λ` be
proper and flat with special fibre `Xₛ`, and let `h₀ : Xₛ ⟶ Y₀` be a morphism to a proper scheme
`Y₀` over `κ` of dimension at most one with `𝒪_{Y₀} ≅ h₀,* 𝒪_{Xₛ}` and `R¹h₀,* 𝒪_{Xₛ} = 0`.
Then there are a projective flat `fY : Y ⟶ Spec Λ`, a morphism `h : X ⟶ Y` over `Spec Λ` and an
identification of the special fibre of `Y` with `Y₀` under which the special fibre of `h` is `h₀`.

This is the formal step of the proof of [Stacks, Tag 0E7C], done as the source does it:

* the truncations `Xₙ = X ×_Λ Λ/𝔪ⁿ⁺¹` are deformations of `Xₛ`, compatibly in `n`;
* the forgetful functor `Def_{Xₛ ⟶ Y₀} ⥤ Def_{Xₛ}` is an equivalence ([Stacks, Tag 0E3X]), so
  essential surjectivity lifts each `Xₙ` to a deformation `Xₙ ⟶ Yₙ` of `h₀` and fullness lifts
  the transitions, giving a tower of flat schemes `Yₙ` over the thickenings with cartesian
  transition squares;
* the tower `Yₙ` is the system of truncations of a projective `Y ⟶ Spec Λ` (the scheme case
  of [Stacks, Tag 0E7R],
  `Stacks.FormalCurve.exists_isProjectiveMorphism_of_topologicalKrullDim_le_one`);
* Grothendieck's algebraization of morphisms ([Stacks, Tag 0A42]) turns the compatible system
  `Xₙ ⟶ Yₙ` into `h : X ⟶ Y`.

## Main results

* `ContractionExistenceComplete.exists_contraction_of_specialFibre_of_isAdicComplete`: the
  statement above.
* `ContractionExistenceComplete.exists_contraction_of_specialFibre_of_isAdicComplete'`: the same,
  with the bound `dim Y₀ ≤ 1` replaced by `dim Xₛ ≤ 1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation Deformation.Examples IsLocalRing

universe u

namespace AlgebraicGeometry

namespace ContractionExistenceComplete

open ContractionUniquenessComplete

/-- Spectra of composites of `𝒞_Λ`-morphisms that compose to the identity compose to the
identity. -/
private theorem baseSpecMap_comp_eq_id {Λ : Type u} [CommRing Λ] [IsLocalRing Λ]
    {A B : ArtinianLocalAlgCat.{u, u, u} Λ (ResidueField Λ)}
    {f : A ⟶ B} {g : B ⟶ A} (h : f ≫ g = 𝟙 A) : baseSpecMap g ≫ baseSpecMap f = 𝟙 _ :=
  (baseSpecMap_comp f g).symm.trans ((congrArg baseSpecMap h).trans (baseSpecMap_id _))

variable {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
  (hc : IsAdicComplete (maximalIdeal Λ) Λ)
  {X : Scheme.{u}} (fX : X ⟶ Spec (.of Λ)) [Flat fX]
  {X₀ : Scheme.{u}} (pX₀ : X₀ ⟶ Spec (.of (ResidueField Λ))) {ιX : X₀ ⟶ X}
  (hιX : IsPullback ιX pX₀ fX (closedPoint Λ))

/-- The `n`-th truncation `X ×_Λ Λ/𝔪ⁿ⁺¹` of a flat `X` over `Spec Λ`, as a deformation of its
special fibre. -/
def truncation (n : ℕ) :
    SchemeDeformationCategory (Λ := Λ) (k := ResidueField Λ)
      (Over.mk pX₀) where
  base := AdicTruncation.obj (selfObj Λ hc) n
  scheme := adicBaseChange Λ (maximalIdeal Λ) fX n
  toBase := pullback.snd fX (adicThickeningι Λ (maximalIdeal Λ) n)
  flat := inferInstanceAs (Flat (pullback.snd fX (adicThickeningι Λ (maximalIdeal Λ) n)))
  specialMap := hιX.isoPullback.hom ≫ specialToLevel hc fX n
  specialCartesian := by
    have h := (IsPullback.of_horiz_isIso (fst := hιX.isoPullback.hom) (snd := pX₀)
      (f := pullback.snd fX (closedPoint Λ)) (g := 𝟙 _)
      ⟨by rw [IsPullback.isoPullback_hom_snd, Category.comp_id]⟩).paste_horiz
      (isPullback_specialToLevel hc fX n)
    rwa [Category.id_comp, levelPoint, baseSpecMap_eq_residueSpecMap] at h

/-- The transition from the `(n + 1)`-st truncation to the `n`-th one. -/
def truncationTransition (n : ℕ) :
    truncation hc fX pX₀ hιX (n + 1) ⟶ truncation hc fX pX₀ hιX n where
  base := AdicTruncation.transition (selfObj Λ hc) n
  map := adicBaseChangeSucc Λ (maximalIdeal Λ) fX n
  cartesian := isPullback_adicBaseChangeSucc Λ (maximalIdeal Λ) fX n
  special_compat := by
    change (hιX.isoPullback.hom ≫ specialToLevel hc fX n) ≫
        adicBaseChangeSucc Λ (maximalIdeal Λ) fX n =
      hιX.isoPullback.hom ≫ specialToLevel hc fX (n + 1)
    rw [Category.assoc, specialToLevel_succ]

/-- The closed point of the zeroth thickening `Spec (Λ / 𝔪)` is an isomorphism. -/
instance isIso_levelPoint_zero : IsIso (levelPoint hc 0) := by
  have hb : baseSpecMap (toResidue hc 0) =
      residueSpecMap (AdicTruncation.obj (selfObj Λ hc) 0) :=
    baseSpecMap_eq_residueSpecMap _ _
  have e : (Artin.residueMap (AdicTruncation.obj (selfObj Λ hc) 0)).comp
      (Ideal.Quotient.mk (maximalIdeal Λ ^ (0 + 1))) = residue Λ := by
    ext r
    exact AdicTruncation.residueEquiv_residue_mk (selfObj Λ hc) 0 r
  have hbij : Function.Bijective (Artin.residueMap (AdicTruncation.obj (selfObj Λ hc) 0)) := by
    refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_, fun c => ?_⟩
    · obtain ⟨a, rfl⟩ : ∃ a : Λ, Ideal.Quotient.mk (maximalIdeal Λ ^ (0 + 1)) a = x :=
        Ideal.Quotient.mk_surjective x
      have h1 : residue Λ a = 0 := by rwa [← e]
      refine Ideal.Quotient.eq_zero_iff_mem.mpr (?_ : a ∈ maximalIdeal Λ ^ (0 + 1))
      rw [zero_add, pow_one]
      exact (residue_eq_zero_iff a).mp h1
    · obtain ⟨r, rfl⟩ := residue_surjective c
      exact ⟨Ideal.Quotient.mk _ r, AdicTruncation.residueEquiv_residue_mk (selfObj Λ hc) 0 r⟩
  have : IsIso (CommRingCat.ofHom
      (Artin.residueMap (AdicTruncation.obj (selfObj Λ hc) 0))) :=
    (inferInstance : IsIso (RingEquiv.ofBijective _ hbij).toCommRingCatIso.hom)
  change IsIso (baseSpecMap (toResidue hc 0))
  rw [hb]
  infer_instance

omit [Flat fX] in
/-- The special fibre of a morphism over `Spec Λ` is the restriction of each of its
truncations. -/
theorem specialMap_specialToLevel {Y : Scheme.{u}} (fY : Y ⟶ Spec (.of Λ)) (c : X ⟶ Y)
    (hcY : c ≫ fY = fX) (n : ℕ) :
    specialMap fX fY c hcY ≫ specialToLevel hc fY n =
      specialToLevel hc fX n ≫ adicBaseChangeMap Λ (maximalIdeal Λ) c hcY n := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, specialToLevel_fst, adicBaseChangeMap_fst,
      specialToLevel_fst_assoc]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, Category.assoc, specialToLevel_snd, adicBaseChangeMap_snd,
      specialToLevel_snd, specialMap_snd_assoc]

/-- Cancelling an inverse on the left of a commutative square. -/
private theorem comp_eq_of_inv_comp {A B C D : Scheme.{u}} (β : A ⟶ B) (γ : B ⟶ A)
    (hβγ : β ≫ γ = 𝟙 A)
    (t : A ⟶ C) (β' : C ⟶ D) (s : B ⟶ D) (h : (γ ≫ t) ≫ β' = s) : t ≫ β' = β ≫ s := by
  rw [← h, ← Category.assoc, ← Category.assoc, hβγ, Category.id_comp]

section Lift

variable {Y₀ : Scheme.{u}} (h₀ : X₀ ⟶ Y₀)
  (pY₀ : Y₀ ⟶ Spec (.of (ResidueField Λ)))
  (hh₀ : h₀ ≫ pY₀ = pX₀)

/-- The forgetful functor from deformations of `h₀` to deformations of `Xₛ`. -/
abbrev forget : schemeMorphismDeformationCategory (Λ := Λ) (k := ResidueField Λ) h₀
      pX₀ pY₀ hh₀ ⥤
    SchemeDeformationCategory (Λ := Λ) (k := ResidueField Λ) (Over.mk pX₀) :=
  schemeMorphismSourceForgetful _ _ _ _

variable [(forget pX₀ h₀ pY₀ hh₀).IsEquivalence]

/-- A deformation of `h₀` lifting the `n`-th truncation of `X`. -/
abbrev lift (n : ℕ) := (forget pX₀ h₀ pY₀ hh₀).objPreimage (truncation hc fX pX₀ hιX n)

/-- The identification of the source of `lift n` with the `n`-th truncation. -/
abbrev liftIso (n : ℕ) :
    (forget pX₀ h₀ pY₀ hh₀).obj (lift hc fX pX₀ hιX h₀ pY₀ hh₀ n) ≅ truncation hc fX pX₀ hιX n :=
  (forget pX₀ h₀ pY₀ hh₀).objObjPreimageIso (truncation hc fX pX₀ hιX n)

/-- The transitions between the lifts. -/
abbrev liftTransition (n : ℕ) :
    lift hc fX pX₀ hιX h₀ pY₀ hh₀ (n + 1) ⟶ lift hc fX pX₀ hιX h₀ pY₀ hh₀ n :=
  (forget pX₀ h₀ pY₀ hh₀).preimage ((liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ (n + 1)).hom ≫
    truncationTransition hc fX pX₀ hιX n ≫ (liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ n).inv)

/-- The target of the `n`-th lift. -/
abbrev T (n : ℕ) : Scheme.{u} := (lift hc fX pX₀ hιX h₀ pY₀ hh₀ n).left.target

/-- The transitions of the targets. -/
abbrev tTrans (n : ℕ) : T hc fX pX₀ hιX h₀ pY₀ hh₀ n ⟶ T hc fX pX₀ hιX h₀ pY₀ hh₀ (n + 1) :=
  (liftTransition hc fX pX₀ hιX h₀ pY₀ hh₀ n).left.target

/-- The identification of the base of the `n`-th lift with the `n`-th thickening. -/
abbrev baseIso (n : ℕ) :
    baseSpec (lift hc fX pX₀ hιX h₀ pY₀ hh₀ n).left.base ⟶ adicThickening Λ (maximalIdeal Λ) n :=
  baseSpecMap (liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ n).inv.base

/-- `baseIso n` is a left inverse of the map of spectra induced by `(liftIso n).hom.base`. -/
theorem baseSpecMap_hom_baseIso (n : ℕ) :
    baseSpecMap (liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ n).hom.base ≫ baseIso hc fX pX₀ hιX h₀ pY₀ hh₀ n =
        𝟙 _ :=
  baseSpecMap_comp_eq_id (congrArg SchemeDeformationCategory.Hom.base
    (liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ n).inv_hom_id)

/-- `baseIso n` is a right inverse of the map of spectra induced by `(liftIso n).hom.base`. -/
theorem baseIso_baseSpecMap_hom (n : ℕ) :
    baseIso hc fX pX₀ hιX h₀ pY₀ hh₀ n ≫ baseSpecMap (liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ n).hom.base =
        𝟙 _ :=
  baseSpecMap_comp_eq_id (congrArg SchemeDeformationCategory.Hom.base
    (liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ n).hom_inv_id)

/-- `baseIso n` is an isomorphism. -/
theorem isIso_baseIso (n : ℕ) : IsIso (baseIso hc fX pX₀ hιX h₀ pY₀ hh₀ n) :=
  ⟨⟨_, baseIso_baseSpecMap_hom hc fX pX₀ hιX h₀ pY₀ hh₀ n,
      baseSpecMap_hom_baseIso hc fX pX₀ hιX h₀ pY₀ hh₀ n⟩⟩

/-- The inverse of `baseIso`. -/
def baseInv (n : ℕ) :
    adicThickening Λ (maximalIdeal Λ) n ⟶ baseSpec (lift hc fX pX₀ hιX h₀ pY₀ hh₀ n).left.base :=
  baseSpecMap (liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ n).hom.base

/-- `baseInv n` followed by `baseIso n` is the identity. -/
theorem baseInv_baseIso (n : ℕ) :
    baseInv hc fX pX₀ hιX h₀ pY₀ hh₀ n ≫ baseIso hc fX pX₀ hιX h₀ pY₀ hh₀ n = 𝟙 _ :=
  baseSpecMap_hom_baseIso hc fX pX₀ hιX h₀ pY₀ hh₀ n

/-- The identification of the `n`-th truncation of `X` with the source of the `n`-th lift. -/
def srcMap (n : ℕ) :
    adicBaseChange Λ (maximalIdeal Λ) fX n ⟶ (lift hc fX pX₀ hιX h₀ pY₀ hh₀ n).left.source :=
  (liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ n).hom.map

/-- The inverse of `srcMap`. -/
def srcInv (n : ℕ) :
    (lift hc fX pX₀ hιX h₀ pY₀ hh₀ n).left.source ⟶ adicBaseChange Λ (maximalIdeal Λ) fX n :=
  (liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ n).inv.map

/-- `srcMap n` followed by `srcInv n` is the identity. -/
theorem srcMap_srcInv (n : ℕ) :
    srcMap hc fX pX₀ hιX h₀ pY₀ hh₀ n ≫ srcInv hc fX pX₀ hιX h₀ pY₀ hh₀ n = 𝟙 _ :=
  congrArg SchemeDeformationCategory.Hom.map (liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ n).inv_hom_id

/-- `srcInv n` followed by `srcMap n` is the identity. -/
theorem srcInv_srcMap (n : ℕ) :
    srcInv hc fX pX₀ hιX h₀ pY₀ hh₀ n ≫ srcMap hc fX pX₀ hιX h₀ pY₀ hh₀ n = 𝟙 _ :=
  congrArg SchemeDeformationCategory.Hom.map (liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ n).hom_inv_id

/-- `srcMap n` is compatible with the structure morphisms of the `n`-th truncation of `X` and
of the source of the `n`-th lift, the bases being identified by `baseInv n`. -/
theorem srcMap_sourceToBase (n : ℕ) :
    srcMap hc fX pX₀ hιX h₀ pY₀ hh₀ n ≫ (lift hc fX pX₀ hιX h₀ pY₀ hh₀ n).left.sourceToBase =
      pullback.snd fX (adicThickeningι Λ (maximalIdeal Λ) n) ≫ baseInv hc fX pX₀ hιX h₀ pY₀ hh₀ n :=
  (liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ n).hom.cartesian.w

/-- On sources, `liftTransition n` is the transition `adicBaseChangeSucc` of the truncations of
`X`, transported along `srcInv n` and `srcMap (n + 1)`. -/
theorem liftTransition_source (n : ℕ) :
    (liftTransition hc fX pX₀ hιX h₀ pY₀ hh₀ n).left.source =
      (srcInv hc fX pX₀ hιX h₀ pY₀ hh₀ n ≫ adicBaseChangeSucc Λ (maximalIdeal Λ) fX n) ≫
        srcMap hc fX pX₀ hιX h₀ pY₀ hh₀ (n + 1) :=
  congrArg SchemeDeformationCategory.Hom.map ((forget pX₀ h₀ pY₀ hh₀).map_preimage _)

/-- The structure morphism of the `n`-th target to the `n`-th thickening. -/
abbrev q (n : ℕ) : T hc fX pX₀ hιX h₀ pY₀ hh₀ n ⟶ adicThickening Λ (maximalIdeal Λ) n :=
  (lift hc fX pX₀ hιX h₀ pY₀ hh₀ n).left.targetToBase ≫ baseIso hc fX pX₀ hιX h₀ pY₀ hh₀ n

/-- The transitions `tTrans n` of the targets form cartesian squares over the transitions
`adicThickeningSucc` of the thickenings. -/
theorem isPullback_tTrans (n : ℕ) :
    IsPullback (tTrans hc fX pX₀ hιX h₀ pY₀ hh₀ n) (q hc fX pX₀ hιX h₀ pY₀ hh₀ n)
        (q hc fX pX₀ hιX h₀ pY₀ hh₀ (n + 1))
      (adicThickeningSucc Λ (maximalIdeal Λ) n) := by
  have := isIso_baseIso hc fX pX₀ hιX h₀ pY₀ hh₀ n
  have := isIso_baseIso hc fX pX₀ hιX h₀ pY₀ hh₀ (n + 1)
  have h1 : (liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ (n + 1)).inv ≫
      (forget pX₀ h₀ pY₀ hh₀).map (liftTransition hc fX pX₀ hιX h₀ pY₀ hh₀ n) ≫
        (liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ n).hom = truncationTransition hc fX pX₀ hιX n := by
    rw [Functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  have h3 : baseSpecMap ((liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ (n + 1)).inv.base ≫
      ((liftTransition hc fX pX₀ hιX h₀ pY₀ hh₀ n).left.base ≫
          (liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ n).hom.base)) =
      adicThickeningSucc Λ (maximalIdeal Λ) n :=
    (congrArg (fun φ => baseSpecMap (SchemeDeformationCategory.Hom.base φ)) h1).trans
      (baseSpecMap_transition hc n)
  have h4 : (baseSpecMap (liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ n).hom.base ≫
      baseSpecMap (liftTransition hc fX pX₀ hιX h₀ pY₀ hh₀ n).left.base) ≫
        baseIso hc fX pX₀ hιX h₀ pY₀ hh₀ (n + 1) = adicThickeningSucc Λ (maximalIdeal Λ) n :=
    ((baseSpecMap_comp _ _).trans (congrArg (· ≫ baseSpecMap _) (baseSpecMap_comp _ _))).symm.trans
      h3
  exact (liftTransition hc fX pX₀ hιX h₀ pY₀ hh₀ n).left.target_pullback.of_iso (Iso.refl _)
    (Iso.refl _) (asIso (baseIso hc fX pX₀ hιX h₀ pY₀ hh₀ n))
    (asIso (baseIso hc fX pX₀ hιX h₀ pY₀ hh₀ (n + 1))) (by simp) (by simp [q]) (by simp [q])
    (comp_eq_of_inv_comp _ _ (baseIso_baseSpecMap_hom hc fX pX₀ hιX h₀ pY₀ hh₀ n) _ _ _ h4)

end Lift

section Special

variable {Y₀ : Scheme.{u}} (h₀ : X₀ ⟶ Y₀)
  (pY₀ : Y₀ ⟶ Spec (.of (ResidueField Λ)))
  (hh₀ : h₀ ≫ pY₀ = pX₀)
  [(forget pX₀ h₀ pY₀ hh₀).IsEquivalence]

/-- The identification of `Y₀` with the special fibre of the zeroth target. -/
abbrev special : Y₀ ⟶ T hc fX pX₀ hιX h₀ pY₀ hh₀ 0 := (lift hc fX pX₀ hιX h₀ pY₀ hh₀ 0).hom.target

/-- `Y₀` is the fibre of the zeroth target over the residue point of its base. -/
theorem isPullback_special :
    IsPullback (special hc fX pX₀ hιX h₀ pY₀ hh₀) pY₀
        (lift hc fX pX₀ hιX h₀ pY₀ hh₀ 0).left.targetToBase
      (residueSpecMap (lift hc fX pX₀ hιX h₀ pY₀ hh₀ 0).left.base) := by
  have h := (lift hc fX pX₀ hιX h₀ pY₀ hh₀ 0).hom.target_pullback
  have e : baseSpecMap (lift hc fX pX₀ hιX h₀ pY₀ hh₀ 0).hom.base =
      residueSpecMap (lift hc fX pX₀ hιX h₀ pY₀ hh₀ 0).left.base :=
    baseSpecMap_eq_residueSpecMap _ _
  rwa [e] at h

/-- The special fibre of `X` inside the source of the zeroth lift. -/
theorem specialToLevel_srcMap :
    (hιX.isoPullback.hom ≫ specialToLevel hc fX 0) ≫ srcMap hc fX pX₀ hιX h₀ pY₀ hh₀ 0 =
        (lift hc fX pX₀ hιX h₀ pY₀ hh₀ 0).hom.source :=
  (liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ 0).hom.special_compat

/-- The zeroth lift restricts to `h₀` on special fibres. -/
theorem h₀_special :
    h₀ ≫ special hc fX pX₀ hιX h₀ pY₀ hh₀ =
      (lift hc fX pX₀ hιX h₀ pY₀ hh₀ 0).hom.source ≫
          (lift hc fX pX₀ hιX h₀ pY₀ hh₀ 0).left.morphism :=
  (lift hc fX pX₀ hιX h₀ pY₀ hh₀ 0).hom.source_pullback.w

/-- Under `baseIso 0`, the residue point of the base of the zeroth lift is the closed point
`levelPoint 0` of the zeroth thickening. -/
theorem residueSpecMap_baseIso :
    residueSpecMap (lift hc fX pX₀ hιX h₀ pY₀ hh₀ 0).left.base ≫
        baseIso hc fX pX₀ hιX h₀ pY₀ hh₀ 0 =
      levelPoint hc 0 :=
  (residueSpecMap_naturality (liftIso hc fX pX₀ hιX h₀ pY₀ hh₀ 0).inv.base).trans
    (baseSpecMap_eq_residueSpecMap _ (toResidue hc 0)).symm

/-- The residue point of the base of the zeroth lift is an isomorphism. -/
theorem isIso_residueSpecMap : IsIso (residueSpecMap
    (lift hc fX pX₀ hιX h₀ pY₀ hh₀ 0).left.base) := by
  have := isIso_baseIso hc fX pX₀ hιX h₀ pY₀ hh₀ 0
  have : residueSpecMap (lift hc fX pX₀ hιX h₀ pY₀ hh₀ 0).left.base =
      levelPoint hc 0 ≫ inv (baseIso hc fX pX₀ hιX h₀ pY₀ hh₀ 0) := by
    rw [← residueSpecMap_baseIso hc fX pX₀ hιX h₀ pY₀ hh₀, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [this]
  infer_instance

/-- `special` is an isomorphism of `Y₀` with the zeroth target. -/
theorem isIso_special : IsIso (special hc fX pX₀ hιX h₀ pY₀ hh₀) :=
  have := isIso_residueSpecMap hc fX pX₀ hιX h₀ pY₀ hh₀
  (isPullback_special hc fX pX₀ hιX h₀ pY₀ hh₀).isIso_fst_of_isIso

/-- Under `special`, the structure morphism `q 0` of the zeroth target is `pY₀` followed by
`levelPoint 0`. -/
theorem q_zero_eq :
    haveI := isIso_special hc fX pX₀ hιX h₀ pY₀ hh₀
    q hc fX pX₀ hιX h₀ pY₀ hh₀ 0 = inv (special hc fX pX₀ hιX h₀ pY₀ hh₀) ≫ pY₀ ≫
        levelPoint hc 0 := by
  have := isIso_special hc fX pX₀ hιX h₀ pY₀ hh₀
  rw [IsIso.eq_inv_comp, ← residueSpecMap_baseIso hc fX pX₀ hιX h₀ pY₀ hh₀, ← Category.assoc,
    (isPullback_special hc fX pX₀ hιX h₀ pY₀ hh₀).w, Category.assoc]

end Special

section Algebraized

variable {Y₀ : Scheme.{u}} (h₀ : X₀ ⟶ Y₀)
  (pY₀ : Y₀ ⟶ Spec (.of (ResidueField Λ)))
  (hh₀ : h₀ ≫ pY₀ = pX₀)
  [(forget pX₀ h₀ pY₀ hh₀).IsEquivalence]
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (.of Λ)) (k : ∀ n, T hc fX pX₀ hιX h₀ pY₀ hh₀ n ⟶ Y)
  (hk : ∀ n, tTrans hc fX pX₀ hιX h₀ pY₀ hh₀ n ≫ k (n + 1) = k n)
  (hpb : ∀ n, IsPullback (k n) (q hc fX pX₀ hιX h₀ pY₀ hh₀ n) fY
      (adicThickeningι Λ (maximalIdeal Λ) n))

/-- The comparison of the targets with the truncations of an algebraization `Y`. -/
def κ (n : ℕ) : T hc fX pX₀ hιX h₀ pY₀ hh₀ n ≅ adicBaseChange Λ (maximalIdeal Λ) fY n :=
  (hpb n).isoPullback

/-- `κ n` followed by the projection to `Y` is `k n`. -/
theorem κ_fst (n : ℕ) :
    (κ hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb n).hom ≫
        pullback.fst fY (adicThickeningι Λ (maximalIdeal Λ) n) =
      k n :=
  (hpb n).isoPullback_hom_fst

/-- `κ n` followed by the projection to the `n`-th thickening is `q n`. -/
theorem κ_snd (n : ℕ) :
    (κ hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb n).hom ≫
        pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) n) =
      q hc fX pX₀ hιX h₀ pY₀ hh₀ n :=
  (hpb n).isoPullback_hom_snd

include hk in
/-- The two composites `Tₙ ⟶ Yₙ₊₁` through `κ n` and through `κ (n + 1)` agree after
projection to `Y`. -/
theorem κ_succ_fst (n : ℕ) :
    ((κ hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb n).hom ≫ adicBaseChangeSucc Λ (maximalIdeal Λ) fY n) ≫
        pullback.fst fY (adicThickeningι Λ (maximalIdeal Λ) (n + 1)) =
      (tTrans hc fX pX₀ hιX h₀ pY₀ hh₀ n ≫ (κ hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb (n + 1)).hom) ≫
        pullback.fst fY (adicThickeningι Λ (maximalIdeal Λ) (n + 1)) := by
  rw [Category.assoc, Category.assoc, κ_fst, adicBaseChangeSucc, pullback.lift_fst, κ_fst, hk]

/-- The two composites `Tₙ ⟶ Yₙ₊₁` through `κ n` and through `κ (n + 1)` agree after
projection to the `(n + 1)`-st thickening. -/
theorem κ_succ_snd (n : ℕ) :
    ((κ hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb n).hom ≫ adicBaseChangeSucc Λ (maximalIdeal Λ) fY n) ≫
        pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) (n + 1)) =
      (tTrans hc fX pX₀ hιX h₀ pY₀ hh₀ n ≫ (κ hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb (n + 1)).hom) ≫
        pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) (n + 1)) := by
  rw [Category.assoc, Category.assoc, (isPullback_adicBaseChangeSucc Λ (maximalIdeal Λ) fY n).w,
    reassoc_of% κ_snd, κ_snd, (isPullback_tTrans hc fX pX₀ hιX h₀ pY₀ hh₀ n).w]
  simp only [q, Category.assoc]

include hk in
/-- The identifications `κ n` commute with the transitions of the targets and of the
truncations of `Y`. -/
theorem κ_succ (n : ℕ) :
    (κ hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb n).hom ≫ adicBaseChangeSucc Λ (maximalIdeal Λ) fY n =
      tTrans hc fX pX₀ hιX h₀ pY₀ hh₀ n ≫ (κ hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb (n + 1)).hom :=
  pullback.hom_ext (κ_succ_fst hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hk hpb n)
    (κ_succ_snd hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb n)

/-- The system of truncated morphisms `Xₙ ⟶ Yₙ`. -/
def g (n : ℕ) : adicBaseChange Λ (maximalIdeal Λ) fX n ⟶ adicBaseChange Λ (maximalIdeal Λ) fY n :=
  srcMap hc fX pX₀ hιX h₀ pY₀ hh₀ n ≫ (lift hc fX pX₀ hιX h₀ pY₀ hh₀ n).left.morphism ≫
    (κ hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb n).hom

/-- `g n` is a morphism over the `n`-th thickening. -/
theorem g_over (n : ℕ) :
    g hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb n ≫ pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) n) =
      pullback.snd fX (adicThickeningι Λ (maximalIdeal Λ) n) := by
  simp only [g, Category.assoc, κ_snd, q]
  rw [reassoc_of% (lift hc fX pX₀ hιX h₀ pY₀ hh₀ n).left.over_base,
    reassoc_of% srcMap_sourceToBase hc fX pX₀ hιX h₀ pY₀ hh₀ n, baseInv_baseIso, Category.comp_id]

include hk in
/-- The morphisms `g n` commute with the transitions of the truncations of `X` and `Y`. -/
theorem g_compat (n : ℕ) :
    adicBaseChangeSucc Λ (maximalIdeal Λ) fX n ≫ g hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb (n + 1) =
      g hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb n ≫ adicBaseChangeSucc Λ (maximalIdeal Λ) fY n := by
  have hw : (lift hc fX pX₀ hιX h₀ pY₀ hh₀ n).left.morphism ≫ tTrans hc fX pX₀ hιX h₀ pY₀ hh₀ n =
      (liftTransition hc fX pX₀ hιX h₀ pY₀ hh₀ n).left.source ≫
        (lift hc fX pX₀ hιX h₀ pY₀ hh₀ (n + 1)).left.morphism :=
    (liftTransition hc fX pX₀ hιX h₀ pY₀ hh₀ n).left.source_pullback.w
  simp only [g, Category.assoc]
  rw [κ_succ hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hk hpb, reassoc_of% hw, liftTransition_source]
  simp only [Category.assoc]
  rw [reassoc_of% srcMap_srcInv hc fX pX₀ hιX h₀ pY₀ hh₀ n]

include hc h₀ pY₀ hh₀ k hpb in
/-- Each truncation `Y ×_Λ Λ/𝔪ⁿ⁺¹` is flat over the `n`-th thickening. -/
theorem flat_snd (n : ℕ) : Flat (pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) n)) := by
  have := (lift hc fX pX₀ hιX h₀ pY₀ hh₀ n).left.target_flat
  have := isIso_baseIso hc fX pX₀ hιX h₀ pY₀ hh₀ n
  have e : pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) n) =
      (κ hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb n).inv ≫ q hc fX pX₀ hιX h₀ pY₀ hh₀ n := by
    rw [← κ_snd hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb n, Iso.inv_hom_id_assoc]
  rw [e]
  infer_instance

/-- The identification of `Y₀` with the special fibre of an algebraization `Y`. -/
def ψ : Y₀ ≅ pullback fY (closedPoint Λ) :=
  haveI := isIso_special hc fX pX₀ hιX h₀ pY₀ hh₀
  haveI : IsIso (specialToLevel hc fY 0) := (isPullback_specialToLevel hc fY 0).isIso_fst_of_isIso
  asIso (special hc fX pX₀ hιX h₀ pY₀ hh₀) ≪≫ κ hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb 0 ≪≫
    (asIso (specialToLevel hc fY 0)).symm

/-- `ψ` followed by the inclusion of the special fibre of `Y` into its zeroth truncation is
`special` followed by `κ 0`. -/
theorem ψ_hom_specialToLevel :
    (ψ hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb).hom ≫ specialToLevel hc fY 0 =
      special hc fX pX₀ hιX h₀ pY₀ hh₀ ≫ (κ hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb 0).hom := by
  simp [ψ]

/-- `ψ` is an isomorphism over `Spec κ`. -/
theorem ψ_hom_snd :
    (ψ hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb).hom ≫ pullback.snd fY (closedPoint Λ) = pY₀ := by
  rw [← cancel_mono (levelPoint hc 0), Category.assoc, ← specialToLevel_snd hc fY 0,
    reassoc_of% ψ_hom_specialToLevel, κ_snd]
  simp only [q]
  rw [← residueSpecMap_baseIso hc fX pX₀ hιX h₀ pY₀ hh₀,
    reassoc_of% (isPullback_special hc fX pX₀ hιX h₀ pY₀ hh₀).w]

/-- A morphism `h : X ⟶ Y` over `Spec Λ` whose truncations are the `g n` restricts on special
fibres to `h₀`, under the identification `ψ`. -/
theorem ιX_comp_eq (h : X ⟶ Y) (hh : h ≫ fY = fX)
    (hn : ∀ n, adicBaseChangeMap Λ (maximalIdeal Λ) h hh n =
      g hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb n) :
    ιX ≫ h = h₀ ≫ (ψ hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb).hom ≫ pullback.fst fY (closedPoint Λ) := by
  have : IsIso (specialToLevel hc fY 0) := (isPullback_specialToLevel hc fY 0).isIso_fst_of_isIso
  have key : hιX.isoPullback.hom ≫ specialMap fX fY h hh =
      h₀ ≫ (ψ hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb).hom := by
    rw [← cancel_mono (specialToLevel hc fY 0), Category.assoc, Category.assoc,
      ψ_hom_specialToLevel, specialMap_specialToLevel hc fX fY h hh 0, hn 0]
    simp only [g]
    rw [reassoc_of% specialToLevel_srcMap hc fX pX₀ hιX h₀ pY₀ hh₀,
      reassoc_of% h₀_special hc fX pX₀ hιX h₀ pY₀ hh₀]
    exact (Category.assoc _ _ _).symm
  have hfst : specialMap fX fY h hh ≫ pullback.fst fY (closedPoint Λ) =
      pullback.fst fX (closedPoint Λ) ≫ h := pullback.lift_fst _ _ _
  conv_lhs => rw [← hιX.isoPullback_hom_fst]
  rw [Category.assoc, ← hfst, ← Category.assoc, key, Category.assoc]

end Algebraized

/-- **Existence of a contraction over a complete Noetherian local ring.** Let `Λ` be a complete
Noetherian local ring with residue field `κ` and closed point `s : Spec κ ⟶ Spec Λ`, let
`fX : X ⟶ Spec Λ` be proper and flat with special fibre `X₀` (a cartesian square `ιX`), and let
`h₀ : X₀ ⟶ Y₀` be a morphism over `κ` to a proper scheme `Y₀` over `κ` of dimension at most one.
If `𝒪_{Y₀} ⟶ h₀,* 𝒪_{X₀}` is an isomorphism and `R¹h₀,* 𝒪_{X₀} = 0`, there are a projective flat
`fY : Y ⟶ Spec Λ`, a morphism `h : X ⟶ Y` over `Spec Λ` and an identification `j` of `Y₀` with
the special fibre of `Y` under which `h` restricts to `h₀`.

This is the formal step of the proof of [Stacks, Tag 0E7C]. -/
theorem exists_contraction_of_specialFibre_of_isAdicComplete
    {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
    (hc : IsAdicComplete (maximalIdeal Λ) Λ)
    {X : Scheme.{u}} (fX : X ⟶ Spec (.of Λ)) [IsProper fX] [Flat fX]
    {X₀ : Scheme.{u}} (pX₀ : X₀ ⟶ Spec (.of (ResidueField Λ))) {ιX : X₀ ⟶ X}
    (hιX : IsPullback ιX pX₀ fX (closedPoint Λ))
    {Y₀ : Scheme.{u}} (h₀ : X₀ ⟶ Y₀)
    (pY₀ : Y₀ ⟶ Spec (.of (ResidueField Λ))) [IsProper pY₀]
    (hh₀ : h₀ ≫ pY₀ = pX₀)
    (hdim : topologicalKrullDim Y₀ ≤ 1)
    (h0 : IsIso (C := Y₀.Modules) (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit X₀.ringCatSheaf))) :
    ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of Λ)), IsProjectiveMorphism fY ∧ Flat fY ∧
      ∃ (h : X ⟶ Y) (_ : h ≫ fY = fX) (j : Y₀ ⟶ Y),
        IsPullback j pY₀ fY (closedPoint Λ) ∧ ιX ≫ h = h₀ ≫ j := by
  have : (forget pX₀ h₀ pY₀ hh₀).IsEquivalence :=
    schemeMorphismSourceForgetful_isEquivalence_of_specialFibre _ _ _ _ h0 hR
  have := isIso_special hc fX pX₀ hιX h₀ pY₀ hh₀
  have hq0 : IsProper (q hc fX pX₀ hιX h₀ pY₀ hh₀ 0) := by
    rw [q_zero_eq]
    infer_instance
  have hdim0 : topologicalKrullDim (T hc fX pX₀ hιX h₀ pY₀ hh₀ 0) ≤ 1 := by
    rwa [← IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (asIso (special hc fX pX₀ hιX h₀ pY₀ hh₀))).isHomeomorph]
  obtain ⟨Y, fY, hproj, k, hk, hpb⟩ :=
    Stacks.FormalCurve.exists_isProjectiveMorphism_of_topologicalKrullDim_le_one Λ (maximalIdeal Λ)
      (q hc fX pX₀ hιX h₀ pY₀ hh₀) (tTrans hc fX pX₀ hιX h₀ pY₀ hh₀)
      (isPullback_tTrans hc fX pX₀ hιX h₀ pY₀ hh₀) hq0 hdim0
  have : IsProper fY := isProper_of_isProjectiveMorphism fY hproj
  obtain ⟨⟨h, hh⟩, hn, -⟩ :=
    existsUnique_algebraization_adicBaseChangeMap_holds Λ (maximalIdeal Λ) hc fX fY
      (g hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb) (g_over hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb)
      (g_compat hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hk hpb)
  set ψ' := ψ hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb
  refine ⟨Y, fY, hproj, flat_of_flat_pullback_adicThickeningι_maximalIdeal fY
      (flat_snd hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb),
    h, hh, ψ'.hom ≫ pullback.fst fY (closedPoint Λ), ?_,
    ιX_comp_eq hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb h hh hn⟩
  refine (IsPullback.of_hasPullback fY (closedPoint Λ)).of_iso ψ'.symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (by simp) ?_ (by simp) (by simp)
  rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp]
  exact ψ_hom_snd hc fX pX₀ hιX h₀ pY₀ hh₀ fY k hpb

/-- **The target of a contraction has at most the dimension of its source.** A universally
closed, quasi-compact `f : X ⟶ Y` with `𝒪_Y ≅ f_*𝒪_X` is scheme-theoretically dominant, hence
dominant and, being closed, surjective; so `dim Y ≤ dim X` by Stacks 02JF. -/
theorem topologicalKrullDim_le_of_isIso_unitToPushforwardUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversallyClosed f] [QuasiCompact f]
    (h0 : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit f)) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  have := isSchemeTheoreticallyDominant_of_isIso_unitToPushforwardUnit f
  exact Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap f.base
    f.base.hom.continuous f.surjective (Or.inl f.isClosedMap.specializingMap)

/-- **Existence of a contraction over a complete Noetherian local ring**, with the dimension
bound on the special fibre of `X`: under the hypotheses of
`exists_contraction_of_specialFibre_of_isAdicComplete` the bound `dim Y₀ ≤ 1` follows from
`dim Xₛ ≤ 1`, the contraction `h₀` being surjective. -/
theorem exists_contraction_of_specialFibre_of_isAdicComplete'
    {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
    (hc : IsAdicComplete (maximalIdeal Λ) Λ)
    {X : Scheme.{u}} (fX : X ⟶ Spec (.of Λ)) [IsProper fX] [Flat fX]
    {X₀ : Scheme.{u}} (pX₀ : X₀ ⟶ Spec (.of (ResidueField Λ))) {ιX : X₀ ⟶ X}
    (hιX : IsPullback ιX pX₀ fX (ContractionUniquenessComplete.closedPoint Λ))
    (hdimX : topologicalKrullDim X₀ ≤ 1)
    {Y₀ : Scheme.{u}} (h₀ : X₀ ⟶ Y₀)
    (pY₀ : Y₀ ⟶ Spec (.of (ResidueField Λ))) [IsProper pY₀]
    (hh₀ : h₀ ≫ pY₀ = pX₀)
    (h0 : IsIso (C := Y₀.Modules) (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit X₀.ringCatSheaf))) :
    ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of Λ)), IsProjectiveMorphism fY ∧ Flat fY ∧
      ∃ (h : X ⟶ Y) (_ : h ≫ fY = fX) (j : Y₀ ⟶ Y),
        IsPullback j pY₀ fY (ContractionUniquenessComplete.closedPoint Λ) ∧ ιX ≫ h = h₀ ≫ j := by
  have : IsProper pX₀ := by
    rw [← hιX.isoPullback_hom_snd]
    infer_instance
  have : IsProper (h₀ ≫ pY₀) := hh₀ ▸ inferInstance
  have : IsProper h₀ := IsProper.of_comp h₀ pY₀
  exact exists_contraction_of_specialFibre_of_isAdicComplete hc fX pX₀ hιX
    h₀ pY₀ hh₀ ((topologicalKrullDim_le_of_isIso_unitToPushforwardUnit h₀ h0).trans hdimX) h0 hR

end ContractionExistenceComplete

end AlgebraicGeometry

end
