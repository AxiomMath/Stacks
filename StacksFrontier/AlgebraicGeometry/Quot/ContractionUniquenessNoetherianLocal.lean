module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessCompleteSite
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfAdicCompletion
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceUnderCompletion
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatSurjectiveMonomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactAffineMorphism
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ProperMorphismDescent

/-!
# Uniqueness of contractions over a Noetherian local object of a big fppf site

Let `W` be an object of the big fppf site of a scheme `S` whose underlying scheme is the spectrum
of a Noetherian local ring `Λ`, let `X`, `Y₁`, `Y₂` be algebraic spaces proper and flat over `W`
and `cᵢ : X ⟶ Yᵢ` morphisms over `W`, and suppose the closed fibres satisfy the hypotheses of
[Stacks, Tag 0E89]: they are presented by schemes of dimension at most one, the closed fibres of
`Y₁` and `Y₂` are identified compatibly with the `cᵢ`, and the closed fibre `a₁` of `c₁` has
`𝒪 ≅ a₁,* 𝒪` and `R¹a₁,* 𝒪 = 0`. Then `Y₁ ≅ Y₂` over `W`, compatibly with the `cᵢ` and with the
identification of closed fibres.

This is the second step of the proof of [Stacks, Tag 0E89], the passage from a Noetherian local
ring `Λ` to its completion `Λ^∧` ([Stacks, Tag 07NU]). The morphism `Spec Λ^∧ ⟶ Spec Λ` is
faithfully flat and affine, hence a one-member fpqc covering; over `Spec Λ^∧` the complete case
`AlgebraicGeometry.Space.exists_iso_of_closedFibre_of_isAdicComplete_of_siteObject` gives an
isomorphism of the base changes compatible with the base changes of the `cᵢ`, and the base change
of `c₁` has scheme-theoretic image everything
(`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_top_of_closedFibre_of_isAdicComplete`).
That is the descent condition of
`Space.exists_iso_desc_of_isFpqcCovering_of_schemeTheoreticImageSubfunctor_eq_top` (the source's
appeal to the commutation of scheme-theoretic images with flat base change, [Stacks, Tag 089E]),
which descends the isomorphism. The closed point of `Spec Λ^∧` is the closed point of `Spec Λ`,
the residue fields being identified, so the closed fibres over `Spec Λ^∧` are the given ones.

## Main results

* `AlgebraicGeometry.Space.exists_iso_of_closedFibre_of_isNoetherianRing_of_siteObject`: the
  statement above.

## References

* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
* [Stacks Project, Tag 07NU](https://stacks.math.columbia.edu/tag/07NU)
* [Stacks Project, Tag 089E](https://stacks.math.columbia.edu/tag/089E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

local notation "𝒯S" => BigFppfOver.toScheme B S hS

/-- **A presentation of a fibre over a point through a morphism of bases is a presentation of the
fibre of the base change.** If the fibre of `f : X ⟶ yoneda W` over `k : K ⟶ W` is presented by
`i : yoneda F ⟶ X` and `k` factors as `k' ≫ π`, then the fibre of the base change of `f` along
`π` over `k'` is presented by the lift of `i`. -/
theorem isPullback_lift_of_isPullback_of_comp_eq {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W W' K F : BigFppfOver B S hS} (f : X ⟶ yoneda.obj W) (π : W' ⟶ W) (k : K ⟶ W)
    (k' : K ⟶ W') (hk : k' ≫ π = k) (t : F ⟶ K) (i : yoneda.obj F ⟶ X)
    (hi : IsPullback i (yoneda.map t) f (yoneda.map k)) :
    IsPullback (pullback.lift i (yoneda.map t ≫ yoneda.map k')
        (by rw [Category.assoc, ← Functor.map_comp, hk, hi.w]) :
          yoneda.obj F ⟶ pullback f (yoneda.map π))
      (yoneda.map t) (pullback.snd f (yoneda.map π)) (yoneda.map k') := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f _)
  rw [pullback.lift_fst, ← Functor.map_comp, hk]
  exact hi

section Completion

variable (Λ : Type u) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]

/-- The residue field of a Noetherian local ring is the residue field of its completion. -/
def completionResidueFieldEquiv :
    ResidueField Λ ≃+* ResidueField (AdicCompletion (maximalIdeal Λ) Λ) :=
  RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective Λ)

/-- The inverse of `completionResidueFieldEquiv` sends the residue of the image of `x : Λ` in the
completion to the residue of `x`. -/
theorem completionResidueFieldEquiv_residue_algebraMap :
    ((completionResidueFieldEquiv Λ).symm : _ →+* ResidueField Λ).comp
        ((residue (AdicCompletion (maximalIdeal Λ) Λ)).comp
          (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ))) = residue Λ := by
  ext x
  apply (completionResidueFieldEquiv Λ).injective
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, RingEquiv.apply_symm_apply]
  exact (ResidueField.map_residue _ x).symm

end Completion

/-- **The Noetherian local case of [Stacks, Tag 0E89] over an object of a big fppf site.** Let
`W` be an object of the big fppf site of `S` whose underlying scheme is, through `ε`, the spectrum
of a Noetherian local ring `Λ`; let `X`, `Y₁`, `Y₂` be algebraic spaces proper and flat over `W`
and `cᵢ : X ⟶ Yᵢ` morphisms over `W`. Let `k : K ⟶ W` be, through `ι` and `ε`, the closed point,
and let the fibres of `X`, `Y₁`, `Y₂` over it be presented by objects `F_X`, `F₁`, `F₂` of
dimension at most one, with `aᵢ : F_X ⟶ Fᵢ` the fibres of `cᵢ` and `φ : F₁ ≅ F₂` an isomorphism
over `K` with `a₁ ≫ φ = a₂`. If `a₁` has fibres of dimension at most one, `𝒪_{F₁} ≅ a₁,* 𝒪_{F_X}`
and `R¹a₁,* 𝒪_{F_X} = 0`, there is an isomorphism `ψ : Y₁ ≅ Y₂` over `W` with `c₁ ≫ ψ = c₂` whose
restriction to the closed fibre is `φ`. -/
theorem exists_iso_of_closedFibre_of_isNoetherianRing_of_siteObject (Λ : Type u) [CommRing Λ]
    [IsLocalRing Λ] [IsNoetherianRing Λ]
    (W : BigFppfOver B S hS) (ε : (𝒯S).obj W ≅ Spec (.of Λ))
    {X Y₁ Y₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY₁ : IsAlgebraicSpace B S hS Y₁)
    (hY₂ : IsAlgebraicSpace B S hS Y₂)
    (fX : X ⟶ yoneda.obj W) (g₁ : Y₁ ⟶ yoneda.obj W) (g₂ : Y₂ ⟶ yoneda.obj W)
    (hpX : IsProper B S hS fX) (hp₁ : IsProper B S hS g₁) (hp₂ : IsProper B S hS g₂)
    (hfX : IsFlat B S hS fX) (hf₁ : IsFlat B S hS g₁) (hf₂ : IsFlat B S hS g₂)
    (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂) (hc₁ : c₁ ≫ g₁ = fX) (hc₂ : c₂ ≫ g₂ = fX)
    {K : BigFppfOver B S hS} (k : K ⟶ W) (ι : Spec (.of (ResidueField Λ)) ≅ (𝒯S).obj K)
    (hι : ι.hom ≫ (𝒯S).map k ≫ ε.hom = ContractionUniquenessComplete.closedPoint Λ)
    {FX F₁ F₂ : BigFppfOver B S hS} (tX : FX ⟶ K) (t₁ : F₁ ⟶ K) (t₂ : F₂ ⟶ K)
    (iX : yoneda.obj FX ⟶ X) (i₁ : yoneda.obj F₁ ⟶ Y₁) (i₂ : yoneda.obj F₂ ⟶ Y₂)
    (hiX : IsPullback iX (yoneda.map tX) fX (yoneda.map k))
    (hi₁ : IsPullback i₁ (yoneda.map t₁) g₁ (yoneda.map k))
    (hi₂ : IsPullback i₂ (yoneda.map t₂) g₂ (yoneda.map k))
    (hdX : topologicalKrullDim ((𝒯S).obj FX) ≤ 1) (hd₁ : topologicalKrullDim ((𝒯S).obj F₁) ≤ 1)
    (hd₂ : topologicalKrullDim ((𝒯S).obj F₂) ≤ 1)
    (a₁ : FX ⟶ F₁) (a₂ : FX ⟶ F₂) (ha₁ : a₁ ≫ t₁ = tX) (ha₂ : a₂ ≫ t₂ = tX)
    (hia₁ : iX ≫ c₁ = yoneda.map a₁ ≫ i₁) (hia₂ : iX ≫ c₂ = yoneda.map a₂ ≫ i₂)
    (φ : F₁ ≅ F₂) (hφ : φ.hom ≫ t₂ = t₁) (hφa : a₁ ≫ φ.hom = a₂)
    (hdimF : ∀ y, topologicalKrullDim (((𝒯S).map a₁).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit ((𝒯S).map a₁)))
    (hR : IsZero (Stacks.AlgebraicGeometry.TopDegreeBaseChange.firstDirectImageStructureSheaf
      ((𝒯S).map a₁))) :
    ∃ ψ : Y₁ ≅ Y₂, ψ.hom ≫ g₂ = g₁ ∧ c₁ ≫ ψ.hom = c₂ ∧ i₁ ≫ ψ.hom = yoneda.map φ.hom ≫ i₂ := by
  set Λ' := AdicCompletion (maximalIdeal Λ) Λ
  obtain ⟨-, -, -, -, hff⟩ := AdicCompletion.noetherian_completeLocal_faithfullyFlat Λ
  have hΛ : B.Contains (Spec (.of Λ)) :=
    (Scheme.size_congr ε).symm.trans_lt W.left.property
  have hΛ' : B.Contains (Spec (.of Λ')) := B.contains_spec_adicCompletion hΛ _
  set αΛ : CommRingCat.of Λ ⟶ CommRingCat.of Λ' := CommRingCat.ofHom (algebraMap Λ Λ')
  set aW : Spec (.of Λ') ⟶ (𝒯S).obj W := Spec.map αΛ ≫ ε.inv
  set W' : BigFppfOver B S hS :=
    Over.mk ((ObjectProperty.homMk aW : B.obj hΛ' ⟶ W.left) ≫ W.hom)
  set π : W' ⟶ W := Over.homMk (ObjectProperty.homMk aW) rfl
  have hπ : (𝒯S).map π = aW := rfl
  set e := completionResidueFieldEquiv Λ
  set kmap : (𝒯S).obj K ⟶ Spec (.of Λ') := ι.inv ≫
    Spec.map (CommRingCat.ofHom ((e.symm : _ →+* ResidueField Λ).comp (residue Λ')))
  have hkmap : kmap ≫ aW = (𝒯S).map k := by
    have hk : (𝒯S).map k = ι.inv ≫ ContractionUniquenessComplete.closedPoint Λ ≫ ε.inv := by
      rw [← hι]; simp
    rw [hk]
    simp only [kmap, aW, Category.assoc]
    congr 1
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    exact congrArg CommRingCat.ofHom (completionResidueFieldEquiv_residue_algebraMap Λ)
  set k' : K ⟶ W' := Over.homMk (ObjectProperty.homMk kmap) (by
    have h := Over.w k
    refine Eq.trans ?_ h
    change (ObjectProperty.homMk kmap : K.left ⟶ B.obj hΛ') ≫
      (ObjectProperty.homMk aW : B.obj hΛ' ⟶ W.left) ≫ W.hom = k.left ≫ W.hom
    rw [← Category.assoc]
    congr 1
    exact ObjectProperty.hom_ext _ hkmap)
  have hk' : k' ≫ π = k := Over.OverMorphism.ext (ObjectProperty.hom_ext _ hkmap)
  set ι' : Spec (.of (ResidueField Λ')) ≅ (𝒯S).obj K :=
    Scheme.Spec.mapIso e.toCommRingCatIso.op ≪≫ ι
  have hι' : ι'.hom ≫ (𝒯S).map k' ≫ (Iso.refl (Spec (.of Λ'))).hom =
      ContractionUniquenessComplete.closedPoint Λ' := by
    change (Spec.map (CommRingCat.ofHom (e : ResidueField Λ →+* ResidueField Λ')) ≫ ι.hom) ≫
      kmap ≫ 𝟙 _ = _
    simp only [kmap, Category.comp_id, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp
  have hWa := isAlgebraicSpace_yoneda B S hS W
  have hW'a := isAlgebraicSpace_yoneda B S hS W'
  set yπ := yoneda.map π
  have hX' := isAlgebraicSpace_pullback B S hS fX yπ hX hW'a hWa
  have hY₁' := isAlgebraicSpace_pullback B S hS g₁ yπ hY₁ hW'a hWa
  have hY₂' := isAlgebraicSpace_pullback B S hS g₂ yπ hY₂ hW'a hWa
  have hmap : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Y ⟶ yoneda.obj W) (c : X ⟶ Y),
      c ≫ g = fX → ∃ c' : pullback fX yπ ⟶ pullback g yπ,
        c' ≫ pullback.snd g yπ = pullback.snd fX yπ ∧
          c' ≫ pullback.fst g yπ = pullback.fst fX yπ ≫ c :=
    fun g c hc => ⟨pullback.map _ _ _ _ c (𝟙 _) (𝟙 _) (by simp [hc]) (by simp), by simp, by simp⟩
  obtain ⟨c₁', hc₁'s, hc₁'f⟩ := hmap g₁ c₁ hc₁
  obtain ⟨c₂', hc₂'s, hc₂'f⟩ := hmap g₂ c₂ hc₂
  have hproper : ∀ {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
      (g : Z ⟶ yoneda.obj W), IsProper B S hS g → IsProper B S hS (pullback.snd g yπ) :=
    fun hZ g hg => isProper_of_isPullback' (isAlgebraicSpace_pullback B S hS g yπ hZ hW'a hWa) hZ
      hW'a hWa (IsPullback.of_hasPullback g yπ) hg
  have hpX' := hproper hX fX hpX
  have hp₁' := hproper hY₁ g₁ hp₁
  have hp₂' := hproper hY₂ g₂ hp₂
  let T : AlgebraicSpaces B S hS := ⟨yoneda.obj W, hWa⟩
  let T' : AlgebraicSpaces B S hS := ⟨yoneda.obj W', hW'a⟩
  let πb : T' ⟶ T := ObjectProperty.homMk yπ
  have sqb : ∀ {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
      (g : Z ⟶ yoneda.obj W),
      IsPullback (ObjectProperty.homMk (pullback.fst g yπ) :
          (⟨pullback g yπ, isAlgebraicSpace_pullback B S hS g yπ hZ hW'a hWa⟩ :
            AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)
        (ObjectProperty.homMk (pullback.snd g yπ) : _ ⟶ T')
        (ObjectProperty.homMk g : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ T) πb :=
    fun hZ g => isPullback_homMk B S hS hZ hW'a hWa
      (isAlgebraicSpace_pullback B S hS g yπ hZ hW'a hWa) (IsPullback.of_hasPullback g yπ)
  have hflat : ∀ {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
      (g : Z ⟶ yoneda.obj W), IsFlat B S hS g → IsFlat B S hS (pullback.snd g yπ) :=
    fun hZ g hg => (isFlat_isStableUnderBaseChange B S hS).of_isPullback (sqb hZ g) hg
  have sqX := isPullback_lift_of_isPullback_of_comp_eq B S hS fX π k k' hk' tX iX hiX
  have sq₁ := isPullback_lift_of_isPullback_of_comp_eq B S hS g₁ π k k' hk' t₁ i₁ hi₁
  have sq₂ := isPullback_lift_of_isPullback_of_comp_eq B S hS g₂ π k k' hk' t₂ i₂ hi₂
  set iX' := pullback.lift iX (yoneda.map tX ≫ yoneda.map k') (by
    rw [Category.assoc, ← Functor.map_comp, hk', hiX.w]) with hiX'
  set i₁' := pullback.lift i₁ (yoneda.map t₁ ≫ yoneda.map k') (by
    rw [Category.assoc, ← Functor.map_comp, hk', hi₁.w]) with hi₁'
  set i₂' := pullback.lift i₂ (yoneda.map t₂ ≫ yoneda.map k') (by
    rw [Category.assoc, ← Functor.map_comp, hk', hi₂.w]) with hi₂'
  have hia : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g : Y ⟶ yoneda.obj W} {F : BigFppfOver B S hS}
      {t : F ⟶ K} {i : yoneda.obj F ⟶ Y} (c : X ⟶ Y) (c' : pullback fX yπ ⟶ pullback g yπ)
      (_ : c' ≫ pullback.snd g yπ = pullback.snd fX yπ)
      (_ : c' ≫ pullback.fst g yπ = pullback.fst fX yπ ≫ c) (a : FX ⟶ F) (_ : a ≫ t = tX)
      (_ : iX ≫ c = yoneda.map a ≫ i) (hi : IsPullback i (yoneda.map t) g (yoneda.map k)),
      iX' ≫ c' = yoneda.map a ≫ pullback.lift i (yoneda.map t ≫ yoneda.map k')
        (by rw [Category.assoc, ← Functor.map_comp, hk', hi.w]) := by
    intro Y g F t i c c' hs hf a ha hia hi
    apply pullback.hom_ext
    · rw [Category.assoc, hf, pullback.lift_fst_assoc, hia, Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, hs, pullback.lift_snd, Category.assoc, pullback.lift_snd, ← ha]
      simp
  have hia₁' := hia c₁ c₁' hc₁'s hc₁'f a₁ ha₁ hia₁ hi₁
  have hia₂' := hia c₂ c₂' hc₂'s hc₂'f a₂ ha₂ hia₂ hi₂
  obtain ⟨ψ', hψ'g, hψ'c, hψ'f⟩ := exists_iso_of_closedFibre_of_isAdicComplete_of_siteObject B S hS
    Λ' W' (Iso.refl _) hX' hY₁' hY₂' _ _ _ hpX' hp₁' hp₂' (hflat hX fX hfX) (hflat hY₁ g₁ hf₁)
    (hflat hY₂ g₂ hf₂) c₁' c₂' hc₁'s hc₂'s k' ι' hι' tX t₁ t₂ iX' i₁' i₂' sqX sq₁ sq₂ hdX hd₁ hd₂
    a₁ a₂ ha₁ ha₂ hia₁' hia₂' φ hφ hφa hdimF h0 hR
  have hdom := schemeTheoreticImageSubfunctor_eq_top_of_closedFibre_of_isAdicComplete B S hS
    Λ' W' (Iso.refl _) hX' hY₁' _ _ hpX' hp₁' (hflat hX fX hfX) c₁' hc₁'s k' ι' hι' tX t₁ iX' i₁'
    sqX sq₁ hdX hd₁ a₁ ha₁ hia₁' hdimF h0 hR
  let Xb : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Y₁b : AlgebraicSpaces B S hS := ⟨Y₁, hY₁⟩
  let Y₂b : AlgebraicSpaces B S hS := ⟨Y₂, hY₂⟩
  let X'b : AlgebraicSpaces B S hS := ⟨pullback fX yπ, hX'⟩
  let Y₁'b : AlgebraicSpaces B S hS := ⟨pullback g₁ yπ, hY₁'⟩
  let Y₂'b : AlgebraicSpaces B S hS := ⟨pullback g₂ yπ, hY₂'⟩
  have hcov : IsFpqcCovering B S hS (fun _ : Unit => πb.hom) := by
    have hfs := (flat_and_surjective_SpecMap_iff αΛ).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 hff)
    have : Flat (Spec.map αΛ) := hfs.1
    have : Surjective (Spec.map αΛ) := hfs.2
    refine isFpqcCovering_of_isQuasiCompact_of_isFlat_of_isSurjective B S hS πb
      (isQuasiCompact_yoneda_map_of_isAffineHom B S hS π ?_) (isFlat_yoneda_map B S hS π ?_)
      (isSurjective_yoneda_map B S hS π ?_)
    · have : IsAffine ((𝒯S).obj W) := .of_isIso ε.hom
      change _root_.AlgebraicGeometry.IsAffineHom (Spec.map αΛ ≫ ε.inv)
      infer_instance
    · rw [hπ]; infer_instance
    · rw [hπ]; infer_instance
  have hqc : IsQuasiCompact B S hS c₁' :=
    (isProper_of_comp_of_isSeparated B S hS hX' hY₁' hW'a c₁' (pullback.snd g₁ yπ)
      (by rw [hc₁'s]; exact hpX') hp₁'.1).2.1.2
  let ψ'b : Y₁'b ≅ Y₂'b := (ObjectProperty.fullyFaithfulι _).preimageIso ψ'
  obtain ⟨ψ, hψg, hψp, hψc⟩ :=
    exists_iso_desc_of_isFpqcCovering_of_schemeTheoreticImageSubfunctor_eq_top
      (T := T) (T' := T') (X := Xb) (Y₁ := Y₁b) (Y₂ := Y₂b) (X' := X'b) (Y₁' := Y₁'b)
      (Y₂' := Y₂'b) (π := πb) hcov (f := ObjectProperty.homMk fX)
      (g₁ := ObjectProperty.homMk g₁) (g₂ := ObjectProperty.homMk g₂) hp₁.1 hp₂.1
      (sqb hX fX) (sqb hY₁ g₁) (sqb hY₂ g₂) (c₁ := ObjectProperty.homMk c₁)
      (ObjectProperty.hom_ext _ hc₁) (c₂ := ObjectProperty.homMk c₂)
      (ObjectProperty.hom_ext _ hc₂) (c₁' := ObjectProperty.homMk c₁')
      (ObjectProperty.hom_ext _ hc₁'f) (ObjectProperty.hom_ext _ hc₁'s) hqc hdom ψ'b
      (ObjectProperty.hom_ext _ hψ'g)
      (ObjectProperty.hom_ext _ (by
        change c₁' ≫ ψ'.hom ≫ pullback.fst g₂ yπ = pullback.fst fX yπ ≫ c₂
        rw [reassoc_of% hψ'c, hc₂'f]))
  have hψp' : pullback.fst g₁ yπ ≫ ψ.hom.hom = ψ'.hom ≫ pullback.fst g₂ yπ :=
    congrArg (fun m => m.hom) hψp
  refine ⟨(ObjectProperty.ι _).mapIso ψ, congrArg (fun m => m.hom) hψg,
    congrArg (fun m => m.hom) hψc, ?_⟩
  change i₁ ≫ ψ.hom.hom = yoneda.map φ.hom ≫ i₂
  have h₁ : i₁ = i₁' ≫ pullback.fst g₁ yπ := (pullback.lift_fst _ _ _).symm
  have h₂ : i₂ = i₂' ≫ pullback.fst g₂ yπ := (pullback.lift_fst _ _ _).symm
  rw [h₁, Category.assoc, hψp', reassoc_of% hψ'f, h₂]

end AlgebraicGeometry.Space

end
