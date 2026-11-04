module

public import StacksFrontier.AlgebraicGeometry.Limits.EventuallyProperOverLimit
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.SeparatedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Induction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianStageModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.PointsRelocalized
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.RestrictedFibreProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnected

/-!
# Noetherian models of proper, flat, finitely presented algebraic spaces

Let `X` be an algebraic space over `Spec A` which is proper, flat and of finite presentation over
`Spec A`. Then there are a ring `A₀ ⊆ A` of finite type over `ℤ` and an algebraic space `X₀` over
`Spec A₀`, proper, flat and of finite presentation, whose base change along `Spec A ⟶ Spec A₀` is
`X`. This is the Noetherian approximation used in the proof of Stacks 0E6B and 0CTM.

## Main results

* `AlgebraicGeometry.Space.isSurjective_relocalizeRestrict_map`: restriction to a smaller base
  preserves surjectivity.
* `AlgebraicGeometry.Space.exists_finiteType_model_of_isFinitePresentation`: a model of finite
  presentation over a ring of finite type over `ℤ`, separated or flat if `X` is.
* `AlgebraicGeometry.Space.exists_finiteType_model_of_isProper`: the proper, flat model.

## Implementation notes

The model of finite presentation is `AlgebraicGeometry.Space.exists_stageModel`; it is separated
and flat, and properness is achieved over a later stage of the Noetherian approximation
`Spec A = lim Spec A_λ` as in Stacks 08K1. By Chow's lemma (Stacks 089J) there is a scheme
`X₀'`, H-quasi-projective over `Spec A₀`, with a proper surjection `X₀' ⟶ X₀`. Its base change
to `Spec A` is proper, being proper over the proper `X`, so by Stacks 081F its base change to some
`Spec A_λ` is proper; and then the base change `X_λ` of `X₀` is universally closed over `Spec A_λ`
by Stacks 08AJ, because it receives a surjection from a scheme proper over `Spec A_λ`.

## References

* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
* [Stacks Project, Tag 0A0X](https://stacks.math.columbia.edu/tag/0A0X)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Surjectivity of a restriction -/

section Restrict

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
  {T : Scheme.{u}} (hT : B.Contains T) (g : B.obj hT ⟶ B.obj hS)

/-- **Restriction to a smaller base preserves surjectivity.** Viewed again over `S`, the
restriction of `f` is a base change of `f`, and the points of a presheaf over `T` are the points
of its lower-shriek extension to `S`. -/
theorem isSurjective_relocalizeRestrict_map (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hf : IsSurjective B S hS f) :
    IsSurjective B T hT ((OverShriek.relocalizeRestrict g).map f) := by
  let Xₐ : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Yₐ : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let XTₐ : AlgebraicSpaces B S hS := ⟨_, isAlgebraicSpace_relocalize B (B.obj hT) (B.obj hS) g _
    (isAlgebraicSpace_relocalizeRestrict B T S hT hS g X hX)⟩
  let YTₐ : AlgebraicSpaces B S hS := ⟨_, isAlgebraicSpace_relocalize B (B.obj hT) (B.obj hS) g _
    (isAlgebraicSpace_relocalizeRestrict B T S hT hS g Y hY)⟩
  have hsq := isPullback_relocalize_relocalizeRestrict_map B S hS f hT g
  have hA : IsPullback
      (ObjectProperty.homMk (OverShriek.relocalizeRestrictCounit g X) : XTₐ ⟶ Xₐ)
      (ObjectProperty.homMk ((OverShriek.relocalizePresheafFunctor g).map
        ((OverShriek.relocalizeRestrict g).map f)) : XTₐ ⟶ YTₐ)
      (ObjectProperty.homMk f : Xₐ ⟶ Yₐ)
      (ObjectProperty.homMk (OverShriek.relocalizeRestrictCounit g Y) : YTₐ ⟶ Yₐ) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hsq.w) hsq
  intro y
  obtain ⟨x', hx'⟩ :=
    isSurjective_of_isPullback B S hS hA hf (relocalizedPointsMap B T S hT hS g _ y)
  obtain ⟨x, rfl⟩ := relocalizedPointsMap_surjective B T S hT hS g _ x'
  refine ⟨x, relocalizedPointsMap_injective B T S hT hS g _ ?_⟩
  rwa [relocalizedPointsMap_naturality]

end Restrict

/-! ### Models over a ring of finite type over `ℤ` -/

variable (B : BigFppfSite.{u}) {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}

include B in
/-- **A model of finite presentation over a ring of finite type over `ℤ`.** Let `X` be an
algebraic space of finite presentation over `Spec A`. Then there are a ring `A₀` of finite type
over `ℤ` with a map `A₀ → A`, and an algebraic space `X₀` of finite presentation over `Spec A₀`,
separated if `X` is separated over `Spec A` and flat if `X` is flat over `Spec A`, whose base
change along `Spec A ⟶ Spec A₀` is `X`. -/
theorem exists_finiteType_model_of_isFinitePresentation
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X) (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hfp : IsFinitePresentation B (Spec (.of A)) hA f) :
    ∃ (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra A₀ A) (_ : Algebra.FiniteType ℤ A₀)
      (hA₀ : B.Contains (Spec (.of A₀))) (X₀ : (BigFppfOver B (Spec (.of A₀)) hA₀)ᵒᵖ ⥤ Type u)
      (_ : IsAlgebraicSpace B (Spec (.of A₀)) hA₀ X₀)
      (f₀ : X₀ ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA₀)))),
      IsFinitePresentation B (Spec (.of A₀)) hA₀ f₀ ∧
      (IsSeparated B (Spec (.of A)) hA f → IsSeparated B (Spec (.of A₀)) hA₀ f₀) ∧
      (IsFlat B (Spec (.of A)) hA f → IsFlat B (Spec (.of A₀)) hA₀ f₀) ∧
      ∀ (g : B.obj hA ⟶ B.obj hA₀),
        B.inclusion.map g = Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) →
        Nonempty (X ≅ (OverShriek.relocalizeRestrict g).obj X₀) := by
  obtain ⟨i, X₀, hX₀, f₀, h₁, h₂, h₃, h₄⟩ := exists_stageModel B hX f hfp
  exact ⟨Algebra.adjoin ℤ (i.unop : Set A), inferInstance, inferInstance,
    finiteType_adjoinFinset_int A i.unop, contains_specAdjoinFinsetDiagram_obj B i, X₀, hX₀, f₀,
    h₁, h₂, h₃, h₄⟩

include B in
/-- **A model of finite presentation over a ring of finite type over `ℤ`, with a model of a
given atlas.** Let `X` be an algebraic space of finite presentation over `Spec A` and
`p : W ⟶ X` a surjective étale atlas with `W` affine. Then there are a ring `A₀` of finite type
over `ℤ` with a map `A₀ → A`, an algebraic space `X₀` of finite presentation over `Spec A₀`,
separated if `X` is separated over `Spec A`, and a surjective étale atlas `q : W₀ ⟶ X₀` with
`W₀` affine, whose base change along `Spec A ⟶ Spec A₀` is `p : W ⟶ X`. -/
theorem exists_finiteType_model_of_atlas
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X) (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hfp : IsFinitePresentation B (Spec (.of A)) hA f) {W : BigFppfOver B (Spec (.of A)) hA}
    (p : yoneda.obj W ⟶ X) (hW : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj W))
    (hps : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf p)
    (hpe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf p) :
    ∃ (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra A₀ A) (_ : Algebra.FiniteType ℤ A₀)
      (hA₀ : B.Contains (Spec (.of A₀))) (X₀ : (BigFppfOver B (Spec (.of A₀)) hA₀)ᵒᵖ ⥤ Type u)
      (_ : IsAlgebraicSpace B (Spec (.of A₀)) hA₀ X₀)
      (f₀ : X₀ ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA₀)))),
      IsFinitePresentation B (Spec (.of A₀)) hA₀ f₀ ∧
      (IsSeparated B (Spec (.of A)) hA f → IsSeparated B (Spec (.of A₀)) hA₀ f₀) ∧
      ∃ (W₀ : BigFppfOver B (Spec (.of A₀)) hA₀) (q : yoneda.obj W₀ ⟶ X₀),
        IsAffine ((BigFppfOver.toScheme B (Spec (.of A₀)) hA₀).obj W₀) ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B (Spec (.of A₀)) hA₀)).presheaf q ∧
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B (Spec (.of A₀)) hA₀)).presheaf q ∧
        ∀ (g : B.obj hA ⟶ B.obj hA₀),
          B.inclusion.map g = Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) →
          ∃ (e : X ≅ (OverShriek.relocalizeRestrict g).obj X₀) (φ : (Over.pullback g).obj W₀ ≅ W),
            p ≫ e.hom = yoneda.map φ.inv ≫ (OverShriek.restrictYonedaIso g W₀).hom ≫
              (OverShriek.relocalizeRestrict g).map q := by
  obtain ⟨i, X₀, hX₀, f₀, h₁, h₂, -, W₀, q, hW₀, hqs, hqe, h₄⟩ :=
    exists_stageModel_of_atlas B hX f hfp p hW hps hpe
  exact ⟨Algebra.adjoin ℤ (i.unop : Set A), inferInstance, inferInstance,
    finiteType_adjoinFinset_int A i.unop, contains_specAdjoinFinsetDiagram_obj B i, X₀, hX₀, f₀,
    h₁, h₂, W₀, q, hW₀, hqs, hqe, h₄⟩

include B in
/-- **Noetherian approximation of a proper, flat, finitely presented algebraic space.** Let `X`
be an algebraic space over `Spec A` whose structure morphism is proper, flat and of finite
presentation. Then there are a ring `A₀` of finite type over `ℤ` with a map `A₀ → A`, and an
algebraic space `X₀` over `Spec A₀` whose structure morphism is proper, flat and of finite
presentation, whose base change along `Spec A ⟶ Spec A₀` is `X`. -/
theorem exists_finiteType_model_of_isProper
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X) (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hprop : IsProper B (Spec (.of A)) hA f) (hflat : IsFlat B (Spec (.of A)) hA f)
    (hfp : IsFinitePresentation B (Spec (.of A)) hA f) :
    ∃ (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra A₀ A) (_ : Algebra.FiniteType ℤ A₀)
      (hA₀ : B.Contains (Spec (.of A₀))) (X₀ : (BigFppfOver B (Spec (.of A₀)) hA₀)ᵒᵖ ⥤ Type u)
      (_ : IsAlgebraicSpace B (Spec (.of A₀)) hA₀ X₀)
      (f₀ : X₀ ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA₀)))),
      IsProper B (Spec (.of A₀)) hA₀ f₀ ∧ IsFlat B (Spec (.of A₀)) hA₀ f₀ ∧
      IsFinitePresentation B (Spec (.of A₀)) hA₀ f₀ ∧
      ∀ (g : B.obj hA ⟶ B.obj hA₀),
        B.inclusion.map g = Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) →
        Nonempty (X ≅ (OverShriek.relocalizeRestrict g).obj X₀) := by
  classical
  obtain ⟨i, X₀, hX₀, f₀, hfp₀, hsep₀, hflat₀, hiso⟩ := exists_stageModel B hX f hfp
  have hsep0 := hsep₀ hprop.1
  let D := specAdjoinFinsetDiagram A
  let c := specAdjoinFinsetCone A
  have h₀ := contains_specAdjoinFinsetDiagram_obj B i
  have hYo₀ := isAlgebraicSpace_yoneda B (D.obj i) h₀ (Over.mk (𝟙 (B.obj h₀)))
  -- Chow's lemma over the stage
  obtain ⟨X', π, hπ, hπs, hX'⟩ := hasChowSchemeCover_of_isSeparated_isFiniteType B
    (CommRingCat.of (Algebra.adjoin ℤ (i.unop : Set A))) h₀ X₀ hX₀ f₀ hsep0
    (isFiniteType_of_isFinitePresentation B _ h₀ hfp₀)
  have hX'a := isAlgebraicSpace_yoneda B (D.obj i) h₀ X'
  let Z : Over (D.obj i) := (Over.post (X := B.obj h₀) B.inclusion).obj X'
  have : LocallyOfFiniteType Z.hom := IsHQuasiProjective.locallyOfFiniteType hX'
  have : QuasiCompact Z.hom := IsHQuasiProjective.quasiCompact hX'
  have : _root_.AlgebraicGeometry.IsSeparated Z.hom := IsHQuasiProjective.isSeparated hX'
  have hZfp : FinitePresentation Z.hom := ⟨inferInstance, inferInstance, inferInstance⟩
  have : MorphismProperty.RespectsIso (@_root_.AlgebraicGeometry.IsProper.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  -- over a base `S` mapping to the stage, the base change of the Chow cover is proper iff its
  -- composite with any map to the base is, as a morphism of spaces
  have hiff : ∀ {S : Scheme.{u}} (hS : B.Contains S) (g : B.obj hS ⟶ B.obj h₀)
      (u : (OverShriek.relocalizeRestrict g).obj X₀ ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS)))),
      IsProper B S hS ((OverShriek.relocalizeRestrict g).map π ≫ u) ↔
        _root_.AlgebraicGeometry.IsProper ((Over.pullback (B.inclusion.map g)).obj Z).hom := by
    intro S hS g u
    let ι := (Over.postPullbackIso B.inclusion g).app X'
    rw [(isTerminal_yoneda_obj_base B _ hS).hom_ext ((OverShriek.relocalizeRestrict g).map π ≫ u)
      ((OverShriek.restrictYonedaIso g X').inv ≫ yoneda.map (Over.homMk _ (Category.comp_id _) :
        (Over.pullback g).obj X' ⟶ Over.mk (𝟙 (B.obj hS))))]
    refine (@isProper_isIso_comp_iff B _ hS _ _ _ (OverShriek.restrictYonedaIso g X').inv
      (Iso.isIso_inv _) _).trans ⟨fun h => prop_of_overIso @_root_.AlgebraicGeometry.IsProper ι
      (isProper_of_isProper_yoneda_map B _ h), fun h => isProper_yoneda_map B _ hS _
        (prop_of_overIso @_root_.AlgebraicGeometry.IsProper ι.symm h)⟩
  -- the base change of the Chow cover to `Spec A` is proper
  let g : B.obj hA ⟶ B.obj h₀ := ObjectProperty.homMk (c.π.app i)
  obtain ⟨e⟩ := hiso g rfl
  have hZA : _root_.AlgebraicGeometry.IsProper ((Over.pullback (c.π.app i)).obj Z).hom := by
    have hXg := isAlgebraicSpace_relocalizeRestrict B _ _ hA h₀ g X₀ hX₀
    have hYg := isAlgebraicSpace_relocalizeRestrict B _ _ hA h₀ g _ hX'a
    have hb := isAlgebraicSpace_yoneda B (Spec (.of A)) hA (Over.mk (𝟙 (B.obj hA)))
    have hπg : IsProper B _ hA ((OverShriek.relocalizeRestrict g).map π) :=
      isProper_relocalizeRestrict_map B (D.obj i) h₀ π hA g hX'a hX₀ hπ
    have hef : IsProper B _ hA (e.inv ≫ f) := (isProper_isIso_comp_iff B _ hA e.inv f).2 hprop
    exact (hiff hA g (e.inv ≫ f)).1 (isProper_comp B _ hA hYg hXg hb _ _ hπg hef)
  -- Stacks 081F: the Chow cover is proper over a later stage
  obtain ⟨j, a, hZj⟩ :=
    exists_isProper_overPullbackObj_of_isLimit D c (isLimit_specAdjoinFinsetCone A) i Z hZfp
  have h₁ := contains_specAdjoinFinsetDiagram_obj B j
  let h : B.obj h₁ ⟶ B.obj h₀ := ObjectProperty.homMk (D.map a)
  let Xj := (OverShriek.relocalizeRestrict h).obj X₀
  have hXj := isAlgebraicSpace_relocalizeRestrict B _ _ h₁ h₀ h X₀ hX₀
  have hYj := isAlgebraicSpace_relocalizeRestrict B _ _ h₁ h₀ h _ hX'a
  have hbj := isAlgebraicSpace_yoneda B (D.obj j) h₁ (Over.mk (𝟙 (B.obj h₁)))
  let τ : (OverShriek.relocalizeRestrict h).obj (yoneda.obj (Over.mk (𝟙 (B.obj h₀)))) ≅
      yoneda.obj (Over.mk (𝟙 (B.obj h₁))) :=
    ((baseYoneda_isTerminal B _ h₀).isTerminalObj (OverShriek.relocalizeRestrict h) _).uniqueUpToIso
      (isTerminal_yoneda_obj_base B _ h₁)
  let fj : Xj ⟶ yoneda.obj (Over.mk (𝟙 (B.obj h₁))) :=
    (OverShriek.relocalizeRestrict h).map f₀ ≫ τ.hom
  have hfpj : IsFinitePresentation B _ h₁ fj :=
    isFinitePresentation_of_arrowIso B _ h₁ ((OverShriek.relocalizeRestrict h).map f₀) fj (𝟙 _)
      τ.hom (by simp [fj])
      (isFinitePresentation_relocalizeRestrict_map B _ h₀ f₀ h₁ h hX₀ hYo₀ hfp₀)
  have hflatj : IsFlat B _ h₁ fj :=
    (holdsOnEveryEtaleChart_comp_iso_iff B _ h₁ _ _ τ.hom).2
      (isFlat_relocalizeRestrict_map B _ h₀ f₀ h₁ h hX₀ hYo₀ (hflat₀ hflat))
  -- Stacks 08AJ: `Xj` is universally closed over the stage
  have hucj : UniversallyClosed B _ h₁ fj := by
    refine universallyClosed_of_isSurjective_comp B _ h₁ hYj hXj hbj
      ((OverShriek.relocalizeRestrict h).map π) fj ?_
      (isSurjective_relocalizeRestrict_map B _ h₀ π h₁ h hX'a hX₀ hπs)
    exact ((hiff h₁ h fj).2 hZj).2.2
  have hpropj : IsProper B _ h₁ fj :=
    ⟨isSeparated_comp B _ h₁ _ _ (isSeparated_relocalizeRestrict_map B _ _ h₁ h₀ h f₀ hsep0)
      (isSeparated_of_isIso B _ h₁ τ.hom), isFiniteType_of_isFinitePresentation B _ h₁ hfpj, hucj⟩
  -- the base change of `Xj` to `Spec A` is `X`
  let gj : B.obj hA ⟶ B.obj h₁ := ObjectProperty.homMk (c.π.app j)
  obtain ⟨e'⟩ := hiso (gj ≫ h) ((B.inclusion.map_comp gj h).trans (c.w a))
  refine ⟨Algebra.adjoin ℤ (j.unop : Set A), inferInstance, inferInstance,
    finiteType_adjoinFinset_int A j.unop, h₁, Xj, hXj, fj, hpropj, hflatj, hfpj,
    fun g' hg' => ?_⟩
  obtain rfl : g' = gj := ObjectProperty.hom_ext _ hg'
  exact ⟨e' ≪≫ (OverShriek.relocalizeRestrictComp gj h X₀).symm⟩

end AlgebraicGeometry.Space
