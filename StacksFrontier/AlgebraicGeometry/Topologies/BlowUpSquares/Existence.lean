module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemma
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Blowup

/-!
# Existence of almost blowup squares

Every closed subscheme of finite type in a quasi-compact and quasi-separated scheme is the centre
of an almost blowup square. Over a locally Noetherian base the honest blowup already is such a
square, so the content of the statement is the reduction to the Noetherian case.

That reduction is absolute Noetherian approximation. A quasi-compact and quasi-separated scheme
`X` is the limit of a directed inverse system of schemes of finite type over `ℤ` with affine
transition morphisms, and such schemes are Noetherian. A closed subscheme of finite type in `X`
is a closed immersion of finite presentation, hence is the base change of a morphism over one of
the stages; one stage further along that morphism is itself a closed immersion. Its kernel is a
quasi-coherent ideal sheaf on a Noetherian scheme, so it is automatically finitely generated and
the blowup of that stage in it is an almost blowup square. Base changing that square back to `X`
gives an almost blowup square whose centre is the inverse image of the stagewise centre, and that
inverse image is the subscheme one started with.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.eq_of_subschemeIso`: two quasi-coherent ideal sheaves
  whose closed subschemes are isomorphic over the ambient scheme are equal.
* `AlgebraicGeometry.exists_isAlmostBlowUpSquare`: a closed subscheme of finite type in a
  quasi-compact and quasi-separated scheme is the centre of an almost blowup square.

## References

* [Stacks Project, Tag 0EVA](https://stacks.math.columbia.edu/tag/0EVA)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZP](https://stacks.math.columbia.edu/tag/01ZP)
* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Quasi-coherent ideal sheaf data is determined by the closed subscheme it cuts out: if the two
closed subschemes are isomorphic by an isomorphism commuting with the two closed immersions, the
ideal sheaves agree. -/
@[ega "II 8.13.4" "injectivity of J ↦ Z"]
public theorem Scheme.IdealSheafData.eq_of_subschemeIso {X : Scheme.{u}}
    (I J : X.IdealSheafData) (e : I.subscheme ≅ J.subscheme)
    (h : e.hom ≫ J.subschemeι = I.subschemeι) : I = J := by
  rw [← I.ker_subschemeι, ← J.ker_subschemeι, ← h]
  exact Scheme.Hom.ker_comp_of_isIso e.hom J.subschemeι

/-- **Stacks Project, Tag 0EVA.** Let `X` be a quasi-compact and quasi-separated scheme and let
`I` be a quasi-coherent ideal sheaf of finite type on `X`, cutting out a closed subscheme `Z`.
Then there is an almost blowup square with centre `Z`, that is, a modification `b : X' ⟶ X`
making `(I.comap b, X', Z, X)` an almost blowup square. -/
@[stacks 0EVA]
public theorem exists_isAlmostBlowUpSquare (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (I : X.IdealSheafData)
    (hI : Scheme.IdealSheafData.IsFiniteType I) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X), IsAlmostBlowUpSquare I b := by
  -- Write `X` as the limit of a directed system of schemes of finite type over `ℤ`.
  let Q := LimitFPObjectDescent.finiteTypeSchemeApproximation X
  let : Preorder Q.indexType := Q.indexPreorder
  have : Nonempty Q.indexType := Q.indexNonempty
  have : IsDirected Q.indexType (· ≤ ·) := Q.indexDirected
  let D := Q.stages
  let c : Cone D := Cone.mk X Q.projection
  have : ∀ {i j : Q.indexTypeᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f) := Q.transition_affine
  have : ∀ i : Q.indexTypeᵒᵖ, LocallyOfFiniteType (terminal.from (D.obj i)) :=
    Q.stage_locallyOfFiniteType
  have : ∀ i : Q.indexTypeᵒᵖ, QuasiCompact (terminal.from (D.obj i)) := Q.stage_quasiCompact
  -- A scheme of finite type over `ℤ` is Noetherian.
  have hnoeth (i : Q.indexTypeᵒᵖ) : IsNoetherian (D.obj i) :=
    isNoetherian_of_locallyOfFiniteType_terminal_from (D.obj i)
  have : ∀ i : Q.indexTypeᵒᵖ, CompactSpace (D.obj i) := fun i => (hnoeth i).toCompactSpace
  have : ∀ i : Q.indexTypeᵒᵖ, QuasiSeparatedSpace (D.obj i) := fun i => inferInstance
  -- Descend the centre to a morphism of finite presentation over some stage.
  let ZOver : Over X := Over.mk I.subschemeι
  obtain ⟨i₀, Z₀, hfpZ₀, hmodel⟩ := LimitFPObjectDescent.exists_model_of_finitePresentation D c
    Q.limit ZOver ((Stacks.Flatness.finitePresentation_subschemeι_iff I).mpr hI)
  have : LocallyOfFinitePresentation Z₀.hom := hfpZ₀.locallyOfFinitePresentation
  have : QuasiCompact Z₀.hom := hfpZ₀.quasiCompact
  have : CompactSpace Z₀.left := QuasiCompact.compactSpace_of_compactSpace Z₀.hom
  have : IsLocallyNoetherian Z₀.left := LocallyOfFiniteType.isLocallyNoetherian Z₀.hom
  let X₀ : Over (D.obj i₀) := Over.mk (𝟙 (D.obj i₀))
  have : CompactSpace X₀.left := inferInstanceAs (CompactSpace (D.obj i₀))
  have : QuasiSeparatedSpace X₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj i₀))
  let f₀ : Z₀ ⟶ X₀ := Over.homMk Z₀.hom (by simp [X₀])
  let P₀ := Over.pullback (c.π.app i₀)
  let eZ₀ : ZOver ≅ P₀.obj Z₀ := hmodel.some
  let eZ₀left := (Over.forget X).mapIso eZ₀
  have hclosed_limit : IsClosedImmersion (P₀.obj Z₀).hom :=
    (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion eZ₀left.hom
      (P₀.obj Z₀).hom).mp (by
        rw [show eZ₀left.hom ≫ (P₀.obj Z₀).hom = I.subschemeι from Over.w eZ₀.hom]
        infer_instance)
  have : IsIso (P₀.obj X₀).hom :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (D.obj i₀)) (c.π.app i₀)))
  have hclosed_f₀base : IsClosedImmersion (P₀.map f₀).left :=
    (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion
      (P₀.map f₀).left (P₀.obj X₀).hom).mp (by rwa [Over.w (P₀.map f₀)])
  have : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType Z₀.hom)
  -- One stage further the descended morphism is already a closed immersion.
  obtain ⟨i₁, hi₁, hclosed_stage⟩ :=
    exists_isClosedImmersion_baseChange_of_isLimit D c Q.limit i₀ Z₀ X₀ f₀
  let transition := D.map hi₁
  let P₁ := Over.pullback transition
  let f₁over := P₁.map f₀
  let Y₁ := P₁.obj X₀
  have : IsClosedImmersion f₁over.left := hclosed_stage
  have : IsIso Y₁.hom := inferInstanceAs (IsIso (pullback.snd (𝟙 (D.obj i₀)) transition))
  have : IsClosedImmersion (pullback.snd Z₀.hom transition) := by
    rw [← show f₁over.left ≫ Y₁.hom = pullback.snd Z₀.hom transition from Over.w f₁over]
    infer_instance
  -- The centre over that stage, as a quasi-coherent ideal sheaf on a Noetherian scheme.
  let J₁ := (pullback.snd Z₀.hom transition).ker
  have hJ₁ : ∀ U : (D.obj i₁).affineOpens, (J₁.ideal U).FG := by
    intro U
    have : IsNoetherianRing Γ(D.obj i₁, U) :=
      (hnoeth i₁).toIsLocallyNoetherian.component_noetherian U
    exact (J₁.ideal U).fg_of_isNoetherianRing
  -- Identify the inverse image of that centre in `X` with the given centre.
  have eComp : P₀.obj Z₀ ≅ (Over.pullback (c.π.app i₁)).obj (P₁.obj Z₀) := by
    have hobj : (Over.pullback (c.π.app i₀)).obj Z₀ =
        (Over.pullback (c.π.app i₁ ≫ transition)).obj Z₀ := by
      rw [show c.π.app i₁ ≫ transition = c.π.app i₀ from c.w hi₁]
    exact eqToIso hobj ≪≫ (Over.pullbackComp (c.π.app i₁) transition).app Z₀
  let eZ₀limit : ZOver ≅ (Over.pullback (c.π.app i₁)).obj (P₁.obj Z₀) := eZ₀ ≪≫ eComp
  let eStageCenter : (P₁.obj Z₀).left ≅ J₁.subscheme :=
    asIso (pullback.snd Z₀.hom transition).toImage
  let eStageCenterOver : P₁.obj Z₀ ≅ Over.mk J₁.subschemeι :=
    Over.isoMk eStageCenter (by
      change eStageCenter.hom ≫
        (pullback.snd Z₀.hom transition).ker.subschemeι = _
      exact Scheme.Hom.toImage_imageι _)
  let eLimitCenter := eZ₀limit ≪≫ (Over.pullback (c.π.app i₁)).mapIso eStageCenterOver
  let eBaseCenter : (J₁.comap (c.π.app i₁)).subscheme ≅
      ((Over.pullback (c.π.app i₁)).obj (Over.mk J₁.subschemeι)).left :=
    J₁.comapIso (c.π.app i₁) ≪≫ pullbackSymmetry (c.π.app i₁) J₁.subschemeι
  have hbaseCenter : eBaseCenter.inv ≫ (J₁.comap (c.π.app i₁)).subschemeι =
      pullback.snd J₁.subschemeι (c.π.app i₁) := by
    have h : eBaseCenter.hom ≫ pullback.snd J₁.subschemeι (c.π.app i₁) =
        (J₁.comap (c.π.app i₁)).subschemeι := by
      simp only [eBaseCenter, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd,
        Scheme.IdealSheafData.comapIso_hom_fst]
    rw [← h, Iso.inv_hom_id_assoc]
  have hcenter_comap : J₁.comap (c.π.app i₁) = I := by
    have hcomm : ((Over.forget X).mapIso eLimitCenter ≪≫ eBaseCenter.symm).hom ≫
        (J₁.comap (c.π.app i₁)).subschemeι = I.subschemeι := by
      change eLimitCenter.hom.left ≫ eBaseCenter.inv ≫
        (J₁.comap (c.π.app i₁)).subschemeι = I.subschemeι
      rw [hbaseCenter]
      exact Over.w eLimitCenter.hom
    exact (Scheme.IdealSheafData.eq_of_subschemeIso I (J₁.comap (c.π.app i₁))
      ((Over.forget X).mapIso eLimitCenter ≪≫ eBaseCenter.symm) hcomm).symm
  -- Blow up the stage and base change the resulting almost blowup square to `X`.
  have : IsLocallyNoetherian (D.obj i₁) := (hnoeth i₁).toIsLocallyNoetherian
  refine ⟨pullback (c.π.app i₁) (blowUpToBase J₁),
    pullback.fst (c.π.app i₁) (blowUpToBase J₁), ?_⟩
  simpa [hcenter_comap] using
    isAlmostBlowUpSquare_baseChange J₁ (blowUpToBase J₁) (c.π.app i₁)
      (isAlmostBlowUpSquare_blowUpToBase_of_fg J₁ hJ₁)

end AlgebraicGeometry

end
