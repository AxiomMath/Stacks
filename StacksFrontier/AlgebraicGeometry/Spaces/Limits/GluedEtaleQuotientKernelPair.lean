module

public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquarePushout
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GluedEtaleQuotient

/-!
# The kernel pair of the étale map of an elementary distinguished square, as a glued relation

For an elementary distinguished square of algebraic spaces with étale map `f : V ⟶ X`, and an
open immersion `W ⟶ V` presenting the part of `V` over the open subspace `U`, the kernel pair
`V ×_X V` is the glued étale relation of `AlgebraicGeometry.Space.GluedEtaleQuotient`. This is the
claim in the proof of Stacks, Tag 07SU.

## Main results

* `AlgebraicGeometry.Space.GluedEtaleQuotient.isPullback_of_isElementaryDistinguishedSquare`: the
  glued relation, with its two maps to `V`, is the kernel pair `V ×_X V` of `f`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### The kernel pair of the étale map, as a glued relation -/

namespace AlgebraicGeometry.Space.GluedEtaleQuotient

/-- Every point of `V ×_X V` lies either on the relative diagonal of `f` or on the part of
`V ×_X V` lying over the open subspace `U`. -/
theorem kernelPair_points_mem_range_diagonal_or_open
    (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))
    {X V : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X) (U : Subfunctor X) (f : V ⟶ X)
    (h : IsElementaryDistinguishedSquare B (⊤_ Scheme.{u}) hZ hX U f)
    (x : points B (⊤_ Scheme.{u}) hZ (pullback f f)) :
    x ∈ Set.range (pointsMap B (⊤_ Scheme.{u}) hZ V (pullback.diagonal f)) ∨
      x ∈ Set.range (pointsMap B (⊤_ Scheme.{u}) hZ (pullback U.ι (pullback.fst f f ≫ f))
        (pullback.snd U.ι (pullback.fst f f ≫ f))) := by
  classical
  set q : pullback f f ⟶ X := pullback.fst f f ≫ f with hq
  by_cases hy : pointsMap B (⊤_ Scheme.{u}) hZ (pullback f f) q x ∈
      Set.range (pointsMap B (⊤_ Scheme.{u}) hZ U.toFunctor U.ι)
  · obtain ⟨z, hz⟩ := hy
    obtain ⟨t, -, ht⟩ :=
      exists_points_of_isPullback B (⊤_ Scheme.{u}) hZ (IsPullback.of_hasPullback U.ι q) z x hz
    exact Or.inr ⟨t, ht⟩
  · obtain ⟨D, hD, hrange⟩ :
        ∃ (D : Subfunctor X), IsIso (D.fromPreimage f) ∧
          Set.range (pointsMap B (⊤_ Scheme.{u}) hZ D.toFunctor D.ι) =
            (Set.range (pointsMap B (⊤_ Scheme.{u}) hZ U.toFunctor U.ι))ᶜ :=
      ⟨_, h.isIsoOverComplement,
        range_pointsMap_ι_reducedClosedSubspace B (⊤_ Scheme.{u}) hZ X hX _ h.isClosedComplement⟩
    obtain ⟨d, hd⟩ : pointsMap B (⊤_ Scheme.{u}) hZ (pullback f f) q x ∈
        Set.range (pointsMap B (⊤_ Scheme.{u}) hZ D.toFunctor D.ι) := by
      rwa [hrange]
    obtain ⟨t, -, ht⟩ :=
      exists_points_of_isPullback B (⊤_ Scheme.{u}) hZ (IsPullback.of_hasPullback D.ι q) d x hd
    set sD : pullback D.ι q ⟶ D.toFunctor := pullback.fst D.ι q with hsD
    set sR : pullback D.ι q ⟶ pullback f f := pullback.snd D.ι q with hsR
    set a₁ : pullback D.ι q ⟶ V := sR ≫ pullback.fst f f with ha₁
    set a₂ : pullback D.ι q ⟶ V := sR ≫ pullback.snd f f with ha₂
    have h₁ : sD ≫ D.ι = a₁ ≫ f := by
      rw [ha₁, hsD, hsR, Category.assoc, ← hq]
      exact pullback.condition
    have h₂ : sD ≫ D.ι = a₂ ≫ f := by
      rw [ha₂, hsD, hsR, Category.assoc, ← pullback.condition, ← hq]
      exact pullback.condition
    have hE : IsPullback (D.fromPreimage f) (D.preimage f).ι D.ι f :=
      Subfunctor.isPullback_preimage f D
    have : IsIso (D.fromPreimage f) := hD
    have hl : hE.lift sD a₁ h₁ = hE.lift sD a₂ h₂ := by
      refine (cancel_mono (D.fromPreimage f)).1 ?_
      rw [hE.lift_fst, hE.lift_fst]
    have ha : a₁ = a₂ := by rw [← hE.lift_snd sD a₁ h₁, hl, hE.lift_snd]
    have hdiag : sR = a₁ ≫ pullback.diagonal f := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, ha₁]
      · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, ha, ha₂]
    refine Or.inl ⟨pointsMap B (⊤_ Scheme.{u}) hZ (pullback D.ι q) a₁ t, ?_⟩
    rwa [← pointsMap_comp_apply, ← hdiag]

/-- The relative diagonal of `f` and the part of `V ×_X V` lying over the open subspace form
an étale covering of `V ×_X V`. -/
theorem isEtaleCovering_kernelPair
    (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))
    {X V : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X) (U : Subfunctor X) (f : V ⟶ X)
    (h : IsElementaryDistinguishedSquare B (⊤_ Scheme.{u}) hZ hX U f) :
    IsEtaleCovering B (⊤_ Scheme.{u}) hZ
      (fun | false => V | true => pullback U.ι (pullback.fst f f ≫ f))
      (fun | false => pullback.diagonal f
           | true => pullback.snd U.ι (pullback.fst f f ≫ f)) := by
  classical
  let W' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ := ⟨X, hX⟩
  let V' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ := ⟨V, h.isAlgebraicSpace⟩
  let U' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ := ⟨U.toFunctor, h.isOpenSubspace.1⟩
  let v' : V' ⟶ W' := ObjectProperty.homMk f
  let i' : U' ⟶ W' := ObjectProperty.homMk U.ι
  let R' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ :=
    AlgebraicSpaces.fiberProduct B (⊤_ Scheme.{u}) hZ v' v'
  let r₁ : R' ⟶ V' := ObjectProperty.homMk (pullback.fst f f)
  let T' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ :=
    AlgebraicSpaces.fiberProduct B (⊤_ Scheme.{u}) hZ i' (r₁ ≫ v')
  have hsq : IsPullback
      (ObjectProperty.homMk (pullback.fst U.ι (pullback.fst f f ≫ f)) : T' ⟶ U')
      (ObjectProperty.homMk (pullback.snd U.ι (pullback.fst f f ≫ f)) : T' ⟶ R')
      i' (r₁ ≫ v') :=
    AlgebraicSpaces.isPullback_fiberProduct B (⊤_ Scheme.{u}) hZ i' (r₁ ≫ v')
  refine ⟨isAlgebraicSpace_pullback B (⊤_ Scheme.{u}) hZ f f h.isAlgebraicSpace
      h.isAlgebraicSpace hX,
    ?_, ?_, ?_⟩
  · intro i
    cases i
    · exact h.isAlgebraicSpace
    · exact T'.property
  · intro i
    cases i
    · exact isEtale_of_presheaf_etale B (⊤_ Scheme.{u}) hZ
        (presheaf_etale_of_isOpenImmersion B (⊤_ Scheme.{u}) hZ
        (isOpenImmersion_diagonal_of_isUnramified B (⊤_ Scheme.{u}) hZ h.isAlgebraicSpace hX f
          (isUnramified_of_isEtale B (⊤_ Scheme.{u}) hZ h.isEtale)))
    · exact isEtale_of_presheaf_etale B (⊤_ Scheme.{u}) hZ
        (presheaf_etale_of_isOpenImmersion B (⊤_ Scheme.{u}) hZ
        (isOpenImmersion_of_isPullback B (⊤_ Scheme.{u}) hZ hsq h.isOpenSubspace.2))
  · refine Set.eq_univ_iff_forall.mpr fun x => ?_
    obtain hx | hx := kernelPair_points_mem_range_diagonal_or_open B hZ hX U f h x
    · exact Set.mem_iUnion.mpr ⟨false, hx⟩
    · exact Set.mem_iUnion.mpr ⟨true, hx⟩

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
  {U : Subfunctor X} {W V : BigFppfOver B (⊤_ Scheme.{u}) hZ} (f : yoneda.obj V ⟶ X)
  (h : IsElementaryDistinguishedSquare B (⊤_ Scheme.{u}) hZ hX U f)
  (w : yoneda.obj W ⟶ U.toFunctor)
  (hw : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf w)
  (ι : W ⟶ V) [AlgebraicGeometry.IsOpenImmersion
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ι)]
  (hWV : IsPullback w (yoneda.map ι) U.ι f)


include hWV hX in
/-- The two maps of the glued relation have the same composite with `f`. -/
theorem tgt_f : yoneda.map (tgt w hw ι) ≫ f = yoneda.map (src w hw ι) ≫ f := by
  refine relation_yoneda_hom_ext w hw ι hX.isSheaf ?_ ?_
  · rw [← Category.assoc, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, inlV_tgt, inlV_src]
  · rw [← Category.assoc, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, inrQ_tgt, inrQ_src, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc, ← hWV.w,
      ← Category.assoc, ← Category.assoc, (isPullback_kernel w hw).w]

/-! ### The kernel pair -/

section KernelPair

variable {hX f}

/-- The piece of `V ×_X V` lying over `U`. -/
local notation "PU" => pullback U.ι (pullback.fst f f ≫ f)

/-- The first point of `V ×_X V` over `U`, lifted to `W`. -/
noncomputable abbrev liftFst : PU ⟶ yoneda.obj W :=
  hWV.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst f f)
    (pullback.condition.trans (Category.assoc _ _ _).symm)

/-- The second point of `V ×_X V` over `U`, lifted to `W`. -/
noncomputable abbrev liftSnd : PU ⟶ yoneda.obj W :=
  hWV.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd f f)
    ((pullback.condition.trans (congrArg (pullback.snd U.ι (pullback.fst f f ≫ f) ≫ ·)
      pullback.condition)).trans (Category.assoc _ _ _).symm)

/-- The part of `V ×_X V` over `U` maps to `Q = W ×_U W`. -/
noncomputable abbrev liftQ : PU ⟶ yoneda.obj (kernelObj w hw) :=
  (isPullback_kernel w hw).lift (liftSnd w ι hWV) (liftFst w ι hWV)
    (by rw [hWV.lift_fst, hWV.lift_fst])

/-- Composing the map from the part of `V ×_X V` over `U` to the glued relation with the first
map of the relation gives the first projection of `V ×_X V`. -/
theorem liftQ_tgt : (liftQ w hw ι hWV ≫ yoneda.map (inrQ w hw ι)) ≫ yoneda.map (tgt w hw ι) =
    pullback.snd _ _ ≫ pullback.fst f f := by
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, inrQ_tgt,
    CategoryTheory.Functor.map_comp, ← Category.assoc, (isPullback_kernel w hw).lift_snd,
    hWV.lift_snd]

/-- Composing the map from the part of `V ×_X V` over `U` to the glued relation with the second
map of the relation gives the second projection of `V ×_X V`. -/
theorem liftQ_src : (liftQ w hw ι hWV ≫ yoneda.map (inrQ w hw ι)) ≫ yoneda.map (src w hw ι) =
    pullback.snd _ _ ≫ pullback.snd f f := by
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, inrQ_src,
    CategoryTheory.Functor.map_comp, ← Category.assoc, (isPullback_kernel w hw).lift_fst,
    hWV.lift_snd]

end KernelPair

include h hWV in
/-- **The glued relation is the kernel pair `V ×_X V`** of the étale morphism of an elementary
distinguished square. -/
theorem isPullback_of_isElementaryDistinguishedSquare :
    IsPullback (yoneda.map (tgt w hw ι)) (yoneda.map (src w hw ι)) f f := by
  classical
  let k₁ := pullback.fst f f
  let k₂ := pullback.snd f f
  let c : yoneda.obj (relationObj w hw ι) ⟶ pullback f f :=
    pullback.lift (yoneda.map (tgt w hw ι)) (yoneda.map (src w hw ι)) (tgt_f hX f w hw ι hWV)
  have hc₁ : c ≫ k₁ = yoneda.map (tgt w hw ι) := pullback.lift_fst _ _ _
  have hc₂ : c ≫ k₂ = yoneda.map (src w hw ι) := pullback.lift_snd _ _ _
  let Xc : Bool → (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u :=
    fun | false => yoneda.obj V | true => pullback U.ι (pullback.fst f f ≫ f)
  let cov : ∀ b, Xc b ⟶ pullback f f :=
    fun | false => pullback.diagonal f | true => pullback.snd U.ι (pullback.fst f f ≫ f)
  have hcov : IsFppfCovering B (⊤_ Scheme.{u}) hZ Xc cov :=
    isFppfCovering_of_isEtaleCovering B (⊤_ Scheme.{u}) hZ
      (isEtaleCovering_kernelPair B hZ hX U f h)
  let g : ∀ b : Bool, Xc b ⟶ yoneda.obj (relationObj w hw ι) :=
    fun | false => yoneda.map (inlV w hw ι) | true => liftQ w hw ι hWV ≫ yoneda.map (inrQ w hw ι)
  have hg₁ : ∀ b : Bool, g b ≫ yoneda.map (tgt w hw ι) = cov b ≫ k₁ := by
    intro b
    cases b
    · show yoneda.map (inlV w hw ι) ≫ yoneda.map (tgt w hw ι) = pullback.diagonal f ≫ k₁
      rw [← CategoryTheory.Functor.map_comp, inlV_tgt, CategoryTheory.Functor.map_id,
        pullback.diagonal_fst]
    · exact liftQ_tgt w hw ι hWV
  have hg₂ : ∀ b : Bool, g b ≫ yoneda.map (src w hw ι) = cov b ≫ k₂ := by
    intro b
    cases b
    · show yoneda.map (inlV w hw ι) ≫ yoneda.map (src w hw ι) = pullback.diagonal f ≫ k₂
      rw [← CategoryTheory.Functor.map_comp, inlV_src, CategoryTheory.Functor.map_id,
        pullback.diagonal_snd]
    · exact liftQ_src w hw ι hWV
  obtain ⟨ψ, hψ, -⟩ := existsUnique_desc_of_isFppfCovering B (⊤_ Scheme.{u}) hZ _ _ hcov
    (isSheaf_iff_isSheaf_of_type _ _ |>.mpr ((isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ
      (relationObj w hw ι)).isSheaf |> (isSheaf_iff_isSheaf_of_type _ _).mp)) g (by
      intro i j
      refine relation_yoneda_jointlyMono w hw ι _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, hg₂, hg₂, ← Category.assoc, ← Category.assoc,
          pullback.condition]
      · rw [Category.assoc, Category.assoc, hg₁, hg₁, ← Category.assoc, ← Category.assoc,
          pullback.condition])
  have hsheafK : Presheaf.IsSheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) (pullback f f) :=
    (isAlgebraicSpace_pullback B (⊤_ Scheme.{u}) hZ f f h.isAlgebraicSpace h.isAlgebraicSpace
      hX).isSheaf
  have hψc : ψ ≫ c = 𝟙 _ := by
    refine hom_ext_of_isFppfCovering B (⊤_ Scheme.{u}) hZ _ _ hcov hsheafK fun b => ?_
    rw [← Category.assoc, hψ b, Category.comp_id]
    apply pullback.hom_ext
    · rw [Category.assoc, hc₁, hg₁]
    · rw [Category.assoc, hc₂, hg₂]
  have hψ₁ : ψ ≫ yoneda.map (tgt w hw ι) = k₁ := by
    rw [← hc₁, ← Category.assoc, hψc, Category.id_comp]
  have hψ₂ : ψ ≫ yoneda.map (src w hw ι) = k₂ := by
    rw [← hc₂, ← Category.assoc, hψc, Category.id_comp]
  have hcψ : c ≫ ψ = 𝟙 _ := by
    refine relation_yoneda_jointlyMono w hw ι _ _ ?_ ?_
    · rw [Category.assoc, hψ₂, hc₂, Category.id_comp]
    · rw [Category.assoc, hψ₁, hc₁, Category.id_comp]
  exact IsPullback.of_iso_pullback ⟨tgt_f hX f w hw ι hWV⟩ ⟨c, ψ, hcψ, hψc⟩ hc₁ hc₂

end AlgebraicGeometry.Space.GluedEtaleQuotient

end
