module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedLiftTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedOnComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable

/-!
# The geometry of an elementary distinguished square with affine étale member

Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a scheme
`S` with `V` affine and `U ×_X V` quasi-compact, and let `T ⊆ |X|` be closed with
quasi-compact open complement.  This file records the facts about this configuration used by
the step of the proof of Stacks 08HN:

* the inverse image in `|V|` of the complement of `T` is quasi-compact
  (`AlgebraicGeometry.Space.isCompact_preimage_range_of_isQuasiCompact`);
* `V ≅ h_{V₀}` for an affine `V₀`, and under it `U ×_X V ≅ h_O` for a quasi-compact open `O` of
  `V₀`, compatibly with the projection to `V` (`AlgebraicGeometry.Space.exists_eds_represented`);
* hence the supported lifting property of the projection `U ×_X V ⟶ V` at the inverse image of
  `T` (`AlgebraicGeometry.Space.supportedLiftProperty_edsSnd`), which is the use the source makes
  of Stacks 08EK and Stacks 08EH: "we will use the equivalence of Lemma 071Q for the
  representable algebraic spaces `V` and `U ×_X V`".

## References

* [Stacks Project, Tag 08HN](https://stacks.math.columbia.edu/tag/08HN)
* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
* [Stacks Project, Tag 03HF](https://stacks.math.columbia.edu/tag/03HF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **The inverse image of a quasi-compact open subspace along a map from a quasi-compact
algebraic space is quasi-compact**, read on points: it is the point set of the fibre product,
which is quasi-compact by the definition of a quasi-compact morphism, and its points form a
compact space by Stacks 03E4. -/
theorem isCompact_preimage_range_of_isQuasiCompact {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : IsQuasiCompactSpace B S hS Y) (f : Y ⟶ X) (G : Subfunctor X)
    (hG : IsOpenSubspace B S hS G) (hGqc : IsQuasiCompact B S hS G.ι) :
    IsCompact (pointsMap B S hS Y f ⁻¹' Set.range (pointsMap B S hS G.toFunctor G.ι)) := by
  have hq' : IsQuasiCompactSpace B S hS (G.preimage f).toFunctor :=
    isQuasiCompactSpace_of_iso B S hS (Subfunctor.isPullback_preimage f G).flip.isoPullback.symm
      (hGqc Y hY hYqc f)
  have := compactSpace_points_of_isQuasiCompactSpace B S hS
    (isOpenSubspace_preimage B S hS f G hX hY hG).1 hq'
  rw [← range_pointsMap_preimage_ι]
  exact isCompact_range (continuous_pointsMap B S hS _)

/-- The point set of the open subspace attached to an open set is that set. -/
private theorem range_openSubspacesOrderIso_symm_of_isOpen
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (W : Set (points B S hS F)) (hW : IsOpen W) :
    Set.range (pointsMap B S hS ((openSubspacesOrderIso B S hS F hF).symm ⟨W, hW⟩).1.toFunctor
      ((openSubspacesOrderIso B S hS F hF).symm ⟨W, hW⟩).1.ι) = W := by
  rw [← openSubspacesOrderIso_apply B S hS F hF, OrderIso.apply_symm_apply]

/-- The point set of the open subspace attached to the complement of a closed set is that
complement. -/
theorem range_openSubspacesOrderIso_symm (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (T : Set (points B S hS F)) (hT : IsClosed T) :
    Set.range (pointsMap B S hS
      ((openSubspacesOrderIso B S hS F hF).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.toFunctor
      ((openSubspacesOrderIso B S hS F hF).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι) = Tᶜ :=
  range_openSubspacesOrderIso_symm_of_isOpen B S hS F hF _ _

/-- The open subspace of `Y` cut out by the preimage of an open subset `W ⊆ |X|` along a morphism
`f : Y ⟶ X` of algebraic spaces is the preimage of the open subspace of `X` cut out by `W`. -/
theorem openSubspacesOrderIso_symm_preimage_of_hom {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : Y ⟶ X)
    (W : Set (points B S hS X)) (hW : IsOpen W) (hW' : IsOpen (pointsMap B S hS Y f ⁻¹' W)) :
    ((openSubspacesOrderIso B S hS Y hY).symm ⟨_, hW'⟩).1 =
      ((openSubspacesOrderIso B S hS X hX).symm ⟨W, hW⟩).1.preimage f := by
  set G := (openSubspacesOrderIso B S hS X hX).symm ⟨W, hW⟩
  have hGr := range_openSubspacesOrderIso_symm_of_isOpen B S hS X hX W hW
  have hG' : IsOpenSubspace B S hS (G.1.preimage f) :=
    isOpenSubspace_preimage B S hS f G.1 hX hY G.2
  have : (openSubspacesOrderIso B S hS Y hY).symm ⟨_, hW'⟩ = ⟨_, hG'⟩ := by
    apply (openSubspacesOrderIso B S hS Y hY).injective
    rw [OrderIso.apply_symm_apply]
    apply TopologicalSpace.Opens.ext
    change pointsMap B S hS Y f ⁻¹' W =
      Set.range (pointsMap B S hS (G.1.preimage f).toFunctor (G.1.preimage f).ι)
    rw [range_pointsMap_preimage_ι, hGr]
  rw [this]

/-- **The complement of the inverse image of a closed set with quasi-compact complement is again
an open subspace with quasi-compact inclusion** (Stacks 03HF, base change). -/
theorem isQuasiCompact_openSubspacesOrderIso_symm_preimage
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : Y ⟶ X)
    (T : Set (points B S hS X)) (hT : IsClosed T)
    (hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS X hX).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)
    (hT' : IsClosed (pointsMap B S hS Y f ⁻¹' T)) :
    IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS Y hY).symm ⟨(pointsMap B S hS Y f ⁻¹' T)ᶜ,
        hT'.isOpen_compl⟩).1.ι := by
  have heq := openSubspacesOrderIso_symm_preimage_of_hom B S hS hX hY f Tᶜ hT.isOpen_compl
    (by simpa only [Set.preimage_compl] using hT'.isOpen_compl)
  simp only [Set.preimage_compl] at heq
  rw [heq]
  exact isQuasiCompact_of_isPullback B S hS (Subfunctor.isPullback_preimage f _) hTqc

section Square

variable {W : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **The affine member of the square and its overlap are represented.**  If `V` is affine and
`U ×_X V` is quasi-compact, then `V ≅ h_{V₀}` for an affine `V₀`, and `U ×_X V ≅ h_O` for a
quasi-compact open `O` of `V₀`, compatibly with the projection `U ×_X V ⟶ V` and the inclusion of
`O`. -/
theorem exists_eds_represented (hVaff : IsAffineSpace B S hS Ve)
    (hUVqc : IsQuasiCompactSpace B S hS (edsInter B S hS hsq).1) :
    ∃ (V₀ : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀))
      (O : ((BigFppfOver.toScheme B S hS).obj V₀).Opens)
      (_ : IsCompact (O : Set ((BigFppfOver.toScheme B S hS).obj V₀)))
      (eV : edsEtale B S hS hsq ≅ ⟨yoneda.obj V₀, isAlgebraicSpace_yoneda B S hS V₀⟩)
      (eI : edsInter B S hS hsq ≅
        ⟨yoneda.obj (openObj B S hS V₀ O), isAlgebraicSpace_yoneda B S hS _⟩),
      eI.hom ≫ representedSpaceMap B S hS (openIncl B S hS V₀ O) = edsSnd B S hS hsq ≫ eV.hom := by
  obtain ⟨V₀, hV₀, ⟨e₀⟩⟩ := hVaff
  let eV : edsEtale B S hS hsq ≅ ⟨yoneda.obj V₀, isAlgebraicSpace_yoneda B S hS V₀⟩ :=
    ObjectProperty.isoMk _ e₀
  let G := Uo.preimage (e₀.inv ≫ fV)
  have hG : IsOpenSubspace B S hS G := isOpenSubspace_preimage B S hS (e₀.inv ≫ fV) Uo W.2
    (isAlgebraicSpace_yoneda B S hS V₀) hsq.isOpenSubspace
  obtain ⟨V', j, e, hj, he⟩ := exists_openImmersion_of_isOpenSubspace B S hS V₀ G hG
  let O := ((BigFppfOver.toScheme B S hS).map j).opensRange
  let isoS := ((BigFppfOver.toScheme B S hS).map j).isoOpensRange
  have hS₁ : isoS.hom ≫ O.ι = (BigFppfOver.toScheme B S hS).map j :=
    Scheme.Hom.isoOpensRange_hom_ι _
  let isoB : (BigFppfOver.forget B S hS).obj V' ≅
      (BigFppfOver.forget B S hS).obj (openObj B S hS V₀ O) :=
    ObjectProperty.isoMk _ isoS
  let isoBig : V' ≅ openObj B S hS V₀ O := Over.isoMk isoB (by
    apply ObjectProperty.hom_ext
    change isoS.hom ≫ O.ι ≫ V₀.hom.hom = V'.hom.hom
    rw [← Category.assoc, hS₁]
    exact congrArg (fun φ => φ.hom) (Over.w j))
  have hisoBig : isoBig.hom ≫ openIncl B S hS V₀ O = j := by
    ext
    exact hS₁
  have hsqG := Subfunctor.isPullback_preimage (e₀.inv ≫ fV) Uo
  have hsqI : IsPullback (pullback.fst Uo.ι fV) (pullback.snd Uo.ι fV ≫ e₀.hom) Uo.ι
      (e₀.inv ≫ fV) :=
    IsPullback.of_iso (IsPullback.of_hasPullback Uo.ι fV) (Iso.refl _) (Iso.refl _) e₀
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  let isoP : pullback Uo.ι fV ≅ G.toFunctor := hsqI.isoIsPullback _ _ hsqG
  have hP : isoP.hom ≫ G.ι = pullback.snd Uo.ι fV ≫ e₀.hom := hsqI.isoIsPullback_hom_snd _ _ hsqG
  let eI : edsInter B S hS hsq ≅
      ⟨yoneda.obj (openObj B S hS V₀ O), isAlgebraicSpace_yoneda B S hS _⟩ :=
    ObjectProperty.isoMk _ (isoP ≪≫ e.symm ≪≫ yoneda.mapIso isoBig)
  have := compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
    (isQuasiCompactSpace_of_iso B S hS (isoP ≪≫ e.symm) hUVqc)
  refine ⟨V₀, hV₀, O, ?_, eV, eI, ?_⟩
  · change IsCompact (Set.range ((BigFppfOver.toScheme B S hS).map j).base)
    exact isCompact_range ((BigFppfOver.toScheme B S hS).map j).base.hom.continuous
  · apply ObjectProperty.hom_ext
    change (isoP.hom ≫ e.inv ≫ yoneda.map isoBig.hom) ≫ yoneda.map (openIncl B S hS V₀ O) =
      pullback.snd Uo.ι fV ≫ e₀.hom
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, hisoBig, ← he, Iso.inv_hom_id_assoc,
      hP]

/-- **The supported lifting property of the projection `U ×_X V ⟶ V`** at the inverse image of
a closed `T ⊆ |X|` with quasi-compact open complement, for `V` affine and `U ×_X V`
quasi-compact.  Under `V ≅ h_{V₀}` and `U ×_X V ≅ h_O` this is
`AlgebraicGeometry.Space.supportedLiftProperty_representedOpen`, i.e. Stacks 08EK and 08EH. -/
theorem supportedLiftProperty_edsSnd (hVaff : IsAffineSpace B S hS Ve)
    (hUVqc : IsQuasiCompactSpace B S hS (edsInter B S hS hsq).1)
    (T : Set (points B S hS W.1)) (hT : IsClosed T)
    (hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS W.1 W.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι) :
    SupportedLiftProperty B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)
      (pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom ⁻¹' T) := by
  obtain ⟨V₀, hV₀, O, hO, eV, eI, hcomm⟩ := exists_eds_represented B S hS hsq hVaff hUVqc
  let Zs' : Set (points B S hS (yoneda.obj V₀)) :=
    pointsMap B S hS (yoneda.obj V₀) eV.inv.hom ⁻¹'
      (pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom ⁻¹' T)
  let Z : Set ((BigFppfOver.toScheme B S hS).obj V₀) := (pointsEquivScheme B S hS V₀).symm ⁻¹' Zs'
  have hZ' : (pointsEquivScheme B S hS V₀) ⁻¹' Z = Zs' := by
    ext p
    simp [Z]
  have hZs'c : IsClosed Zs' :=
    (hT.preimage (continuous_pointsMap B S hS _)).preimage (continuous_pointsMap B S hS _)
  have hZc : IsClosed Z := hZs'c.preimage (schemePointsHomeomorph B S hS V₀).symm.continuous
  have hZcpt : IsCompact Zᶜ := by
    let G := (openSubspacesOrderIso B S hS W.1 W.2).symm ⟨Tᶜ, hT.isOpen_compl⟩
    have h₁ := isCompact_preimage_range_of_isQuasiCompact B S hS W.2
      (isAlgebraicSpace_yoneda B S hS V₀) (isQuasiCompactSpace_yoneda_of_isAffine B S hS V₀ hV₀)
      (eV.inv.hom ≫ (edsEtaleHom B S hS hsq).hom) G.1 G.2 hTqc
    rw [range_openSubspacesOrderIso_symm B S hS W.1 W.2 T hT, pointsMap_comp,
      Set.preimage_comp] at h₁
    have h₂ := h₁.image (schemePointsHomeomorph B S hS V₀).continuous
    convert h₂ using 1
    ext x
    simp only [Z, Zs', Set.mem_compl_iff, Set.mem_preimage, Set.mem_image]
    refine ⟨fun hx => ⟨(pointsEquivScheme B S hS V₀).symm x, hx, Equiv.apply_symm_apply _ _⟩, ?_⟩
    rintro ⟨p, hp, rfl⟩
    have hp' : (pointsEquivScheme B S hS V₀).symm ((schemePointsHomeomorph B S hS V₀) p) = p :=
      (pointsEquivScheme B S hS V₀).symm_apply_apply p
    rw [hp']
    simpa only [pointsMap_comp, Function.comp_apply] using hp
  have h := supportedLiftProperty_of_iso B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)
    (representedSpaceMap B S hS (openIncl B S hS V₀ O))
    (isEtale_representedSpaceMap_openIncl B S hS V₀ O) eI eV hcomm _
    (supportedLiftProperty_representedOpen B S hS V₀ O hO Z hZc hZcpt)
  have hset : pointsMap B S hS (edsEtale B S hS hsq).1 eV.hom.hom ⁻¹' Zs' =
      pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom ⁻¹' T := by
    have : eV.hom.hom ≫ eV.inv.hom = 𝟙 (edsEtale B S hS hsq).1 :=
      congrArg (fun φ => φ.hom) eV.hom_inv_id
    simp only [Zs']
    rw [← Set.preimage_comp, ← pointsMap_comp, this, pointsMap_id, Set.preimage_id]
  rwa [hZ', hset] at h

end Square

end AlgebraicGeometry.Space
