module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianApproximationStep
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAbsolute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae

/-!
# Quasi-separated algebraic spaces of finite type under enlarging the big fppf site

Let `B ⊆ B'` be big fppf sites and let `AlgebraicGeometry.changeBigSite` be the inverse image of
algebraic spaces over the terminal scheme `Spec ℤ` along the inclusion (Stacks 03FP, 04W1). An
algebraic space over `Spec ℤ` which is quasi-separated and of finite type over `Spec ℤ` is small:
it has an affine étale atlas which is of finite type over `Spec ℤ`, and the kernel pair of that
atlas is a quasi-compact scheme étale over it, so both have size at most that of `Spec ℤ` and
lie in every big fppf site. This file draws the two consequences for the enlargement.

## Main results

* `AlgebraicGeometry.Space.exists_affine_etale_atlas_of_isFiniteType`: an algebraic space which
  is quasi-separated and of finite type over `Spec ℤ` has a surjective étale atlas by an affine
  scheme locally of finite type over `Spec ℤ`, whose kernel pair is quasi-compact, both of size
  at most the size of `Spec ℤ`.
* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_and_isFiniteType_of_affine_etale_atlas`:
  conversely such an atlas makes an algebraic space quasi-separated and of finite type over
  `Spec ℤ`.
* `AlgebraicGeometry.exists_changeBigSite_iso_of_small_etale_atlas`: an algebraic space on the
  larger site with a surjective étale atlas by an object of the smaller site, whose kernel pair
  is an object of the smaller site, is the inverse image of an algebraic space on the smaller
  site having that atlas and that kernel pair.
* `AlgebraicGeometry.mem_essImage_changeBigSite_of_isFiniteType`: an algebraic space over
  `Spec ℤ` on the larger site which is quasi-separated and of finite type over `Spec ℤ` lies in
  the essential image of `AlgebraicGeometry.changeBigSite`.
* `AlgebraicGeometry.isAbsolutelyQuasiSeparated_and_isFiniteType_of_changeBigSite`: an
  algebraic space over `Spec ℤ` whose inverse image is quasi-separated and of finite type over
  `Spec ℤ` is itself quasi-separated and of finite type over `Spec ℤ`.

## Implementation notes

Reflection goes through the essential image rather than through the properties themselves: the
atlas of the inverse image descends to the smaller site together with its kernel pair, the
quotient on the smaller site is identified with the given space by full faithfulness
(Stacks 04W1), and the atlas so obtained is affine, of finite type over `Spec ℤ` and has a
quasi-compact kernel pair, which is what Stacks 07S4 and the chart criterion for finite type
consume.

## References

* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
* [Stacks Project, Tag 07S4](https://stacks.math.columbia.edu/tag/07S4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))

/-- If a presheaf `X` on the big fppf site over `Spec ℤ` is of finite type over `Spec ℤ`, then
the scheme `V` of any étale map `yoneda.obj V ⟶ X` is locally of finite type over `Spec ℤ`. -/
theorem locallyOfFiniteType_terminal_from_of_etale
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hft : IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from X))
    {V : BigFppfOver B (⊤_ Scheme.{u}) hZ} {q : yoneda.obj V ⟶ X}
    (hqe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf q) :
    LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V)) := by
  have hetaleId : ∀ U : BigFppfOver B (⊤_ Scheme.{u}) hZ,
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)) (𝟙 U) := by
    intro U
    change AlgebraicGeometry.Etale ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (𝟙 U))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  have hterm : IsTerminal
      (yoneda.obj (Over.mk (𝟙 (B.obj hZ)) : BigFppfOver B (⊤_ Scheme.{u}) hZ)) :=
    (Over.mkIdTerminal (X := B.obj hZ)).isTerminalObj yoneda _
  have hbT : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf
      (hterm.uniqueUpToIso terminalIsTerminal).hom :=
    presheaf_of_isIso B (⊤_ Scheme.{u}) hZ
      (MorphismProperty.RespectsIso.inverseImage _ _) hetaleId _
  have hlft0 : AlgebraicGeometry.LocallyOfFiniteType
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map
        (Over.mkIdTerminal.from V : V ⟶ Over.mk (𝟙 (B.obj hZ)))) :=
    hft.1 V (Over.mk (𝟙 (B.obj hZ))) q (hterm.uniqueUpToIso terminalIsTerminal).hom _ hqe hbT
      (terminal.hom_ext _ _)
  have he : (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V)) =
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map
        (Over.mkIdTerminal.from V : V ⟶ Over.mk (𝟙 (B.obj hZ))) :
          (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V ⟶ ⊤_ Scheme.{u}) :=
    terminal.hom_ext _ _
  rwa [he]

/-- A scheme which is compact and locally of finite type over an affine scheme has size at most
that of the affine scheme. -/
private theorem size_le_of_compactSpace_of_isAffine {W T : Scheme.{u}} (f : W ⟶ T)
    (hf : LocallyOfFiniteType f) (hT : IsAffine T) (hW : CompactSpace W) : W.size ≤ T.size := by
  have := quasiCompact_of_compactSpace_of_isAffine f hT hW
  exact Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact f

/-- **A quasi-separated algebraic space of finite type over `Spec ℤ` has a small affine
presentation.** It has a surjective étale atlas by an affine scheme locally of finite type over
`Spec ℤ`, the kernel pair of the atlas is represented by a quasi-compact scheme, and both
schemes have size at most the size of `Spec ℤ`. -/
theorem exists_affine_etale_atlas_of_isFiniteType
    (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X)
    (hft : IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ X))) :
    ∃ (V Q : BigFppfOver B (⊤_ Scheme.{u}) hZ) (r s : Q ⟶ V) (q : yoneda.obj V ⟶ X),
      IsPullback (yoneda.map r) (yoneda.map s) q q ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf q ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf q ∧
      IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V) ∧
      CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Q) ∧
      LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V)) ∧
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V).size ≤ (⊤_ Scheme.{u}).size ∧
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Q).size ≤ (⊤_ Scheme.{u}).size := by
  have hTaff : IsAffine (⊤_ Scheme.{u}) :=
    IsAffine.of_isIso (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).inv
  have hft' := isFiniteType_terminal_of_isFiniteType_viewOverIntegers B hZ hft
  have hqc := isQuasiCompactSpace_of_isFiniteType_terminal B hZ hft'
  obtain ⟨V, q, hV, hqsurj, hqet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B _ hZ X hX).1 hqc
  have hqe := (isEtale_iff_presheaf_of_yoneda B _ hZ q).1 hqet
  let Q := hqe.rep.pullback q
  let r : Q ⟶ V := hqe.rep.fst' q
  let s : Q ⟶ V := hqe.rep.snd q
  have hR : IsPullback (yoneda.map r) (yoneda.map s) q q := hqe.rep.isPullback' q
  have hVc : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V) := inferInstance
  have hQc : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Q) :=
    compactSpace_of_isAbsolutelyQuasiSeparated B _ hZ hZ hqs hR hVc hVc
  have hlft := locallyOfFiniteType_terminal_from_of_etale B hZ hft' hqe
  -- Size bounds.
  have hVsize := size_le_of_compactSpace_of_isAffine
    (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V)) hlft hTaff hVc
  have hs : Etale ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map s) :=
    hqe.property q (yoneda.map r) s hR
  have hQsize := (size_le_of_compactSpace_of_isAffine
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map s) inferInstance hV hQc).trans hVsize
  exact ⟨V, Q, r, s, q, hR, hqsurj, hqe, hV, hQc, hlft, hVsize, hQsize⟩

/-- **An affine étale atlas of finite type over `Spec ℤ` with a quasi-compact kernel pair makes
an algebraic space quasi-separated and of finite type over `Spec ℤ`.** Quasi-separatedness is
Stacks 07S4 at the atlas, whose kernel-pair projection is quasi-compact; finite type is the chart
criterion `AlgebraicGeometry.Space.GluedEtaleQuotient.isFiniteType_of_chart`. -/
theorem isAbsolutelyQuasiSeparated_and_isFiniteType_of_affine_etale_atlas
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    {V Q : BigFppfOver B (⊤_ Scheme.{u}) hZ} {r s : Q ⟶ V} {q : yoneda.obj V ⟶ X}
    (hR : IsPullback (yoneda.map r) (yoneda.map s) q q)
    (hqs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf q)
    (hqe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf q)
    (hV : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V))
    (hQ : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Q))
    (hlft : LocallyOfFiniteType
      (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V))) :
    IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X ∧
      IsFiniteType B (⊤_ Scheme.{u}) hZ
        (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ X)) := by
  have hVc : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V) := inferInstance
  have hU : QuasiSeparated (B.inclusion.map V.hom ≫ terminal.from (⊤_ Scheme.{u})) := by
    have hq := (quasiSeparatedSpace_iff_quasiSeparated
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V)).mp inferInstance
    rwa [terminal.hom_ext (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V))
      (B.inclusion.map V.hom ≫ terminal.from (⊤_ Scheme.{u}))] at hq
  exact ⟨isAbsolutelyQuasiSeparated_of_etaleAtlas_quasiCompact_projection B _ hZ hZ hX hqs hqe
      hU hR (quasiCompact_of_compactSpace_of_isAffine _ hV hQ),
    GluedEtaleQuotient.isFiniteType_of_chart hX q hqe hqs hlft⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry

open Space Stacks.Groupoids

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B')

/-- **An algebraic space on the larger site with a small étale presentation descends together
with its presentation.** If an algebraic space `X'` over `S` on the larger site has a surjective
étale atlas by the image of an object `V` of the smaller site, whose kernel pair is the image of
an object `Q` of the smaller site with projections the images of `r, s : Q ⟶ V`, then `X'` is the
inverse image of the quotient of `V` by `Q` on the smaller site, which has a surjective étale
atlas by `V` with kernel pair `r, s`. -/
theorem exists_changeBigSite_iso_of_small_etale_atlas (S : Scheme.{u}) (hS : B.Contains S)
    (X' : AlgebraicSpaces B' S (largerContains h hS)) (V Q : BigFppfOver B S hS)
    (r s : Q ⟶ V) (q : yoneda.obj ((inclusionOver h S hS).obj V) ⟶ X'.obj)
    (hQ : IsPullback (yoneda.map ((inclusionOver h S hS).map r))
      (yoneda.map ((inclusionOver h S hS).map s)) q q)
    (hqs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B' S (largerContains h hS))).presheaf q)
    (hqe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B' S (largerContains h hS))).presheaf q) :
    ∃ (X : AlgebraicSpaces B S hS) (q₀ : yoneda.obj V ⟶ X.obj),
      IsPullback (yoneda.map r) (yoneda.map s) q₀ q₀ ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q₀ ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q₀ ∧
      Nonempty ((changeBigSite B B' h S hS).obj X ≅ X') := by
  let hS' : B'.Contains S := largerContains h hS
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S hS'
  let i := inclusionOver h S hS
  let : i.IsContinuous J K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  let : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let : HasSheafify J (Type u) := hasSheafify_overTopology B S hS
  let : HasSheafify K (Type u) := hasSheafify_overTopology B' S hS'
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    inferInstanceAs (HasSheafify J (Type u))
  let : HasSheafify (BigFppfOver.topology B' S hS') (Type u) :=
    inferInstanceAs (HasSheafify K (Type u))
  let : J.Subcanonical := subcanonical_overTopology B S hS
  let : K.Subcanonical := subcanonical_overTopology B' S hS'
  have hr : Etale ((Over.post B.inclusion).map r).left :=
    hqe.property q (yoneda.map (i.map s)) (i.map r) hQ.flip
  have hs : Etale ((Over.post B.inclusion).map s).left :=
    hqe.property q (yoneda.map (i.map r)) (i.map s) hQ
  let : IsEtaleEquivalenceRelation (relation B S hS s r) := {
    isEquivalenceRelation := by
      have hrel : IsEquivalenceRelation ((Over.post B.inclusion).map r)
          ((Over.post B.inclusion).map s) :=
        isEquivalenceRelation_of_isPullback B' S hS' q (i.map r) (i.map s) hQ
      simpa only [relation, PreRelation.target, PreRelation.source, prod.lift_fst,
        prod.lift_snd] using hrel
    etale_source := by
      simpa only [relation, PreRelation.source, prod.lift_snd] using hs
    etale_target := by
      simpa only [relation, PreRelation.target, prod.lift_fst] using hr }
  let F := quotientSheaf J (Over.post B.inclusion) (relation B S hS s r)
  have hF : IsAlgebraicSpace B S hS F.obj :=
    isAlgebraicSpace_quotientSheaf_relation_of_diagDescent B S hS s r
      (descentForQuotients B S hS)
  let q₀ := quotientMap B S hS s r
  have hQ₀ := quotientMap_isPullback B S hS s r
  have hFrep : yoneda.relativelyRepresentable (quotientMap B S hS s r) :=
    relativelyRepresentable_quotientMap_of_isAlgebraicSpace B S hS s r hF
  have hq₀s := quotientMap_surjective B S hS s r hFrep
  have hq₀e := quotientMap_etale B S hS s r hFrep
  obtain ⟨_, _, ⟨hq₀⟩⟩ := isCoequalizer_of_surjectiveEtale B S hS q₀ r s hQ₀ hF hq₀s hq₀e
  obtain ⟨_, _, ⟨hq⟩⟩ := isCoequalizer_of_surjectiveEtale B' S hS' q (i.map r) (i.map s) hQ
    X'.property hqs hqe
  let : PreservesColimits (i.sheafPullback (Type u) J K) :=
    (i.sheafAdjunctionContinuous (Type u) J K).leftAdjoint_preservesColimits
  let e := coequalizerIsoOfNatIso J.yoneda (i ⋙ K.yoneda) (i.sheafPullback (Type u) J K)
    (pullbackYonedaIso i J K) r s
    (show J.yoneda.obj V ⟶ F from ⟨q₀⟩)
    (by apply Sheaf.hom_ext; exact hQ₀.w)
    (show (i ⋙ K.yoneda).obj V ⟶ (⟨X'.obj, X'.property.isSheaf⟩ : Sheaf K (Type u)) from ⟨q⟩)
    (by apply Sheaf.hom_ext; exact hQ.w) hq₀ hq
  exact ⟨⟨F.obj, hF⟩, q₀, hQ₀, hq₀s, hq₀e,
    ⟨ObjectProperty.isoMk _ ((sheafToPresheaf K (Type u)).mapIso e)⟩⟩

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **A quasi-separated algebraic space of finite type over `Spec ℤ` on the larger site descends,
with an affine presentation.** It is the inverse image of an algebraic space on the smaller site
which has a surjective étale atlas by an affine object `V` locally of finite type over `Spec ℤ`,
with kernel pair a quasi-compact object `Q` of the smaller site. -/
theorem exists_changeBigSite_iso_of_isFiniteType
    (Z' : AlgebraicSpaces B' (⊤_ Scheme.{u}) (largerContains h hZ))
    (hqs : IsAbsolutelyQuasiSeparated B' (⊤_ Scheme.{u}) (largerContains h hZ)
      (largerContains h hZ) Z'.obj)
    (hft : IsFiniteType B' (⊤_ Scheme.{u}) (largerContains h hZ)
      (terminal.from (viewOverIntegers B' (⊤_ Scheme.{u}) (largerContains h hZ)
        (largerContains h hZ) Z'.obj))) :
    ∃ (X : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ) (V Q : BigFppfOver B (⊤_ Scheme.{u}) hZ)
      (r s : Q ⟶ V) (q : yoneda.obj V ⟶ X.obj),
      IsPullback (yoneda.map r) (yoneda.map s) q q ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf q ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf q ∧
      IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V) ∧
      CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Q) ∧
      LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V)) ∧
      Nonempty ((changeBigSite B B' h (⊤_ Scheme.{u}) hZ).obj X ≅ Z') := by
  obtain ⟨V', Q', r', s', q', hR', hq's, hq'e, hV', hQ'c, hlft', hV'size, hQ'size⟩ :=
    exists_affine_etale_atlas_of_isFiniteType B' (largerContains h hZ) Z'.obj Z'.property hqs hft
  let V : BigFppfOver B (⊤_ Scheme.{u}) hZ :=
    Over.mk (Y := B.obj (hV'size.trans_lt hZ)) (X := B.obj hZ) ⟨V'.hom.hom⟩
  let Q : BigFppfOver B (⊤_ Scheme.{u}) hZ :=
    Over.mk (Y := B.obj (hQ'size.trans_lt hZ)) (X := B.obj hZ) ⟨Q'.hom.hom⟩
  let mk : (Q' ⟶ V') → (Q ⟶ V) := fun f => Over.homMk ⟨f.left.hom⟩ (by
    apply ObjectProperty.hom_ext
    change f.left.hom ≫ V'.hom.hom = Q'.hom.hom
    exact congrArg InducedCategory.Hom.hom (Over.w f))
  let r : Q ⟶ V := mk r'
  let s : Q ⟶ V := mk s'
  obtain ⟨X, q, hR, hqs, hqe, hX⟩ :=
    exists_changeBigSite_iso_of_small_etale_atlas B B' h (⊤_ Scheme.{u}) hZ Z' V Q r s q'
      hR' hq's hq'e
  exact ⟨X, V, Q, r, s, q, hR, hqs, hqe, hV', hQ'c, hlft', hX⟩

/-- **Quasi-separated algebraic spaces of finite type over `Spec ℤ` descend along an
enlargement of the big fppf site.** An algebraic space over `Spec ℤ` on the larger site which is
quasi-separated and of finite type over `Spec ℤ` lies in the essential image of the inverse image
`AlgebraicGeometry.changeBigSite`. -/
theorem mem_essImage_changeBigSite_of_isFiniteType
    (Z' : AlgebraicSpaces B' (⊤_ Scheme.{u}) (largerContains h hZ))
    (hqs : IsAbsolutelyQuasiSeparated B' (⊤_ Scheme.{u}) (largerContains h hZ)
      (largerContains h hZ) Z'.obj)
    (hft : IsFiniteType B' (⊤_ Scheme.{u}) (largerContains h hZ)
      (terminal.from (viewOverIntegers B' (⊤_ Scheme.{u}) (largerContains h hZ)
        (largerContains h hZ) Z'.obj))) :
    (changeBigSite B B' h (⊤_ Scheme.{u}) hZ).essImage Z' := by
  obtain ⟨X, -, -, -, -, -, -, -, -, -, -, -, hX⟩ :=
    exists_changeBigSite_iso_of_isFiniteType B B' h hZ Z' hqs hft
  exact ⟨X, hX⟩

/-- **Quasi-separatedness and finite type over `Spec ℤ` reflect along an enlargement
of the big fppf site.** An algebraic space over `Spec ℤ` whose inverse image on the larger site is
quasi-separated and of finite type over `Spec ℤ` is itself quasi-separated and of finite type
over `Spec ℤ`.

The inverse image is the inverse image of an algebraic space with an affine étale atlas of finite
type over `Spec ℤ` and quasi-compact kernel pair
(`AlgebraicGeometry.exists_changeBigSite_iso_of_isFiniteType`); full faithfulness (Stacks 04W1)
identifies that space with the given one, which therefore has such an atlas. -/
theorem isAbsolutelyQuasiSeparated_and_isFiniteType_of_changeBigSite
    (Z : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ)
    (hqs : IsAbsolutelyQuasiSeparated B' (⊤_ Scheme.{u}) (largerContains h hZ)
      (largerContains h hZ) ((changeBigSite B B' h (⊤_ Scheme.{u}) hZ).obj Z).obj)
    (hft : IsFiniteType B' (⊤_ Scheme.{u}) (largerContains h hZ)
      (terminal.from (viewOverIntegers B' (⊤_ Scheme.{u}) (largerContains h hZ)
        (largerContains h hZ) ((changeBigSite B B' h (⊤_ Scheme.{u}) hZ).obj Z).obj))) :
    IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Z.obj ∧
      IsFiniteType B (⊤_ Scheme.{u}) hZ
        (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ Z.obj)) := by
  obtain ⟨X, V, Q, r, s, q, hR, hqsurj, hqe, hV, hQ, hlft, ⟨eX⟩⟩ :=
    exists_changeBigSite_iso_of_isFiniteType B B' h hZ _ hqs hft
  let eo : X.obj ≅ Z.obj := (ObjectProperty.ι _).mapIso
    ((changeBigSite_fullyFaithful B B' h (⊤_ Scheme.{u}) hZ).some.preimageIso eX)
  have hR' : IsPullback (yoneda.map r) (yoneda.map s) (q ≫ eo.hom) (q ≫ eo.hom) :=
    hR.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eo (by simp) (by simp)
      ((Category.id_comp _).symm) ((Category.id_comp _).symm)
  have _ : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have _ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  exact isAbsolutelyQuasiSeparated_and_isFiniteType_of_affine_etale_atlas B hZ Z.property hR'
    (MorphismProperty.RespectsIso.postcomp _ eo.hom q hqsurj)
    (MorphismProperty.RespectsIso.postcomp _ eo.hom q hqe) hV hQ hlft

end AlgebraicGeometry

end
