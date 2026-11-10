module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAffineApproximation
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAlgebraicBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoproductSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoproductZariskiCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductClopenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSheaf
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.MapToFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraicSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringRestrictionFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproductSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesGraph
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValuedRefined
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.CategoryTheory.Limits.VanKampenCoproductSquares
public import StacksFrontier.CategoryTheory.Limits.VanKampenCoproducts

/-!
# Glueing the Noetherian approximations of `Coh_{X/Y}` over a disjoint union of affines

Over `Spec ℤ`, let `f : X ⟶ V` be separated and of finite presentation with `V = ∐ Wᵢ` a disjoint
union of affine schemes of the site. Over each `Wᵢ` the morphism descends (Stacks 07SK, 0851) to a
model `fᵢ : Xᵢ ⟶ Tᵢ` with `Tᵢ` affine of finite type over `ℤ`; the models glue to
`f₀ = ∐ fᵢ : X₀ = ∐ Xᵢ ⟶ V₀ = ∐ Tᵢ`, a separated morphism of finite presentation to a scheme
locally of finite presentation over `ℤ`, and `f` is the base change of `f₀` along
`V ⟶ V₀`. So `Coh_{X/V}` is algebraic as soon as `Coh_{X₀/V₀}` is. This is how the proof of
Stacks 09DS passes from an affine base to an arbitrary scheme base, with the sizes of the glued
objects controlled: every `Xᵢ` has an atlas of countable size.

## Main results

* `AlgebraicGeometry.Space.exists_atlas_size_le_of_isFinitePresentation`: an algebraic space of
  finite presentation over an affine scheme of the site has an affine étale atlas no larger than
  that scheme.
* `AlgebraicGeometry.Space.locallyOfFinitePresentation_of_isColimit_cofan`: a coproduct in the
  site of objects locally of finite presentation over the base is locally of finite presentation.
* `AlgebraicGeometry.Space.isAlgebraicStack_of_coproductAffine`: the gluing step, over a target
  which is a coproduct of affine objects of the site.
* `AlgebraicGeometry.Space.isAlgebraicStack_of_overIntegers`: over `Spec ℤ`, algebraicity of
  `Coh_{X/Y}` for an arbitrary target `Y`, granted representability of the diagonal and the case
  of a target locally of finite presentation over `ℤ`.

## References

* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

namespace AlgebraicGeometry.Space

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An algebraic space of finite presentation over an affine scheme of the site has an affine
étale atlas no larger than that scheme.** The space is quasi-compact (Stacks 06G5), so it has an
affine étale atlas (Stacks 03H6); the atlas is locally of finite presentation over the affine
base, hence of finite type and quasi-compact over it, and Stacks 04T7 bounds its size. -/
theorem exists_atlas_size_le_of_isFinitePresentation
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (f : X ⟶ yoneda.obj V) (hf : IsFinitePresentation B S hS f) :
    ∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) p ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) p ∧
      ((BigFppfOver.toScheme B S hS).obj U).size ≤ ((BigFppfOver.toScheme B S hS).obj V).size := by
  have hqc : IsQuasiCompactSpace B S hS X :=
    isQuasiCompactSpace_of_isFinitePresentation B S hS f (isAlgebraicSpace_yoneda B S hS V)
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS V inferInstance) hf
  obtain ⟨U, p, hU, hps, hpe⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X hX).1 hqc
  have hlfp : IsLocallyOfFinitePresentation B S hS (p ≫ f) :=
    isLocallyOfFinitePresentation_comp B S hS (isAlgebraicSpace_yoneda B S hS U) hX
      (isAlgebraicSpace_yoneda B S hS V) p f (isLocallyOfFinitePresentation_of_isEtale B S hS hpe)
      hf.1
  let m : U ⟶ V := yoneda.preimage (p ≫ f)
  have hm : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map m) := by
    refine (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget m).1 ?_
    rwa [Functor.map_preimage]
  have := hU
  have : QuasiCompact ((BigFppfOver.toScheme B S hS).map m) := inferInstance
  exact ⟨U, p, hps, (isEtale_iff_presheaf_of_yoneda B S hS p).1 hpe,
    Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact ((BigFppfOver.toScheme B S hS).map m)⟩

/-- A stage `Spec ℤ[j]` of a ring is a countable scheme. -/
theorem size_finsetStage_le (hZ : B.Contains (⊤_ Scheme.{u})) (R : Type u) [CommRing R]
    (j : (Finset R)ᵒᵖ) :
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
      ((BigAffineFppf.inclusion _ _ hZ).obj (finsetStage hZ R j))).size ≤ ℵ₀ := by
  have := countable_adjoinFinset R j.unop
  change (Spec (CommRingCat.of (Algebra.adjoin ℤ ((j.unop : Finset R) : Set R)))).size ≤ ℵ₀
  rw [Scheme.size_Spec]
  exact max_le le_rfl Cardinal.mk_le_aleph0

/-- **A coproduct in the site of objects locally of finite presentation over the base is locally
of finite presentation over the base**: on the disjoint union of the underlying schemes the
structure morphism is the morphism out of the coproduct, and local finite presentation is local
on the source. -/
theorem locallyOfFinitePresentation_of_isColimit_cofan {I : Type u}
    {T : I → BigFppfOver B S hS} {V : BigFppfOver B S hS} {c : ∀ i, T i ⟶ V}
    (hV : IsColimit (Cofan.mk V c))
    (hT : ∀ i, LocallyOfFinitePresentation (B.inclusion.map (T i).hom)) :
    LocallyOfFinitePresentation (B.inclusion.map V.hom) := by
  obtain ⟨hV'⟩ := nonempty_isColimit_cofan_toScheme hV
  let e := (colimit.isColimit (Discrete.functor fun i => (BigFppfOver.toScheme B S hS).obj (T i))
    ).coconePointUniqueUpToIso hV'
  have he : ∀ i, Sigma.ι (fun i => (BigFppfOver.toScheme B S hS).obj (T i)) i ≫ e.hom =
      (BigFppfOver.toScheme B S hS).map (c i) := fun i =>
    IsColimit.comp_coconePointUniqueUpToIso_hom _ hV' ⟨i⟩
  have hdesc : e.hom ≫ B.inclusion.map V.hom =
      Sigma.desc fun i => B.inclusion.map (T i).hom := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [Sigma.ι_comp_desc]
    calc Sigma.ι (fun i => (BigFppfOver.toScheme B S hS).obj (T i)) i ≫ e.hom ≫
          B.inclusion.map V.hom
        = (BigFppfOver.toScheme B S hS).map (c i) ≫ B.inclusion.map V.hom := by
          rw [← Category.assoc, he i]
      _ = B.inclusion.map (T i).hom :=
          (Functor.map_comp B.inclusion (c i).left V.hom).symm.trans
            (congrArg B.inclusion.map (Over.w (c i)))
  have _ : IsZariskiLocalAtSource (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
  have _ : LocallyOfFinitePresentation (Sigma.desc fun i => B.inclusion.map (T i).hom) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation) fun i => hT i
  rw [(Iso.eq_inv_comp e).2 hdesc]
  infer_instance

/-- An object of the big fppf site over `Spec ℤ` is a *coproduct of affines* when it is the point
of a coproduct cofan of objects with affine underlying schemes. -/
def IsCoproductOfAffines {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
    (V₀ : BigFppfOver B (⊤_ Scheme.{u}) hZ) : Prop :=
  ∃ (K : Type u) (W : K → BigFppfOver B (⊤_ Scheme.{u}) hZ)
    (_ : ∀ k, IsAffine ((BigFppfOver.toScheme B _ hZ).obj (W k))) (c : ∀ k, W k ⟶ V₀),
    Nonempty (IsColimit (Cofan.mk V₀ c))

set_option synthInstance.maxHeartbeats 400000 in
-- instance synthesis for limits and coproducts of presheaves on the big fppf site is expensive
set_option maxHeartbeats 1600000 in
-- instance search for limits and coproducts of presheaves on the big fppf site
/-- **The gluing step of Stacks 09DS.** Over `Spec ℤ`, let `f : X ⟶ Y` be separated and of finite
presentation, with `Y` the presheaf represented by an object `V` of the site which is a coproduct
of affine objects `Tᵢ`, indexed by a type of size below the cutoff of the site. If `Coh_{X₀/V₀}` is
an algebraic stack for every separated `f₀ : X₀ ⟶ V₀` of finite presentation whose target is (the
algebraic space of) an object of the site locally of finite presentation over `ℤ`, then
`Coh_{X/Y}` is an algebraic stack.

Over each `Tᵢ` the morphism descends to a model `fᵢ : Xᵢ ⟶ Spec ℤ[jᵢ]`
(`AlgebraicGeometry.Space.exists_stageModelSE`); the coproduct `f₀ : ∐ Xᵢ ⟶ ∐ Spec ℤ[jᵢ]` of the
models is separated, of finite presentation, with target locally of finite presentation over
`ℤ`, and `f` is its base change along `V ⟶ ∐ Spec ℤ[jᵢ]`, which is checked summand by summand
over the universal coproduct `V`. -/
theorem isAlgebraicStack_of_coproductAffine {B : BigFppfSite.{u}}
    (hZ : B.Contains (⊤_ Scheme.{u})) {I : Type u} (hI : #I < B.cutoff)
    (T : I → BigAffineFppf B (⊤_ Scheme.{u}) hZ) {V : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (c : ∀ i, (BigAffineFppf.inclusion _ _ hZ).obj (T i) ⟶ V) (hV : IsColimit (Cofan.mk V c))
    (D : CoherentSituation B (⊤_ Scheme.{u}) hZ) (eY : D.Y.1 ≅ yoneda.obj V)
    (hsep : IsSeparated B _ hZ D.f.hom)
    (hbase : ∀ (V₀ : BigFppfOver B (⊤_ Scheme.{u}) hZ),
      LocallyOfFinitePresentation (B.inclusion.map V₀.hom) →
      IsCoproductOfAffines V₀ →
      ∀ (D₀ : CoherentSituation B (⊤_ Scheme.{u}) hZ),
        D₀.Y = (schemeSpaceFunctor B _ hZ).obj V₀ →
        IsSeparated B _ hZ D₀.f.hom →
        Stack.IsAlgebraicStack.{u, w} B _ hZ D₀.coherentCFG.val) :
    Stack.IsAlgebraicStack.{u, w} B _ hZ D.coherentCFG.val := by
  classical
  let J := BigFppfOver.topology B (⊤_ Scheme.{u}) hZ
  have : J.Subcanonical := BigFppfOver.subcanonical B _ hZ
  have : HasSheafify J (Type u) := bigFppfOver_hasSheafify B _ hZ
  have : HasLimitsOfShape WalkingCospan (Sheaf J (Type u)) := inferInstance
  have : ∀ {X Y Z : Sheaf J (Type u)} (f : X ⟶ Z) (g : Y ⟶ Z), HasPullback f g :=
    fun _ _ => HasLimitsOfShape.has_limit _
  have : HasColimitsOfShape (Discrete I) (Sheaf J (Type u)) := inferInstance
  let incl := BigAffineFppf.inclusion B (⊤_ Scheme.{u}) hZ
  -- the target, as a coproduct of representable sheaves
  have hcG : IsColimit (Cofan.mk (J.yoneda.obj V) fun i => J.yoneda.map (c i)) :=
    isColimit_yoneda_of_isColimit_toScheme B _ hZ (fun i => incl.obj (T i)) V c
      (nonempty_isColimit_cofan_toScheme hV).some
  have hGu := isUniversalColimit_of_isColimit_sheafOfTypes J hcG
  -- the source as a sheaf, and the structure morphism
  let Xsh : Sheaf J (Type u) := ⟨D.X.1, D.X.2.isSheaf⟩
  let a : Xsh ⟶ J.yoneda.obj V := ObjectProperty.homMk (D.f.hom ≫ eY.hom)
  have hsqa : IsPullback (𝟙 D.X.1) a.hom D.f.hom eY.inv :=
    IsPullback.of_horiz_isIso (CommSq.mk (by simp [a]))
  have hYV : IsAlgebraicSpace B _ hZ (yoneda.obj V) := isAlgebraicSpace_yoneda B _ hZ V
  have hfpa : IsFinitePresentation B _ hZ a.hom :=
    IsFinitePresentation.of_isPullback B _ hZ D.X.2 D.X.2 hYV D.Y.2 hsqa D.finitePresentation
  have hsepa : IsSeparated B _ hZ a.hom := isSeparated_of_isPullback B _ hZ hsqa hsep
  -- the pieces `X ×_V Tᵢ` and their models at a stage
  let P : I → Sheaf J (Type u) := fun i => pullback a (J.yoneda.map (c i))
  have hsqP : ∀ i, IsPullback (pullback.fst a (J.yoneda.map (c i))).hom
      (pullback.snd a (J.yoneda.map (c i))).hom a.hom (yoneda.map (c i)) := fun i =>
    isPullback_hom_of_sheaf (IsPullback.of_hasPullback a (J.yoneda.map (c i)))
  have hPalg : ∀ i, IsAlgebraicSpace B _ hZ (P i).obj := fun i =>
    isAlgebraicSpace_of_iso B _ hZ (hsqP i).isoPullback.symm
      (isAlgebraicSpace_pullback B _ hZ a.hom (yoneda.map (c i)) D.X.2
        (isAlgebraicSpace_yoneda B _ hZ _) hYV)
  let Di : I → CoherentSituation B (⊤_ Scheme.{u}) hZ := fun i =>
    { X := ⟨(P i).obj, hPalg i⟩
      Y := (schemeSpaceFunctor B _ hZ).obj (incl.obj (T i))
      f := ObjectProperty.homMk (pullback.snd a (J.yoneda.map (c i))).hom
      finitePresentation := IsFinitePresentation.of_isPullback B _ hZ (hPalg i) D.X.2
        (isAlgebraicSpace_yoneda B _ hZ _) hYV (hsqP i) hfpa }
  have hsepi : ∀ i, IsSeparated B _ hZ (Di i).f.hom := fun i =>
    isSeparated_of_isPullback B _ hZ (hsqP i) hsepa
  choose j Xj fj k hXj hfj hsepj hsqj using fun i =>
    exists_stageModelSE hZ (T i) (Di i) (Iso.refl _) (hsepi i)
  -- the stages and the maps to them
  let St : I → BigFppfOver B (⊤_ Scheme.{u}) hZ := fun i =>
    incl.obj (finsetStage hZ (affineRing hZ (T i)) (j i))
  let p : ∀ i, incl.obj (T i) ⟶ St i := fun i =>
    incl.map ((finsetStageCone hZ (T i)).π.app (j i))
  have hStaff : ∀ i, IsAffine ((BigFppfOver.toScheme B _ hZ).obj (St i)) := fun i =>
    (finsetStage hZ (affineRing hZ (T i)) (j i)).property
  -- the glued base `V₀ = ∐ Spec ℤ[jᵢ]`
  let μ : Cardinal.{u} := max ℵ₀ #I
  have hℵ : ℵ₀ ≤ μ := le_max_left _ _
  have hμ : μ < B.cutoff := max_lt B.aleph0_lt_cutoff hI
  have hIμ : #I ≤ μ := le_max_right _ _
  have hStμ : ∀ i, ((BigFppfOver.toScheme B _ hZ).obj (St i)).size ≤ μ := fun i =>
    (size_finsetStage_le hZ _ (j i)).trans hℵ
  obtain ⟨V₀, c₀, ⟨hV₀⟩⟩ : ∃ (V₀ : BigFppfOver B (⊤_ Scheme.{u}) hZ) (c₀ : ∀ i, St i ⟶ V₀),
      Nonempty (IsColimit (Cofan.mk V₀ c₀)) :=
    BigFppfOver.exists_isColimit_cofan_of_size_le B _ hZ St hℵ hμ hIμ hStμ
  have hcG₀ : IsColimit (Cofan.mk (J.yoneda.obj V₀) fun i => J.yoneda.map (c₀ i)) :=
    isColimit_yoneda_of_isColimit_toScheme B _ hZ St V₀ c₀
      (nonempty_isColimit_cofan_toScheme hV₀).some
  have hV₀lfp : LocallyOfFinitePresentation (B.inclusion.map V₀.hom) :=
    locallyOfFinitePresentation_of_isColimit_cofan hV₀ fun i => by
      have : LocallyOfFiniteType (terminal.from
          ((specAdjoinFinsetDiagram (affineRing hZ (T i))).obj (j i))) :=
        locallyOfFiniteType_terminalFrom_specAdjoinFinsetDiagram_obj _ (j i)
      have e : (show (specAdjoinFinsetDiagram (affineRing hZ (T i))).obj (j i) ⟶ ⊤_ Scheme.{u}
          from B.inclusion.map (St i).hom) = terminal.from _ := terminal.hom_ext _ _
      change LocallyOfFinitePresentation (show (specAdjoinFinsetDiagram (affineRing hZ (T i))).obj
        (j i) ⟶ ⊤_ Scheme.{u} from B.inclusion.map (St i).hom)
      rw [e]
      infer_instance
  -- the glued source `X₀ = ∐ Xᵢ`
  let Xs : I → Sheaf J (Type u) := fun i => ⟨Xj i, (hXj i).isSheaf⟩
  let X₀s : Sheaf J (Type u) := ∐ Xs
  have hX₀ : IsColimit (Cofan.mk X₀s (Sigma.ι Xs)) := coproductIsCoproduct Xs
  have hatlas := fun i => exists_atlas_size_le_of_isFinitePresentation (hXj i) (St i) (fj i) (hfj i)
  choose U pa hpas hpae hUsize using hatlas
  have hX₀alg : IsAlgebraicSpace B _ hZ X₀s.obj :=
    isAlgebraicSpace_coproduct_of_size_le B _ hZ Xj hXj X₀s (Sigma.ι Xs) hX₀ U pa hpas hpae
      (Equiv.refl I) hℵ hμ hIμ fun i => (hUsize i).trans (hStμ i)
  have hYV₀ : IsAlgebraicSpace B _ hZ (yoneda.obj V₀) := isAlgebraicSpace_yoneda B _ hZ V₀
  -- the glued morphism, cartesian over each summand
  let fj' : ∀ i, Xj i ⟶ yoneda.obj (St i) := fj
  let fs : ∀ i, Xs i ⟶ J.yoneda.obj (St i) := fun i => ObjectProperty.homMk (fj' i)
  let f₀s : X₀s ⟶ J.yoneda.obj V₀ := Sigma.desc fun i => fs i ≫ J.yoneda.map (c₀ i)
  let yc : ∀ i, yoneda.obj (St i) ⟶ yoneda.obj V₀ := fun i => yoneda.map (c₀ i)
  have hsq₀ : ∀ i, IsPullback (Sigma.ι Xs i).hom (fj' i) f₀s.hom (yc i) := fun i =>
    isPullback_hom_of_sheaf (IsVanKampenColimit.isPullback_inj hX₀
      (isVanKampenColimit_of_isColimit_sheafOfTypes J hcG₀) fs f₀s
      (fun i => Sigma.ι_comp_desc _ i) i)
  have hmono₀ : ∀ i, Mono (yc i) := fun i =>
    Sheaf.mono_hom_cofan_inj (fun i => J.yoneda.map (c₀ i)) hcG₀ i
  have hf₀sep : IsSeparated B _ hZ f₀s.hom :=
    isSeparated_of_isColimit_cofan B _ hZ (Sigma.ι Xs) hX₀ hXj hX₀alg hYV₀ f₀s.hom fun i => by
      rw [(hsq₀ i).w]
      exact isSeparated_comp B _ hZ _ _ (hsepj i) (isSeparated_of_mono _ (hmono₀ i))
  have hf₀fp : IsFinitePresentation B _ hZ f₀s.hom := by
    refine isFinitePresentation_of_zariskiCover B _ hZ hX₀alg hYV₀ f₀s.hom
      (isZariskiCover_range_cofan_inj (fun i => J.yoneda.map (c₀ i)) hcG₀
        fun i => isAlgebraicSpace_yoneda B _ hZ _) fun i => ?_
    have : Mono (yc i) := hmono₀ i
    let r := Subfunctor.toRange (yc i)
    have : IsIso r := inferInstance
    have hbig : IsPullback (Sigma.ι Xs i).hom (fj' i ≫ r) f₀s.hom
        (Subfunctor.range (yc i)).ι := by
      have h0 := (hsq₀ i).paste_vert
        (IsPullback.of_vert_isIso (f := 𝟙 (yoneda.obj V₀))
          (g := (Subfunctor.range (yc i)).ι)
          ⟨(Category.comp_id _).trans (Subfunctor.toRange_ι _).symm⟩)
      simpa using h0
    have hR : IsAlgebraicSpace B _ hZ (Subfunctor.range (yc i)).toFunctor :=
      isAlgebraicSpace_of_iso B _ hZ (asIso r) (isAlgebraicSpace_yoneda B _ hZ _)
    have hsqr : IsPullback hbig.isoPullback.inv
        (pullback.snd f₀s.hom (Subfunctor.range (yc i)).ι) (fj' i) (inv r) :=
      IsPullback.of_horiz_isIso (CommSq.mk (by
        rw [← hbig.isoPullback_inv_snd, Category.assoc, Category.assoc, IsIso.hom_inv_id,
          Category.comp_id]))
    exact isFinitePresentation_of_isPullback' hsqr
      (isAlgebraicSpace_pullback B _ hZ _ _ hX₀alg hR hYV₀) (hXj i) hR
      (isAlgebraicSpace_yoneda B _ hZ _) (hfj i)
  -- the comparison `V ⟶ V₀` and the square, checked over each summand of `V`
  let q : V ⟶ V₀ := Cofan.IsColimit.desc hV fun i => p i ≫ c₀ i
  have hq : ∀ i, c i ≫ q = p i ≫ c₀ i := fun i => Cofan.IsColimit.fac hV _ i
  have hXcolim := hGu.isColimitCofanPullback a
  let κs : Xsh ⟶ X₀s := Cofan.IsColimit.desc hXcolim fun i =>
    (ObjectProperty.homMk (k i ≫ (Sigma.ι Xs i).hom) : P i ⟶ X₀s)
  have hκ : ∀ i, pullback.fst a (J.yoneda.map (c i)) ≫ κs =
      (ObjectProperty.homMk (k i ≫ (Sigma.ι Xs i).hom) : P i ⟶ X₀s) := fun i =>
    Cofan.IsColimit.fac hXcolim _ i
  have hsqi : ∀ i, IsPullback (k i ≫ (Sigma.ι Xs i).hom)
      (pullback.snd a (J.yoneda.map (c i))).hom f₀s.hom (yoneda.map (c i) ≫ yoneda.map q) := by
    intro i
    have h1 : IsPullback (k i) (pullback.snd a (J.yoneda.map (c i))).hom (fj' i)
        (yoneda.map (p i)) := hsqj i
    have h2 := h1.paste_horiz (hsq₀ i)
    have h3 : yoneda.map (p i) ≫ yc i = yoneda.map (c i) ≫ yoneda.map q := by
      simp only [yc, ← Functor.map_comp, hq]
    rwa [h3] at h2
  have hw : κs ≫ f₀s = a ≫ J.yoneda.map q := by
    refine Cofan.IsColimit.hom_ext hXcolim _ _ fun i => ?_
    change pullback.fst a (J.yoneda.map (c i)) ≫ κs ≫ f₀s =
      pullback.fst a (J.yoneda.map (c i)) ≫ a ≫ J.yoneda.map q
    rw [← Category.assoc, hκ, pullback.condition_assoc]
    exact Sheaf.hom_ext (hsqi i).w
  have hi : ∀ i, IsPullback (pullback.fst a (J.yoneda.map (c i)) ≫ κs)
      (pullback.snd a (J.yoneda.map (c i))) f₀s (J.yoneda.map (c i) ≫ J.yoneda.map q) := by
    intro i
    rw [hκ]
    exact isPullback_sheaf_of_hom (hsqi i)
  have hPs := hGu.isPullback_of_forall_isPullback κs a f₀s (J.yoneda.map q) hw hi
  have hPp : IsPullback κs.hom a.hom f₀s.hom (yoneda.map q) := isPullback_hom_of_sheaf hPs
  have hP' : IsPullback κs.hom D.f.hom f₀s.hom (eY.hom ≫ yoneda.map q) :=
    hPp.of_iso (Iso.refl _) (Iso.refl _) eY.symm (Iso.refl _) (by simp) (by simp [a]) (by simp)
      (by simp)
  -- the glued situation and the conclusion, as in the affine case
  let D₀ : CoherentSituation B (⊤_ Scheme.{u}) hZ :=
    { X := ⟨X₀s.obj, hX₀alg⟩
      Y := (schemeSpaceFunctor B _ hZ).obj V₀
      f := ObjectProperty.homMk f₀s.hom
      finitePresentation := hf₀fp }
  have h₀ : Stack.IsAlgebraicStack.{u, w} B _ hZ D₀.coherentCFG.val :=
    hbase V₀ hV₀lfp ⟨I, St, hStaff, c₀, ⟨hV₀⟩⟩ D₀ rfl hf₀sep
  let g : D.Y ⟶ D₀.Y := ObjectProperty.homMk (eY.hom ≫ yoneda.map q)
  have h₁ := D₀.isAlgebraicStack_baseChange.{u, w} g h₀
  let e : D.X ≅ (D₀.baseChange g).X := ObjectProperty.isoMk _ hP'.isoPullback
  have he : e.hom ≫ (D₀.baseChange g).f = D.f :=
    ObjectProperty.hom_ext _ hP'.isoPullback_hom_snd
  exact (CoherentSituation.isAlgebraicStack_isoSituation_iff (D := D₀.baseChange g) (f' := D.f)
    D.finitePresentation e he).mpr h₁

/-- **Stacks 09DS over `Spec ℤ`, granted the base case.** Over `Spec ℤ`, let `f : X ⟶ Y` be a
separated morphism of finite presentation of algebraic spaces such that `Coh_{X/Y}` has
representable diagonal. If `Coh_{X₀/V₀}` is an algebraic stack for every separated `f₀ : X₀ ⟶ V₀`
of finite presentation whose target is (the algebraic space of) an object of the site locally of
finite presentation over `ℤ`, then `Coh_{X/Y}` is an algebraic stack.

An étale atlas of `Y`, refined by the disjoint union of all affine opens of its source, is a
surjective smooth morphism `V ⟶ Y` from a coproduct of affines; `Coh_{X/Y}` is algebraic as soon
as its base change `Coh_{X_V/V}` is
(`AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_of_baseChange`), and the latter is
`AlgebraicGeometry.Space.isAlgebraicStack_of_coproductAffine`. -/
theorem isAlgebraicStack_of_overIntegers {B : BigFppfSite.{u}}
    (hZ : B.Contains (⊤_ Scheme.{u})) (D : CoherentSituation B (⊤_ Scheme.{u}) hZ)
    (hsep : IsSeparated B _ hZ D.f.hom)
    (hdiag : Stack.HasRepresentableDiagonal B _ hZ D.coherentCFG)
    (hbase : ∀ (V₀ : BigFppfOver B (⊤_ Scheme.{u}) hZ),
      LocallyOfFinitePresentation (B.inclusion.map V₀.hom) →
      IsCoproductOfAffines V₀ →
      ∀ (D₀ : CoherentSituation B (⊤_ Scheme.{u}) hZ),
        D₀.Y = (schemeSpaceFunctor B _ hZ).obj V₀ →
        IsSeparated B _ hZ D₀.f.hom →
        Stack.IsAlgebraicStack.{u, w} B _ hZ D₀.coherentCFG.val) :
    Stack.IsAlgebraicStack.{u, w} B _ hZ D.coherentCFG.val := by
  obtain ⟨U, pU, hpUs, hpUe⟩ := D.Y.2.exists_atlas
  obtain ⟨ι, X, V, c, q, haff, -, hι, -, hqs, hqe, ⟨hV⟩, -⟩ :=
    BigFppfOver.exists_affineOpens_surjective_etale_sigma' B _ hZ U
  let g : (schemeSpaceFunctor B _ hZ).obj V ⟶ D.Y := ObjectProperty.homMk (yoneda.map q ≫ pU)
  have hgs : IsSurjective B _ hZ g.hom :=
    isSurjective_comp B _ hZ (isSurjective_yoneda_map B _ hZ q hqs)
      ((surjective_iff_surjective_pointsMap B _ hZ D.Y.1 D.Y.2 U pU).1 hpUs)
  have hge : IsEtale B _ hZ g.hom :=
    isEtale_yoneda_map_comp B _ hZ pU q hqe ((isEtale_iff_presheaf_of_yoneda B _ hZ pU).2 hpUe)
  refine D.isAlgebraicStack_of_baseChange g ⟨hgs, isSmooth_of_isEtale B _ hZ D.Y.2 hge⟩ hdiag ?_
  have hsep' : IsSeparated B _ hZ (D.baseChange g).f.hom :=
    isSeparated_of_isPullback B _ hZ (IsPullback.of_hasPullback D.f.hom g.hom) hsep
  exact isAlgebraicStack_of_coproductAffine hZ (hι.trans_lt U.left.property)
    (fun i => ⟨X i, haff i⟩) c hV (D.baseChange g) (Iso.refl _) hsep' hbase

/-- **Stacks 09DS over `Spec ℤ`, from the inputs of Artin's criterion.** Over `Spec ℤ`, let
`f : X ⟶ Y` be separated and of finite presentation. Granted that `Coh` has representable
diagonal (Stacks 08W6) for every standing datum over `Spec ℤ`, and, for every separated standing
datum whose target is an object of the site locally of finite presentation over `ℤ`, axiom [-1],
the finiteness of tangent spaces (Stacks 08W8), the effectivity of formal objects (Stacks 08W9)
and of square-zero systems (from Flatness on Spaces, Theorem 0CXB), `Coh_{X/Y}` is an algebraic
stack. -/
theorem isAlgebraicStack_overIntegers_of_artinInputs {B : BigFppfSite.{u}}
    (hZ : B.Contains (⊤_ Scheme.{u})) (D : CoherentSituation B (⊤_ Scheme.{u}) hZ)
    (hsep : IsSeparated B _ hZ D.f.hom)
    (hdiag : ∀ D : CoherentSituation B (⊤_ Scheme.{u}) hZ,
      Stack.HasRepresentableDiagonal B _ hZ D.coherentCFG)
    (hinputs : ∀ (V₀ : BigFppfOver B (⊤_ Scheme.{u}) hZ),
      LocallyOfFinitePresentation (B.inclusion.map V₀.hom) →
      IsCoproductOfAffines V₀ →
      ∀ (D₀ : CoherentSituation B (⊤_ Scheme.{u}) hZ),
        D₀.Y = (schemeSpaceFunctor B _ hZ).obj V₀ → IsSeparated B _ hZ D₀.f.hom →
        Stack.IsSizeBounded B _ hZ D₀.coherentCFG ∧
        Stack.HasFiniteDimensionalTangentSpaces B _ hZ D₀.coherentCFG ∧
        (∀ ξ : Deformation.Artin.FormalObject B _ hZ D₀.coherentCFG.val.p,
          Deformation.Artin.FormalObject.IsEffective B _ hZ D₀.coherentCFG.val.p
            D₀.coherentCFG.property ξ) ∧
        Deformation.Artin.IsSquareZeroEffective B _ hZ D₀.coherentCFG.val.p
          D₀.coherentCFG.isFiberedInGroupoids) :
    Stack.IsAlgebraicStack.{u, w, u + 1, u + 1} B _ hZ D.coherentCFG.val :=
  isAlgebraicStack_of_overIntegers hZ D hsep (hdiag D) fun V₀ hV₀ hV₀c D₀ hY hsep₀ => by
    obtain ⟨hsize, htangent, heffective, hsq⟩ := hinputs V₀ hV₀ hV₀c D₀ hY hsep₀
    exact D₀.isAlgebraicStack_coherentCFG_overIntegers V₀ hV₀
      (eqToIso (congrArg (fun Y : AlgebraicSpaces B _ hZ => Y.1) hY)) (hdiag D₀) hsize htangent
      heffective hsq

end AlgebraicGeometry.Space

end
