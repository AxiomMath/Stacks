module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.BaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceEtalePullback
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.PullbackOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedChartHenselization

/-!
# Weakly associated points under a field base change, for a represented source

Stacks 0CUS for an algebraic space represented by a scheme of the site is the schemes statement
Stacks 0CUC, read across the comparison of the two descriptions of a module on a represented
algebraic space.  This file carries out that reading.

Let `T` be an object of the big fppf site over `S`, let `G` be a quasi-coherent module on the
algebraic space `h_T` it represents and let `T' = T ×_{T_k} T_{k'}` be a base change of `T` in
the site along a morphism `g_k` which induces `Spec K → Spec k`.  Weak association of a point of
`h_{T'}` to the inverse image of `G` is, by Stacks 0CTW on a represented algebraic space,
Zariski weak association of the corresponding point of the scheme `T'` to the Zariski
restriction of that inverse image; the restriction commutes with base change, so that module is
the Zariski pullback along `T' → T` of the restriction of `G`; and the schemes statement
Stacks 0CUC then puts the image point of `T` in the weak assassin of the restriction of `G`,
which is weak association of the point of `h_T` by Stacks 0CTW once more.

## Main results

* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_of_siteBaseChange`: the statement for a base
  change formed inside the site.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_of_fieldBaseChange_represented`: the same for
  an arbitrary cartesian square of algebraic spaces whose source is `h_T`, which is the form
  Stacks 0CUS consumes.

## Implementation notes

The comparison of the two descriptions of a module on a represented algebraic space, the gap
that made the represented case of Stacks 0CUS an assumption, is supplied by three results.
Stacks 0CTW on a represented algebraic space,
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_restrictToChart_idEtaleChart_iff`, matches the
two weak assassins with no hypothesis beyond quasi-coherence of the module;
`AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme` identifies the two readings of
the chart restriction; and
`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent` is the
compatibility of the second reading with base change along a morphism of the site.

The square of schemes is obtained from the square of the site by
`CategoryTheory.Functor.map_isPullback`, the forgetful functor to schemes preserving fibre
products, and is then carried onto `Spec k` and `Spec K` by `CategoryTheory.IsPullback.of_iso`.
Stacks 0CUC is stated at the chosen fibre product `Spec K ×_{Spec k} T`, so the comparison
`CategoryTheory.IsPullback.isoPullback` of the two is crossed by
`AlgebraicGeometry.isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion` at an isomorphism,
together with the composition comparison of Zariski pullbacks.

For an arbitrary cartesian square the source `V'` is identified with the represented base change:
the site has fibre products, `CategoryTheory.yoneda` preserves them, and a cartesian square of
algebraic spaces with the same cospan therefore differs from the represented one by a unique
isomorphism.  Weak association crosses that isomorphism because an isomorphism is étale, so
Stacks 0CUU applies to it.

## References

* [Stacks Project, Tag 0CUS](https://stacks.math.columbia.edu/tag/0CUS)
* [Stacks Project, Tag 0CUC](https://stacks.math.columbia.edu/tag/0CUC)
* [Stacks Project, Tag 0CTW](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Stacks 0CTW on a represented algebraic space, read on the Zariski restriction of the module to
the representing scheme. -/
private theorem isWeaklyAssociatedPoint_restrictToChartScheme_iff (T : BigFppfOver B S hS)
    (G : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    [G.IsQuasicoherentOnSite] (t : (BigFppfOver.toScheme B S hS).obj T) :
    Stacks.Divisors.IsWeaklyAssociatedPoint
        (restrictToChartScheme B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) G
          (idEtaleChart B S hS T)) t ↔
      IsWeaklyAssociatedPoint B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ G
        ((pointsEquivScheme B S hS T).symm t) :=
  (isWeaklyAssociatedPoint_iff_of_iso
    (restrictToChartIsoRestrictToChartScheme B S hS (isAlgebraicSpace_yoneda B S hS T) G
      (idEtaleChart B S hS T)) t).symm.trans
    (isWeaklyAssociatedPoint_restrictToChart_idEtaleChart_iff B S hS T G t)

/-- **Stacks 0CUS for a base change formed in the site.** Let `g_k : T_{k'} ⟶ T_k` be a morphism
of the big fppf site over `S` inducing `Spec K → Spec k` for a field extension `K/k`, let
`t_k : T ⟶ T_k` be an object of the site over `T_k` and let `T' = T ×_{T_k} T_{k'}`.  For a
quasi-coherent module `G` on the algebraic space represented by `T`, a weakly associated point of
the inverse image of `G` on the algebraic space represented by `T'` has weakly associated
image. -/
theorem isWeaklyAssociatedPoint_of_siteBaseChange (k K : Type u) [Field k] [Field K]
    [Algebra k K] {T Tk Tk' T' : BigFppfOver B S hS} (tk : T ⟶ Tk) (gk : Tk' ⟶ Tk)
    (r : T' ⟶ T) (s : T' ⟶ Tk') (sq : IsPullback r s tk gk)
    (ek : (BigFppfOver.toScheme B S hS).obj Tk ≅ Spec (CommRingCat.of k))
    (eK : (BigFppfOver.toScheme B S hS).obj Tk' ≅ Spec (CommRingCat.of K))
    (hgk : (BigFppfOver.toScheme B S hS).map gk =
      eK.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ ek.inv)
    (G : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hG : G.IsQuasicoherentOnSite) (w : points B S hS (yoneda.obj T'))
    (hw : IsWeaklyAssociatedPoint B S hS
      ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩
      ((modulePullback B S hS (representedSpaceMap B S hS r)).obj G) w) :
    IsWeaklyAssociatedPoint B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ G
      (pointsMap B S hS (yoneda.obj T') (yoneda.map r) w) := by
  have : G.IsQuasicoherentOnSite := hG
  have hGr : ((modulePullback B S hS (representedSpaceMap B S hS r)).obj
      G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (representedSpaceMap B S hS r) G hG
  -- The Zariski restriction of `G` to the representing scheme, a quasi-coherent module.
  set F₀ : ((BigFppfOver.toScheme B S hS).obj T).Modules :=
    restrictToChartScheme B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) G
      (idEtaleChart B S hS T) with hF₀def
  have hF₀qc : F₀.IsQuasicoherent :=
    isQuasicoherent_restrictToChartScheme B S hS (schemeSpace T) G hG (idEtaleChart B S hS T)
  -- The point of the scheme `T'` named by `w`.
  set t' := pointsEquivScheme B S hS T' w with ht'def
  have hwt' : (pointsEquivScheme B S hS T').symm t' = w := by
    rw [ht'def, Equiv.symm_apply_apply]
  -- Stacks 0CTW on the represented algebraic space `h_{T'}`, read on the scheme chart restriction.
  have h2 := (isWeaklyAssociatedPoint_restrictToChartScheme_iff B S hS T'
    ((modulePullback B S hS (representedSpaceMap B S hS r)).obj G) t').2 (hwt' ▸ hw)
  obtain ⟨ebc⟩ := nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent r G hG
  have h3 : Stacks.Divisors.IsWeaklyAssociatedPoint
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj F₀) t' :=
    (isWeaklyAssociatedPoint_iff_of_iso ebc t').1 h2
  -- The square of schemes over `Spec k`.
  have hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  have sqS : IsPullback ((BigFppfOver.toScheme B S hS).map r)
      ((BigFppfOver.toScheme B S hS).map s ≫ eK.hom)
      ((BigFppfOver.toScheme B S hS).map tk ≫ ek.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    refine (sq.map (BigFppfOver.toScheme B S hS)).of_iso (Iso.refl _) (Iso.refl _) eK ek
      (by simp) (by simp) (by simp) ?_
    rw [hgk]
    simp
  set fk := (BigFppfOver.toScheme B S hS).map tk ≫ ek.hom with hfkdef
  set gKk := Spec.map (CommRingCat.ofHom (algebraMap k K)) with hgKkdef
  have hefst : sqS.isoPullback.hom ≫ pullback.fst fk gKk =
      (BigFppfOver.toScheme B S hS).map r := sqS.isoPullback_hom_fst
  -- Crossing the comparison with the chosen fibre product of schemes.
  have hcomp : (Scheme.Modules.pullback sqS.isoPullback.hom).obj
        ((Scheme.Modules.pullback (pullback.fst fk gKk)).obj F₀) ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj F₀ :=
    (Scheme.Modules.pullbackComp sqS.isoPullback.hom (pullback.fst fk gKk)).app F₀ ≪≫
      eqToIso (congrArg (fun m ↦ (Scheme.Modules.pullback m).obj F₀) hefst)
  have h5 : Stacks.Divisors.IsWeaklyAssociatedPoint
      ((Scheme.Modules.pullback (pullback.fst fk gKk)).obj F₀)
      (sqS.isoPullback.hom.base t') :=
    (isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion sqS.isoPullback.hom _ t').1
      ((isWeaklyAssociatedPoint_iff_of_iso hcomp t').2 h3)
  -- Stacks 0CUC.
  have hyx : (pullback.fst fk gKk).base (sqS.isoPullback.hom.base t') =
      ((BigFppfOver.toScheme B S hS).map r).base t' :=
    congrArg (fun m : (BigFppfOver.toScheme B S hS).obj T' ⟶
      (BigFppfOver.toScheme B S hS).obj T ↦ m.base t') hefst
  have h6 : Stacks.Divisors.IsWeaklyAssociatedPoint F₀
      (((BigFppfOver.toScheme B S hS).map r).base t') :=
    isWeaklyAssociatedPoint_of_baseChange (k := k) (K := K) fk F₀
      (sqS.isoPullback.hom.base t') _ hyx h5
  -- Stacks 0CTW once more, on the represented algebraic space `h_T`.
  have h7 := (isWeaklyAssociatedPoint_restrictToChartScheme_iff B S hS T G _).1 h6
  rwa [pointsEquivScheme_symm_map B S hS r t', hwt'] at h7

/-- **Stacks 0CUS for a source represented by a scheme of the site.** Let `g : Y' ⟶ Y` be a
morphism of algebraic spaces presented, through objects `T_k` and `T_{k'}` of the site with
underlying schemes `Spec k` and `Spec K`, by a field extension `K/k`.  For a cartesian square
over `g` whose source is the algebraic space represented by an object `T` of the site and every
quasi-coherent module `G` on it, a weakly associated point of the inverse image of `G` has
weakly associated image. -/
theorem isWeaklyAssociatedPoint_of_fieldBaseChange_represented (k K : Type u) [Field k] [Field K]
    [Algebra k K] {Y Y' V' : AlgebraicSpaces B S hS} (T Tk Tk' : BigFppfOver B S hS)
    (gk : Tk' ⟶ Tk) (g : Y' ⟶ Y)
    (ek : (BigFppfOver.toScheme B S hS).obj Tk ≅ Spec (CommRingCat.of k))
    (eK : (BigFppfOver.toScheme B S hS).obj Tk' ≅ Spec (CommRingCat.of K))
    (hgk : (BigFppfOver.toScheme B S hS).map gk =
      eK.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ ek.inv)
    (eY : Y.1 ≅ yoneda.obj Tk) (eY' : Y'.1 ≅ yoneda.obj Tk')
    (hg : g.hom ≫ eY.hom = eY'.hom ≫ yoneda.map gk)
    (fV : (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (fV' : V' ⟶ Y')
    (p : V' ⟶ (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS))
    (sqV : IsPullback p fV' fV g)
    (G : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hG : G.IsQuasicoherentOnSite) (w : points B S hS V'.1)
    (hw : IsWeaklyAssociatedPoint B S hS V' ((modulePullback B S hS p).obj G) w) :
    IsWeaklyAssociatedPoint B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ G
      (pointsMap B S hS V'.1 p.hom w) := by
  let : HasPullbacks (BigFppfOver B S hS) := inferInstance
  -- The morphism of the site under the structure morphism of the source.
  set tk : T ⟶ Tk := yoneda.preimage (fV.hom ≫ eY.hom) with htkdef
  have htkmap : yoneda.map tk = fV.hom ≫ eY.hom := yoneda.map_preimage _
  have sq0 : IsPullback (pullback.fst tk gk) (pullback.snd tk gk) tk gk :=
    IsPullback.of_hasPullback tk gk
  -- The represented base change, cartesian over `g`.
  have sqBig : IsPullback (yoneda.map (pullback.fst tk gk))
      (yoneda.map (pullback.snd tk gk) ≫ eY'.inv) fV.hom g.hom := by
    refine (sq0.map yoneda).of_iso (Iso.refl _) (Iso.refl _) eY'.symm eY.symm (by simp) (by simp)
      ?_ ?_
    · simp [htkmap]
    · rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, hg,
        Iso.inv_hom_id_assoc]
  have sqBigSp : IsPullback (representedSpaceMap B S hS (pullback.fst tk gk))
      (ObjectProperty.homMk (yoneda.map (pullback.snd tk gk) ≫ eY'.inv) :
        (⟨yoneda.obj (pullback tk gk),
          isAlgebraicSpace_yoneda B S hS (pullback tk gk)⟩ : AlgebraicSpaces B S hS) ⟶ Y')
      fV g :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι fun F ↦ IsAlgebraicSpace B S hS F) sqBig
  set ι := sqBigSp.isoIsPullback _ _ sqV with hιdef
  have hιp : ι.hom ≫ p = representedSpaceMap B S hS (pullback.fst tk gk) :=
    sqBigSp.isoIsPullback_hom_fst _ _ sqV
  have : IsIso ι.hom.hom :=
    ((ObjectProperty.ι fun F ↦ IsAlgebraicSpace B S hS F).mapIso ι).isIso_hom
  have hιet : IsEtale B S hS ι.hom.hom := isEtale_of_isIso B S hS ι.hom.hom
  -- The point of the represented base change named by `w`.
  set w' := pointsMap B S hS V'.1 ι.inv.hom w with hw'def
  have hww' : pointsMap B S hS (yoneda.obj (pullback tk gk)) ι.hom.hom w' = w := by
    rw [hw'def, ← pointsMap_comp_apply]
    have : ι.inv.hom ≫ ι.hom.hom = 𝟙 V'.1 :=
      congrArg InducedCategory.Hom.hom ι.inv_hom_id
    rw [this]
    exact congrFun (pointsMap_id B S hS V'.1) w
  have hwpull : IsWeaklyAssociatedPoint B S hS
      ⟨yoneda.obj (pullback tk gk), isAlgebraicSpace_yoneda B S hS (pullback tk gk)⟩
      ((modulePullback B S hS (representedSpaceMap B S hS (pullback.fst tk gk))).obj G) w' := by
    have h := (isWeaklyAssociatedPoint_congr B S hS
        ((modulePullbackCompIso B S hS ι.hom p).app G) w').1
      ((isWeaklyAssociatedPoint_modulePullback_iff B S hS ι.hom hιet
        ((modulePullback B S hS p).obj G) w').2 (hww' ▸ hw))
    rwa [hιp] at h
  have hmain := isWeaklyAssociatedPoint_of_siteBaseChange B S hS k K tk gk
    (pullback.fst tk gk) (pullback.snd tk gk) sq0 ek eK hgk G hG w' hwpull
  have hpt : pointsMap B S hS (yoneda.obj (pullback tk gk))
      (yoneda.map (pullback.fst tk gk)) w' = pointsMap B S hS V'.1 p.hom w := by
    have hcomp : ι.hom.hom ≫ p.hom = yoneda.map (pullback.fst tk gk) :=
      congrArg InducedCategory.Hom.hom hιp
    rw [← hcomp, pointsMap_comp_apply, hww']
  rwa [hpt] at hmain

end AlgebraicGeometry.Space

end
