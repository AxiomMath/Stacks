module

public import StacksFrontier.AlgebraicGeometry.Quot.EtaleLocallyProjectiveCurvesChartDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFromElementaryChart
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierChartEquations

/-!
# The finite piece of a chart divisor as an effective Cartier divisor on the family

Let `fX : X ⟶ S₀` be a separated morphism from an algebraic space to a scheme of the site,
`e : W ⟶ X` an étale morphism from an affine scheme with a point `w` whose residue-field point is
a monomorphism into `X` (the distinguished point of an elementary étale chart, Stacks 0BBP), with
`W ⟶ S₀` flat and locally of finite presentation, and `Z ⊆ W` a closed subscheme principal near
`w`, whose fibre over `s₀ = g(w)` is an effective Cartier divisor near `w`, and which is
quasi-finite over `S₀` at a point over `w`.

Then there is an affine scheme `U` of the site with an étale morphism `U ⟶ S₀` through `s₀`
such that for every étale `T ⟶ U` and every base change `X_T = X ×_{S₀} T` there are a scheme
`P` of the site, finite and flat over `T`, and a closed immersion `P ⟶ X_T` over `T`, factoring
through `e` after `X_T ⟶ X`, whose points over the distinguished point `u` of `U` all lie over
`w`, and whose image is an effective Cartier divisor on `X_T` (Stacks 083B).

This is the step of the proof that families of curves are étale locally schemes (Stacks 0E6F)
which moves a local divisor from an étale chart to the family. It combines
`AlgebraicGeometry.Space.exists_etale_cartier_piece_of_chart` (the Cartier piece on an étale
scheme `N` over `W ×_{S₀} U`),
`AlgebraicGeometry.Space.exists_isOpen_isClosedImmersion_baseChange_of_elementaryChart` (the piece
is a closed subspace of `X_U` over a neighbourhood `V` of `u`) and
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_range_of_etaleChart_of_ideal` (Stacks 083C
through the chart `N`), after replacing `U` by an affine open neighbourhood of `u` inside `V` and
every piece of data by its base change.

## Main results

* `AlgebraicGeometry.Space.exists_etale_isEffectiveCartierDivisor_range_of_chart`.

## References

* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "𝒯" => BigFppfOver.toScheme B S hS

open Stacks.Divisors in
/-- **The finite piece of a chart divisor is an effective Cartier divisor on the family.** Let
`fX : X ⟶ S₀` be a separated morphism from an algebraic space, `e : W ⟶ X` an étale morphism from
an affine scheme of the site with a point `w` whose residue-field point is a monomorphism into
`X`, lying over `gW : W ⟶ S₀` flat and locally of finite presentation, and `Z` a closed subscheme
of `W` principal near `w`, with effective Cartier fibre near `w` and quasi-finite over `S₀` at a
point `z` over `w`. Then there are an affine scheme `U` of the site, an étale `φ : U ⟶ S₀` and
`u ∈ U` over `gW(w)` such that for every étale `ψ : T ⟶ U` of the site and every base change
`X_T` of `X` along `ψ ≫ φ` there are a scheme `P` of the site, finite and flat over `T` by `p`,
and a closed immersion `π : P ⟶ X_T` over `T` with `P ⟶ X_T ⟶ X` equal to `P ⟶ W ⟶ X` for some
`r : P ⟶ W` sending the points over the fibre of `ψ` over `u` to `w`, with a point of `P` over
every point of that fibre, whose image is an effective Cartier divisor on `X_T`. The neighbourhood
`(U, u)` is elementary: the residue field map of `φ` at `u` is an isomorphism. Taking `ψ = 𝟙`
gives the piece over `U` itself; the étale `ψ` serve to
put finitely many pieces over one étale neighbourhood. -/
theorem exists_etale_isEffectiveCartierDivisor_range_of_chart
    {X : AlgebraicSpaces B S hS} {S₀ W : BigFppfOver B S hS} (fX : X.1 ⟶ yoneda.obj S₀)
    (hsep : IsSeparated B S hS fX)
    (e : yoneda.obj W ⟶ X.1) (he : (MorphismProperty.inverseImage @Etale (𝒯)).presheaf e)
    (w : W.left.1) (hw : B.Contains (Spec (.of (W.left.1.residueField w))))
    (hmono : Mono (yoneda.map (residueFieldMap B S hS W w hw) ≫ e))
    (gW : W ⟶ S₀) (hgW : e ≫ fX = yoneda.map gW)
    [Flat ((𝒯).map gW)] [LocallyOfFinitePresentation ((𝒯).map gW)] [IsAffine ((𝒯).obj W)]
    (Z : ((𝒯).obj W).IdealSheafData) (hwZ : w ∈ Z.support)
    (hprin : ∃ V : ((𝒯).obj W).affineOpens, w ∈ (V : ((𝒯).obj W).Opens) ∧ (Z.ideal V).IsPrincipal)
    (hfib : ∃ V : (((𝒯).map gW).fiber ((𝒯).map gW w)).Opens, ((𝒯).map gW).asFiber w ∈ V ∧
      Stacks.Divisors.IsEffectiveCartierDivisor
        ((Z.comap (((𝒯).map gW).fiberι ((𝒯).map gW w))).comap V.ι))
    (z : Z.subscheme) (hz : Z.subschemeι z = w)
    (hqf : (Z.subschemeι ≫ (𝒯).map gW).QuasiFiniteAt z) :
    ∃ (U : BigFppfOver B S hS) (φ : U ⟶ S₀) (u : (𝒯).obj U),
      Etale ((𝒯).map φ) ∧ IsAffine ((𝒯).obj U) ∧ (𝒯).map φ u = (𝒯).map gW w ∧
      IsIso (((𝒯).map φ).residueFieldMap u) ∧
      ∀ (T : BigFppfOver B S hS) (ψ : T ⟶ U), Etale ((𝒯).map ψ) →
      ∀ (XU : AlgebraicSpaces B S hS) (qU : XU.1 ⟶ X.1) (fU : XU.1 ⟶ yoneda.obj T),
        IsPullback qU fU fX (yoneda.map (ψ ≫ φ)) →
        ∃ (P : BigFppfOver B S hS) (π : yoneda.obj P ⟶ XU.1) (p : P ⟶ T) (r : P ⟶ W)
          (hπ : IsClosedImmersion B S hS π),
          π ≫ fU = yoneda.map p ∧ π ≫ qU = yoneda.map r ≫ e ∧
          _root_.AlgebraicGeometry.IsFinite ((𝒯).map p) ∧ Flat ((𝒯).map p) ∧
          (∀ v, (𝒯).map ψ ((𝒯).map p v) = u → (𝒯).map r v = w) ∧
          (∀ t, (𝒯).map ψ t = u → ∃ v, (𝒯).map p v = t ∧ (𝒯).map r v = w) ∧
          Space.IsEffectiveCartierDivisor B S hS XU
            ⟨Subfunctor.range π, isClosedSubspace_range_of_isClosedImmersion B S hS π
              (isAlgebraicSpace_yoneda B S hS P) hπ⟩ := by
  obtain ⟨U, N, P, φ, u, ι, j, hφ, hUaff, hu, hres, hι, hjc, hfin, hflat, hPu, ⟨v₀, hv₀⟩, J, hJ,
      ε, hε⟩ :=
    exists_etale_cartier_piece_of_chart gW Z w hwZ hprin hfib z hz hqf
  let XU₀ := pullback fX (yoneda.map φ)
  have hXU₀ : IsAlgebraicSpace B S hS XU₀ :=
    isAlgebraicSpace_pullback B S hS fX (yoneda.map φ) X.2 (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS S₀)
  have sq₀ : IsPullback (pullback.fst fX (yoneda.map φ)) (pullback.snd fX (yoneda.map φ)) fX
      (yoneda.map φ) := IsPullback.of_hasPullback _ _
  let eU₀ : yoneda.obj (pullback gW φ) ⟶ XU₀ :=
    pullback.lift (yoneda.map (pullback.fst gW φ) ≫ e) (yoneda.map (pullback.snd gW φ)) (by
      rw [Category.assoc, hgW, ← Functor.map_comp, ← Functor.map_comp, pullback.condition])
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((𝒯).map (j ≫ ι)) := hjc
  have : _root_.AlgebraicGeometry.IsFinite ((𝒯).map ((j ≫ ι) ≫ pullback.snd gW φ)) := by
    rwa [Category.assoc]
  obtain ⟨V, huV, hV⟩ := exists_isOpen_isClosedImmersion_baseChange_of_elementaryChart hXU₀ fX
    hsep e he w hw hmono gW hgW φ _ _ sq₀ eU₀ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (j ≫ ι) u (by simpa only [Category.assoc] using hPu)
  obtain ⟨U₂, hU₂, huU₂, hU₂V⟩ := exists_isAffineOpen_mem_and_subset (X := (𝒯).obj U) huV
  have : IsAffine (U₂ : Scheme.{u}) := hU₂
  have hcU₂ : B.Contains (U₂ : Scheme.{u}) :=
    BigFppfSite.contains_of_locallyOfFinitePresentation B U₂.ι U.left.property
  let U' : BigFppfOver B S hS := BigFppfOver.siteObjectOver B S hS U hcU₂ U₂.ι
  let ι₂ : U' ⟶ U := BigFppfOver.siteMapOver B S hS U hcU₂ U₂.ι
  have hι₂ : (𝒯).map ι₂ = U₂.ι := rfl
  let u' : (𝒯).obj U' := (⟨u, huU₂⟩ : (U₂ : Scheme.{u}))
  have hu' : (𝒯).map ι₂ u' = u := rfl
  have hU₂e : Etale U₂.ι := inferInstance
  have hφ' : Etale ((𝒯).map (ι₂ ≫ φ)) := by
    rw [Functor.map_comp, hι₂]
    exact MorphismProperty.comp_mem @Etale _ _ hU₂e hφ
  have hres' : IsIso (((𝒯).map (ι₂ ≫ φ)).residueFieldMap u') := by
    let u₂ : (U₂ : Scheme.{u}) := ⟨u, huU₂⟩
    have : IsIso (((𝒯).map φ).residueFieldMap (U₂.ι u₂)) := hres
    have h : IsIso (((𝒯).map φ).residueFieldMap (U₂.ι u₂) ≫ U₂.ι.residueFieldMap u₂) :=
      IsIso.comp_isIso
    exact Scheme.residueFieldMap_comp U₂.ι ((𝒯).map φ) u₂ ▸ h
  refine ⟨U', ι₂ ≫ φ, u', hφ', hU₂, ?_, hres', ?_⟩
  · rw [Functor.map_comp, Scheme.Hom.comp_apply, hu', hu]
  intro T ψ hψ XU qU fU sqU₀
  obtain ⟨κ, hκ⟩ : ∃ κ : T ⟶ U, κ = ψ ≫ ι₂ := ⟨_, rfl⟩
  have sqU : IsPullback qU fU fX (yoneda.map (κ ≫ φ)) := by
    rwa [hκ, Category.assoc]
  have hκet : Etale ((𝒯).map κ) := by
    rw [hκ, Functor.map_comp, hι₂]
    exact MorphismProperty.comp_mem @Etale _ _ hψ hU₂e
  have hκφ : Etale ((𝒯).map (κ ≫ φ)) := by
    rw [Functor.map_comp]
    exact MorphismProperty.comp_mem @Etale _ _ hκet hφ
  -- `X_{U'}` is the base change of `X_U` along `U' ⟶ U`
  let q : XU.1 ⟶ XU₀ := pullback.lift qU (fU ≫ yoneda.map κ) (by
    rw [sqU.w, Functor.map_comp, Category.assoc])
  have hq₁ : q ≫ pullback.fst fX (yoneda.map φ) = qU := pullback.lift_fst _ _ _
  have hq₂ : q ≫ pullback.snd fX (yoneda.map φ) = fU ≫ yoneda.map κ := pullback.lift_snd _ _ _
  have sqq : IsPullback q fU (pullback.snd fX (yoneda.map φ)) (yoneda.map κ) :=
    IsPullback.of_right (by rwa [hq₁, ← Functor.map_comp]) hq₂ sq₀
  -- the base changes of `P` and `N`
  let P' := pullback ((j ≫ ι) ≫ pullback.snd gW φ) κ
  let pP : P' ⟶ P := pullback.fst _ _
  let p' : P' ⟶ T := pullback.snd _ _
  have sqP : IsPullback pP p' ((j ≫ ι) ≫ pullback.snd gW φ) κ := IsPullback.of_hasPullback _ _
  have hPw : pP ≫ j ≫ ι ≫ pullback.snd gW φ = p' ≫ κ := by
    simpa only [Category.assoc] using sqP.w
  let N' := pullback (ι ≫ pullback.snd gW φ) κ
  let nN : N' ⟶ N := pullback.fst _ _
  let nU : N' ⟶ T := pullback.snd _ _
  have hN : nN ≫ ι ≫ pullback.snd gW φ = nU ≫ κ := pullback.condition
  let j' : P' ⟶ N' := pullback.lift (pP ≫ j) p' (by rwa [Category.assoc])
  have hj'₁ : j' ≫ nN = pP ≫ j := pullback.lift_fst _ _ _
  have hj'₂ : j' ≫ nU = p' := pullback.lift_snd _ _ _
  -- the étale chart `N' ⟶ X_{U'}`
  let m : N' ⟶ pullback gW (κ ≫ φ) := pullback.lift (nN ≫ ι ≫ pullback.fst gW φ) nU (by
    rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hN])
  have hm₁ : m ≫ pullback.fst gW (κ ≫ φ) = nN ≫ ι ≫ pullback.fst gW φ := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd gW (κ ≫ φ) = nU := pullback.lift_snd _ _ _
  let eU : yoneda.obj (pullback gW (κ ≫ φ)) ⟶ XU.1 :=
    sqU.lift (yoneda.map (pullback.fst gW (κ ≫ φ)) ≫ e) (yoneda.map (pullback.snd gW (κ ≫ φ)))
      (by rw [Category.assoc, hgW, ← Functor.map_comp, ← Functor.map_comp, pullback.condition])
  have heU₁ : eU ≫ qU = yoneda.map (pullback.fst gW (κ ≫ φ)) ≫ e := sqU.lift_fst _ _ _
  have heU₂ : eU ≫ fU = yoneda.map (pullback.snd gW (κ ≫ φ)) := sqU.lift_snd _ _ _
  have sqW : IsPullback (yoneda.map (pullback.fst gW (κ ≫ φ))) eU e qU := by
    refine IsPullback.of_bot ?_ heU₁.symm sqU
    rw [heU₂, hgW]
    exact (IsPullback.of_hasPullback gW (κ ≫ φ)).map yoneda
  have := MorphismProperty.relative_isStableUnderBaseChange
    (P := MorphismProperty.inverseImage @Etale (𝒯)) (F := yoneda)
  have heU : (MorphismProperty.inverseImage @Etale (𝒯)).presheaf eU :=
    MorphismProperty.of_isPullback sqW he
  have hfstet : Etale ((𝒯).map (pullback.fst gW (κ ≫ φ))) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback gW (κ ≫ φ)).map (𝒯)).flip hκφ
  have hnNe : Etale ((𝒯).map nN) :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback (ι ≫ pullback.snd gW φ) κ).map (𝒯)).flip hκet
  have hfst : Etale ((𝒯).map (pullback.fst gW φ)) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback gW φ).map (𝒯)).flip hφ
  have : Etale ((𝒯).map m ≫ (𝒯).map (pullback.fst gW (κ ≫ φ))) := by
    rw [← Functor.map_comp, hm₁, Functor.map_comp, Functor.map_comp]
    infer_instance
  have hmet : Etale ((𝒯).map m) := Etale.of_comp _ ((𝒯).map (pullback.fst gW (κ ≫ φ)))
  have : (MorphismProperty.inverseImage @Etale (𝒯)).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  let e' : yoneda.obj N' ⟶ XU.1 := yoneda.map m ≫ eU
  have he' : (MorphismProperty.inverseImage @Etale (𝒯)).presheaf e' :=
    MorphismProperty.comp_mem _ _ _
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS @Etale m).2 hmet) heU
  have he'₁ : e' ≫ qU = yoneda.map (nN ≫ ι ≫ pullback.fst gW φ) ≫ e := by
    simp only [e', Category.assoc, heU₁, ← Functor.map_comp_assoc, hm₁]
  have he'₂ : e' ≫ fU = yoneda.map nU := by
    simp only [e', Category.assoc, heU₂, ← Functor.map_comp, hm₂]
  -- the piece `P' ⟶ X_{U'}` and its properties
  let π : yoneda.obj P' ⟶ XU.1 := yoneda.map j' ≫ e'
  let r : P' ⟶ W := pP ≫ j ≫ ι ≫ pullback.fst gW φ
  have hπ₁ : π ≫ qU = yoneda.map r ≫ e := by
    simp only [π, r, Category.assoc, he'₁, ← Functor.map_comp_assoc, reassoc_of% hj'₁]
  have hπ₂ : π ≫ fU = yoneda.map p' := by
    simp only [π, Category.assoc, he'₂, ← Functor.map_comp, hj'₂]
  have hπq : π ≫ q = yoneda.map pP ≫ yoneda.map (j ≫ ι) ≫ eU₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hq₁, hπ₁, Category.assoc, Category.assoc, pullback.lift_fst,
        ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
      simp only [r, Category.assoc]
    · rw [Category.assoc, hq₂, reassoc_of% hπ₂, Category.assoc, Category.assoc, pullback.lift_snd,
        ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← sqP.w]
  have hπc : IsClosedImmersion B S hS π :=
    hV XU.2 κ (fun t => by
        rw [hκ, Functor.map_comp, Scheme.Hom.comp_apply]
        exact hU₂V ((𝒯).map ψ t).2)
      q fU sqq pP p' sqP π hπq hπ₂
  refine ⟨P', π, p', r, hπc, hπ₂, hπ₁, ?_, ?_, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsFinite) (sqP.map (𝒯))
      inferInstance
  · exact MorphismProperty.of_isPullback (P := @Flat) (sqP.map (𝒯)) (by rwa [Category.assoc])
  · intro v hv
    have h1 : (𝒯).map (j ≫ ι ≫ pullback.snd gW φ) ((𝒯).map pP v) = u := by
      rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hPw, Functor.map_comp,
        Scheme.Hom.comp_apply, hκ, Functor.map_comp, Scheme.Hom.comp_apply, hv, hu']
    change (𝒯).map (pP ≫ j ≫ ι ≫ pullback.fst gW φ) v = w
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact hPu _ h1
  · intro t ht
    have sqP𝒯 := sqP.map (𝒯)
    have hab : (𝒯).map ((j ≫ ι) ≫ pullback.snd gW φ) v₀ = (𝒯).map κ t := by
      rw [Category.assoc, hv₀, hκ, Functor.map_comp, Scheme.Hom.comp_apply, ht, hu']
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := (𝒯).map ((j ≫ ι) ≫ pullback.snd gW φ)) (g := (𝒯).map κ) v₀ t hab
    refine ⟨sqP𝒯.isoPullback.inv z, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, sqP𝒯.isoPullback_inv_snd, hz₂]
    · have hz : (𝒯).map pP (sqP𝒯.isoPullback.inv z) = v₀ := by
        rw [← Scheme.Hom.comp_apply, sqP𝒯.isoPullback_inv_fst, hz₁]
      change (𝒯).map (pP ≫ j ≫ ι ≫ pullback.fst gW φ) _ = w
      rw [Functor.map_comp, Scheme.Hom.comp_apply, hz]
      exact hPu v₀ hv₀
  · -- `P' ⟶ N'` is the base change of the divisor `J` along the open immersion `N' ⟶ N`
    have sqA : IsPullback j' pP nN j :=
      IsPullback.of_right (h₁₂ := nU) (h₂₂ := ι ≫ pullback.snd gW φ) (v₁₃ := κ)
        (by simpa only [hj'₂, Category.assoc] using sqP.flip) hj'₁
        (IsPullback.of_hasPullback (ι ≫ pullback.snd gW φ) κ).flip
    have sqε : IsPullback ((𝒯).map j') ((𝒯).map pP ≫ ε.hom) ((𝒯).map nN) J.subschemeι :=
      (sqA.map (𝒯)).of_iso (Iso.refl _) (Iso.refl _) ε (Iso.refl _) (by simp) (by simp)
        (by simp) (by rw [Iso.refl_hom, Category.comp_id, hε])
    let J' := J.comap ((𝒯).map nN)
    have sqJ : IsPullback J'.subschemeι ((J.comapIso ((𝒯).map nN)).hom ≫ pullback.snd _ _)
        ((𝒯).map nN) J.subschemeι :=
      IsPullback.of_iso_pullback ⟨by
        rw [Category.assoc, ← pullback.condition,
          Scheme.IdealSheafData.comapIso_hom_fst_assoc]⟩ (J.comapIso ((𝒯).map nN))
        (Scheme.IdealSheafData.comapIso_hom_fst _ _) rfl
    let ε' : (𝒯).obj P' ≅ J'.subscheme := sqε.isoIsPullback _ _ sqJ
    have hε' : (𝒯).map j' = ε'.hom ≫ J'.subschemeι :=
      (IsPullback.isoIsPullback_hom_fst _ _ sqε sqJ).symm
    have hJ' : Stacks.Divisors.IsEffectiveCartierDivisor J' :=
      isPullbackDefined_of_flat ((𝒯).map nN) J hJ
    exact isEffectiveCartierDivisor_range_of_etaleChart_of_ideal e' he' j' hπc J' hJ' ε' hε'

end AlgebraicGeometry.Space

end
