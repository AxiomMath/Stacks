module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraicSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringRestrictionFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.EffectiveOneMemberCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFppfCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Precoverage

/-!
# A sheaf over a scheme which is locally an algebraic space of finite type

Let `F` be an fppf sheaf on the big fppf site of `S` with a morphism `π : F ⟶ h_U` to the presheaf
represented by an object `U` of the site, and suppose that along the members of a flat, locally
finitely presented, jointly surjective family `{g k : W k ⟶ U}` the base changes of `F` are
algebraic spaces of finite type over `W k`. This file proves, from the bootstrap theorem
Stacks 04S6 condition (3), that `F` is an algebraic space, and, without it, that once `F` is an
algebraic space `π` is of finite type. Together they are the second half of the source's proof of
condition (3) of Stacks 04UD: "This follows from Bootstrap, Lemma 0ADV part (2). By Descent on
Spaces, Lemma 041T we see that `X ⟶ U` is of finite type".

## Main results

* `AlgebraicGeometry.SpacesDescent.exists_affine_refinement`: a covering sieve of the big fppf site
  of `S` contains a flat, locally finitely presented, jointly surjective family of affine objects,
  indexed by a type of the working universe of cardinality at most `2 ^ size U`, of members of size
  at most `size U`.
* `AlgebraicGeometry.SpacesDescent.isAlgebraicSpace_of_isPullback_of_isFiniteType`: Stacks 04U0
  over an object of the site.
* `AlgebraicGeometry.SpacesDescent.isFiniteType_of_forall_isPullback`: being of finite type is fppf
  local on the base, along a covering family of schemes.

## Implementation notes

The proof of algebraicity follows Stacks 04U0. The size bounds make the disjoint union `Z` of the
`W k` an object of the site; the base change `F ×_U Z` is the coproduct of the base changes along
the `g k` (`AlgebraicGeometry.Space.nonempty_isColimit_cofanMk_of_isPullback`), which is an
algebraic space by Stacks 02WQ in the form
`AlgebraicGeometry.isAlgebraicSpace_coproduct_of_size_le` because the summands have affine étale
atlases of size at most that of `U`. The projection `F ×_U Z ⟶ F` is a base change of `Z ⟶ U`,
which is surjective, flat and locally of finite presentation, and the bootstrap theorem applies to
it through the one-member covering lemmas
`AlgebraicGeometry.Space.Descent.isRepresentableByAlgebraicSpaces_fibreProj` and
`AlgebraicGeometry.Space.Descent.hasProperty_fibreProj`.

Stacks 04S6 condition (3) is
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`.
Nothing here is registered with a tag.

## References

* [Stacks Project, Tag 04U0](https://stacks.math.columbia.edu/tag/04U0)
* [Stacks Project, Tag 04UD](https://stacks.math.columbia.edu/tag/04UD)
* [Stacks Project, Tag 0ADV](https://stacks.math.columbia.edu/tag/0ADV)
* [Stacks Project, Tag 041U](https://stacks.math.columbia.edu/tag/041U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u v

namespace AlgebraicGeometry.SpacesDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A covering sieve of the big fppf site of `S` is refined by a single surjective, flat,
locally finitely presented morphism out of a disjoint union of affine members of the sieve.** For
every point `x` of `U` an arrow of the sieve and an affine open of its source through a preimage of
`x` is chosen; the affine opens are objects of the site of size at most that of `U`, there are at
most `2 ^ size U` of them, and the cutoff of the site is a strong limit, so their disjoint union is
an object of the site. -/
theorem exists_affine_refinement {U : BigFppfOver B S hS} {R : Sieve U}
    (hR : R ∈ BigFppfOver.topology B S hS U) :
    ∃ (K : Type u) (W : K → BigFppfOver B S hS) (V : K → BigFppfOver B S hS)
      (j : ∀ k, W k ⟶ V k) (f : ∀ k, V k ⟶ U),
      (∀ k, R.arrows (f k)) ∧
      (∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (W k))) ∧
      (∀ k, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j k))) ∧
      (∀ k, Flat ((BigFppfOver.toScheme B S hS).map (j k ≫ f k))) ∧
      (∀ k, LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (j k ≫ f k))) ∧
      (∀ x : (BigFppfOver.toScheme B S hS).obj U, ∃ k,
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (j k ≫ f k))) ∧
      #K ≤ 2 ^ ((BigFppfOver.toScheme B S hS).obj U).size ∧
      (∀ k, ((BigFppfOver.toScheme B S hS).obj (W k)).size ≤
        ((BigFppfOver.toScheme B S hS).obj U).size) := by
  classical
  obtain ⟨I, Wf, m, hmR, hflat, hlfp, hsurj⟩ := exists_family_of_mem_topology B S hS hR
  let V : I → BigFppfOver B S hS := fun i => Over.mk (m i ≫ U.hom)
  let f : ∀ i, V i ⟶ U := fun i => Over.homMk (m i)
  choose ix hix using hsurj
  choose y hy using hix
  have hO : ∀ x, ∃ O : ((BigFppfOver.toScheme B S hS).obj (V (ix x))).Opens,
      IsAffineOpen O ∧ y x ∈ O := by
    intro x
    obtain ⟨O, hO, hyO, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      ((BigFppfOver.toScheme B S hS).obj (V (ix x))).isBasis_affineOpens)
      (show y x ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj (V (ix x))).Opens) from trivial)
    exact ⟨O, hO, hyO⟩
  choose O hOaff hyO using hO
  choose W j hjoi hjrange _ using fun x => exists_restrict_bigFppfOver (V (ix x)) (O x)
  have hWaff : ∀ x, IsAffine ((BigFppfOver.toScheme B S hS).obj (W x)) := by
    intro x
    have := hjoi x
    have h : IsAffineOpen ((BigFppfOver.toScheme B S hS).map (j x)).opensRange := by
      have he : ((BigFppfOver.toScheme B S hS).map (j x)).opensRange = O x :=
        TopologicalSpace.Opens.ext (by rw [Scheme.Hom.coe_opensRange]; exact hjrange x)
      rw [he]
      exact hOaff x
    rw [← Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion] at h
    have : IsAffine (⊤ : ((BigFppfOver.toScheme B S hS).obj (W x)).Opens).toScheme := h
    exact IsAffine.of_isIso (Scheme.topIso _).inv
  have hjflat : ∀ x, Flat ((BigFppfOver.toScheme B S hS).map (j x ≫ f (ix x))) := fun x => by
    have := hjoi x
    rw [Functor.map_comp]
    exact Flat.comp _ _ (hg := hflat _)
  have hjlfp : ∀ x, LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (j x ≫ f (ix x))) := fun x => by
    have := hjoi x
    rw [Functor.map_comp]
    exact locallyOfFinitePresentation_comp _ _ (hg := hlfp _)
  refine ⟨(BigFppfOver.toScheme B S hS).obj U, W, fun x => V (ix x), j, fun x => f (ix x),
    fun x => hmR _, hWaff, hjoi, hjflat, hjlfp, fun x => ⟨x, ?_⟩,
    Scheme.mk_le_two_pow_size _, fun x => ?_⟩
  · obtain ⟨z, hz⟩ : y x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (j x)) := by
      rw [hjrange x]
      exact hyO x
    refine ⟨z, ?_⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply, hz]
    exact hy x
  · have := hWaff x
    have := hjlfp x
    exact Scheme.size_le_of_locallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (j x ≫ f (ix x)))

/-- An affine étale chart `a : h_Y ⟶ X` of an algebraic space `X` locally of finite type over
`h_W`, followed by a locally finitely presented `g : W ⟶ U`, has `size Y ≤ size U`. -/
private theorem size_le_of_isEtale_of_isLocallyOfFiniteType {U W Y : BigFppfOver B S hS}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (a : yoneda.obj Y ⟶ X) (q : X ⟶ yoneda.obj W) (g : W ⟶ U)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)]
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g)]
    (ha : Space.IsEtale B S hS a) (hq : Space.IsLocallyOfFiniteType B S hS q) :
    ((BigFppfOver.toScheme B S hS).obj Y).size ≤ ((BigFppfOver.toScheme B S hS).obj U).size := by
  have hcompose : Space.IsLocallyOfFiniteType B S hS (a ≫ q) :=
    Space.isLocallyOfFiniteType_comp B S hS
      (isAlgebraicSpace_yoneda B S hS Y) hX (isAlgebraicSpace_yoneda B S hS W) a q
      (Space.holdsOnEveryEtaleChart_of_isEtale B S hS
        (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (fun _ hg => have := hg; inferInstance) hX ha)
      hq
  have hgmap : Space.IsLocallyOfFiniteType B S hS (yoneda.map (yoneda.preimage (a ≫ q))) := by
    rwa [Functor.map_preimage]
  have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ q))) :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget (yoneda.preimage (a ≫ q))).1 hgmap
  exact Scheme.size_le_of_locallyOfFiniteType
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ q)) ≫
      (BigFppfOver.toScheme B S hS).map g)

/-- An algebraic space `X` of finite type over an affine `h_W`, with `g : W ⟶ U` locally of finite
presentation, has a surjective étale chart by an affine `Y` with `size Y ≤ size U`. -/
private theorem exists_affine_etale_cover_size_le {U W : BigFppfOver B S hS}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (q : X ⟶ yoneda.obj W) (g : W ⟶ U) [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g)]
    (hq : Space.IsFiniteType B S hS q) :
    ∃ (Y : BigFppfOver B S hS) (a : yoneda.obj Y ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Y) ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      Space.IsEtale B S hS a ∧
      ((BigFppfOver.toScheme B S hS).obj Y).size ≤
        ((BigFppfOver.toScheme B S hS).obj U).size := by
  obtain ⟨Y, a, hY, hsurj, het⟩ :=
    (Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X hX).1
      (Space.isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 (yoneda.obj W)) q))
        (hq.2 _ (isAlgebraicSpace_yoneda B S hS W)
          (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS W inferInstance) (𝟙 _)))
  have := hY
  exact ⟨Y, a, hY, hsurj, het, size_le_of_isEtale_of_isLocallyOfFiniteType hX a q g het hq.1⟩

/-- The base change `F ×_U Z` of a sheaf `F` along the map `v : Z ⟶ U` out of a disjoint union `Z`
of affine objects `W k` is an algebraic space when every base change of `F` along `W k ⟶ U` is an
algebraic space of finite type over `W k`. -/
private theorem isAlgebraicSpace_pullback_of_isColimit_cofan
    {U : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (π : F ⟶ yoneda.obj U)
    {K : Type u} (W : K → BigFppfOver B S hS) (g : ∀ k, W k ⟶ U)
    (hWaff : ∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (W k)))
    (hlfp : ∀ k, LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (g k)))
    {μ : Cardinal.{u}} (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff) (hK : #K ≤ μ)
    (hUμ : ((BigFppfOver.toScheme B S hS).obj U).size ≤ μ)
    {Z : BigFppfOver B S hS} {c : ∀ k, W k ⟶ Z} (hZ : IsColimit (Cofan.mk Z c)) (v : Z ⟶ U)
    (hcv : ∀ k, c k ≫ v = g k)
    (X : K → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : ∀ k, IsAlgebraicSpace B S hS (X k))
    (ζ : ∀ k, X k ⟶ F) (q : ∀ k, X k ⟶ yoneda.obj (W k))
    (hsq : ∀ k, IsPullback (ζ k) (q k) π (yoneda.map (g k)))
    (hft : ∀ k, Space.IsFiniteType B S hS (q k)) :
    IsAlgebraicSpace B S hS (pullback π (yoneda.map v)) := by
  classical
  let J := BigFppfOver.topology B S hS
  obtain ⟨hZs⟩ := nonempty_isColimit_cofan_toScheme (B := B) (S := S) (hS := hS) hZ
  let hZy := Space.isColimit_yoneda_of_isColimit_toScheme B S hS W Z c hZs
  have hGsh : Presheaf.IsSheaf J (pullback π (yoneda.map v)) :=
    Presheaf.isSheaf_pullback _ π (yoneda.map v) hF (isAlgebraicSpace_yoneda B S hS Z).isSheaf
      (isAlgebraicSpace_yoneda B S hS U).isSheaf
  let p : ∀ k, X k ⟶ pullback π (yoneda.map v) := fun k =>
    pullback.lift (ζ k) (q k ≫ yoneda.map (c k)) (by
      rw [Category.assoc, ← Functor.map_comp, hcv]
      exact (hsq k).w)
  have hpb : ∀ k, IsPullback (p k) (q k) (pullback.snd π (yoneda.map v)) (yoneda.map (c k)) := by
    intro k
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback π _)
    rw [pullback.lift_fst, ← Functor.map_comp, hcv]
    exact hsq k
  let Gsh : Sheaf J (Type u) := ⟨pullback π (yoneda.map v), hGsh⟩
  have hGcolim : Nonempty (IsColimit (Cofan.mk Gsh
      (fun k => (⟨p k⟩ : (⟨X k, (hX k).isSheaf⟩ : Sheaf J (Type u)) ⟶ Gsh)))) :=
    Space.nonempty_isColimit_cofanMk_of_isPullback B S hS
      (fun k => J.yoneda.map (c k)) hZy (⟨pullback.snd π (yoneda.map v)⟩ : Gsh ⟶ J.yoneda.obj Z)
      (fun k => (⟨p k⟩ : (⟨X k, (hX k).isSheaf⟩ : Sheaf J (Type u)) ⟶ Gsh))
      (fun k => (⟨q k⟩ : (⟨X k, (hX k).isSheaf⟩ : Sheaf J (Type u)) ⟶ J.yoneda.obj (W k)))
      (fun k => IsPullback.of_map_of_faithful (sheafToPresheaf J (Type u)) (hpb k))
  choose Y a hYaff hYsurj hYetale hYsize using fun k =>
    have := hWaff k
    have := hlfp k
    exists_affine_etale_cover_size_le (hX k) (q k) (g k) (hft k)
  exact isAlgebraicSpace_coproduct_of_size_le B S hS X hX Gsh
    (fun k => (⟨p k⟩ : (⟨X k, (hX k).isSheaf⟩ : Sheaf J (Type u)) ⟶ Gsh)) hGcolim.some
    Y a hYsurj (fun k => (Space.isEtale_iff_presheaf_of_yoneda B S hS (a k)).1 (hYetale k))
    (Equiv.refl K) hℵ hμ hK fun k => (hYsize k).trans hUμ

/-- **Stacks 04U0 over an object of the site.** Let `F` be a sheaf with a morphism
`π : F ⟶ h_U`, and let `{g k : W k ⟶ U}` be a family of morphisms out of affine objects of the site
which is flat, locally of finite presentation and jointly surjective, indexed by a type of the
working universe and of uniformly bounded size. If every base change of `F` along `g k` is an
algebraic space of finite type over `W k`, then `F` is an algebraic space.

The disjoint union `Z` of the `W k` is an object of the site, and the base change `F ×_U Z` is the
coproduct of the base changes of `F` along the `g k`. Each summand is quasi-compact, being of finite
type over an affine scheme, so it has an affine étale atlas, of size bounded by that of `U`; so the
coproduct is an algebraic space by Stacks 02WQ. The projection `F ×_U Z ⟶ F` is a base change of
the surjective, flat, locally finitely presented `Z ⟶ U`, and Stacks 04S6 condition (3)
concludes. -/
theorem isAlgebraicSpace_of_isPullback_of_isFiniteType
    {U : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (π : F ⟶ yoneda.obj U)
    {K : Type u} (W : K → BigFppfOver B S hS) (g : ∀ k, W k ⟶ U)
    (hWaff : ∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (W k)))
    (hflat : ∀ k, Flat ((BigFppfOver.toScheme B S hS).map (g k)))
    (hlfp : ∀ k, LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (g k)))
    (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj U, ∃ k,
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g k)))
    {μ : Cardinal.{u}} (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff) (hK : #K ≤ μ)
    (hUμ : ((BigFppfOver.toScheme B S hS).obj U).size ≤ μ)
    (hWμ : ∀ k, ((BigFppfOver.toScheme B S hS).obj (W k)).size ≤ μ)
    (X : K → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : ∀ k, IsAlgebraicSpace B S hS (X k))
    (ζ : ∀ k, X k ⟶ F) (q : ∀ k, X k ⟶ yoneda.obj (W k))
    (hsq : ∀ k, IsPullback (ζ k) (q k) π (yoneda.map (g k)))
    (hft : ∀ k, Space.IsFiniteType B S hS (q k)) :
    IsAlgebraicSpace B S hS F := by
  classical
  obtain ⟨Z, c, ⟨hZ⟩⟩ := BigFppfOver.exists_isColimit_cofan_of_size_le B S hS W hℵ hμ hK hWμ
  set v : Z ⟶ U := Cofan.IsColimit.desc hZ g
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hZa : IsAlgebraicSpace B S hS (yoneda.obj Z) := isAlgebraicSpace_yoneda B S hS Z
  have hGalg : IsAlgebraicSpace B S hS (pullback π (yoneda.map v)) :=
    isAlgebraicSpace_pullback_of_isColimit_cofan hF π W g hWaff hlfp hℵ hμ hK hUμ hZ v
      (Cofan.IsColimit.fac hZ g) X hX ζ q hsq hft
  obtain ⟨⟨hvsurj, hvflat⟩, hvlfp⟩ :=
    surjective_inf_flat_inf_locallyOfFinitePresentation_desc hZ g hflat hlfp hsurj
  let f₁ : Unit → (yoneda.obj Z ⟶ yoneda.obj U) := fun _ => yoneda.map v
  have hcov : Space.IsFppfCovering B S hS (fun _ : Unit => yoneda.obj Z) f₁ :=
    Space.isFppfCovering_yoneda_map B S hS (fun _ : Unit => Z) (fun _ => v)
      (fun _ => hvflat) (fun _ => hvlfp) fun x => ⟨(), hvsurj.surj x⟩
  let Fsh : Space.Descent.SheavesWithSpaceFibres f₁ := ⟨Over.mk π, hF, fun _ => hGalg⟩
  exact Space.isBootstrapAlgebraicSpaceAlongFlatSurjection B S hS (pullback.fst π (yoneda.map v))
    hF hGalg
    (Space.Descent.isRepresentableByAlgebraicSpaces_fibreProj f₁ hU (fun _ => hZa) Fsh ())
    (Space.Descent.hasProperty_fibreProj f₁ hU (fun _ => hZa)
      (Space.surjectiveMorphismProperty B S hS) Fsh ()
      (Space.isSurjective_yoneda_map B S hS v hvsurj))
    (Space.Descent.hasProperty_fibreProj f₁ hU (fun _ => hZa) (Space.flatProperty B S hS) Fsh ()
      (hcov.flat ()))
    (Space.Descent.hasProperty_fibreProj f₁ hU (fun _ => hZa)
      (Space.locallyOfFinitePresentationProperty B S hS) Fsh ()
      (hcov.locallyOfFinitePresentation ()))

/-- **Being of finite type is fppf local on the base, read along a covering family of schemes.**
A morphism `π : F ⟶ h_U` of algebraic spaces whose base changes along the members of a flat,
locally finitely presented, jointly surjective family `{g k : W k ⟶ U}` are of finite type is of
finite type. This is Stacks 041U for an fppf covering, through Stacks 041M and Stacks 041L. -/
theorem isFiniteType_of_forall_isPullback {U : BigFppfOver B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (π : F ⟶ yoneda.obj U) {K : Type v} (W : K → BigFppfOver B S hS) (g : ∀ k, W k ⟶ U)
    (hflat : ∀ k, Flat ((BigFppfOver.toScheme B S hS).map (g k)))
    (hlfp : ∀ k, LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (g k)))
    (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj U, ∃ k,
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g k)))
    (X : K → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : ∀ k, IsAlgebraicSpace B S hS (X k))
    (ζ : ∀ k, X k ⟶ F) (q : ∀ k, X k ⟶ yoneda.obj (W k))
    (hsq : ∀ k, IsPullback (ζ k) (q k) π (yoneda.map (g k)))
    (hft : ∀ k, Space.IsFiniteType B S hS (q k)) :
    Space.IsFiniteType B S hS π := by
  have hlft : (Space.locallyOfFiniteTypeProperty B S hS).IsLocalAtTarget
      (Space.Topology.precoverage.{u, v} .fppf B S hS) :=
    (Space.isLocallyOfFiniteType_isLocalAtTarget_fpqc.{u, v} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, v} B S hS)
  have hqc : (Space.quasiCompactProperty B S hS).IsLocalAtTarget
      (Space.Topology.precoverage.{u, v} .fppf B S hS) :=
    Space.isQuasiCompact_isLocalAtTarget_fppf B S hS
  have := Space.finiteTypeProperty_isLocalAtTarget B S hS hlft hqc
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  let Ya : AlgebraicSpaces B S hS := ⟨yoneda.obj U, hU⟩
  let Fa : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let Wa : K → AlgebraicSpaces B S hS := fun k =>
    ⟨yoneda.obj (W k), isAlgebraicSpace_yoneda B S hS (W k)⟩
  let ga : ∀ k, Wa k ⟶ Ya := fun k => ObjectProperty.homMk (yoneda.map (g k))
  have hR : Presieve.ofArrows Wa ga ∈
      (Space.Topology.precoverage.{u, v} .fppf B S hS).coverings Ya :=
    ⟨K, Wa, ga, rfl, hU, fun k => isAlgebraicSpace_yoneda B S hS (W k),
      Space.isFppfCovering_yoneda_map B S hS W g hflat hlfp hsurj⟩
  refine (MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd
    (P := Space.finiteTypeProperty B S hS) hR (f := (ObjectProperty.homMk π : Fa ⟶ Ya))).2 ?_
  rintro Uo h _ ⟨k⟩
  have h₂ : IsPullback (ObjectProperty.homMk (ζ k) : (⟨X k, hX k⟩ : AlgebraicSpaces B S hS) ⟶ Fa)
      (ObjectProperty.homMk (q k)) (ObjectProperty.homMk π : Fa ⟶ Ya) (ga k) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) (hsq k)
  let e := h₂.isoIsPullback _ _
    (IsPullback.of_hasPullback (ObjectProperty.homMk π : Fa ⟶ Ya) (ga k))
  refine (MorphismProperty.cancel_left_of_respectsIso (Space.finiteTypeProperty B S hS)
    e.hom _).1 ?_
  rw [IsPullback.isoIsPullback_hom_snd]
  exact hft k

/-- A base change of a morphism of finite type between algebraic spaces is of finite type, for a
cartesian square of presheaves: Stacks 03XH, read without passing to the category of algebraic
spaces. -/
theorem isFiniteType_of_isPullback_of_isFiniteType {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hF' : IsAlgebraicSpace B S hS F') (hG' : IsAlgebraicSpace B S hS G')
    {a : F ⟶ F'} {b : F ⟶ G} {p : F' ⟶ G'} {q : G ⟶ G'}
    (sq : IsPullback a b p q) (hp : Space.IsFiniteType B S hS p) :
    Space.IsFiniteType B S hS b := by
  have sq' : IsPullback
      (ObjectProperty.homMk a : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F', hF'⟩)
      (ObjectProperty.homMk b : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
      (ObjectProperty.homMk p : (⟨F', hF'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G', hG'⟩)
      (ObjectProperty.homMk q : (⟨G, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G', hG'⟩) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) sq
  exact ⟨(Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback sq' hp.1,
    Space.isQuasiCompact_of_isPullback B S hS sq hp.2⟩

end AlgebraicGeometry.SpacesDescent

end
