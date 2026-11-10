module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.PurelyInseparableDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.BaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.EtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.FppfSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-!
# Finite open unions as étale charts of the finite part

Auxiliary results for the étale chart of the finite part `(X/Y)_fin` of a separated, locally
quasi-finite morphism (Stacks 04QG), assembled in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.EtaleCover`: the base change of
the finite part (Stacks 04QF), open subspaces finite over a representable base as sections of the
finite part, open immersions out of coproducts of opens, étale neighbourhoods of points inside
the big fppf site, cardinality bounds that cut the index set of the chart down to the site's
cardinal bound, sections of the finite part over a coproduct in the site (Stacks 04PE), and the
étale morphism to the finite part given by a finite union of opens finite over the base
(Stacks 04QE).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FinitePartChart

attribute [local instance] Stacks.Morphisms.isFinite_isZariskiLocalAtTarget
  Stacks.Morphisms.isFinite_respectsIso

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_FiniteOpenUnion
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The comparison morphism of finite parts attached to a cartesian square of algebraic spaces
exhibits the square of finite parts as cartesian, which is Stacks 04QF in existential form. -/
theorem exists_isPullback_finitePart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X Y' Y : AlgebraicSpaces B S hS}
    (f' : X' ⟶ X) (g' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (h : IsPullback f' g' f g) :
    ∃ φ : (Space.finiteOpenSubspacePresheaf B S hS g').toFunctor ⟶
        (Space.finiteOpenSubspacePresheaf B S hS f).toFunctor,
      IsPullback φ (Space.finiteOpenSubspacePresheaf B S hS g').baseMap
        (Space.finiteOpenSubspacePresheaf B S hS f).baseMap g.hom :=
  ⟨Space.FinitePartPresheaf.mapOfPullbackSquare B S hS f' g' f g h _ _,
    Space.FinitePartPresheaf.isPullback_mapOfPullbackSquare
      B S hS f' g' f g h _ _⟩

attribute [local instance] schemeSizeBelow_isClosedUnderIsomorphisms
  schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan
  BigFppfSite.hasPullbacks_schemes
  Space.preservesLimitsOfShape_walkingCospan_toScheme

/-- If `P` is a morphism property of schemes stable under base change and `f : U ⟶ V` is a
morphism of the big fppf site over `S` whose underlying morphism of schemes satisfies `P`,
then the morphism of representable presheaves `yoneda.map f` is relatively representable with
the property `P`. -/
theorem presheaf_yoneda_map
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (hf : P ((BigFppfOver.toScheme B S hS).map f)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map f) := by
  let Q := P.inverseImage (BigFppfOver.toScheme B S hS)
  have : Q.IsStableUnderBaseChange := ⟨fun sq hg ↦
    P.of_isPullback (sq.map (BigFppfOver.toScheme B S hS)) hg⟩
  exact MorphismProperty.relative_map hf

private theorem isFinite_of_presheaf_isFinite
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    Space.IsFinite B S hS f := by
  intro U hU ξ
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  let V := hf.rep.pullback ξ
  let p : V ⟶ U := hf.rep.snd ξ
  have hp : IsFinite ((BigFppfOver.toScheme B S hS).map p) :=
    hf.property_snd ξ
  exact ⟨V, p, hf.rep.fst ξ, isAffine_of_isAffineHom
    ((BigFppfOver.toScheme B S hS).map p), hp, hf.rep.isPullback ξ⟩

private theorem exists_finiteOpenSubspace_of_represented_open
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (U W : BigFppfOver B S hS)
    (a : schemeSpace U ⟶ Y)
    (j : yoneda.obj W ⟶ pullback a.hom f.hom) (hmono : Mono j)
    (hj : Space.IsOpenImmersion B S hS j)
    (hfin : (MorphismProperty.inverseImage (@IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (j ≫ pullback.fst a.hom f.hom)) :
    ∃ p : Space.FiniteOpenSubspace B S hS f (schemeSpace U),
      p.toBase = a ∧ HEq p.subspace (Subfunctor.range j) := by
  let Z := Subfunctor.range j
  have hZ : IsAlgebraicSpace B S hS Z.toFunctor :=
    AlgebraicGeometry.Space.isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange j))
      (isAlgebraicSpace_yoneda B S hS W)
  have hopen : Space.IsOpenImmersion B S hS Z.ι :=
    (MorphismProperty.cancel_left_of_respectsIso (P := (MorphismProperty.inverseImage
      (@IsOpenImmersion.{u}) (BigFppfOver.toScheme B S hS)).presheaf)
      (Subfunctor.toRange j) _).mp (by simpa [Z] using hj)
  have hfinite : (MorphismProperty.inverseImage (@IsFinite.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (Z.ι ≫ pullback.fst a.hom f.hom) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := (MorphismProperty.inverseImage
      (@IsFinite.{u}) (BigFppfOver.toScheme B S hS)).presheaf)
      (Subfunctor.toRange j) _).mp (by simpa [← Category.assoc, Z] using hfin)
  exact ⟨⟨a, Z, ⟨hZ, hopen⟩, isFinite_of_presheaf_isFinite B S hS _ hfinite⟩, rfl, HEq.rfl⟩

private theorem finiteOpenSubspace_ext
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {p q : Space.FiniteOpenSubspace B S hS f T}
    (ha : p.toBase = q.toBase) (hZ : HEq p.subspace q.subspace) : p = q := by
  cases p
  cases q
  cases ha
  cases hZ
  rfl

private theorem finiteOpenSubspace_eq_of_isBaseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (p : Space.FiniteOpenSubspace B S hS f (schemeSpace T))
    (q r : Space.FiniteOpenSubspace B S hS f (schemeSpace T'))
    (hq : Space.FiniteOpenSubspace.IsBaseChange B S hS f h p q)
    (hr : Space.FiniteOpenSubspace.IsBaseChange B S hS f h p r) : q = r := by
  rcases q with ⟨a, Q, hQopen, hQfin⟩
  rcases r with ⟨b, R, hRopen, hRfin⟩
  obtain rfl : a = b := ObjectProperty.hom_ext _ (hq.1.trans hr.1.symm)
  obtain ⟨_, jQ, sqQ, hjQ⟩ := hq
  obtain ⟨_, jR, sqR, hjR⟩ := hr
  let e := sqQ.isoIsPullback _ _ sqR
  have hι : e.hom ≫ R.ι = Q.ι := by
    apply pullback.hom_ext
    · exact sqQ.isoIsPullback_hom_fst _ _ sqR
    · rw [Category.assoc, ← hjR, ← Category.assoc, ← Category.assoc,
        show e.hom ≫ jR = jQ from sqQ.isoIsPullback_hom_snd _ _ sqR]
      exact hjQ
  have : Epi e.hom := @IsIso.epi_of_iso _ _ _ _ e.hom (Iso.isIso_hom e)
  have hQR : Q = R := by
    rw [← Subfunctor.range_ι Q, ← hι, Subfunctor.range_comp,
      Subfunctor.range_eq_top, Subfunctor.image_top, Subfunctor.range_ι]
  exact finiteOpenSubspace_ext B S hS rfl (hQR ▸ HEq.rfl)

theorem finitePart_map_sections_eq_of_isBaseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (p : (Space.finiteOpenSubspacePresheaf B S hS f).toFunctor.obj (.op T))
    (q : Space.FiniteOpenSubspace B S hS f (schemeSpace T'))
    (hq : Space.FiniteOpenSubspace.IsBaseChange B S hS f h
      ((Space.finiteOpenSubspacePresheaf B S hS f).sections T p) q) :
    (Space.finiteOpenSubspacePresheaf B S hS f).sections T'
      ((Space.finiteOpenSubspacePresheaf B S hS f).toFunctor.map h.op p) = q :=
  finiteOpenSubspace_eq_of_isBaseChange B S hS h _ _ _
    ((Space.finiteOpenSubspacePresheaf B S hS f).map_isBaseChange h p) hq

theorem exists_finite_representation_of_affine_base
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (z : Space.FiniteOpenSubspace B S hS f (schemeSpace T)) :
    ∃ (W : BigFppfOver B S hS) (p : W ⟶ T)
      (e : yoneda.obj W ≅ z.subspace.toFunctor),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
      IsFinite ((BigFppfOver.toScheme B S hS).map p) ∧
      e.hom ≫ z.subspace.ι ≫ pullback.fst z.toBase.hom f.hom = yoneda.map p ∧
      Space.IsOpenImmersion B S hS (e.hom ≫ z.subspace.ι) := by
  let ξ : yoneda.obj T ⟶ (schemeSpace T).obj := 𝟙 (yoneda.obj T)
  have hξ : IsIso ξ := inferInstanceAs (IsIso (𝟙 (yoneda.obj T)))
  obtain ⟨W, p, i, hW, hp, sq⟩ := z.finite_projection T hT ξ
  have : IsIso i := sq.isIso_fst_of_isIso hξ
  exact ⟨W, p, asIso i, hW, hp, by
    have hw : i ≫ z.subspace.ι ≫ pullback.fst z.toBase.hom f.hom =
        yoneda.map p ≫ (𝟙 (yoneda.obj T)) := sq.w
    exact hw.trans (Category.comp_id _),
    MorphismProperty.RespectsIso.precomp _ _ _ z.isOpen.2⟩

private theorem exists_etale_map_of_finiteOpenSubspace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (U : BigFppfOver B S hS)
    (z : Space.FiniteOpenSubspace B S hS f (schemeSpace U))
    (hz : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf z.toBase.hom) :
    ∃ p : yoneda.obj U ⟶ (Space.finiteOpenSubspacePresheaf B S hS f).toFunctor,
      p ≫ (Space.finiteOpenSubspacePresheaf B S hS f).baseMap = z.toBase.hom ∧
      (Space.finiteOpenSubspacePresheaf B S hS f).sections U (yonedaEquiv p) = z ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p := by
  let F := Space.finiteOpenSubspacePresheaf B S hS f
  let t := (F.sections U).symm z
  let p : yoneda.obj U ⟶ F.toFunctor := yonedaEquiv.symm t
  have hsec : F.sections U t = z := (F.sections U).apply_symm_apply z
  have hbase := F.baseMap_spec U t
  rw [hsec] at hbase
  have hp : p ≫ F.baseMap = z.toBase.hom := by
    apply yonedaEquiv.injective
    simpa [p, yonedaEquiv_comp] using congrArg yonedaEquiv hbase
  exact ⟨p, hp, by simp [p, t, F], Space.isEtale_of_isEtale_comp_baseMap
    B S hS f U p (hp.symm ▸ hz)⟩

theorem isOpenImmersion_sigmaDesc_opens
    {T : Scheme.{u}} {ι : Type u} (D : ι → T.Opens)
    (hD : Pairwise (fun i j ↦ Disjoint (D i) (D j))) :
    IsOpenImmersion (Sigma.desc fun i ↦ (D i).ι) := by
  apply isOpenImmersion_sigmaDesc
  intro i j hij
  simpa using hD hij

private theorem finite_open_union
    {T U : Scheme.{u}} (g : T ⟶ U) {ι : Type u} [Finite ι]
    (D : ι → T.Opens)
    (hD : Pairwise (fun i j ↦ Disjoint (D i) (D j)))
    (hfin : ∀ i, IsFinite ((D i).ι ≫ g)) :
    IsOpenImmersion (Sigma.desc fun i ↦ (D i).ι) ∧
      IsFinite ((Sigma.desc fun i ↦ (D i).ι) ≫ g) := by
  refine ⟨isOpenImmersion_sigmaDesc_opens D hD, ?_⟩
  have heq : (Sigma.desc fun i ↦ (D i).ι) ≫ g =
      Sigma.desc (fun i ↦ (D i).ι ≫ g) := by
    ext i
    simp
  rw [heq]
  let (i : ι) : IsFinite ((D i).ι ≫ g) := hfin i
  exact AlgebraicGeometry.isFinite_sigmaDesc

private theorem exists_finiteOpenSubspace_of_scheme_open
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y U W : BigFppfOver B S hS} (f : X ⟶ Y) (a : U ⟶ Y)
    (j : W ⟶ pullback a f)
    (hj : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j))
    (hf : IsFinite ((BigFppfOver.toScheme B S hS).map
      (j ≫ pullback.fst a f))) :
    ∃ p : Space.FiniteOpenSubspace B S hS (schemeSpaceMap f)
        (schemeSpace U),
      p.toBase = schemeSpaceMap a ∧
        HEq p.subspace (Subfunctor.range
          (yoneda.map j ≫ ((IsPullback.of_hasPullback a f).map yoneda).isoPullback.hom)) := by
  let q := BigFppfOver.toScheme B S hS
  let e := ((IsPullback.of_hasPullback a f).map yoneda).isoPullback
  let j' : yoneda.obj W ⟶ pullback (yoneda.map a) (yoneda.map f) := yoneda.map j ≫ e.hom
  have : IsOpenImmersion (q.map j) := hj
  have : Mono j := q.mono_of_mono_map inferInstance
  have : Mono e.hom := @IsIso.mono_of_iso _ _ _ _ e.hom (Iso.isIso_hom e)
  have hjmono : Mono j' := mono_comp _ _
  have hj' : Space.IsOpenImmersion B S hS j' :=
    MorphismProperty.RespectsIso.postcomp _ e.hom (yoneda.map j)
      (presheaf_yoneda_map B S hS _ j hj)
  have hfin' : (MorphismProperty.inverseImage (@IsFinite.{u}) q).presheaf
      (j' ≫ pullback.fst (yoneda.map a) (yoneda.map f)) := by
    have heq : j' ≫ pullback.fst (yoneda.map a) (yoneda.map f) =
        yoneda.map (j ≫ pullback.fst a f) := by
      simp [j', e, Category.assoc]
    rw [heq]
    exact presheaf_yoneda_map B S hS _ _ hf
  exact exists_finiteOpenSubspace_of_represented_open B S hS
    (schemeSpaceMap f) U W (schemeSpaceMap a) j' hjmono hj' hfin'

private theorem mem_range_sigma_ι_iff
    {I : Type u} (X : I → Scheme.{u}) (i j : I) (x : X j) :
    Sigma.ι X j x ∈ Set.range (Sigma.ι X i) ↔ j = i := by
  constructor
  · rintro ⟨y, hy⟩
    exact (congrArg Sigma.fst ((sigmaι_eq_iff X i j y x).mp hy)).symm
  · rintro rfl
    exact ⟨x, rfl⟩

private theorem isPullback_sigma_desc
    {I : Type u} {X Y : I → Scheme.{u}} (f : ∀ i, X i ⟶ Y i) (i : I) :
    IsPullback (f i) (Sigma.ι X i) (Sigma.ι Y i)
      (Sigma.desc (fun j ↦ f j ≫ Sigma.ι Y j)) := by
  apply IsOpenImmersion.isPullback
  · simp
  · ext z
    obtain ⟨⟨j, x⟩, rfl⟩ := (sigmaMk X).surjective z
    simp only [sigmaMk_mk]
    change (Sigma.desc (fun j ↦ f j ≫ Sigma.ι Y j)) (Sigma.ι X j x) ∈
      Set.range (Sigma.ι Y i) ↔ Sigma.ι X j x ∈ Set.range (Sigma.ι X i)
    have hcomp : (Sigma.desc (fun j ↦ f j ≫ Sigma.ι Y j)) (Sigma.ι X j x) =
        Sigma.ι Y j (f j x) := by
      change (Sigma.ι X j ≫ Sigma.desc (fun j ↦ f j ≫ Sigma.ι Y j)) x = _
      rw [Sigma.ι_comp_desc]
      rfl
    rw [hcomp, mem_range_sigma_ι_iff, mem_range_sigma_ι_iff]

private theorem isFinite_sigma_desc_to_sigma
    {I : Type u} {X Y : I → Scheme.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, IsFinite (f i)) :
    IsFinite (Sigma.desc (fun i ↦ f i ≫ Sigma.ι Y i)) := by
  let g := Sigma.desc (fun i ↦ f i ≫ Sigma.ι Y i)
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite.{u})
    (f := g) (sigmaOpenCover Y)).mpr
  intro i
  change IsFinite (pullback.snd g (Sigma.ι Y i))
  let sq := (isPullback_sigma_desc f i).flip
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) sq.isoPullback.hom]
  simpa [g, sq] using hf i

private theorem exists_affine_etale_neighborhood_of_point
    {U Y : Scheme.{u}} (a : U ⟶ Y) [Etale a] (u : U) :
    ∃ (V : Scheme.{u}) (j : V ⟶ U) (v : V),
      IsAffine V ∧ IsOpenImmersion j ∧ j v = u ∧
        Etale (j ≫ a) ∧ V.size ≤ Y.size := by
  obtain ⟨v, hv⟩ := U.affineCover.covers u
  exact ⟨_, U.affineCover.f _, v, inferInstance, inferInstance, hv, inferInstance,
    Scheme.size_le_of_locallyOfFiniteType (U.affineCover.f _ ≫ a)⟩

private theorem exists_site_etale_neighborhood_of_point
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Y : BigFppfOver B S hS)
    {U : Scheme.{u}} (a : U ⟶ (BigFppfOver.toScheme B S hS).obj Y)
    [Etale a] (u : U) :
    ∃ (V : BigFppfOver B S hS)
      (j : (BigFppfOver.toScheme B S hS).obj V ⟶ U)
      (b : V ⟶ Y) (v : (BigFppfOver.toScheme B S hS).obj V),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      IsOpenImmersion j ∧ j v = u ∧
      j ≫ a = (BigFppfOver.toScheme B S hS).map b ∧
      Etale ((BigFppfOver.toScheme B S hS).map b) ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤
        ((BigFppfOver.toScheme B S hS).obj Y).size := by
  obtain ⟨V, j, v, hVaff, hj, hv, ha, hsize⟩ :=
    exists_affine_etale_neighborhood_of_point a u
  have hV : B.Contains V := hsize.trans_lt Y.left.property
  let V' : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk ((j ≫ a) ≫ Y.hom.hom) : B.obj hV ⟶ B.obj hS)
  let b : V' ⟶ Y := Over.homMk (ObjectProperty.homMk (j ≫ a)) (by rfl)
  exact ⟨V', j, b, v, hVaff, hj, hv, rfl, ha, hsize⟩

theorem exists_site_pullback_neighborhood
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : BigFppfOver B S hS} (f : X ⟶ Y)
    {U : Scheme.{u}} (a : U ⟶ (BigFppfOver.toScheme B S hS).obj Y)
    [Etale a] (u : U) :
    ∃ (V : BigFppfOver B S hS) (b : V ⟶ Y)
      (j : (BigFppfOver.toScheme B S hS).obj V ⟶ U)
      (v : (BigFppfOver.toScheme B S hS).obj V)
      (k : (BigFppfOver.toScheme B S hS).obj (pullback b f) ⟶
        pullback ((BigFppfOver.toScheme B S hS).map f) a),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      IsOpenImmersion j ∧ j v = u ∧
      j ≫ a = (BigFppfOver.toScheme B S hS).map b ∧
      Etale ((BigFppfOver.toScheme B S hS).map b) ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤
        ((BigFppfOver.toScheme B S hS).obj Y).size ∧
      k ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map f) a =
        (BigFppfOver.toScheme B S hS).map (pullback.snd b f) ∧
      IsPullback k ((BigFppfOver.toScheme B S hS).map (pullback.fst b f))
        (pullback.snd ((BigFppfOver.toScheme B S hS).map f) a) j := by
  let q := BigFppfOver.toScheme B S hS
  obtain ⟨V, j, b, v, hV, hj, hv, ha, hb, hsize⟩ :=
    exists_site_etale_neighborhood_of_point B S hS Y a u
  have hpb := (IsPullback.of_hasPullback b f).map q
  let k : q.obj (pullback b f) ⟶ pullback (q.map f) a :=
    pullback.lift (q.map (pullback.snd b f)) (q.map (pullback.fst b f) ≫ j) (by
      rw [Category.assoc, ha]
      exact hpb.w.symm)
  have hkfst : k ≫ pullback.fst (q.map f) a = q.map (pullback.snd b f) :=
    pullback.lift_fst _ _ _
  have hksnd : k ≫ pullback.snd (q.map f) a = q.map (pullback.fst b f) ≫ j :=
    pullback.lift_snd _ _ _
  refine ⟨V, b, j, v, k, hV, hj, hv, ha, hb, hsize, hkfst, ?_⟩
  apply IsPullback.of_right _ hksnd (IsPullback.of_hasPullback (q.map f) a)
  rw [hkfst, ha]
  exact hpb.flip

theorem exists_lift_of_subsingleton_of_mem_range
    {T U V : Scheme.{u}} [Subsingleton T] (b : T ⟶ U) (j : V ⟶ U)
    [IsOpenImmersion j] (t : T) (v : V) (hv : j v = b t) :
    ∃ l : T ⟶ V, l ≫ j = b ∧ l t = v := by
  have hmem : Set.range b ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    exact ⟨v, hv.trans (congrArg b (Subsingleton.elim t x))⟩
  refine ⟨IsOpenImmersion.lift j b hmem, IsOpenImmersion.lift_fac j b hmem, ?_⟩
  apply j.injective
  change (IsOpenImmersion.lift j b hmem ≫ j) t = j v
  rw [IsOpenImmersion.lift_fac, hv]

private theorem cardinal_mk_scheme_le_power_size (X : Scheme.{u}) :
    Cardinal.mk X ≤ 2 ^ X.size := by
  let g : X → Set X.affineOpens := fun x ↦ {U | x ∈ U.1}
  have hg : Function.Injective g := by
    intro x y h
    apply X.isBasis_affineOpens.eq_iff.mpr
    rintro V ⟨U, hU, rfl⟩
    exact Set.ext_iff.mp h ⟨U, hU⟩
  calc
    Cardinal.mk X ≤ Cardinal.mk (Set X.affineOpens) := Cardinal.mk_le_of_injective hg
    _ = 2 ^ Cardinal.mk X.affineOpens := Cardinal.mk_set
    _ ≤ 2 ^ X.size := Cardinal.power_le_power_left (by norm_num) X.mk_affineOpens_le_size

private theorem cardinal_mk_finset_le_max_aleph0 (A : Type u) :
    Cardinal.mk (Finset A) ≤ max Cardinal.aleph0 (Cardinal.mk A) := by
  cases finite_or_infinite A with
  | inl h => exact (Cardinal.lt_aleph0_of_finite _).le.trans (le_max_left _ _)
  | inr h => exact (Cardinal.mk_finset_of_infinite A).le.trans (le_max_right _ _)

private theorem cardinal_mk_sigma_finite_le
    (A : Type u) (C : A → Type u) [∀ a, Finite (C a)]
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hA : Cardinal.mk A ≤ κ) : Cardinal.mk (Σ a, C a) ≤ κ := by
  calc
    Cardinal.mk (Σ a, C a) = Cardinal.sum (fun a ↦ Cardinal.mk (C a)) :=
      Cardinal.mk_sigma C
    _ ≤ Cardinal.mk A * ⨆ a, Cardinal.mk (C a) :=
      Cardinal.sum_le_mk_mul_iSup _
    _ ≤ κ * κ :=
      mul_le_mul' hA (ciSup_le' fun a ↦ (Cardinal.lt_aleph0_of_finite (C a)).le.trans hκ)
    _ = κ := Cardinal.mul_eq_self hκ

theorem cardinal_mk_finite_piece_choices_le
    (A : Type u) (I : A → Type u) [∀ a, Finite (I a)]
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hA : Cardinal.mk A ≤ κ) :
    Cardinal.mk (Σ a, Set (I a)) ≤ κ := by
  let (a : A) : Finite (Set (I a)) := inferInstance
  exact cardinal_mk_sigma_finite_le A (fun a ↦ Set (I a)) κ hκ hA

private theorem cardinal_mk_finite_fiber_subsets_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 ≤ κ) (hX : Cardinal.mk X ≤ κ) (hY : Cardinal.mk Y ≤ κ) :
    Cardinal.mk (Σ y : Y, Finset (f.fiber y)) ≤ κ := by
  let e (y : Y) : f.fiber y ↪ X := ⟨f.fiberι y, (f.fiberι y).isEmbedding.injective⟩
  let g : (Σ y : Y, Finset (f.fiber y)) → Y × Finset X :=
    fun p ↦ (p.1, p.2.map (e p.1))
  have hg : Function.Injective g := by
    rintro ⟨y, s⟩ ⟨z, t⟩ h
    obtain rfl : y = z := congrArg Prod.fst h
    obtain rfl : s = t := Finset.map_injective (e y) (congrArg Prod.snd h)
    rfl
  calc
    Cardinal.mk (Σ y : Y, Finset (f.fiber y)) ≤ Cardinal.mk (Y × Finset X) :=
      Cardinal.mk_le_of_injective hg
    _ = Cardinal.mk Y * Cardinal.mk (Finset X) := by simp
    _ ≤ κ * κ := mul_le_mul' hY
      ((cardinal_mk_finset_le_max_aleph0 X).trans (max_le hκ hX))
    _ = κ := Cardinal.mul_eq_self hκ

theorem exists_uniform_bound_finite_fiber_subsets
    (B : BigFppfSite.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : B.Contains X) (hY : B.Contains Y) :
    ∃ κ : Cardinal.{u}, Cardinal.aleph0 ≤ κ ∧ κ < B.cutoff ∧
      Cardinal.mk (Σ y : Y, Finset (f.fiber y)) ≤ κ ∧ Y.size ≤ κ := by
  let c := max X.size Y.size
  have hc : c < B.cutoff := max_lt hX hY
  have hcκ : c ≤ 2 ^ c := (Cardinal.cantor c).le
  have hκ : Cardinal.aleph0 ≤ 2 ^ c :=
    (X.aleph0_le_size.trans (le_max_left _ _)).trans hcκ
  have hmk (Z : Scheme.{u}) (hZ : Z.size ≤ c) : Cardinal.mk Z ≤ 2 ^ c :=
    (cardinal_mk_scheme_le_power_size Z).trans (Cardinal.power_le_power_left (by norm_num) hZ)
  exact ⟨2 ^ c, hκ, B.cutoff_isStrongPrelimit hc,
    cardinal_mk_finite_fiber_subsets_le f _ hκ (hmk X (le_max_left _ _))
      (hmk Y (le_max_right _ _)),
    (le_max_right _ _).trans hcκ⟩

theorem exists_site_coproduct_of_uniform_bound
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} (U : I → BigFppfOver B S hS)
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hκB : κ < B.cutoff)
    (hI : Cardinal.mk I ≤ κ)
    (hU : ∀ i, ((BigFppfOver.toScheme B S hS).obj (U i)).size ≤ κ) :
    ∃ (V : BigFppfOver B S hS) (ι : ∀ i, U i ⟶ V)
      (e : (BigFppfOver.toScheme B S hS).obj V ≅
        ∐ fun i ↦ (BigFppfOver.toScheme B S hS).obj (U i)),
      (∀ i, (BigFppfOver.toScheme B S hS).map (ι i) ≫ e.hom =
        Sigma.ι (fun i ↦ (BigFppfOver.toScheme B S hS).obj (U i)) i) ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤ κ := by
  let q := BigFppfOver.toScheme B S hS
  let A := fun i ↦ q.obj (U i)
  have hsize : (∐ A).size ≤ κ := schemeSize_coproduct_le A κ hκ hI hU
  have hV : B.Contains (∐ A) := hsize.trans_lt hκB
  let V : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (Sigma.desc fun i ↦ (U i).hom.hom) :
      B.obj hV ⟶ B.obj hS)
  let ι : ∀ i, U i ⟶ V := fun i ↦ Over.homMk (ObjectProperty.homMk (Sigma.ι A i))
    (ObjectProperty.hom_ext _ (Sigma.ι_comp_desc _ i))
  exact ⟨V, ι, Iso.refl _, fun _ ↦ Category.comp_id _, hsize⟩

private theorem etale_sigma_desc {I : Type u} (X : I → Scheme.{u})
    {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y) (hf : ∀ i, Etale (f i)) :
    Etale (Sigma.desc f) := by
  have : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (sigmaOpenCover X)]
  intro i
  change Etale (Sigma.ι X i ≫ Sigma.desc f)
  simpa using hf i

/-- A morphism out of a scheme identified with a coproduct is étale when its restriction to
each summand is étale. -/
private theorem etale_of_iso_sigma {I : Type u} (X : I → Scheme.{u}) {T Y : Scheme.{u}}
    (e : T ≅ ∐ X) (f : T ⟶ Y) (hf : ∀ i, Etale (Sigma.ι X i ≫ e.inv ≫ f)) : Etale f := by
  have hdesc := etale_sigma_desc X _ hf
  have heq : f = e.hom ≫ Sigma.desc fun i ↦ Sigma.ι X i ≫ e.inv ≫ f := by
    rw [← Iso.inv_comp_eq]
    ext i
    rw [Sigma.ι_comp_desc]
  rw [heq]
  exact Etale.etale_comp _ (f := e.hom)

/-- A morphism out of a site coproduct is étale when each of its restrictions to the summands
is étale. -/
theorem etale_map_of_site_coproduct
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} (U : I → BigFppfOver B S hS) {V Y : BigFppfOver B S hS} (ι : ∀ i, U i ⟶ V)
    (e : (BigFppfOver.toScheme B S hS).obj V ≅
      ∐ fun i ↦ (BigFppfOver.toScheme B S hS).obj (U i))
    (he : ∀ i, (BigFppfOver.toScheme B S hS).map (ι i) ≫ e.hom =
      Sigma.ι (fun i ↦ (BigFppfOver.toScheme B S hS).obj (U i)) i)
    (g : V ⟶ Y) (hg : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (ι i ≫ g))) :
    Etale ((BigFppfOver.toScheme B S hS).map g) := by
  refine etale_of_iso_sigma (fun i ↦ (BigFppfOver.toScheme B S hS).obj (U i)) e _ fun i ↦ ?_
  have hc : Sigma.ι (fun i ↦ (BigFppfOver.toScheme B S hS).obj (U i)) i ≫ e.inv =
      (BigFppfOver.toScheme B S hS).map (ι i) := by
    rw [Iso.comp_inv_eq, he i]
  rw [← Category.assoc, hc, ← Functor.map_comp]
  exact hg i

private theorem fppf_family_mem_topology (B : BigFppfSite.{u})
    {T : B.Schemes} (E : PreZeroHypercover.{u + 1} T)
    (hE : AlgebraicGeometry.IsFppfCovering ⟨T, E⟩) :
    E.sieve₀ ∈ B.topology T := by
  obtain ⟨E', hE', ⟨hT, heq⟩⟩ := B.fppf_has_representative ⟨T, E⟩ hE
  cases hT
  have hp : E.presieve₀ = E'.2.presieve₀ := by
    simpa using PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent heq
  change Sieve.generate E.presieve₀ ∈ B.topology E'.1
  rw [hp]
  exact Precoverage.generate_mem_toGrothendieck ⟨E'.2, rfl, hE'⟩

private theorem fppf_over_family_mem_topology
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V : BigFppfOver B S hS} {I : Type (u + 1)}
    (U : I → BigFppfOver B S hS) (a : ∀ i, U i ⟶ V)
    (hfp : Presieve.ofArrows
      (fun i ↦ (BigFppfOver.toScheme B S hS).obj (U i))
      (fun i ↦ (BigFppfOver.toScheme B S hS).map (a i)) ∈
        Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj V)) :
    Sieve.ofArrows U a ∈ BigFppfOver.topology B S hS V := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  let E : PreZeroHypercover.{u + 1} V.left :=
    ⟨I, fun i ↦ (U i).left, fun i ↦ (a i).left⟩
  apply fppf_family_mem_topology B E
  simpa [AlgebraicGeometry.IsFppfCovering, E, PreZeroHypercover.presieve₀_map] using hfp

private theorem subsingleton_sections_of_empty_scheme
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (T : BigFppfOver B S hS)
    (hT : IsEmpty ((BigFppfOver.toScheme B S hS).obj T)) :
    Subsingleton (F.obj (Opposite.op T)) := by
  have hcover : Sieve.ofArrows (X := T)
      (fun i : ULift.{u + 1} Empty ↦ isEmptyElim i.down)
      (fun i : ULift.{u + 1} Empty ↦ isEmptyElim i.down) ∈
      BigFppfOver.topology B S hS T := by
    apply fppf_over_family_mem_topology B S hS
    change Presieve.ofArrows
      (fun i : ULift.{u + 1} Empty ↦
        (BigFppfOver.toScheme B S hS).obj (isEmptyElim i.down))
      (fun i : ULift.{u + 1} Empty ↦
        (BigFppfOver.toScheme B S hS).map (isEmptyElim i.down)) ∈
        Scheme.precoverage (@Flat.{u} ⊓ @LocallyOfFinitePresentation.{u}) _
    rw [Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨fun t ↦ isEmptyElim t, fun i ↦ isEmptyElim i⟩
  have hs : Presieve.IsSheafFor F
      (Presieve.ofArrows (X := T)
        (fun i : ULift.{u + 1} Empty ↦ isEmptyElim i.down)
        (fun i : ULift.{u + 1} Empty ↦ isEmptyElim i.down)) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hF.isSheafFor _ hcover
  have hu := ((Presieve.isSheafFor_arrows_iff F
    (fun i : ULift.{u + 1} Empty ↦ isEmptyElim i.down)).mp hs)
    (fun i : ULift.{u + 1} Empty ↦ isEmptyElim i.down)
    (fun i : ULift.{u + 1} Empty ↦ isEmptyElim i.down)
  exact ⟨fun a b ↦ hu.unique (fun i ↦ isEmptyElim i.down)
    (fun i ↦ isEmptyElim i.down)⟩

theorem exists_sections_of_site_coproduct
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {I : Type u} (U : I → BigFppfOver B S hS)
    (V : BigFppfOver B S hS) (ι : ∀ i, U i ⟶ V)
    (e : (BigFppfOver.toScheme B S hS).obj V ≅
      ∐ fun i ↦ (BigFppfOver.toScheme B S hS).obj (U i))
    (he : ∀ i, (BigFppfOver.toScheme B S hS).map (ι i) ≫ e.hom =
      Sigma.ι (fun i ↦ (BigFppfOver.toScheme B S hS).obj (U i)) i)
    (s : ∀ i, F.obj (Opposite.op (U i))) :
    ∃ t : F.obj (Opposite.op V), ∀ i, F.map (ι i).op t = s i := by
  let q := BigFppfOver.toScheme B S hS
  let A : I → Scheme.{u} := fun i ↦ q.obj (U i)
  let U' : ULift.{u + 1} I → BigFppfOver B S hS := fun i ↦ U i.down
  let ι' : ∀ i, U' i ⟶ V := fun i ↦ ι i.down
  have hfp : Presieve.ofArrows (fun i ↦ q.obj (U' i)) (fun i ↦ q.map (ι' i)) ∈
      Scheme.fppfPrecoverage (q.obj V) := by
    change Presieve.ofArrows (fun i ↦ q.obj (U' i)) (fun i ↦ q.map (ι' i)) ∈
      Scheme.precoverage (@Flat.{u} ⊓ @LocallyOfFinitePresentation.{u}) _
    rw [Scheme.ofArrows_mem_precoverage_iff]
    constructor
    · intro v
      obtain ⟨⟨i, w⟩, hw⟩ := (sigmaMk A).surjective (e.hom v)
      refine ⟨⟨i⟩, w, ?_⟩
      apply e.hom.injective
      exact (congrArg (fun m : q.obj (U i) ⟶ ∐ A ↦ m w) (he i)).trans
        (by simpa only [sigmaMk_mk] using hw)
    · intro i
      change Flat (q.map (ι' i)) ∧ LocallyOfFinitePresentation (q.map (ι' i))
      have : IsOpenImmersion (q.map (ι' i)) := by
        have hh : IsOpenImmersion (q.map (ι' i) ≫ e.hom) := by
          rw [he i.down]
          infer_instance
        exact (MorphismProperty.cancel_right_of_respectsIso
          (P := @IsOpenImmersion) (q.map (ι' i)) e.hom).mp hh
      exact ⟨inferInstance, inferInstance⟩
  have hcover := fppf_over_family_mem_topology B S hS U' ι' hfp
  have hs : Presieve.IsSheafFor F (Presieve.ofArrows U' ι') := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hF.isSheafFor _ hcover
  have hcompat : Presieve.Arrows.Compatible F ι' (fun i ↦ s i.down) := by
    intro i j T g h hgh
    have hcomm : q.map g ≫ Sigma.ι A i.down = q.map h ≫ Sigma.ι A j.down := by
      have heq := congrArg q.map hgh
      rw [q.map_comp, q.map_comp] at heq
      calc
        q.map g ≫ Sigma.ι A i.down = (q.map g ≫ q.map (ι' i)) ≫ e.hom := by
          rw [Category.assoc, he i.down]
        _ = (q.map h ≫ q.map (ι' j)) ≫ e.hom := congrArg (· ≫ e.hom) heq
        _ = q.map h ≫ Sigma.ι A j.down := by rw [Category.assoc, he j.down]
    by_cases hij : i = j
    · subst j
      obtain rfl : g = h :=
        Over.OverMorphism.ext (ObjectProperty.hom_ext _ ((cancel_mono _).mp hcomm))
      rfl
    · have hq : IsEmpty (q.obj T) :=
        isEmpty_of_commSq_sigmaι_of_ne (g := A) (a := q.map g) (b := q.map h) ⟨hcomm⟩
          (fun hh ↦ hij (ULift.ext hh))
      have := subsingleton_sections_of_empty_scheme B S hS F hF T hq
      exact Subsingleton.elim _ _
  obtain ⟨t, ht, _⟩ := ((Presieve.isSheafFor_arrows_iff F ι').mp hs)
    (fun i ↦ s i.down) hcompat
  exact ⟨t, fun i ↦ ht ⟨i⟩⟩

private theorem exists_site_open_immersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    {W : Scheme.{u}} (j : W ⟶ (BigFppfOver.toScheme B S hS).obj T)
    (hj : IsOpenImmersion j) :
    ∃ (W' : BigFppfOver B S hS) (j' : W' ⟶ T)
      (e : (BigFppfOver.toScheme B S hS).obj W' ≅ W),
      e.hom ≫ j = (BigFppfOver.toScheme B S hS).map j' := by
  have hW : B.Contains W := Scheme.size_lt_of_isOpenImmersion j T.left.property
  let W' : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (j ≫ T.hom.hom) : B.obj hW ⟶ B.obj hS)
  let j' : W' ⟶ T := Over.homMk (ObjectProperty.homMk j) (by rfl)
  exact ⟨W', j', Iso.refl W, Category.id_comp j⟩

private theorem exists_site_finite_open_union
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T U : BigFppfOver B S hS} (g : T ⟶ U)
    {ι : Type u} [Finite ι]
    (D : ι → ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (hD : Pairwise (fun i j ↦ Disjoint (D i) (D j)))
    (hfin : ∀ i, IsFinite ((D i).ι ≫ (BigFppfOver.toScheme B S hS).map g)) :
    ∃ (W : BigFppfOver B S hS) (j : W ⟶ T)
      (e : (BigFppfOver.toScheme B S hS).obj W ≅ ∐ fun i ↦ (D i).toScheme),
      e.hom ≫ Sigma.desc (fun i ↦ (D i).ι) =
        (BigFppfOver.toScheme B S hS).map j ∧
      IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
      IsFinite ((BigFppfOver.toScheme B S hS).map (j ≫ g)) := by
  let q := BigFppfOver.toScheme B S hS
  obtain ⟨hopen, hfinite⟩ := finite_open_union (q.map g) D hD hfin
  obtain ⟨W, j, e, he⟩ := exists_site_open_immersion B S hS T
    (Sigma.desc fun i ↦ (D i).ι) hopen
  refine ⟨W, j, e, he, ?_, ?_⟩
  · rw [← he]
    exact IsOpenImmersion.comp e.hom _
  · change IsFinite (q.map (j ≫ g))
    rw [q.map_comp, ← he, Category.assoc]
    infer_instance

theorem exists_etale_chart_of_finite_open_union
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y U : BigFppfOver B S hS} (f : X ⟶ Y) (a : U ⟶ Y)
    (ha : Etale ((BigFppfOver.toScheme B S hS).map a))
    {ι : Type u} [Finite ι]
    (D : ι → ((BigFppfOver.toScheme B S hS).obj (pullback a f)).Opens)
    (hD : Pairwise (fun i j ↦ Disjoint (D i) (D j)))
    (hfin : ∀ i, IsFinite ((D i).ι ≫
      (BigFppfOver.toScheme B S hS).map (pullback.fst a f))) :
    ∃ (W : BigFppfOver B S hS) (j : W ⟶ pullback a f)
      (e : (BigFppfOver.toScheme B S hS).obj W ≅ ∐ fun i ↦ (D i).toScheme)
      (z : Space.FiniteOpenSubspace B S hS (schemeSpaceMap f)
        (schemeSpace U))
      (p : yoneda.obj U ⟶
        (Space.finiteOpenSubspacePresheaf B S hS (schemeSpaceMap f)).toFunctor),
      e.hom ≫ Sigma.desc (fun i ↦ (D i).ι) =
        (BigFppfOver.toScheme B S hS).map j ∧
      z.toBase = schemeSpaceMap a ∧
      HEq z.subspace (Subfunctor.range
        (yoneda.map j ≫ ((IsPullback.of_hasPullback a f).map yoneda).isoPullback.hom)) ∧
      (Space.finiteOpenSubspacePresheaf B S hS (schemeSpaceMap f)).sections U
        (yonedaEquiv p) = z ∧
      p ≫ (Space.finiteOpenSubspacePresheaf B S hS
        (schemeSpaceMap f)).baseMap = yoneda.map a ∧
      (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p := by
  obtain ⟨W, j, e, he, hj, hfinite⟩ :=
    exists_site_finite_open_union B S hS (pullback.fst a f) D hD hfin
  obtain ⟨z, hz, hzsub⟩ := exists_finiteOpenSubspace_of_scheme_open B S hS f a j hj hfinite
  have hetale : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf z.toBase.hom := by
    rw [hz]
    exact presheaf_yoneda_map B S hS _ a ha
  obtain ⟨p, hp, hsec, hpetale⟩ :=
    exists_etale_map_of_finiteOpenSubspace B S hS (schemeSpaceMap f) U z hetale
  exact ⟨W, j, e, z, p, he, hz, hzsub, hsec,
    hp.trans (congrArg (fun a ↦ a.hom) hz), hpetale⟩

end AlgebraicGeometry.FinitePartChart

end
