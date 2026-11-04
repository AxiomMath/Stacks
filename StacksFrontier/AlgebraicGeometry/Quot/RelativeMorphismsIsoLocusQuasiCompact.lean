module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Quot.IsomorphismLocusQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatIsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ProperMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria

/-!
# The isomorphism locus of the graph projection is quasi-compact

Let `z : Z ⟶ Q` and `x : X ⟶ Q` be morphisms of algebraic spaces over a scheme `S` of a big fppf
site, with `x` separated and `z` of finite presentation, flat and proper, and both relatively
representable. The realisation `Mor_Q(Z, X) ⟶ M` of the relative morphism functor in a model of
the Hilbert functor of `Z ×_Q X` over `Q` is representable by open immersions (Stacks 0D1B). This
file shows that its base change along a point `ξ : H ⟶ M` with `H` quasi-compact and
quasi-separated is a quasi-compact open subscheme of `H`.

The point `ξ` is a family `Y ⊆ (Z ×_Q X)_H`, and a morphism `T' ⟶ H` factors through the base
change exactly when the projection of the base-changed family to the base change of `Z` is an
isomorphism. The family and the base change of `Z` are represented by schemes over `H`, of finite
presentation and proper, the first also flat, and the projection by a morphism between them; the
quasi-compactness of the isomorphism locus is then
`AlgebraicGeometry.IsoLocus.isCompact_of_forall_range_subset_iff_isIso`.

## Main results

* `AlgebraicGeometry.Space.exists_fac_iff_isIso_graphProjection`: a morphism of the site factors
  through the base change of the realisation exactly when the graph projection of the
  base-changed family is an isomorphism.
* `AlgebraicGeometry.Space.exists_scheme_triangle_graphProjection`: the graph projection of a
  family over a scheme of the site is represented by a morphism of schemes over that scheme.
* `AlgebraicGeometry.Space.exists_isPullback_compactSpace_morToHilbertModel`: the base change of
  the realisation along a point over a quasi-compact quasi-separated scheme is a quasi-compact
  open subscheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/-- A morphism over a base becomes an isomorphism after base change along `g` exactly when a
morphism over the same base, isomorphic to it as a triangle, does. -/
theorem CategoryTheory.Limits.isIso_pullbackLift_iff_of_isoOverBase {C : Type*} [Category C]
    {X X' Y Y' Z Z' : C} (k : X ⟶ Y) (a : X ⟶ Z) (b : Y ⟶ Z) (hk : k ≫ b = a) (k' : X' ⟶ Y')
    (a' : X' ⟶ Z) (b' : Y' ⟶ Z) (hk' : k' ≫ b' = a') (eX : X' ≅ X) (eY : Y' ≅ Y)
    (ha : eX.hom ≫ a = a') (hb : eY.hom ≫ b = b') (he : k' ≫ eY.hom = eX.hom ≫ k) (g : Z' ⟶ Z)
    [HasPullback a g] [HasPullback b g] [HasPullback a' g] [HasPullback b' g] :
    IsIso (pullback.lift (f := b) (g := g) (pullback.fst a g ≫ k) (pullback.snd a g)
        (by rw [Category.assoc, hk, pullback.condition])) ↔
      IsIso (pullback.lift (f := b') (g := g) (pullback.fst a' g ≫ k') (pullback.snd a' g)
        (by rw [Category.assoc, hk', pullback.condition])) := by
  have hφX : IsIso (pullback.map a' g a g eX.hom (𝟙 _) (𝟙 _) (by simp [← ha]) (by simp)) :=
    pullback.map_isIso _ _ _ _ _ _ _ _ _
  have hφY : IsIso (pullback.map b' g b g eY.hom (𝟙 _) (𝟙 _) (by simp [← hb]) (by simp)) :=
    pullback.map_isIso _ _ _ _ _ _ _ _ _
  have hsq : pullback.lift (f := b') (g := g) (pullback.fst a' g ≫ k') (pullback.snd a' g)
      (by rw [Category.assoc, hk', pullback.condition]) ≫
        pullback.map b' g b g eY.hom (𝟙 _) (𝟙 _) (by simp [← hb]) (by simp) =
      pullback.map a' g a g eX.hom (𝟙 _) (𝟙 _) (by simp [← ha]) (by simp) ≫
        pullback.lift (f := b) (g := g) (pullback.fst a g ≫ k) (pullback.snd a g)
          (by rw [Category.assoc, hk, pullback.condition]) := by
    apply pullback.hom_ext
    · simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, he]
    · simp only [pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id]
  exact ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (@asIso _ _ _ _ _ hφX) (@asIso _ _ _ _ _ hφY) hsq.symm)).symm

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)

local notation "𝒯" => BigFppfOver.toScheme B S hS

/-- A scheme of the big fppf site with a morphism `g` to the scheme underlying `H`, read as a
morphism of the site over `S`. -/
abbrev isoLocusTestHom (H : BigFppfOver B S hS) {T' : Scheme.{u}} (hT' : B.Contains T')
    (g : T' ⟶ (𝒯).obj H) : siteObject B S hS hT' (g ≫ H.hom.hom) ⟶ H :=
  Over.homMk (ObjectProperty.homMk g) (ObjectProperty.hom_ext _ rfl)

/-- A morphism `g` from a scheme of the site lands in the range of an open immersion `q` of the
site exactly when the corresponding morphism of the site factors through `q`. -/
theorem range_subset_opensRange_iff_exists_fac {V H : BigFppfOver B S hS} (q : V ⟶ H)
    [_root_.AlgebraicGeometry.IsOpenImmersion ((𝒯).map q)] {T' : Scheme.{u}}
    (hT' : B.Contains T') (g : T' ⟶ (𝒯).obj H) :
    Set.range g ⊆ (((𝒯).map q).opensRange : Set ((𝒯).obj H)) ↔
      ∃ t : siteObject B S hS hT' (g ≫ H.hom.hom) ⟶ V, t ≫ q = isoLocusTestHom H hT' g := by
  constructor
  · intro hg
    let l := IsOpenImmersion.lift ((𝒯).map q) g (by rwa [Scheme.Hom.coe_opensRange] at hg)
    have hl : l ≫ (𝒯).map q = g := IsOpenImmersion.lift_fac _ _ _
    refine ⟨Over.homMk (ObjectProperty.homMk l) (ObjectProperty.hom_ext _ ?_), ?_⟩
    · show l ≫ V.hom.hom = g ≫ H.hom.hom
      rw [← hl, Category.assoc]
      exact congrArg (l ≫ ·) (congrArg (fun m => m.hom) (Over.w q)).symm
    · exact Over.OverMorphism.ext (ObjectProperty.hom_ext _ hl)
  · rintro ⟨t, ht⟩ _ ⟨y, rfl⟩
    refine ⟨((𝒯).map t) y, ?_⟩
    show ((𝒯).map q) (((𝒯).map t) y) = ((𝒯).map (isoLocusTestHom H hT' g)) y
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, ht]

/-- A morphism of the site factors through the base change of the realisation of `Mor_Q(Z, X)`
in a model of the Hilbert functor along a point `ξ` exactly when the graph projection of the
family `ξ` names, base changed along that morphism, is an isomorphism. -/
theorem exists_fac_iff_isIso_graphProjection (hsep : IsSeparated B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z)
    (M : HilbertPresheafModel (graphAmbientMap B S hS z x hZ hX hQ)) {H V : BigFppfOver B S hS}
    {ξ : yoneda.obj H ⟶ M.presheaf} {s : yoneda.obj V ⟶ relativeHom B S hS Z X Q z x hZ hX hQ}
    {q : V ⟶ H}
    (hpb : IsPullback s (yoneda.map q) (morToHilbertModel z x hZ hX hQ M hsep hfp hflat hproper) ξ)
    (T' : BigFppfOver B S hS) (h : T' ⟶ H) :
    (∃ t : T' ⟶ V, t ≫ q = h) ↔
      IsIso (graphProjection z x ((M.familyEquiv H (yonedaEquiv ξ)).baseChange h).toBase
        ((M.familyEquiv H (yonedaEquiv ξ)).baseChange h).family.Z) := by
  have hmf : ∀ r : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (Opposite.op T'),
      M.familyEquiv T'
          ((morToHilbertModel z x hZ hX hQ M hsep hfp hflat hproper).app (Opposite.op T') r) =
        (graphTransformation hZ hX hQ hsep hfp hflat hproper).app (Opposite.op T')
          (ULift.up r) :=
    fun r => types_congr_hom (M.iso.inv_hom_id_app (Opposite.op T')) _
  have hξ : M.familyEquiv T' (M.presheaf.map h.op (yonedaEquiv ξ)) =
      (M.familyEquiv H (yonedaEquiv ξ)).baseChange h :=
    M.familyEquiv_map h _
  constructor
  · rintro ⟨t, rfl⟩
    have hc : (morToHilbertModel z x hZ hX hQ M hsep hfp hflat hproper).app (Opposite.op T')
        (yonedaEquiv (yoneda.map t ≫ s)) = M.presheaf.map (t ≫ q).op (yonedaEquiv ξ) := by
      rw [← yonedaEquiv_comp, yonedaEquiv_naturality]
      exact congrArg yonedaEquiv (by rw [Category.assoc, hpb.w, Functor.map_comp, Category.assoc])
    have heq := (hmf _).symm.trans ((congrArg (M.familyEquiv T') hc).trans
      (M.familyEquiv_map (t ≫ q) _))
    rw [← heq]
    exact isIso_graphProjection_range_graphMap z x
      (relativeHomSections B S hS Z X Q z x hZ hX hQ T' (yonedaEquiv (yoneda.map t ≫ s)))
  · intro hiso
    obtain ⟨r, hr₁, hr₂⟩ := hiso.out
    have hr := graphTransformation_app_relativeHomSectionOfGraph z x hZ hX hQ hsep hfp hflat
      hproper ((M.familyEquiv H (yonedaEquiv ξ)).baseChange h) r hr₂ hr₁
    have hc := (M.familyEquiv T').injective ((hmf _).trans (hr.trans hξ.symm))
    have hs' : yonedaEquiv.symm (relativeHomSectionOfGraph z x hZ hX hQ
        ((M.familyEquiv H (yonedaEquiv ξ)).baseChange h) r hr₂) ≫
          morToHilbertModel z x hZ hX hQ M hsep hfp hflat hproper =
        yoneda.map h ≫ ξ := yonedaEquiv.injective (by
      rwa [yonedaEquiv_comp, Equiv.apply_symm_apply, ← yonedaEquiv_naturality])
    exact ⟨yoneda.preimage (hpb.lift _ _ hs'),
      yoneda.map_injective (by rw [Functor.map_comp, Functor.map_preimage, hpb.lift_snd])⟩

/-- A morphism `kP : F ⟶ G` of algebraic spaces over a scheme `H` of the site, with `F ⟶ H`
flat, proper and of finite presentation and `G ⟶ H` proper and of finite presentation, both
representable, is represented by a morphism `k : W ⟶ V` of schemes over the scheme underlying `H`:
the base change of `kP` along a scheme `T' ⟶ H` of the site is an isomorphism exactly when the
base change of `k` is. -/
theorem exists_scheme_triangle_of_relativelyRepresentable {H : BigFppfOver B S hS}
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (kP : F ⟶ G) (p₁ : F ⟶ yoneda.obj H)
    (p₂ : G ⟶ yoneda.obj H) (hkP : kP ≫ p₂ = p₁) (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (hrep₁ : yoneda.relativelyRepresentable p₁)
    (hrep₂ : yoneda.relativelyRepresentable p₂) (hfp₁ : IsFinitePresentation B S hS p₁)
    (hfl₁ : IsFlat B S hS p₁) (hpr₁ : IsProper B S hS p₁) (hfp₂ : IsFinitePresentation B S hS p₂)
    (hpr₂ : IsProper B S hS p₂) :
    ∃ (W V : Scheme.{u}) (a : W ⟶ (𝒯).obj H) (b : V ⟶ (𝒯).obj H) (k : W ⟶ V) (hk : k ≫ b = a),
      FinitePresentation a ∧ Flat a ∧ _root_.AlgebraicGeometry.IsProper a ∧
      FinitePresentation b ∧ _root_.AlgebraicGeometry.IsProper b ∧
      ∀ (T' : Scheme.{u}) (hT' : B.Contains T') (g : T' ⟶ (𝒯).obj H),
        IsIso (baseChangeOverBase B S hS kP p₁ p₂ hkP (yoneda.map (isoLocusTestHom H hT' g))) ↔
          IsIso (pullback.lift (f := b) (g := g) (pullback.fst a g ≫ k) (pullback.snd a g)
            (by rw [Category.assoc, hk, pullback.condition])) := by
  have hT := isAlgebraicSpace_yoneda B S hS H
  obtain ⟨W', aa, e₁, he₁⟩ := hrep₁ (𝟙 (yoneda.obj H))
  obtain ⟨V', bb, e₂, he₂⟩ := hrep₂ (𝟙 (yoneda.obj H))
  have he₁iso : IsIso e₁ := he₁.isIso_fst_of_isIso
  have he₂iso : IsIso e₂ := he₂.isIso_fst_of_isIso
  have hw₁ : e₁ ≫ p₁ = yoneda.map aa := he₁.w.trans (Category.comp_id _)
  have hw₂ : e₂ ≫ p₂ = yoneda.map bb := he₂.w.trans (Category.comp_id _)
  let kk : W' ⟶ V' := yoneda.preimage (e₁ ≫ kP ≫ inv e₂)
  have hkk' : yoneda.map kk ≫ e₂ = e₁ ≫ kP := by
    simp only [kk, Functor.map_preimage, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hkk : kk ≫ bb = aa := yoneda.map_injective (by
    rw [Functor.map_comp, ← hw₂, reassoc_of% hkk', hkP, hw₁])
  have hW'alg := isAlgebraicSpace_yoneda B S hS W'
  have hV'alg := isAlgebraicSpace_yoneda B S hS V'
  have hfp1 : IsFinitePresentation B S hS (yoneda.map aa) :=
    IsFinitePresentation.of_isPullback B S hS hW'alg hF hT hT he₁ hfp₁
  have hfl1 : IsFlat B S hS (yoneda.map aa) :=
    isFlat_of_isPullback_of_isAlgebraicSpace B S hS he₁.flip hF hT hfl₁
  have hpr1 : IsProper B S hS (yoneda.map aa) :=
    isProper_of_isPullback' hW'alg hF hT hT he₁ hpr₁
  have hfp2 : IsFinitePresentation B S hS (yoneda.map bb) :=
    IsFinitePresentation.of_isPullback B S hS hV'alg hG hT hT he₂ hfp₂
  have hpr2 : IsProper B S hS (yoneda.map bb) :=
    isProper_of_isPullback' hV'alg hG hT hT he₂ hpr₂
  have haprop : _root_.AlgebraicGeometry.IsProper ((𝒯).map aa) :=
    (isProper_yoneda_map_iff B S hS aa).1 hpr1
  have hbprop : _root_.AlgebraicGeometry.IsProper ((𝒯).map bb) :=
    (isProper_yoneda_map_iff B S hS bb).1 hpr2
  have haflat : Flat ((𝒯).map aa) :=
    (holdsOnEveryEtaleChart_yoneda_map_iff B S hS Flat.isEtaleLocalOnSourceAndTarget aa).1 hfl1
  have hafp : FinitePresentation ((𝒯).map aa) :=
    FinitePresentation.mk ((holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget aa).1 hfp1.1)
      inferInstance inferInstance
  have hbfp : FinitePresentation ((𝒯).map bb) :=
    FinitePresentation.mk ((holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget bb).1 hfp2.1)
      inferInstance inferInstance
  refine ⟨_, _, (𝒯).map aa, (𝒯).map bb, (𝒯).map kk, by rw [← Functor.map_comp, hkk], hafp,
    haflat, haprop, hbfp, hbprop, fun T' hT' g => ?_⟩
  have := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  refine (isIso_pullbackLift_iff_of_isoOverBase kP p₁ p₂ hkP (yoneda.map kk) (yoneda.map aa)
    (yoneda.map bb) (by rw [← Functor.map_comp, hkk]) (asIso e₁)
    (asIso e₂) hw₁ hw₂ hkk' (yoneda.map (isoLocusTestHom H hT' g))).trans ?_
  refine (Functor.isIso_pullbackLift_iff_of_preserves yoneda kk aa bb hkk
    (isoLocusTestHom H hT' g)).symm.trans ?_
  exact Functor.isIso_pullbackLift_iff_of_preserves (𝒯) kk aa bb hkk (isoLocusTestHom H hT' g)

/-- The graph projection of a family over a scheme `H` of the site is represented by a morphism
`k : W ⟶ V` of schemes over the scheme underlying `H`, with `W` flat, proper and of finite
presentation and `V` proper and of finite presentation: the graph projection of the family base
changed along a scheme `T' ⟶ H` of the site is an isomorphism exactly when the base change of `k`
is. -/
theorem exists_scheme_triangle_graphProjection (hfp : IsFinitePresentation B S hS z)
    (hproper : IsProper B S hS z) (hzrep : yoneda.relativelyRepresentable z)
    (hxrep : yoneda.relativelyRepresentable x) (H : BigFppfOver B S hS)
    (Y : HilbertFamilyOver (graphAmbientMap B S hS z x hZ hX hQ) H) :
    ∃ (W V : Scheme.{u}) (a : W ⟶ (𝒯).obj H) (b : V ⟶ (𝒯).obj H) (k : W ⟶ V) (hk : k ≫ b = a),
      FinitePresentation a ∧ Flat a ∧ _root_.AlgebraicGeometry.IsProper a ∧
      FinitePresentation b ∧ _root_.AlgebraicGeometry.IsProper b ∧
      ∀ (T' : Scheme.{u}) (hT' : B.Contains T') (g : T' ⟶ (𝒯).obj H),
        IsIso (graphProjection z x (Y.baseChange (isoLocusTestHom H hT' g)).toBase
            (Y.baseChange (isoLocusTestHom H hT' g)).family.Z) ↔
          IsIso (pullback.lift (f := b) (g := g) (pullback.fst a g ≫ k) (pullback.snd a g)
            (by rw [Category.assoc, hk, pullback.condition])) := by
  have hT := isAlgebraicSpace_yoneda B S hS H
  have hrep1 : yoneda.relativelyRepresentable
      (Y.family.Z.ι ≫ pullback.snd (pullback.fst z x ≫ z) Y.toBase) := by
    refine yoneda.relativelyRepresentable.comp_mem _ _ Y.family.closed.2.rep ?_
    exact MorphismProperty.pullback_snd _ _ (yoneda.relativelyRepresentable.comp_mem _ _
      (MorphismProperty.pullback_fst _ _ hxrep) hzrep)
  have hrep2 : yoneda.relativelyRepresentable (pullback.fst Y.toBase z) :=
    MorphismProperty.pullback_fst _ _ hzrep
  have hZHalg := isAlgebraicSpace_pullback B S hS Y.toBase z hT hZ hQ
  obtain ⟨W, V, a, b, k, hk, ha, haflat, haprop, hb, hbprop, hiso⟩ :=
    exists_scheme_triangle_of_relativelyRepresentable (graphProjection z x Y.toBase Y.family.Z)
      (Y.family.Z.ι ≫ pullback.snd (pullback.fst z x ≫ z) Y.toBase) (pullback.fst Y.toBase z)
      (graphProjection_comp_fst z x Y.toBase Y.family.Z) Y.family.closed.1 hZHalg hrep1 hrep2
      Y.family.finitePresentation Y.family.flat Y.family.proper
      (IsFinitePresentation.of_isPullback B S hS hZHalg hZ hT hQ
        (IsPullback.of_hasPullback Y.toBase z).flip hfp)
      (isProper_pullback_fst B S hS hZ hQ hT z Y.toBase hproper)
  refine ⟨W, V, a, b, k, hk, ha, haflat, haprop, hb, hbprop, fun T' hT' g => ?_⟩
  exact (isIso_graphProjection_preimage_iff z x (yoneda.map (isoLocusTestHom H hT' g)) Y.toBase
      Y.family.Z (schemeBaseChangeMap (graphAmbientMap B S hS z x hZ hX hQ)
        (HilbertFamilyOver.restrict (isoLocusTestHom H hT' g) Y.toBase))
      (schemeBaseChangeMap_graphAmbientMap hZ hX hQ (isoLocusTestHom H hT' g) Y.toBase)).trans
    (hiso T' hT' g)

/-- **The base change of the realisation of `Mor_Q(Z, X)` along a point over a quasi-compact
quasi-separated scheme is quasi-compact.** For `x` separated and `z` of finite presentation, flat
and proper, both relatively representable, the base change of the realisation of `Mor_Q(Z, X)` in
a model of the Hilbert functor of `Z ×_Q X` over `Q` along a point `ξ : H ⟶ M`, with `H` a
quasi-compact and quasi-separated scheme of the site, is an open subscheme `V ⟶ H` with `V`
quasi-compact.

The open subscheme is the locus over which the graph projection of the family `ξ` is an
isomorphism (`AlgebraicGeometry.Space.exists_fac_iff_isIso_graphProjection`); that projection is
represented by a morphism of schemes over `H` between a flat proper scheme of finite presentation
and a proper scheme of finite presentation
(`AlgebraicGeometry.Space.exists_scheme_triangle_graphProjection`), so its isomorphism locus is
quasi-compact by `AlgebraicGeometry.IsoLocus.isCompact_of_forall_range_subset_iff_isIso`. -/
theorem exists_isPullback_compactSpace_morToHilbertModel
    (hsep : IsSeparated B S hS x) (hfp : IsFinitePresentation B S hS z)
    (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z)
    (hzrep : yoneda.relativelyRepresentable z) (hxrep : yoneda.relativelyRepresentable x)
    (M : HilbertPresheafModel (graphAmbientMap B S hS z x hZ hX hQ))
    (H : BigFppfOver B S hS) [CompactSpace ((𝒯).obj H)] [QuasiSeparatedSpace ((𝒯).obj H)]
    (ξ : yoneda.obj H ⟶ M.presheaf) :
    ∃ (V : BigFppfOver B S hS) (s : yoneda.obj V ⟶ relativeHom B S hS Z X Q z x hZ hX hQ)
      (q : V ⟶ H),
      IsPullback s (yoneda.map q) (morToHilbertModel z x hZ hX hQ M hsep hfp hflat hproper) ξ ∧
      _root_.AlgebraicGeometry.IsOpenImmersion ((𝒯).map q) ∧ CompactSpace ((𝒯).obj V) := by
  have hopen := morToHilbertModel_isOpenImmersion z x hZ hX hQ M hsep hfp hflat hproper
  obtain ⟨V, q, s, hpb⟩ := hopen.1 ξ
  have hq : _root_.AlgebraicGeometry.IsOpenImmersion ((𝒯).map q) := hopen.2 ξ s q hpb
  refine ⟨V, s, q, hpb, hq, ?_⟩
  obtain ⟨W, V₀, a, b, k, hk, ha, haflat, haprop, hb, hbprop, hiso⟩ :=
    exists_scheme_triangle_graphProjection hZ hX hQ hfp hproper hzrep hxrep H
      (M.familyEquiv H (yonedaEquiv ξ))
  have hcpt : IsCompact (((𝒯).map q).opensRange : Set ((𝒯).obj H)) :=
    IsoLocus.isCompact_of_forall_range_subset_iff_isIso B
      (show B.Contains ((𝒯).obj H) from H.left.property) a b k hk ha hb _
      (fun T' hT' g => (range_subset_opensRange_iff_exists_fac q hT' g).trans
        ((exists_fac_iff_isIso_graphProjection hZ hX hQ hsep hfp hflat hproper M hpb _ _).trans
          (hiso T' hT' g)))
  rw [Scheme.Hom.coe_opensRange] at hcpt
  exact isCompact_univ_iff.1
    (((𝒯).map q).isOpenEmbedding.toIsEmbedding.isCompact_iff.2 (by rwa [Set.image_univ]))

end AlgebraicGeometry.Space

end
