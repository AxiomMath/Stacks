module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.MilnorChainLocalization
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.GaloisCoverDiscreteValuationRing
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleGluing
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverSpreading.GenericFibre
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.GeometricallyUnibranch

/-!
# Tag 0EYJ: reduction to a quasi-compact morphism

The maximal-open argument in the proof of [Stacks, Tag 0EYJ] spreads a Galois cover of the
generic fibre `X_η` out over an open of the base, which needs `f : X ⟶ S` quasi-compact; the
source does not say so. This file deduces Tag 0EYJ for an arbitrary smooth `f` with geometrically
connected fibres and a section from the quasi-compact case.

SOURCE GAP: the proof of Tag 0EYJ never says that `X` is quasi-compact, but its maximal-open
argument needs it. A smooth morphism with geometrically connected fibres need not be
quasi-compact: `S ×_k L`, for `L` the affine line with infinitely many origins, is not.

## Main results

* `Abhyankar.exists_finiteEtaleGaloisCover_extending_genericFiber_of_quasiCompact_case`: the
  reduction. Tag 0EYJ for quasi-compact `f` implies Tag 0EYJ.
* `AlgebraicGeometry.Abhyankar.geometricallyConnected_ι_comp`: an open of `X` containing the image
  of the section again has geometrically connected fibres.
* `AlgebraicGeometry.Abhyankar.nonempty_iso_of_iso_finiteEtaleBaseChange_fiberι`: over a
  quasi-compact irreducible geometrically unibranch scheme, a finite étale cover is determined by
  its generic fibre.
* `AlgebraicGeometry.Abhyankar.exists_galoisCover_of_isCompact`: the quasi-compact case, applied
  to a quasi-compact open containing the section.

## References

* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Abhyankar

/-- A nonempty open subscheme of an irreducible scheme is irreducible. -/
private theorem irreducibleSpace_opens_of_nonempty {X : Scheme.{u}} [IrreducibleSpace X]
    (O : X.Opens) [Nonempty O] : IrreducibleSpace O.toScheme :=
  Subtype.irreducibleSpace
    ((IrreducibleSpace.isIrreducible_univ X).2.subset_irreducible
      (by simpa using (inferInstance : Nonempty O)) O.isOpen (fun _ ↦ id) (by simp))

/-- The underlying morphism of an isomorphism of finite étale covers is an isomorphism. -/
private theorem isIso_hom_left_of_iso {T : Scheme.{u}} {A B : FiniteEtaleOver T} (β : A ≅ B) :
    IsIso β.hom.left :=
  inferInstanceAs (IsIso ((MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).map β.hom))

/-- The section of the generic fibre lies over every open containing the image of the section. -/
private theorem genericFiberSection_mem_preimage {S X : Scheme.{u}} [IsIntegral S] (f : X ⟶ S)
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) {O : X.Opens} (hO : Set.range σ ⊆ O)
    (y : Spec (S.residueField (genericPoint S))) :
    genericFiberSection f σ hσ y ∈ f.fiberι (genericPoint S) ⁻¹ᵁ O := by
  change f.fiberι _ (genericFiberSection f σ hσ y) ∈ O
  rw [← Scheme.Hom.comp_apply, genericFiberSection_fiberι, Scheme.Hom.comp_apply]
  exact hO ⟨_, rfl⟩

/-- **An open containing a section has geometrically connected fibres.** Let `f : X ⟶ S` be
smooth with geometrically connected fibres and `σ` a section. The fibres of `f` over field-valued
points are smooth and connected, hence irreducible, and an open `O ⊇ σ(S)` meets each of them in a
nonempty open, which is therefore connected. -/
theorem geometricallyConnected_ι_comp {S X : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    [GeometricallyConnected f] (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) (O : X.Opens)
    (hO : Set.range σ ⊆ O) : GeometricallyConnected (O.ι ≫ f) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  rw [← (pullbackRightPullbackFstIso f x O.ι).hom.homeomorph.connectedSpace_iff]
  have : ConnectedSpace ↥(pullback f x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  have : IrreducibleSpace ↥(pullback f x) :=
    irreducibleSpace_of_smooth_of_connectedSpace (pullback.snd f x)
  let p := pullback.fst f x
  let t : Spec (.of K) ⟶ pullback f x :=
    pullback.lift (x ≫ σ) (𝟙 _) (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  obtain ⟨pt⟩ : Nonempty (Spec (.of K)) := inferInstance
  have : Nonempty (p ⁻¹ᵁ O) := ⟨⟨t pt, by
    change p (t pt) ∈ O
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
    exact hO ⟨_, rfl⟩⟩⟩
  exact (pullbackSymmetry O.ι p ≪≫
    pullbackRestrictIsoRestrict p O).hom.homeomorph.connectedSpace_iff.mpr inferInstance

/-- **A finite étale cover is determined by its generic fibre.** Let `S` be integral with generic
point `η` and `g : T ⟶ S` quasi-compact and quasi-separated, with `T` irreducible and
geometrically unibranch and `T_η` nonempty. Two finite étale covers of `T` whose restrictions to
`T_η` are isomorphic are isomorphic: the isomorphism spreads out to `g⁻¹(W)` for an open `W ∋ η`,
and restriction to the dense open `g⁻¹(W)` is fully faithful. -/
theorem nonempty_iso_of_iso_finiteEtaleBaseChange_fiberι {S T : Scheme.{u}} [IsIntegral S]
    (g : T ⟶ S) [QuasiCompact g] [QuasiSeparated g] [IrreducibleSpace T]
    (hT : IsGeometricallyUnibranch T) (hne : Nonempty (g.fiber (genericPoint S)))
    (A B : FiniteEtaleOver T)
    (φ : (finiteEtaleBaseChange (g.fiberι (genericPoint S))).obj A ≅
      (finiteEtaleBaseChange (g.fiberι (genericPoint S))).obj B) :
    Nonempty (A ≅ B) := by
  let D := preimageAffineOpenNhdsDiagram g (genericPoint S)
  let c := genericFiberCone g
  have hc : IsLimit c := isLimitGenericFiberCone g
  obtain ⟨W₀⟩ : Nonempty (AffineOpenNhds S (genericPoint S)) := inferInstance
  let ι₀ := (g ⁻¹ᵁ W₀.opens).ι
  let comp₀ := finiteEtaleBaseChangeComp (genericFiberToPreimage g W₀.opens W₀.mem_opens) ι₀
    (g.fiberι (genericPoint S)) (genericFiberToPreimage_ι g W₀.opens W₀.mem_opens).symm
  let A₀ : FiniteEtaleOver (D.obj W₀) := (finiteEtaleBaseChange ι₀).obj A
  let B₀ : FiniteEtaleOver (D.obj W₀) := (finiteEtaleBaseChange ι₀).obj B
  let φ₀ : (finiteEtaleBaseChange (c.π.app W₀)).obj A₀ ≅
      (finiteEtaleBaseChange (c.π.app W₀)).obj B₀ :=
    (comp₀.app A).symm ≪≫ φ ≪≫ comp₀.app B
  obtain ⟨W₁, e₁, χ, hχ⟩ := exists_finiteEtale_hom_model D c hc W₀ A₀ B₀ φ₀.hom
  have : IsIso ((finiteEtaleBaseChange (c.π.app W₁)).map χ) := by
    have : (finiteEtaleBaseChange (c.π.app W₁)).map χ =
        (finiteEtaleLimitCompIso D c e₁).inv.app A₀ ≫ φ₀.hom ≫
          (finiteEtaleLimitCompIso D c e₁).hom.app B₀ := by
      rw [hχ]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
      exact (Category.comp_id _).symm
    rw [this]
    infer_instance
  let χ' : Over.mk ((finiteEtaleBaseChange (D.map e₁)).obj A₀).hom ⟶
      Over.mk ((finiteEtaleBaseChange (D.map e₁)).obj B₀).hom :=
    Over.homMk χ.left (MorphismProperty.Over.w χ)
  have : IsIso ((Over.pullback (c.π.app W₁)).map χ').left :=
    inferInstanceAs (IsIso ((MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).map
      ((finiteEtaleBaseChange (c.π.app W₁)).map χ)))
  obtain ⟨hA₁, hA₂⟩ := ((finiteEtaleBaseChange (D.map e₁)).obj A₀).prop
  obtain ⟨hB₁, hB₂⟩ := ((finiteEtaleBaseChange (D.map e₁)).obj B₀).prop
  have : CompactSpace ((Functor.fromPUnit (D.obj W₁)).obj
      ((finiteEtaleBaseChange (D.map e₁)).obj A₀).right) :=
    inferInstanceAs (CompactSpace (D.obj W₁))
  have : QuasiSeparatedSpace ((Functor.fromPUnit (D.obj W₁)).obj
      ((finiteEtaleBaseChange (D.map e₁)).obj A₀).right) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj W₁))
  have : CompactSpace ((Functor.fromPUnit (D.obj W₁)).obj
      ((finiteEtaleBaseChange (D.map e₁)).obj B₀).right) :=
    inferInstanceAs (CompactSpace (D.obj W₁))
  have : QuasiSeparatedSpace ((Functor.fromPUnit (D.obj W₁)).obj
      ((finiteEtaleBaseChange (D.map e₁)).obj B₀).right) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj W₁))
  have : CompactSpace (Over.mk ((finiteEtaleBaseChange (D.map e₁)).obj A₀).hom).left :=
    QuasiCompact.compactSpace_of_compactSpace ((finiteEtaleBaseChange (D.map e₁)).obj A₀).hom
  have : QuasiSeparatedSpace (Over.mk ((finiteEtaleBaseChange (D.map e₁)).obj A₀).hom).left :=
    quasiSeparatedSpace_of_quasiSeparated ((finiteEtaleBaseChange (D.map e₁)).obj A₀).hom
  have : CompactSpace (Over.mk ((finiteEtaleBaseChange (D.map e₁)).obj B₀).hom).left :=
    QuasiCompact.compactSpace_of_compactSpace ((finiteEtaleBaseChange (D.map e₁)).obj B₀).hom
  have : QuasiSeparatedSpace (Over.mk ((finiteEtaleBaseChange (D.map e₁)).obj B₀).hom).left :=
    quasiSeparatedSpace_of_quasiSeparated ((finiteEtaleBaseChange (D.map e₁)).obj B₀).hom
  have : LocallyOfFinitePresentation χ'.left := by
    change LocallyOfFinitePresentation χ.left
    have : Etale (χ.left ≫ ((finiteEtaleBaseChange (D.map e₁)).obj B₀).hom) := by
      rw [MorphismProperty.Over.w χ]
      exact hA₂
    have : Etale χ.left := Etale.of_comp _ ((finiteEtaleBaseChange (D.map e₁)).obj B₀).hom
    infer_instance
  obtain ⟨W₂, e₂, hiso⟩ := exists_isIso_baseChange_of_isIso_limitBaseChange D c hc W₁ _ _ χ'
  -- the isomorphism over `g⁻¹(W₂)`
  have hχ₂ : IsIso ((finiteEtaleBaseChange (D.map e₂)).map χ) := by
    have h : (finiteEtaleBaseChange (D.map e₂)).map χ = (MorphismProperty.Over.isoMk
        (@asIso _ _ _ _ ((Over.pullback (D.map e₂)).map χ').left hiso)
        (MorphismProperty.Over.w ((finiteEtaleBaseChange (D.map e₂)).map χ))).hom := by
      ext
      rfl
    rw [h]
    infer_instance
  let ι₂ := (g ⁻¹ᵁ W₂.opens).ι
  have hι₂ : ι₂ = D.map e₂ ≫ D.map e₁ ≫ ι₀ := by
    simp only [ι₂, ι₀, D, preimageAffineOpenNhdsDiagram_map_ι]
  let comp₂ := finiteEtaleBaseChangeComp (D.map e₂) (D.map e₁ ≫ ι₀) ι₂ hι₂
  let comp₁ := finiteEtaleBaseChangeComp (D.map e₁) ι₀
  let ψ : (finiteEtaleBaseChange ι₂).obj A ≅ (finiteEtaleBaseChange ι₂).obj B :=
    comp₂.app A ≪≫ (finiteEtaleBaseChange (D.map e₂)).mapIso (comp₁.app A) ≪≫
      @asIso _ _ _ _ ((finiteEtaleBaseChange (D.map e₂)).map χ) hχ₂ ≪≫
      (finiteEtaleBaseChange (D.map e₂)).mapIso (comp₁.app B).symm ≪≫ (comp₂.app B).symm
  -- restriction to the dense open `g⁻¹(W₂)` is fully faithful
  have hne₂ : Nonempty (g ⁻¹ᵁ W₂.opens) :=
    ⟨genericFiberToPreimage g W₂.opens W₂.mem_opens hne.some⟩
  obtain ⟨hff⟩ := nonempty_fullyFaithful_finiteEtaleBaseChange_opensι T hT (g ⁻¹ᵁ W₂.opens)
  exact ⟨hff.preimageIso ψ⟩

section OpenRestriction

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsIntegral S]

/-- The generic fibre of the restriction of `f` to an open `O ⊆ X` is the part of `X_η` lying
over `O`. -/
theorem isPullback_fiberι_morphismRestrict (O : X.Opens) :
    IsPullback (f.fiberι (genericPoint S) ∣_ O)
      ((f.fiberι (genericPoint S) ⁻¹ᵁ O).ι ≫ f.fiberToSpecResidueField (genericPoint S))
      (O.ι ≫ f) (S.fromSpecResidueField (genericPoint S)) :=
  (isPullback_morphismRestrict (f.fiberι (genericPoint S)) O).paste_vert
    (IsPullback.of_hasPullback f (S.fromSpecResidueField (genericPoint S)))

/-- The total space of a finite étale Galois cover of the generic fibre of a smooth morphism is
irreducible. -/
theorem irreducibleSpace_galoisCover_left [Smooth f] {G : Type v} [Group G] [Finite G]
    (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G) : IrreducibleSpace Z.obj.left := by
  have : Etale Z.obj.hom := Z.obj.prop.2
  have : Smooth (Z.obj.hom ≫ f.fiberToSpecResidueField (genericPoint S)) := by
    have : Smooth (f.fiberToSpecResidueField (genericPoint S)) :=
      inferInstanceAs (Smooth (pullback.snd _ _))
    infer_instance
  have : ConnectedSpace Z.obj.left := Z.connected
  exact irreducibleSpace_of_smooth_of_connectedSpace (k := S.residueField (genericPoint S))
    (Z.obj.hom ≫ f.fiberToSpecResidueField (genericPoint S))

/-- The restriction of a finite étale Galois cover of `X_η` to an open meeting its image is
connected. -/
theorem connectedSpace_finiteEtaleBaseChange_opensι [Smooth f] {G : Type v} [Group G] [Finite G]
    (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G)
    (U : (f.fiber (genericPoint S)).Opens) (hU : ∃ x, Z.obj.hom x ∈ U) :
    ConnectedSpace ((finiteEtaleBaseChange U.ι).obj Z.obj).left := by
  have := irreducibleSpace_galoisCover_left f Z
  obtain ⟨x, hx⟩ := hU
  have : Nonempty (Z.obj.hom ⁻¹ᵁ U) := ⟨⟨x, hx⟩⟩
  exact (pullbackRestrictIsoRestrict Z.obj.hom U).hom.homeomorph.connectedSpace_iff.mpr
    (connectedSpace_opens_of_irreducibleSpace Z.obj.left _)

end OpenRestriction

/-- **The quasi-compact case over a quasi-compact open.** Granted Tag 0EYJ for quasi-compact
morphisms, the restriction of the generic Galois cover `Z` to the part of `X_η` over a
quasi-compact open `O ⊇ σ(S)` extends, equivariantly, to a finite étale Galois cover of `O`. -/
theorem exists_galoisCover_of_isCompact
    (hqc : ∀ {S X : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsIntegral S] [IsNormal S]
      [QuasiCompact f] [Smooth f] [GeometricallyConnected f]
      (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
      (G : Type v) [Group G] [Finite G]
      (_hG : ∀ s : S, IsUnit (Nat.card G : S.residueField s))
      (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G)
      (z : Spec (S.residueField (genericPoint S)) ⟶ Z.obj.left)
      (_hz : z ≫ Z.obj.hom = genericFiberSection f σ hσ),
      ∃ (Y : FiniteEtaleGaloisCover X G)
        (e : (finiteEtaleBaseChange (f.fiberι (genericPoint S))).obj Y.obj ≅ Z.obj),
        ∀ g : Gᵐᵒᵖ, (finiteEtaleBaseChange (f.fiberι (genericPoint S))).map (Y.action g).asIso.hom ≫
          e.hom = e.hom ≫ (Z.action g).asIso.hom)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsIntegral S] [IsNormal S]
    [Smooth f] [GeometricallyConnected f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (G : Type v) [Group G] [Finite G]
    (hG : ∀ s : S, IsUnit (Nat.card G : S.residueField s))
    (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G)
    (z : Spec (S.residueField (genericPoint S)) ⟶ Z.obj.left)
    (hz : z ≫ Z.obj.hom = genericFiberSection f σ hσ)
    (O : X.Opens) (hOc : IsCompact (O : Set X)) (hO : Set.range σ ⊆ O)
    (hZO : ConnectedSpace
      ((finiteEtaleBaseChange (f.fiberι (genericPoint S) ⁻¹ᵁ O).ι).obj Z.obj).left) :
    ∃ (Y : FiniteEtaleGaloisCover O.toScheme G)
      (e : (finiteEtaleBaseChange (f.fiberι (genericPoint S) ∣_ O)).obj Y.obj ≅
        (finiteEtaleBaseChange (f.fiberι (genericPoint S) ⁻¹ᵁ O).ι).obj Z.obj),
      ∀ g : Gᵐᵒᵖ,
        (finiteEtaleBaseChange (f.fiberι (genericPoint S) ∣_ O)).map (Y.action g).asIso.hom ≫
          e.hom = e.hom ≫
            (finiteEtaleBaseChange (f.fiberι (genericPoint S) ⁻¹ᵁ O).ι).map
              (Z.action g).asIso.hom := by
  let U := f.fiberι (genericPoint S) ⁻¹ᵁ O
  have : CompactSpace O.toScheme := isCompact_iff_compactSpace.mp hOc
  have : GeometricallyConnected (O.ι ≫ f) := geometricallyConnected_ι_comp f σ hσ O hO
  have hσO : Set.range σ ⊆ Set.range O.ι := by rwa [Scheme.Opens.range_ι]
  let σO : S ⟶ O.toScheme := IsOpenImmersion.lift O.ι σ hσO
  have hσO' : σO ≫ O.ι ≫ f = 𝟙 S := by
    rw [IsOpenImmersion.lift_fac_assoc, hσ]
  -- the generic fibre of `O ⟶ S` is the part `U` of `X_η` over `O`
  have hFib := isPullback_fiberι_morphismRestrict f O
  let kO : U.toScheme ≅ pullback (O.ι ≫ f) (S.fromSpecResidueField (genericPoint S)) :=
    hFib.isoPullback
  let ZO := Z.baseChange U.ι hZO
  let kinv : (O.ι ≫ f).fiber (genericPoint S) ⟶ U.toScheme := kO.inv
  have : IsIso kinv := inferInstanceAs (IsIso kO.inv)
  have hZO' : ConnectedSpace ((finiteEtaleBaseChange kinv).obj ZO.obj).left := by
    have : ConnectedSpace ((𝟭 Scheme).obj ZO.obj.left) := ZO.connected
    exact (asIso (pullback.fst ZO.obj.hom kinv)).hom.homeomorph.connectedSpace_iff.mpr
      inferInstance
  let ZO' := ZO.baseChange kinv hZO'
  have hk₁ : kinv ≫ (f.fiberι (genericPoint S) ∣_ O) = (O.ι ≫ f).fiberι (genericPoint S) :=
    hFib.isoPullback_inv_fst
  have hk₂ : kinv ≫ U.ι ≫ f.fiberToSpecResidueField (genericPoint S) =
      (O.ι ≫ f).fiberToSpecResidueField (genericPoint S) :=
    hFib.isoPullback_inv_snd
  -- the rational point
  have hgU : Set.range (genericFiberSection f σ hσ) ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact genericFiberSection_mem_preimage f σ hσ hO y
  let t : Spec (S.residueField (genericPoint S)) ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι (genericFiberSection f σ hσ) hgU
  have ht : t = genericFiberSection (O.ι ≫ f) σO hσO' ≫ kinv := by
    apply hFib.hom_ext
    · rw [Category.assoc, hk₁, ← cancel_mono O.ι, Category.assoc, morphismRestrict_ι,
        IsOpenImmersion.lift_fac_assoc, genericFiberSection_fiberι,
        genericFiberSection_fiberι (O.ι ≫ f) σO hσO', Category.assoc, IsOpenImmersion.lift_fac]
    · rw [Category.assoc, hk₂, IsOpenImmersion.lift_fac_assoc]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  let zU : Spec (S.residueField (genericPoint S)) ⟶ ZO.obj.left :=
    pullback.lift z t (by rw [hz, IsOpenImmersion.lift_fac])
  have hzU : zU ≫ ZO.obj.hom = t := pullback.lift_snd _ _ _
  let zO : Spec (S.residueField (genericPoint S)) ⟶ ZO'.obj.left :=
    pullback.lift zU (genericFiberSection (O.ι ≫ f) σO hσO') (hzU.trans ht)
  have hzO : zO ≫ ZO'.obj.hom = genericFiberSection (O.ι ≫ f) σO hσO' := pullback.lift_snd _ _ _
  obtain ⟨Y, e₁, he₁⟩ := hqc (O.ι ≫ f) σO hσO' G hG ZO' zO hzO
  -- transport the comparison to `U`
  obtain ⟨n, hn, hnact⟩ := GaloisCoverLimits.exists_equivariant_isPullback_of_iso
    ((O.ι ≫ f).fiberι (genericPoint S)) Y.obj ZO'.obj e₁ (fun g : Gᵐᵒᵖ ↦ (Y.action g).asIso.hom)
    (fun g : Gᵐᵒᵖ ↦ (ZO'.action g).asIso.hom) he₁
  let p₁ : ZO'.obj.left ⟶ ZO.obj.left := pullback.fst ZO.obj.hom kinv
  have : IsIso p₁ := inferInstanceAs (IsIso (pullback.fst ZO.obj.hom kinv))
  have hp₁ : p₁ ≫ ZO.obj.hom = ZO'.obj.hom ≫ kinv := pullback.condition
  let P : ZO.obj.left ⟶ Y.obj.left := inv p₁ ≫ n
  have hP : IsPullback P ZO.obj.hom Y.obj.hom (f.fiberι (genericPoint S) ∣_ O) := by
    refine hn.of_iso (asIso p₁) (Iso.refl _) (asIso kinv) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [P]
    · exact hp₁.symm
    · simp
    · rw [Iso.refl_hom, Category.comp_id, asIso_hom, hk₁]
  have hact (g : Gᵐᵒᵖ) : (ZO.action g).asIso.hom.left ≫ P = P ≫ (Y.action g).asIso.hom.left := by
    rw [← cancel_epi p₁]
    have h₁ : (ZO'.action g).asIso.hom.left ≫ p₁ = p₁ ≫ (ZO.action g).asIso.hom.left :=
      FiniteEtaleGaloisCover.baseChange_action_fst kinv ZO hZO' g
    simp only [P, ← Category.assoc, ← h₁]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    exact hnact g
  obtain ⟨e, he⟩ := GaloisCoverLimits.exists_equivariant_iso_of_isPullback
    (f.fiberι (genericPoint S) ∣_ O) Y.obj ZO.obj P hP (fun g : Gᵐᵒᵖ ↦ (Y.action g).asIso.hom)
    (fun g : Gᵐᵒᵖ ↦ (ZO.action g).asIso.hom) hact
  exact ⟨Y, e, he⟩

/-- **An extension over an open containing `O₀`.** A finite étale cover `F` of an open `W ⊇ O₀`
whose restriction to `O₀` is `E` is an extension of `E` over `W` in the sense of
`AlgebraicGeometry.FiniteEtaleGluing.Ext`. -/
theorem nonempty_ext_of_le {X : Scheme.{u}} {O₀ W : X.Opens} (h : O₀ ≤ W)
    (E : FiniteEtaleOver O₀.toScheme) (F : FiniteEtaleOver W.toScheme)
    (β : (finiteEtaleBaseChange (X.homOfLE h)).obj F ≅ E) :
    Nonempty (FiniteEtaleGluing.Ext O₀ E W) := by
  let i := X.homOfLE h
  let r := W.ι ∣_ O₀
  have hri : r ≫ i = (FiniteEtaleGluing.part O₀ W).ι := by
    rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]
  let m : pullback F.hom (FiniteEtaleGluing.part O₀ W).ι ⟶ pullback F.hom i :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ r) (by
      rw [pullback.condition, Category.assoc, hri])
  have hA : IsPullback m (pullback.snd F.hom (FiniteEtaleGluing.part O₀ W).ι)
      (pullback.snd F.hom i) r := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback F.hom i)
    rw [pullback.lift_fst, hri]
    exact IsPullback.of_hasPullback F.hom _
  have := isIso_hom_left_of_iso β
  have hB : IsPullback β.hom.left (pullback.snd F.hom i) E.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨(MorphismProperty.Over.w β.hom).trans (Category.comp_id _).symm⟩
  exact ⟨⟨F, m ≫ β.hom.left, by simpa only [Category.comp_id] using hA.paste_horiz hB⟩⟩

/-- **A finite étale cover of a quasi-compact open is determined by its generic fibre.** The form
of `AlgebraicGeometry.Abhyankar.nonempty_iso_of_iso_finiteEtaleBaseChange_fiberι` for an open of
an irreducible normal locally Noetherian `X` over a quasi-separated integral base, with the
generic fibre of the open written as the part of `X_η` over it. -/
theorem nonempty_iso_of_iso_finiteEtaleBaseChange_morphismRestrict {S X : Scheme.{u}}
    (f : X ⟶ S) [IsIntegral S] [QuasiSeparatedSpace S] [IsLocallyNoetherian X] [IsNormal X]
    [IrreducibleSpace X] (O : X.Opens) (hOc : IsCompact (O : Set X))
    (hne : Nonempty (f.fiberι (genericPoint S) ⁻¹ᵁ O)) (A B : FiniteEtaleOver O.toScheme)
    (φ : (finiteEtaleBaseChange (f.fiberι (genericPoint S) ∣_ O)).obj A ≅
      (finiteEtaleBaseChange (f.fiberι (genericPoint S) ∣_ O)).obj B) :
    Nonempty (A ≅ B) := by
  have : CompactSpace O.toScheme := isCompact_iff_compactSpace.mp hOc
  have : IsNoetherian O.toScheme := {}
  have : QuasiSeparated (O.ι ≫ f) := QuasiSeparated.of_quasiSeparatedSpace _
  have : Nonempty O := ⟨⟨f.fiberι (genericPoint S) hne.some.1, hne.some.2⟩⟩
  have := irreducibleSpace_opens_of_nonempty O
  have hFib := isPullback_fiberι_morphismRestrict f O
  let kinv : (O.ι ≫ f).fiber (genericPoint S) ⟶ (f.fiberι (genericPoint S) ⁻¹ᵁ O).toScheme :=
    hFib.isoPullback.inv
  let c := finiteEtaleBaseChangeComp kinv (f.fiberι (genericPoint S) ∣_ O) _
    hFib.isoPullback_inv_fst.symm
  exact nonempty_iso_of_iso_finiteEtaleBaseChange_fiberι (O.ι ≫ f)
    isGeometricallyUnibranch_of_isNormal ⟨hFib.isoPullback.hom hne.some⟩ A B
    (c.app A ≪≫ (finiteEtaleBaseChange kinv).mapIso φ ≪≫ (c.app B).symm)

/-- **Tag 0EYJ reduces to quasi-compact morphisms.** Granted [Stacks, Tag 0EYJ] for
quasi-compact `f`, it holds for every smooth `f : X ⟶ S` with geometrically connected fibres and a
section `σ`, over an integral normal Noetherian `S`.

The proof: `X` is irreducible and normal. Fix a quasi-compact open `O₀ ⊇ σ(S)` and the extension
`Y₀` of `Z` over `O₀` given by the quasi-compact case. Every point of `X` lies in a quasi-compact
open `W ⊇ O₀`, over which `Z` extends again; the restriction of that extension to `O₀` is `Y₀`,
both being determined by their generic fibres. Restriction of finite étale covers to dense opens
of `X` is fully faithful, so these local extensions glue to a finite étale cover of `X`
(`AlgebraicGeometry.FiniteEtaleGluing.exists_extension`), which carries the Galois structure of
`Y₀` (`AlgebraicGeometry.exists_finiteEtaleGaloisCover_of_fullyFaithful`) and restricts to `Z`
on `X_η`, by full faithfulness of restriction to the dense open `X_η ∩ O₀` of `X_η`. -/
theorem exists_finiteEtaleGaloisCover_extending_genericFiber_of_quasiCompact_case
    (hqc : (∀ {S X : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsIntegral S] [IsNormal S]
      [QuasiCompact f] [Smooth f] [GeometricallyConnected f]
      (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
      (G : Type v) [Group G] [Finite G]
      (_hG : ∀ s : S, IsUnit (Nat.card G : S.residueField s))
      (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G)
      (z : Spec (S.residueField (genericPoint S)) ⟶ Z.obj.left)
      (_hz : z ≫ Z.obj.hom = genericFiberSection f σ hσ),
      ∃ (Y : FiniteEtaleGaloisCover X G)
        (e : (finiteEtaleBaseChange (f.fiberι (genericPoint S))).obj Y.obj ≅ Z.obj),
        ∀ g : Gᵐᵒᵖ, (finiteEtaleBaseChange (f.fiberι (genericPoint S))).map (Y.action g).asIso.hom ≫
          e.hom = e.hom ≫ (Z.action g).asIso.hom)) :
    ∀ {S X : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsIntegral S] [IsNormal S]
      [Smooth f] [GeometricallyConnected f]
      (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
      (G : Type v) [Group G] [Finite G]
      (_hG : ∀ s : S, IsUnit (Nat.card G : S.residueField s))
      (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G)
      (z : Spec (S.residueField (genericPoint S)) ⟶ Z.obj.left)
      (_hz : z ≫ Z.obj.hom = genericFiberSection f σ hσ),
      ∃ (Y : FiniteEtaleGaloisCover X G)
        (e : (finiteEtaleBaseChange (f.fiberι (genericPoint S))).obj Y.obj ≅ Z.obj),
        ∀ g : Gᵐᵒᵖ, (finiteEtaleBaseChange (f.fiberι (genericPoint S))).map (Y.action g).asIso.hom ≫
          e.hom = e.hom ≫ (Z.action g).asIso.hom := by
  intro S X f _ _ _ _ _ σ hσ G _ _ hG Z z hz
  -- the geometry of `X`
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNormal X := isNormal_of_smooth f
  have : ConnectedSpace X := GeometricallyConnected.connectedSpace f f.isOpenMap
  have : IrreducibleSpace X := by
    -- a connected locally Noetherian normal scheme is irreducible (Tag 033M on affine opens)
    refine Topology.irreducibleSpace_of_connectedSpace_of_forall_exists_isIrreducible fun x ↦ ?_
    obtain ⟨V, hxV⟩ : ∃ V : X.affineOpens, x ∈ V.1 := by
      rw [← TopologicalSpace.Opens.mem_iSup, iSup_affineOpens_eq_top]
      trivial
    have : IsAffine V.1.toScheme := V.2
    have : IsNoetherian V.1.toScheme := ⟨⟩
    have : IsNormal V.1.toScheme := inferInstance
    obtain ⟨ι, _, W, _, hint, ⟨e⟩⟩ :=
      (isNormal_iff_exists_iso_finite_coproduct_integral_normal V.1.toScheme).mp inferInstance
    obtain ⟨⟨i, w⟩, hw⟩ := (sigmaMk W).surjective (e.hom ⟨x, hxV⟩)
    rw [sigmaMk_mk] at hw
    let j : W i ⟶ X := Sigma.ι W i ≫ e.inv ≫ V.1.ι
    have := hint i
    refine ⟨Set.range j, j.isOpenEmbedding.isOpen_range, ⟨w, ?_⟩, ?_⟩
    · change V.1.ι (e.inv (Sigma.ι W i w)) = x
      rw [hw]
      change (e.hom ≫ e.inv ≫ V.1.ι) ⟨x, hxV⟩ = x
      rw [e.hom_inv_id_assoc]
      rfl
    · rw [← Set.image_univ]
      exact ((IrreducibleSpace.isIrreducible_univ (W i)).image j j.continuous.continuousOn).2
  have hXu : IsGeometricallyUnibranch X := isGeometricallyUnibranch_of_isNormal
  -- the point of `X_η` given by the section
  obtain ⟨pt⟩ : Nonempty (Spec (S.residueField (genericPoint S))) := inferInstance
  have hZconn (O : X.Opens) (hO : Set.range σ ⊆ O) : ConnectedSpace
      ((finiteEtaleBaseChange (f.fiberι (genericPoint S) ⁻¹ᵁ O).ι).obj Z.obj).left :=
    connectedSpace_finiteEtaleBaseChange_opensι f Z _ ⟨z pt, by
      rw [← Scheme.Hom.comp_apply, hz]
      exact genericFiberSection_mem_preimage f σ hσ hO pt⟩
  -- a quasi-compact open through the section and the extension over it
  obtain ⟨O₀, hO₀c, hO₀⟩ := exists_isCompact_opens_superset (isCompact_range σ.continuous)
  obtain ⟨Y₀, e₀, he₀⟩ :=
    exists_galoisCover_of_isCompact hqc f σ hσ G hG Z z hz O₀ hO₀c hO₀ (hZconn O₀ hO₀)
  let E := Y₀.obj
  have hne₀ : Nonempty (f.fiberι (genericPoint S) ⁻¹ᵁ O₀) :=
    ⟨⟨_, genericFiberSection_mem_preimage f σ hσ hO₀ pt⟩⟩
  -- extensions over neighbourhoods of every point
  have hloc (x : X) : ∃ W : X.Opens, x ∈ W ∧ Nonempty (FiniteEtaleGluing.Ext O₀ E W) := by
    obtain ⟨W, hWc, hW⟩ :=
      exists_isCompact_opens_superset (hO₀c.union (isCompact_singleton (x := x)))
    have hO₀W : O₀ ≤ W := fun y hy ↦ hW (Or.inl hy)
    have hσW : Set.range σ ⊆ W := hO₀.trans hO₀W
    obtain ⟨YW, eW, -⟩ :=
      exists_galoisCover_of_isCompact hqc f σ hσ G hG Z z hz W hWc hσW (hZconn W hσW)
    let i := X.homOfLE hO₀W
    let h := (f.fiber (genericPoint S)).homOfLE (Scheme.Hom.preimage_mono
      (f.fiberι (genericPoint S)) hO₀W)
    have hfac : (f.fiberι (genericPoint S) ∣_ O₀) ≫ i = h ≫ (f.fiberι (genericPoint S) ∣_ W) := by
      rw [← cancel_mono W.ι]
      simp only [Category.assoc, i, h, Scheme.homOfLE_ι, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
    let c₁ := finiteEtaleBaseChangeComp (f.fiberι (genericPoint S) ∣_ O₀) i
    let c₂ := finiteEtaleBaseChangeComp h (f.fiberι (genericPoint S) ∣_ W) _ hfac
    let c₃ := finiteEtaleBaseChangeComp h (f.fiberι (genericPoint S) ⁻¹ᵁ W).ι _
      (Scheme.homOfLE_ι _ _).symm
    let φ := (c₁.app YW.obj).symm ≪≫ c₂.app YW.obj ≪≫
      (finiteEtaleBaseChange h).mapIso eW ≪≫ (c₃.app Z.obj).symm ≪≫ e₀.symm
    obtain ⟨β⟩ := nonempty_iso_of_iso_finiteEtaleBaseChange_morphismRestrict f O₀ hO₀c hne₀ _ _ φ
    exact ⟨W, hW (Or.inr rfl), nonempty_ext_of_le hO₀W E YW.obj β⟩
  -- restriction from an open to its part over `O₀` is fully faithful
  have : Nonempty O₀ := ⟨⟨_, hO₀ ⟨genericPoint S, rfl⟩⟩⟩
  have hff (W : X.Opens) :
      Nonempty (finiteEtaleBaseChange (FiniteEtaleGluing.part O₀ W).ι).FullyFaithful := by
    rcases isEmpty_or_nonempty W with hW | hW
    · have htop : FiniteEtaleGluing.part O₀ W = ⊤ := by
        ext x
        exact (hW.false x).elim
      rw [htop]
      have : (finiteEtaleBaseChange (⊤ : W.toScheme.Opens).ι).IsEquivalence := by
        let eW := asIso (⊤ : W.toScheme.Opens).ι
        exact (CategoryTheory.Equivalence.mk (finiteEtaleBaseChange eW.hom)
          (finiteEtaleBaseChange eW.inv)
          (finiteEtaleBaseChangeId.symm ≪≫
            finiteEtaleBaseChangeComp eW.inv eW.hom (𝟙 _) eW.inv_hom_id.symm)
          ((finiteEtaleBaseChangeComp eW.hom eW.inv (𝟙 _) eW.hom_inv_id.symm).symm ≪≫
            finiteEtaleBaseChangeId)).isEquivalence_functor
      exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩
    · have := irreducibleSpace_opens_of_nonempty W
      obtain ⟨y, hy₀, hyW⟩ := (IrreducibleSpace.isIrreducible_univ X).2 O₀ W O₀.isOpen W.isOpen
        ⟨_, trivial, hO₀ ⟨genericPoint S, rfl⟩⟩ ⟨hW.some.1, trivial, hW.some.2⟩
      have : Nonempty (FiniteEtaleGluing.part O₀ W) := ⟨⟨⟨y, hyW.2⟩, hyW.1⟩⟩
      exact nonempty_fullyFaithful_finiteEtaleBaseChange_opensι W.toScheme
        isGeometricallyUnibranch_of_isNormal _
  obtain ⟨F, ⟨α⟩⟩ := FiniteEtaleGluing.exists_extension (U := O₀) (E := E) hff hloc
  -- the glued cover is connected, its part over the dense open `O₀` being connected
  have hF₂ : Etale F.hom := F.prop.2
  have hFconn : ConnectedSpace F.left := by
    have hd : DenseRange (pullback.fst F.hom O₀.ι) := by
      rw [DenseRange, Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
      exact (O₀.isOpen.dense ⟨_, hO₀ ⟨genericPoint S, rfl⟩⟩).preimage F.hom.isOpenMap
    have : ConnectedSpace E.left := Y₀.connected
    have := isIso_hom_left_of_iso α
    have : ConnectedSpace ↥(pullback F.hom O₀.ι) :=
      (asIso α.hom.left).hom.homeomorph.connectedSpace_iff.mpr inferInstance
    have : Nonempty F.left := ⟨pullback.fst F.hom O₀.ι (Nonempty.some inferInstance)⟩
    exact { toPreconnectedSpace := hd.preconnectedSpace (pullback.fst F.hom O₀.ι).continuous,
            toNonempty := inferInstance }
  -- the Galois structure
  obtain ⟨hffX⟩ := nonempty_fullyFaithful_finiteEtaleBaseChange_opensι X hXu O₀
  obtain ⟨Y', e', he'⟩ :=
    exists_finiteEtaleGaloisCover_of_fullyFaithful O₀.ι hffX G F hFconn Y₀ α
  -- the comparison with `Z` on `X_η`, through its dense open `X_η ∩ O₀`
  have : IsNormal (Spec (S.residueField (genericPoint S))) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed _)
  have : Smooth (f.fiberToSpecResidueField (genericPoint S)) :=
    inferInstanceAs (Smooth (pullback.snd _ _))
  have : IrreducibleSpace (f.fiber (genericPoint S)) :=
    irreducibleSpace_of_smooth_of_connectedSpace (k := S.residueField (genericPoint S))
      (f.fiberToSpecResidueField (genericPoint S))
  have : IsNormal (f.fiber (genericPoint S)) :=
    isNormal_of_smooth (f.fiberToSpecResidueField (genericPoint S))
  have : Nonempty (f.fiberι (genericPoint S) ⁻¹ᵁ O₀) := hne₀
  obtain ⟨hffη⟩ := nonempty_fullyFaithful_finiteEtaleBaseChange_opensι (f.fiber (genericPoint S))
    isGeometricallyUnibranch_of_isNormal (f.fiberι (genericPoint S) ⁻¹ᵁ O₀)
  let c₁ := finiteEtaleBaseChangeComp (f.fiberι (genericPoint S) ⁻¹ᵁ O₀).ι
    (f.fiberι (genericPoint S))
  let c₂ := finiteEtaleBaseChangeComp (f.fiberι (genericPoint S) ∣_ O₀) O₀.ι _
    (morphismRestrict_ι _ _).symm
  let β := (c₁.app Y'.obj).symm ≪≫ c₂.app Y'.obj ≪≫
    (finiteEtaleBaseChange (f.fiberι (genericPoint S) ∣_ O₀)).mapIso e' ≪≫ e₀
  have hβ (g : Gᵐᵒᵖ) : (finiteEtaleBaseChange (f.fiberι (genericPoint S) ⁻¹ᵁ O₀).ι).map
      ((finiteEtaleBaseChange (f.fiberι (genericPoint S))).map (Y'.action g).asIso.hom) ≫ β.hom =
      β.hom ≫
        (finiteEtaleBaseChange (f.fiberι (genericPoint S) ⁻¹ᵁ O₀).ι).map
          (Z.action g).asIso.hom := by
    have n₁ := c₁.inv.naturality (Y'.action g).asIso.hom
    have n₂ := c₂.hom.naturality (Y'.action g).asIso.hom
    simp only [Functor.comp_map] at n₁ n₂
    simp only [β, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
      Category.assoc]
    rw [reassoc_of% n₁, reassoc_of% n₂, ← Functor.map_comp_assoc, he' g, Functor.map_comp_assoc,
      he₀ g]
  refine ⟨Y', hffη.preimageIso β, fun g ↦ hffη.map_injective ?_⟩
  simpa only [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage] using hβ g

end AlgebraicGeometry.Abhyankar
