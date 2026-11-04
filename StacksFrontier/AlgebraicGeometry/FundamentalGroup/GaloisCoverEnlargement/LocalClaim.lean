module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.GaloisCoverDiscreteValuationRing
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverEnlargement.GenericSection
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.BaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.DenseOpen
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuncturedSpectrumGalois.Extension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE

/-!
# The local claim in the proof of Stacks Tag 0EYJ

Let `S` be a normal integral Noetherian scheme with generic point `η`, `f : X ⟶ S` smooth with
geometrically connected fibres and a section `σ`, and `Y` a finite étale Galois cover of
`f⁻¹(U)` with group `G` extending a generic Galois cover `Z ⟶ X_η` with a `κ(η)`-point over
`σ(η)`. Let `s` be a point outside `U` whose proper generizations all lie in `U`, so that the
preimage of `U` in `Spec 𝒪_{S, s}` is the punctured spectrum. Then the restriction of `Y` to
`X ×_S (Spec 𝒪_{S, s} ∖ {s})` extends to a finite étale cover of `X ×_S Spec 𝒪_{S, s}`: by the
discrete valuation ring case of [Stacks, Tag 0EYJ] if `dim 𝒪_{S, s} = 1`, and by the local claim
at a point of codimension at least two otherwise.

## Main results

* `AlgebraicGeometry.Abhyankar.exists_finiteEtale_extension_to_stalk`: the local claim.
* `AlgebraicGeometry.Abhyankar.connectedSpace_baseChange_of_stalk`: the restriction of `Y` to an
  open of `X ×_S Spec 𝒪_{S, s}` containing the generic fibre is connected.

## References

* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Algebraization (IsInfinitesimalSectionsComplete
  CompletionFullyFaithfulOnFiniteLocallyFree)

universe v u

namespace AlgebraicGeometry.Abhyankar

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsIntegral S]

/-- The map `Spec κ(η) ⟶ Spec 𝒪_{S, s}` induced by the generization `η ⤳ s` lands on the generic
point of `Spec 𝒪_{S, s}`. -/
lemma specMap_stalkSpecializes_residue_apply (s : S) [IsIntegral (Spec (S.presheaf.stalk s))]
    (p : Spec (S.residueField (genericPoint S))) :
    Spec.map (S.presheaf.stalkSpecializes (genericPoint_specializes s) ≫
      S.residue (genericPoint S)) p = genericPoint (Spec (S.presheaf.stalk s)) := by
  apply (S.fromSpecStalk s).isEmbedding.injective
  rw [fromSpecStalk_genericPoint, ← Scheme.Hom.comp_apply, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.fromSpecResidueField_apply _ _

/-- A morphism whose image lies in an open subscheme factors through its inclusion. -/
private theorem exists_lift_opens_ι {X Y : Scheme.{u}} (U : Y.Opens) (g : X ⟶ Y)
    (h : ∀ x, g x ∈ U) : ∃ l : X ⟶ U.toScheme, l ≫ U.ι = g :=
  ⟨IsOpenImmersion.lift U.ι g (by rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact h x),
    IsOpenImmersion.lift_fac _ _ _⟩

/-- If `j` is compatible with `a, b` and `a', b'`, an isomorphism of the base changes of `Y'` along
`a` and of `Y` along `b` restricts along `j` to one for `a'` and `b'`. -/
private theorem nonempty_iso_baseChange_of_comp {A B C D : Scheme.{u}} (j : A ⟶ B) (a : B ⟶ C)
    (b : B ⟶ D) (a' : A ⟶ C) (b' : A ⟶ D) (ha : j ≫ a = a') (hb : b' = j ≫ b)
    (Y' : FiniteEtaleOver C) (Y : FiniteEtaleOver D)
    (e : (finiteEtaleBaseChange a).obj Y' ≅ (finiteEtaleBaseChange b).obj Y) :
    Nonempty ((finiteEtaleBaseChange a').obj Y' ≅ (finiteEtaleBaseChange b').obj Y) :=
  ⟨(finiteEtaleBaseChangeComp j a a' ha.symm).app Y' ≪≫ (finiteEtaleBaseChange j).mapIso e ≪≫
    (finiteEtaleBaseChangeComp j b b' hb).symm.app Y⟩

/-- **The restriction of `Y` to the part of `X ×_S Spec 𝒪_{S, s}` over the punctured spectrum is
connected.** More generally, for an open `V` of `X ×_S Spec 𝒪_{S, s}` lying over `f⁻¹(U)` and
containing the generic fibre, the restriction of `Y` to `V` is connected: its points over the
generic point of `Spec 𝒪_{S, s}` form a copy of the connected generic cover `Z`, and they are
dense since the restriction is flat over `Spec 𝒪_{S, s}`. -/
theorem connectedSpace_baseChange_of_stalk [Flat f] (s : S)
    [IsIntegral (Spec (S.presheaf.stalk s))] {U : S.Opens} (hη : genericPoint S ∈ U)
    {G : Type v} [Group G] [Finite G] (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G)
    (Y : FiniteEtaleOver (f ⁻¹ᵁ U).toScheme)
    (e : (finiteEtaleBaseChange (genericFiberToPreimage f U hη)).obj Y ≅ Z.obj)
    (V : (pullback f (S.fromSpecStalk s)).Opens) (q : V.toScheme ⟶ (f ⁻¹ᵁ U).toScheme)
    (hq : q ≫ (f ⁻¹ᵁ U).ι = V.ι ≫ pullback.fst f (S.fromSpecStalk s))
    (hVgen : ∀ x, pullback.snd f (S.fromSpecStalk s) x =
      genericPoint (Spec (S.presheaf.stalk s)) → x ∈ V) :
    ConnectedSpace ((finiteEtaleBaseChange q).obj Y).left := by
  let ι := S.fromSpecStalk s
  let c := Spec.map (S.presheaf.stalkSpecializes (genericPoint_specializes s) ≫
    S.residue (genericPoint S))
  have hc : c ≫ ι = S.fromSpecResidueField (genericPoint S) := by
    show Spec.map (_ ≫ _) ≫ _ = _
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl
  have hcgen := specMap_stalkSpecializes_residue_apply s
  -- the generic fibre of `X` inside `X ×_S Spec 𝒪_{S, s}`
  let a' : f.fiber (genericPoint S) ⟶ pullback f ι :=
    pullback.lift (f.fiberι (genericPoint S)) (f.fiberToSpecResidueField _ ≫ c)
      (by rw [Category.assoc, hc]; exact f.fiber_fac _)
  have ha'snd (w) : pullback.snd f ι (a' w) = genericPoint (Spec (S.presheaf.stalk s)) := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply]
    exact hcgen _
  -- every point over the generic point of `Spec 𝒪_{S, s}` comes from the generic fibre
  have hra' (x) (hx : pullback.snd f ι x = genericPoint (Spec (S.presheaf.stalk s))) :
      x ∈ Set.range a' := by
    let m : pullback (pullback.snd f ι) c ⟶ f.fiber (genericPoint S) :=
      pullback.lift (pullback.fst _ c ≫ pullback.fst f ι) (pullback.snd _ c) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
          Category.assoc, hc])
    have hm : m ≫ a' = pullback.fst (pullback.snd f ι) c := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst]
        exact pullback.lift_fst _ _ _
      · calc (m ≫ a') ≫ pullback.snd f ι = m ≫ (a' ≫ pullback.snd f ι) := Category.assoc _ _ _
          _ = m ≫ (f.fiberToSpecResidueField _ ≫ c) := congrArg (m ≫ ·) (pullback.lift_snd _ _ _)
          _ = (m ≫ f.fiberToSpecResidueField _) ≫ c := (Category.assoc _ _ _).symm
          _ = pullback.snd _ c ≫ c := congrArg (· ≫ c) (pullback.lift_snd _ _ _)
          _ = _ := pullback.condition.symm
    obtain ⟨w, rfl⟩ : x ∈ Set.range (pullback.fst (pullback.snd f ι) c) := by
      rw [Scheme.Pullback.range_fst]
      obtain ⟨p⟩ := (inferInstance : Nonempty (Spec (S.residueField (genericPoint S))))
      exact ⟨p, (hcgen p).trans hx.symm⟩
    exact ⟨m w, by rw [← Scheme.Hom.comp_apply, hm]⟩
  obtain ⟨a, haι⟩ := exists_lift_opens_ι V a' fun w ↦ hVgen _ (ha'snd w)
  have haq : a ≫ q = genericFiberToPreimage f U hη := by
    rw [← cancel_mono (f ⁻¹ᵁ U).ι, Category.assoc, hq, ← Category.assoc, haι,
      genericFiberToPreimage_ι]
    exact pullback.lift_fst _ _ _
  let YV := (finiteEtaleBaseChange q).obj Y
  -- the part over the generic fibre is a copy of `Z`
  let eQ : (finiteEtaleBaseChange a).obj YV ≅ Z.obj :=
    (finiteEtaleBaseChangeComp a q _ haq.symm).symm.app Y ≪≫ e
  let eQL : Z.obj.left ⟶ ((finiteEtaleBaseChange a).obj YV).left :=
    ((MorphismProperty.Over.forget finiteEtale ⊤ _ ⋙ Over.forget _).mapIso eQ).inv
  have : ConnectedSpace Z.obj.left := Z.connected
  have hs : Function.Surjective eQL := by
    have : IsIso eQL := Iso.isIso_inv
      ((MorphismProperty.Over.forget finiteEtale ⊤ _ ⋙ Over.forget _).mapIso eQ)
    exact eQL.homeomorph.surjective
  have : ConnectedSpace ((finiteEtaleBaseChange a).obj YV).left :=
    hs.connectedSpace eQL.continuous
  -- and it is dense
  have : Etale YV.hom := YV.prop.2
  let φ := YV.hom ≫ V.ι ≫ pullback.snd f ι
  have hd : DenseRange (finiteEtaleBaseChangeProj a YV) := by
    intro y
    obtain ⟨y', hy'y, hφy'⟩ := Flat.generalizingMap φ (genericPoint_specializes (φ y))
    refine hy'y.mem_closed isClosed_closure (subset_closure ?_)
    show y' ∈ Set.range (pullback.fst YV.hom a)
    rw [Scheme.Pullback.range_fst]
    obtain ⟨w, hw⟩ := hra' (V.ι (YV.hom y')) hφy'
    exact ⟨w, V.ι.isOpenEmbedding.injective (by rw [← hw, ← haι]; rfl)⟩
  have : PreconnectedSpace YV.left :=
    hd.preconnectedSpace (finiteEtaleBaseChangeProj a YV).continuous
  obtain ⟨y⟩ := (inferInstance : Nonempty ((finiteEtaleBaseChange a).obj YV).left)
  exact { toNonempty := ⟨finiteEtaleBaseChangeProj a YV y⟩ }

/-- **The local claim in the proof of [Stacks, Tag 0EYJ].** Let `s` be a point outside `U` all of
whose proper generizations lie in `U`, so that `U` pulls back to the punctured spectrum of
`𝒪_{S, s}`. Then the restriction of `Y` to the part of `X ×_S Spec 𝒪_{S, s}` over `U` is the
restriction of a finite étale cover of `X ×_S Spec 𝒪_{S, s}`. If `dim 𝒪_{S, s} = 1` this is the
discrete valuation ring case of Tag 0EYJ (`h0BMA`, `h0EYD`); otherwise it is the local claim at a
point of codimension at least two, whose section over the punctured spectrum comes from
the rational point of `Z` (`AlgebraicGeometry.exists_section_of_genericPoint`). -/
theorem exists_finiteEtale_extension_to_stalk (h0BMA : PurityAtRegularLocalRings.{u})
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover)
    [IsNoetherian S] [IsNormal S] [Smooth f] [GeometricallyConnected f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) (G : Type v) [Group G] [Finite G]
    (hG : ∀ s : S, IsUnit (Nat.card G : S.residueField s))
    (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G)
    (z : Spec (S.residueField (genericPoint S)) ⟶ Z.obj.left)
    (hz : z ≫ Z.obj.hom = genericFiberSection f σ hσ)
    {U : S.Opens} (hη : genericPoint S ∈ U) (Y : FiniteEtaleGaloisCover (f ⁻¹ᵁ U).toScheme G)
    (e : (finiteEtaleBaseChange (genericFiberToPreimage f U hη)).obj Y.obj ≅ Z.obj)
    (s : S) (hP : ∀ p : Spec (S.presheaf.stalk s),
      S.fromSpecStalk s p ∈ U ↔ p ≠ IsLocalRing.closedPoint (S.presheaf.stalk s)) :
    ∃ YO : FiniteEtaleOver (pullback f (S.fromSpecStalk s)),
      Nonempty ((finiteEtaleBaseChange
          (pullback.fst f (S.fromSpecStalk s) ⁻¹ᵁ (f ⁻¹ᵁ U)).ι).obj YO ≅
        (finiteEtaleBaseChange (pullback.fst f (S.fromSpecStalk s) ∣_ (f ⁻¹ᵁ U))).obj Y.obj) := by
  classical
  let O := S.presheaf.stalk s
  let ι := S.fromSpecStalk s
  let fO := pullback.snd f ι
  have : IsIntegrallyClosed O := IsNormal.stalk_normal s
  have : IsDomain O := IsNormal.stalk_isDomain s
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNormal X := isNormal_of_smooth f
  let σO : Spec O ⟶ pullback f ι := pullback.lift (ι ≫ σ) (𝟙 _) (by
    rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  have hσO : σO ≫ fO = 𝟙 _ := pullback.lift_snd _ _ _
  have hσOfst : σO ≫ pullback.fst f ι = ι ≫ σ := pullback.lift_fst _ _ _
  let XP := pullback.fst f ι ⁻¹ᵁ (f ⁻¹ᵁ U)
  let k := pullback.fst f ι ∣_ (f ⁻¹ᵁ U)
  have hk : k ≫ (f ⁻¹ᵁ U).ι = XP.ι ≫ pullback.fst f ι := morphismRestrict_ι _ _
  have hgenι : ι (genericPoint (Spec O)) = genericPoint S := fromSpecStalk_genericPoint s
  have hXP (x : ↥(pullback f ι)) : x ∈ XP ↔ ι (fO x) ∈ U := by
    show f (pullback.fst f ι x) ∈ U ↔ _
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hgenP : genericPoint (Spec O) ≠ IsLocalRing.closedPoint O := (hP _).1 (by rwa [hgenι])
  -- the section of `Y` over `U` through `σ`
  obtain ⟨σU, hσUι⟩ := exists_lift_opens_ι (f ⁻¹ᵁ U) (U.ι ≫ σ) fun x ↦ by
    show (σ ≫ f) (U.ι x) ∈ U
    rw [hσ]
    exact x.2
  obtain ⟨ηU, hηUι⟩ := exists_lift_opens_ι U (S.fromSpecResidueField (genericPoint S)) fun p ↦ by
    rw [Scheme.fromSpecResidueField_apply]
    exact hη
  let H := (finiteEtaleBaseChange σU).obj Y.obj
  let pz : Spec (S.residueField (genericPoint S)) ⟶ Y.obj.left :=
    z ≫ e.inv.left ≫ finiteEtaleBaseChangeProj (genericFiberToPreimage f U hη) Y.obj
  have hpz : pz ≫ Y.obj.hom = ηU ≫ σU := by
    rw [← cancel_mono (f ⁻¹ᵁ U).ι]
    simp only [pz, Category.assoc, finiteEtaleBaseChangeProj_comp_hom, genericFiberToPreimage_ι,
      hσUι]
    rw [← Category.assoc e.inv.left, MorphismProperty.Over.w e.inv, ← Category.assoc, hz,
      genericFiberSection_fiberι, ← hηUι, Category.assoc]
  let pH : Spec (S.residueField (genericPoint S)) ⟶ H.left := pullback.lift pz ηU hpz
  have hpH : pH ≫ H.hom = ηU := pullback.lift_snd _ _ _
  obtain ⟨tH, htH⟩ := exists_section_of_genericPoint U hη H pH (by
    rw [← Category.assoc, hpH, hηUι])
  let τ : U.toScheme ⟶ Y.obj.left := tH ≫ finiteEtaleBaseChangeProj σU Y.obj
  have hτ : τ ≫ Y.obj.hom = σU := by
    simp only [τ, Category.assoc, finiteEtaleBaseChangeProj_comp_hom]
    rw [← Category.assoc, htH, Category.id_comp]
  -- the order of `G` is invertible on `Spec 𝒪_{S, s}`
  have hGres : ∀ p : Spec O, IsUnit (Nat.card G : (Spec O).residueField p) :=
    isUnit_natCast_residueField_of_hom ι _ hG
  have hGO : IsUnit (Nat.card G : O) := by
    have h := hG s
    have : IsLocalHom (S.residue s).hom := inferInstanceAs (IsLocalHom (IsLocalRing.residue O))
    rw [← map_natCast (S.residue s).hom] at h
    exact (isUnit_map_iff (S.residue s).hom _).mp h
  -- `𝒪_{S, s}` is not a field
  have hnf : ¬ IsField O := fun hF ↦ hgenP <| by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext (IsLocalRing.isField_iff_maximalIdeal_eq.mp hF).symm
  by_cases hdim : 2 ≤ ringKrullDim O
  · -- codimension at least two: the local claim
    let P := Stacks.puncturedSpectrum O
    have hPU (p : Spec O) : p ∈ P ↔ ι p ∈ U :=
      (Stacks.mem_puncturedSpectrum O).trans (hP p).symm
    let V := fO ⁻¹ᵁ P
    have hVX : V = XP := by
      ext x
      show fO x ∈ P ↔ x ∈ XP
      rw [hPU, hXP]
    have hVgen (x) (hx : fO x = genericPoint (Spec O)) : x ∈ V := by
      show fO x ∈ P
      rw [hx, hPU, hgenι]
      exact hη
    let q := (pullback f ι).homOfLE hVX.le ≫ k
    have hq : q ≫ (f ⁻¹ᵁ U).ι = V.ι ≫ pullback.fst f ι := by
      rw [Category.assoc, hk, Scheme.homOfLE_ι_assoc]
    let YJ := Y.baseChange q (connectedSpace_baseChange_of_stalk f s hη Z Y.obj e V q hq hVgen)
    obtain ⟨PU, hPUι⟩ := exists_lift_opens_ι U (P.ι ≫ ι) fun p ↦ (hPU p.1).1 p.2
    obtain ⟨σP, hσPι⟩ := exists_lift_opens_ι V (P.ι ≫ σO) fun p ↦ by
      show fO (σO (P.ι p)) ∈ P
      rw [show fO (σO (P.ι p)) = P.ι p by rw [← Scheme.Hom.comp_apply, hσO]; rfl]
      exact p.2
    have htw : (PU ≫ τ) ≫ Y.obj.hom = σP ≫ q := by
      rw [← cancel_mono (f ⁻¹ᵁ U).ι]
      simp only [Category.assoc, reassoc_of% hτ, hσUι, reassoc_of% hPUι, hq, reassoc_of% hσPι,
        hσOfst]
    let t : P.toScheme ⟶ YJ.obj.left := pullback.lift (PU ≫ τ) σP htw
    have ht : t ≫ YJ.obj.hom ≫ V.ι = P.ι ≫ σO := by
      have : t ≫ YJ.obj.hom = σP := pullback.lift_snd _ _ _
      rw [← Category.assoc, this, hσPι]
    obtain ⟨Y', e', -⟩ :=
      exists_finiteEtaleGaloisCover_extending_puncturedSpectrum O hdim fO σO hσO G hGO
        YJ t ht
    let i := (pullback f ι).isoOfEq hVX
    have hi : i.inv ≫ V.ι = XP.ι := Scheme.isoOfEq_inv_ι _ _
    have hik : k = i.inv ≫ q := by
      rw [← cancel_mono (f ⁻¹ᵁ U).ι, hk, Category.assoc, hq, ← Category.assoc, hi]
    exact ⟨Y'.obj, nonempty_iso_baseChange_of_comp i.inv V.ι q XP.ι k hi hik Y'.obj Y.obj e'⟩
  · -- dimension one: a discrete valuation ring
    have hdim1 : ringKrullDim O = 1 := by
      apply le_antisymm
      · by_contra h
        exact hdim (Order.succ_le_of_lt (lt_of_not_ge h))
      · have : ¬ ringKrullDim O ≤ 0 := fun h ↦ hnf (by
          have : Ring.KrullDimLE 0 O := Ring.krullDimLE_iff.mpr h
          exact Ring.KrullDimLE.isField_of_isDomain)
        exact Order.succ_le_of_lt (lt_of_not_ge this)
    have h5 : IsNoetherianRing O ∧ IsLocalRing O ∧ IsDomain O ∧ IsIntegrallyClosed O ∧
        ringKrullDim O = 1 := ⟨inferInstance, inferInstance, inferInstance, inferInstance, hdim1⟩
    obtain ⟨_, hDVR⟩ := ((Stacks.DiscreteValuationRing.Criteria.solution O).out 5 1).mp h5
    have := hDVR
    let F := fO.fiberι (genericPoint (Spec O))
    have : IsOpenImmersion F :=
      @Stacks.Chow.isOpenImmersion_fiberι_genericPoint O _ (IsNormal.stalk_isDomain s) hDVR _ fO
    have hgen (p : Spec O) : p ≠ IsLocalRing.closedPoint O ↔ p = genericPoint (Spec O) := by
      refine ⟨fun hp ↦ ?_, fun hp ↦ hp ▸ hgenP⟩
      rw [genericPoint_eq_bot_of_affine]
      by_contra hbot
      apply hp
      have hne : p.asIdeal ≠ ⊥ := fun h ↦ hbot (PrimeSpectrum.ext h)
      have := p.isPrime
      exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal hne))
    have hrange : Set.range F = Set.range XP.ι := by
      rw [Scheme.Hom.range_fiberι, Scheme.Opens.range_ι]
      ext x
      show fO x = genericPoint (Spec O) ↔ x ∈ XP
      rw [hXP, hP, hgen]
    let g := IsOpenImmersion.isoOfRangeEq F XP.ι hrange
    have hg : g.hom ≫ XP.ι = F := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    have hconnXP := connectedSpace_baseChange_of_stalk f s hη Z Y.obj e XP k hk
      (fun x hx ↦ (hXP x).2 (by rw [hx, hgenι]; exact hη))
    let q₁ := g.hom ≫ k
    have hconn₁ : ConnectedSpace ((finiteEtaleBaseChange q₁).obj Y.obj).left := by
      let c := (finiteEtaleBaseChangeComp g.hom k q₁ rfl).app Y.obj
      have hP : IsPullback (𝟙 _) (((finiteEtaleBaseChange k).obj Y.obj).hom ≫ g.inv)
          ((finiteEtaleBaseChange k).obj Y.obj).hom g.hom :=
        IsPullback.of_horiz_isIso ⟨by simp⟩
      let φ : ((finiteEtaleBaseChange q₁).obj Y.obj).left ≅
          ((finiteEtaleBaseChange k).obj Y.obj).left :=
        (MorphismProperty.Over.forget finiteEtale ⊤ _ ⋙ Over.forget _).mapIso c ≪≫
          hP.isoPullback.symm
      have : IsIso φ.inv := Iso.isIso_inv φ
      exact φ.inv.homeomorph.surjective.connectedSpace φ.inv.continuous
    let ZO := Y.baseChange q₁ hconn₁
    obtain ⟨ηO, hηOι⟩ := exists_lift_opens_ι U
        ((Spec O).fromSpecResidueField (genericPoint (Spec O)) ≫ ι) fun p ↦ by
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply, hgenι]
      exact hη
    have hzw : (ηO ≫ τ) ≫ Y.obj.hom = genericFiberSection fO σO hσO ≫ q₁ := by
      rw [← cancel_mono (f ⁻¹ᵁ U).ι]
      simp only [q₁, Category.assoc, reassoc_of% hτ, hσUι, reassoc_of% hηOι, hk, reassoc_of% hg,
        F]
      have h1 := genericFiberSection_fiberι fO σO hσO
      rw [reassoc_of% h1, hσOfst]
    let zO : Spec ((Spec O).residueField (genericPoint (Spec O))) ⟶ ZO.obj.left :=
      pullback.lift (ηO ≫ τ) (genericFiberSection fO σO hσO) hzw
    have hzO : zO ≫ ZO.obj.hom = genericFiberSection fO σO hσO := pullback.lift_snd _ _ _
    obtain ⟨Y', e', -⟩ :=
      @exists_finiteEtaleGaloisCover_extending_genericFiber_of_isDiscreteValuationRing O _
        (IsNormal.stalk_isDomain s) hDVR _ fO h0BMA h0EYD _ _ σO hσO G _ _ hGres ZO zO hzO
    have hgι : g.inv ≫ F = XP.ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
    have hgk : k = g.inv ≫ q₁ := by
      rw [Iso.inv_hom_id_assoc]
    exact ⟨Y'.obj, nonempty_iso_baseChange_of_comp g.inv F q₁ XP.ι k hgι hgk Y'.obj Y.obj e'⟩

end AlgebraicGeometry.Abhyankar
