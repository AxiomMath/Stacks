module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.ChartRelationLift
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.FirstOrderClauseAndAffineSize
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.SiteThickening
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.AmbientSizeBound
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.ChartRelationLift

/-!
# Universal thickening existence: the construction

The thickening datum of a formally unramified morphism of algebraic spaces and the construction of
its universal first order thickening as the quotient of the universal thickening of an étale
chart by the lifted étale equivalence relation.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Spaces.UniversalThickening

open AlgebraicGeometry.Space

/-- Data of an algebraic space containing the source as a subfunctor and
mapping to the target. The specification of a universal thickening is stated
separately. -/
structure ThickeningDatum
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicGeometry.AlgebraicSpaces B S hS} (h : Z ⟶ X) where
  /-- The ambient algebraic space. -/
  ambient : AlgebraicGeometry.AlgebraicSpaces B S hS
  /-- The embedded source in the ambient algebraic space. -/
  source : Subfunctor ambient.1
  /-- The embedded source is the original algebraic space. -/
  sourceIso : Z.1 ≅ source.toFunctor
  /-- The structure map to the target. -/
  toBase : ambient ⟶ X

/-- The target of the pre-relation induced by a pair of arrows is the first arrow. -/
private theorem sitePreRelation_target_eq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R U : AlgebraicGeometry.BigFppfOver B S hS} (s t : R ⟶ U) :
    (AlgebraicGeometry.Space.sitePreRelation B S hS s t).target =
      (Over.post B.inclusion).map s := by
  dsimp [AlgebraicGeometry.Space.sitePreRelation, Stacks.Groupoids.PreRelation.target]
  rw [Limits.prod.lift_fst]

/-- The source of the pre-relation induced by a pair of arrows is the second arrow. -/
private theorem sitePreRelation_source_eq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R U : AlgebraicGeometry.BigFppfOver B S hS} (s t : R ⟶ U) :
    (AlgebraicGeometry.Space.sitePreRelation B S hS s t).source =
      (Over.post B.inclusion).map t := by
  dsimp [AlgebraicGeometry.Space.sitePreRelation, Stacks.Groupoids.PreRelation.source]
  rw [Limits.prod.lift_snd]

theorem exists_universalFirstOrderThickening_with_spec
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicGeometry.AlgebraicSpaces B S hS} (h : Z ⟶ X)
    (hh : AlgebraicGeometry.Space.FormallyUnramified h.hom) :
    ∃ t : ThickeningDatum B S hS h,
      (t.sourceIso.hom ≫ t.source.ι ≫ t.toBase.hom = h.hom) ∧
        AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS t.source t.toBase := by
  classical
  obtain ⟨D⟩ := exists_chartThickening B S hS h hh
  let K := chartKernelPair B S hS D.sourceChart D.sourceEtale
  obtain ⟨W, α, β, r, H, k, hrα, hrβ, hα, hβ, hWpb, hαuniv, hβuniv,
    hs, ht, hp, hq, hsu, htu⟩ :=
    exists_lifted_chartKernelPair_over_targetRelation B S hS D K
  have hDambient : B.Contains D.thickening.ambient :=
    contains_ambient_of_isUniversalFirstOrderThickening B D.V.left.property D.U.left.property
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map D.chartMap)
      D.thickening.inclusion D.thickening.toBase D.thickening.isUniversal
  have hHambient : B.Contains H.ambient :=
    contains_ambient_of_isUniversalFirstOrderThickening B K.R.left.property W.left.property
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map r)
      H.inclusion H.toBase H.isUniversal
  obtain ⟨V', R', iV, pV, iR, pR, s', t', hiVpV, hiRpR,
    hsSite, htSite, hpSite, hqSite,
    hV'obj, hR'obj, hiVscheme, hiRscheme, hpVscheme, hpRscheme,
    hfirstV, hfirstR, hVunivScheme, hRunivScheme,
    hVuniv, hRuniv, hRunivα, hRunivβ,
    hs'scheme, ht'scheme⟩ :=
    bridge_liftedRelation_siteMaps B S hS D.chartMap r α β
      K.source K.target D.thickening H hDambient hHambient k
      hs ht hp hq hαuniv hβuniv
  let : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (AlgebraicGeometry.Space.sitePreRelation B S hS K.source K.target) := K.etaleRelation
  have hKsource : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map K.source) := by
    have h : Etale (AlgebraicGeometry.Space.sitePreRelation B S hS K.source K.target).target.left :=
      inferInstance
    rw [sitePreRelation_target_eq] at h
    simpa [
      AlgebraicGeometry.BigFppfOver.toScheme, AlgebraicGeometry.BigFppfOver.forget,
      Over.post] using h
  have hKtarget : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map K.target) := by
    have h : Etale (AlgebraicGeometry.Space.sitePreRelation B S hS K.source K.target).source.left :=
      inferInstance
    rw [sitePreRelation_source_eq] at h
    simpa [
      AlgebraicGeometry.BigFppfOver.toScheme, AlgebraicGeometry.BigFppfOver.forget,
      Over.post] using h
  obtain ⟨hs'etale, hs'pb⟩ :=
    bridge_etale_of_universalSiteThickenings B S hS iV iR pV (pR ≫ α)
      hfirstV hfirstR hVuniv hRunivα K.source s' hKsource hsSite hpSite
  obtain ⟨ht'etale, ht'pb⟩ :=
    bridge_etale_of_universalSiteThickenings B S hS iV iR pV (pR ≫ β)
      hfirstV hfirstR hVuniv hRunivβ K.target t' hKtarget htSite hqSite
  have hWRel : IsEquivalenceRelation
      ((Over.post B.inclusion).map α) ((Over.post B.inclusion).map β) :=
    AlgebraicGeometry.Space.isEquivalenceRelation_of_isPullback
      B S hS D.targetChart α β hWpb
  have hs'pbSite : IsPullback K.source iR iV s' :=
    IsPullback.of_map yoneda hsSite.symm hs'pb
  have ht'pbSite : IsPullback K.target iR iV t' :=
    IsPullback.of_map yoneda htSite.symm ht'pb
  have hWext : ∀ {T} (f g : T ⟶ W), f ≫ α = g ≫ α → f ≫ β = g ≫ β → f = g := by
    intro T f g h₁ h₂
    apply Functor.map_injective yoneda
    apply hWpb.hom_ext
    · simpa only [← Functor.map_comp] using congrArg yoneda.map h₁
    · simpa only [← Functor.map_comp] using congrArg yoneda.map h₂
  obtain ⟨dK, hdKs, hdKt⟩ := bridge_targetRelation_diagonal
    B S hS D.sourceChart K.source K.target K.kernelPair
  obtain ⟨dW, hdWα, hdWβ⟩ := bridge_targetRelation_diagonal
    B S hS D.targetChart α β hWpb
  have hdBase : dK ≫ r = D.chartMap ≫ dW := by
    refine hWext _ _ ?_ ?_
    · simp [hrα, reassoc_of% hdKs, hdWα]
    · simp [hrβ, reassoc_of% hdKt, hdWβ]
  have hdCompat : iV ≫ (pV ≫ dW) = dK ≫ r := by
    rw [← Category.assoc, hiVpV]
    exact hdBase.symm
  obtain ⟨d', hd', _⟩ := bridge_site_lift_of_universalThickening
    B S hS iV hfirstV dK (pV ≫ dW) r iR pR hRunivScheme hdCompat
  have hd's : d' ≫ s' = 𝟙 V' := by
    refine bridge_site_endomorphism_id_of_universalThickening
      B S hS iV D.chartMap pV hfirstV hVunivScheme hiVpV _ ?_ ?_
    · simp [reassoc_of% hd'.1, hsSite, reassoc_of% hdKs]
    · simp [hpSite, reassoc_of% hd'.2, hdWα]
  have hd't : d' ≫ t' = 𝟙 V' := by
    refine bridge_site_endomorphism_id_of_universalThickening
      B S hS iV D.chartMap pV hfirstV hVunivScheme hiVpV _ ?_ ?_
    · simp [reassoc_of% hd'.1, htSite, reassoc_of% hdKt]
    · simp [hqSite, reassoc_of% hd'.2, hdWβ]
  obtain ⟨eK, heKs, heKt⟩ := bridge_targetRelation_swap
    B S hS D.sourceChart K.source K.target K.kernelPair
  obtain ⟨eW, heWα, heWβ⟩ := bridge_targetRelation_swap
    B S hS D.targetChart α β hWpb
  have heBase : eK ≫ r = r ≫ eW := by
    refine hWext _ _ ?_ ?_
    · simp [hrα, hrβ, reassoc_of% heKs, heWα]
    · simp [hrα, hrβ, reassoc_of% heKt, heWβ]
  have heCompat : iR ≫ (pR ≫ eW) = eK ≫ r := by
    rw [← Category.assoc, hiRpR]
    exact heBase.symm
  obtain ⟨e', he', _⟩ := bridge_site_lift_of_universalThickening
    B S hS iR hfirstR eK (pR ≫ eW) r iR pR hRunivScheme heCompat
  have he's : e' ≫ s' = t' := by
    refine bridge_site_hom_ext_of_universalThickening
      B S hS iR hfirstR K.target (pR ≫ β) D.chartMap iV pV hVunivScheme ?_ _ _
      ⟨?_, ?_⟩ ⟨htSite, hqSite⟩
    · simp [reassoc_of% hiRpR, hrβ]
    · simp [reassoc_of% he'.1, hsSite, reassoc_of% heKs]
    · simp [hpSite, reassoc_of% he'.2, heWα]
  have he't : e' ≫ t' = s' := by
    refine bridge_site_hom_ext_of_universalThickening
      B S hS iR hfirstR K.source (pR ≫ α) D.chartMap iV pV hVunivScheme ?_ _ _
      ⟨?_, ?_⟩ ⟨hsSite, hpSite⟩
    · simp [reassoc_of% hiRpR, hrα]
    · simp [reassoc_of% he'.1, htSite, reassoc_of% heKt]
    · simp [hqSite, reassoc_of% he'.2, heWβ]
  have hKjointScheme : JointlyMono₂
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map K.source)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map K.target) := by
    let hKRel := AlgebraicGeometry.Space.isEquivalenceRelation_of_isPullback
      B S hS D.sourceChart K.source K.target K.kernelPair
    let E := hKRel.nonempty_equivalenceRelation.some
    exact bridge_jointlyMono_scheme_of_over
      ((Over.post B.inclusion).map K.source)
      ((Over.post B.inclusion).map K.target)
      ⟨E.right_cancellation⟩
  have hWjointScheme : JointlyMono₂
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map α)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map β) := by
    let E := hWRel.nonempty_equivalenceRelation.some
    exact bridge_jointlyMono_scheme_of_over
      ((Over.post B.inclusion).map α) ((Over.post B.inclusion).map β)
      ⟨E.right_cancellation⟩
  have : IsClosedImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iV) := hfirstV.1
  have : Mono ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iV) := inferInstance
  have hJointScheme : JointlyMono₂
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s')
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map t') := by
    apply bridge_jointlyMono_of_universalRelation
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map K.source)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map K.target)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s')
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map t')
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map r)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map α)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map β)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iV)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iR)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map pV)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map pR)
      hKjointScheme hWjointScheme hRunivScheme
      (hs'pbSite.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS))
      (by simp only [← Functor.map_comp, htSite])
      (by simp only [← Functor.map_comp, hpSite])
      (by simp only [← Functor.map_comp, hqSite])
  have hJointOver : JointlyMono₂
      ((Over.post B.inclusion).map s') ((Over.post B.inclusion).map t') :=
    bridge_jointlyMono_over_of_scheme _ _ hJointScheme
  have : IsClosedImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iR) := hfirstR.1
  have : Mono iR := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).mono_of_mono_map
    (inferInstance : Mono ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iR))
  obtain ⟨iP, hiPpb, hiPsnd⟩ :=
    bridge_relationPullback_square K.source K.target s' t' iV iR
      hs'pbSite htSite
  have hiPfirst : Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iP) :=
    bridge_firstOrder_of_isPullback
      (hiPpb.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) hfirstR
  obtain ⟨cK, hcKs, hcKt⟩ := bridge_targetRelation_comp
    B S hS D.sourceChart K.source K.target K.kernelPair
  obtain ⟨cW, hcWα, hcWβ⟩ := bridge_targetRelation_comp
    B S hS D.targetChart α β hWpb
  have hmatchW :
      (Limits.pullback.fst t' s' ≫ pR) ≫ β =
      (Limits.pullback.snd t' s' ≫ pR) ≫ α := by
    calc
      (Limits.pullback.fst t' s' ≫ pR) ≫ β =
          Limits.pullback.fst t' s' ≫ (pR ≫ β) := Category.assoc _ _ _
      _ = Limits.pullback.fst t' s' ≫ (t' ≫ pV) := by rw [hqSite]
      _ = (Limits.pullback.fst t' s' ≫ t') ≫ pV :=
        (Category.assoc _ _ _).symm
      _ = (Limits.pullback.snd t' s' ≫ s') ≫ pV := by
        rw [Limits.pullback.condition]
      _ = Limits.pullback.snd t' s' ≫ (s' ≫ pV) := Category.assoc _ _ _
      _ = Limits.pullback.snd t' s' ≫ (pR ≫ α) := by rw [hpSite]
      _ = (Limits.pullback.snd t' s' ≫ pR) ≫ α :=
        (Category.assoc _ _ _).symm
  let mW : Limits.pullback t' s' ⟶ Limits.pullback β α :=
    Limits.pullback.lift
      (Limits.pullback.fst t' s' ≫ pR)
      (Limits.pullback.snd t' s' ≫ pR) hmatchW
  let bP : Limits.pullback t' s' ⟶ W := mW ≫ cW
  have hbPα : bP ≫ α = (Limits.pullback.fst t' s' ≫ pR) ≫ α := by
    calc
      bP ≫ α = mW ≫ (cW ≫ α) := Category.assoc _ _ _
      _ = mW ≫ (Limits.pullback.fst β α ≫ α) := by rw [hcWα]
      _ = (mW ≫ Limits.pullback.fst β α) ≫ α :=
        (Category.assoc _ _ _).symm
      _ = (Limits.pullback.fst t' s' ≫ pR) ≫ α := by
        rw [Limits.pullback.lift_fst]
  have hbPβ : bP ≫ β = (Limits.pullback.snd t' s' ≫ pR) ≫ β := by
    calc
      bP ≫ β = mW ≫ (cW ≫ β) := Category.assoc _ _ _
      _ = mW ≫ (Limits.pullback.snd β α ≫ β) := by rw [hcWβ]
      _ = (mW ≫ Limits.pullback.snd β α) ≫ β :=
        (Category.assoc _ _ _).symm
      _ = (Limits.pullback.snd t' s' ≫ pR) ≫ β := by
        rw [Limits.pullback.lift_snd]
  have hcPbase : iP ≫ bP = cK ≫ r := by
    refine hWext _ _ ?_ ?_
    · simp [hbPα, reassoc_of% hiPpb.w.symm, reassoc_of% hcKs, hrα, reassoc_of% hiRpR]
    · simp [hbPβ, reassoc_of% hiPsnd, reassoc_of% hcKt, hrβ, reassoc_of% hiRpR]
  obtain ⟨c', hc', _⟩ := bridge_site_lift_of_universalThickening
    B S hS iP hiPfirst cK bP r iR pR hRunivScheme hcPbase
  have hc's : c' ≫ s' = Limits.pullback.fst t' s' ≫ s' := by
    refine bridge_site_hom_ext_of_universalThickening B S hS
      iP hiPfirst (Limits.pullback.fst K.target K.source ≫ K.source)
      (bP ≫ α) D.chartMap iV pV hVunivScheme ?_ _ _ ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · simp [reassoc_of% hcPbase, hrα, reassoc_of% hcKs]
    · simp [reassoc_of% hc'.1, hsSite, reassoc_of% hcKs]
    · simp [hpSite, reassoc_of% hc'.2]
    · simp [reassoc_of% hiPpb.w.symm, hsSite]
    · simp [hpSite, hbPα]
  have hc't : c' ≫ t' = Limits.pullback.snd t' s' ≫ t' := by
    refine bridge_site_hom_ext_of_universalThickening B S hS
      iP hiPfirst (Limits.pullback.snd K.target K.source ≫ K.target)
      (bP ≫ β) D.chartMap iV pV hVunivScheme ?_ _ _ ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · simp [reassoc_of% hcPbase, hrβ, reassoc_of% hcKt]
    · simp [reassoc_of% hc'.1, htSite, reassoc_of% hcKt]
    · simp [hqSite, reassoc_of% hc'.2]
    · simp [reassoc_of% hiPsnd, htSite]
    · simp [hqSite, hbPβ]
  let FOver : AlgebraicGeometry.BigFppfOver B S hS ⥤ Over S :=
    Over.post (X := B.obj hS) B.inclusion
  have hFcondition : FOver.map (Limits.pullback.fst t' s') ≫ FOver.map t' =
      FOver.map (Limits.pullback.snd t' s') ≫ FOver.map s' := by
    simpa only [← FOver.map_comp] using congrArg FOver.map
      (show Limits.pullback.fst t' s' ≫ t' =
        Limits.pullback.snd t' s' ≫ s' from Limits.pullback.condition)
  have hFP : IsPullback
      (FOver.map (Limits.pullback.fst t' s'))
      (FOver.map (Limits.pullback.snd t' s'))
      (FOver.map t') (FOver.map s') := by
    apply IsPullback.of_map (Over.forget S) hFcondition
    exact (IsPullback.of_hasPullback t' s').map
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  have hRel' : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (AlgebraicGeometry.Space.sitePreRelation B S hS s' t') := by
    refine { isEquivalenceRelation := ?_, etale_source := ?_, etale_target := ?_ }
    · rw [sitePreRelation_target_eq, sitePreRelation_source_eq]
      refine EquivalenceRelation.isEquivalenceRelation
        { right_cancellation := hJointOver.right_cancellation
          r := FOver.map d'
          reflexivity₁ := by rw [← FOver.map_comp, hd's, FOver.map_id]
          reflexivity₂ := by rw [← FOver.map_comp, hd't, FOver.map_id]
          s := FOver.map e'
          symmetry₁ := by rw [← FOver.map_comp, he's]
          symmetry₂ := by rw [← FOver.map_comp, he't]
          c := PullbackCone.mk
            (FOver.map (Limits.pullback.fst t' s'))
            (FOver.map (Limits.pullback.snd t' s'))
            hFcondition
          isLimit := hFP.isLimit
          t := FOver.map c'
          transitivity₁ := by
            change FOver.map c' ≫ FOver.map s' =
              FOver.map (Limits.pullback.fst t' s') ≫ FOver.map s'
            simpa only [FOver.map_comp, PullbackCone.mk_fst] using
              congrArg FOver.map hc's
          transitivity₂ := by
            change FOver.map c' ≫ FOver.map t' =
              FOver.map (Limits.pullback.snd t' s') ≫ FOver.map t'
            simpa only [FOver.map_comp, PullbackCone.mk_snd] using
              congrArg FOver.map hc't }
    · rw [sitePreRelation_source_eq]
      exact ht'etale
    · rw [sitePreRelation_target_eq]
      exact hs'etale
  let : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (AlgebraicGeometry.Space.relation B S hS t' s') := hRel'
  let := AlgebraicGeometry.essentiallySmall_bigFppfOver B S hS
  let : HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u) :=
    hasSheafifyEssentiallySmallSite _ _
  let Qfun :=
    (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS)
      (Over.post B.inclusion) (AlgebraicGeometry.Space.sitePreRelation B S hS s' t')).obj
  let Q : AlgebraicGeometry.AlgebraicSpaces B S hS :=
    ⟨Qfun, AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional B S hS t' s'⟩
  let qV' : yoneda.obj V' ⟶ Q.1 := AlgebraicGeometry.Space.quotientMap B S hS t' s'
  have hqV'surj := AlgebraicGeometry.Space.quotientMap_surjective_unconditional B S hS t' s'
  have hqV'etale := AlgebraicGeometry.Space.quotientMap_etale_unconditional B S hS t' s'
  have hqV'kernel := AlgebraicGeometry.Space.quotientMap_isPullback B S hS t' s'
  have hqV'equal : yoneda.map s' ≫ qV' = yoneda.map t' ≫ qV' :=
    hqV'kernel.w
  have hqVequal : yoneda.map K.source ≫ (yoneda.map iV ≫ qV') =
      yoneda.map K.target ≫ (yoneda.map iV ≫ qV') := by
    rw [← Functor.map_comp_assoc, ← hsSite, Functor.map_comp_assoc, hqV'equal,
      ← Functor.map_comp_assoc, htSite, Functor.map_comp_assoc]
  obtain ⟨gZ, hgZ⟩ := bridge_descend_map_from_atlas B S hS
    Z.property Q.property.isSheaf K.source K.target D.sourceChart
    K.kernelPair D.sourceSurjective D.sourceEtale
    (yoneda.map iV ≫ qV') hqVequal
  let gZalg : Z ⟶ Q := ObjectProperty.homMk gZ
  have hqV'X : yoneda.map s' ≫ (yoneda.map pV ≫ D.targetChart) =
      yoneda.map t' ≫ (yoneda.map pV ≫ D.targetChart) := by
    rw [← Functor.map_comp_assoc, hpSite, Functor.map_comp_assoc, hWpb.w,
      ← Functor.map_comp_assoc, ← hqSite, Functor.map_comp_assoc]
  obtain ⟨gX, hgX⟩ := bridge_descend_map_from_atlas B S hS
    Q.property X.property.isSheaf s' t' qV' hqV'kernel
    hqV'surj hqV'etale (yoneda.map pV ≫ D.targetChart) hqV'X
  let gXalg : Q ⟶ X := ObjectProperty.homMk gX
  have hgZX : gZalg ≫ gXalg = h := by
    apply ObjectProperty.hom_ext
    apply bridge_maps_equal_of_atlas B S hS Z.property X.property.isSheaf
      K.source K.target D.sourceChart K.kernelPair
      D.sourceSurjective D.sourceEtale
    change D.sourceChart ≫ (gZ ≫ gX) = D.sourceChart ≫ h.hom
    calc
      D.sourceChart ≫ (gZ ≫ gX) =
          (yoneda.map iV ≫ qV') ≫ gX := by
            rw [← Category.assoc, hgZ]
      _ = yoneda.map iV ≫ (yoneda.map pV ≫ D.targetChart) := by
            rw [Category.assoc, hgX]
      _ = yoneda.map (iV ≫ pV) ≫ D.targetChart := by
            simp only [Functor.map_comp, Category.assoc]
      _ = yoneda.map D.chartMap ≫ D.targetChart := by rw [hiVpV]
      _ = D.sourceChart ≫ h.hom := D.comm
  let Tsite := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have : Mono (Tsite.map iV) := by
    have : IsClosedImmersion (Tsite.map iV) := hfirstV.1
    infer_instance
  let A : Subobject (Tsite.obj V') := Subobject.mk (Tsite.map iV)
  have hAclosed : _root_.AlgebraicGeometry.IsClosedImmersion A.arrow := by
    change IsClosedImmersion (Subobject.mk (Tsite.map iV)).arrow
    rw [← Subobject.underlyingIso_hom_comp_eq_mk (Tsite.map iV)]
    infer_instance
  have hAsub : (Subobject.pullback (Tsite.map s')).obj A =
      (Subobject.pullback (Tsite.map t')).obj A := by
    change (Subobject.pullback (Tsite.map s')).obj
        (Subobject.mk (Tsite.map iV)) =
      (Subobject.pullback (Tsite.map t')).obj
        (Subobject.mk (Tsite.map iV))
    rw [Subobject.pullback_obj_mk (hs'pbSite.map Tsite),
      Subobject.pullback_obj_mk (ht'pbSite.map Tsite)]
  let P := AlgebraicGeometry.Space.quotientPresentation B S hS t' s' Q.property
  let : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (AlgebraicGeometry.Space.sitePreRelation B S hS P.target P.source) :=
    P.isEtaleEquivalenceRelation
  have hPU : P.U = V' := rfl
  have hPR : P.R = R' := rfl
  have hPt : P.target = s' := rfl
  have hPs : P.source = t' := rfl
  let G := AlgebraicGeometry.Space.relationGroupoid B S hS P.target P.source
  let hExt := AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation_extendsRelation
    (AlgebraicGeometry.Space.sitePreRelation B S hS P.target P.source)
  let hObj : G.objects.left = Tsite.obj V' := congrArg Over.left hExt.objects_eq
  let hArr : G.arrows.left = Tsite.obj R' := congrArg Over.left hExt.arrows_eq
  have hGtarget : eqToHom hArr.symm ≫ G.target.left ≫ eqToHom hObj =
      Tsite.map P.target := by
    have hh := congrArg Over.Hom.left hExt.target_eq
    rw [sitePreRelation_target_eq] at hh
    simp only [Over.comp_left, Over.eqToHom_left] at hh
    convert hh using 1
    rfl
  have hGsource : eqToHom hArr.symm ≫ G.source.left ≫ eqToHom hObj =
      Tsite.map P.source := by
    have hh := congrArg Over.Hom.left hExt.source_eq
    rw [sitePreRelation_source_eq] at hh
    simp only [Over.comp_left, Over.eqToHom_left] at hh
    convert hh using 1
    rfl
  have hAinv : Stacks.Groupoids.IsInvariantMonomorphism G
      (A.arrow ≫ eqToHom hObj.symm) := by
    let j : (A : Scheme) ⟶ G.objects.left := A.arrow ≫ eqToHom hObj.symm
    have : Mono j := inferInstance
    have hUi : (Subobject.pullback (eqToHom hObj.symm)).obj
        (Subobject.mk j) = A := by
      have hp : IsPullback (𝟙 (A : Scheme)) A.arrow j
          (eqToHom hObj.symm) :=
        IsPullback.of_horiz_isIso (by simp [j])
      simpa only [Subobject.mk_arrow] using
        (Subobject.pullback_obj_mk hp)
    have hconj : ∀ (g : G.arrows.left ⟶ G.objects.left) (f : Tsite.obj R' ⟶ Tsite.obj V'),
        eqToHom hArr.symm ≫ g ≫ eqToHom hObj = f → g = eqToHom hArr ≫ f ≫ eqToHom hObj.symm := by
      rintro g f rfl
      simp
    have hgt : G.target.left =
        eqToHom hArr ≫ Tsite.map P.target ≫ eqToHom hObj.symm := hconj _ _ hGtarget
    have hgs : G.source.left =
        eqToHom hArr ≫ Tsite.map P.source ≫ eqToHom hObj.symm := hconj _ _ hGsource
    have key : ∀ f : Tsite.obj R' ⟶ Tsite.obj V',
        (Subobject.pullback (eqToHom hArr ≫ f ≫ eqToHom hObj.symm)).obj (Subobject.mk j) =
          (Subobject.pullback (eqToHom hArr)).obj ((Subobject.pullback f).obj A) := by
      intro f
      rw [Subobject.pullback_comp, Subobject.pullback_comp]
      exact congrArg (fun Z : Subobject (Tsite.obj V') =>
        (Subobject.pullback (eqToHom hArr)).obj ((Subobject.pullback f).obj Z)) hUi
    change (Subobject.pullback G.target.left).obj (Subobject.mk j) =
      (Subobject.pullback G.source.left).obj (Subobject.mk j)
    calc (Subobject.pullback G.target.left).obj (Subobject.mk j)
        = (Subobject.pullback (eqToHom hArr ≫ Tsite.map P.target ≫ eqToHom hObj.symm)).obj
            (Subobject.mk j) := by rw [hgt]
      _ = (Subobject.pullback (eqToHom hArr)).obj
            ((Subobject.pullback (Tsite.map P.target)).obj A) := key _
      _ = (Subobject.pullback (eqToHom hArr)).obj
            ((Subobject.pullback (Tsite.map P.source)).obj A) :=
          congrArg (fun W : Subobject (Tsite.obj R') =>
            (Subobject.pullback (eqToHom hArr)).obj W) hAsub
      _ = (Subobject.pullback (eqToHom hArr ≫ Tsite.map P.source ≫ eqToHom hObj.symm)).obj
            (Subobject.mk j) := (key _).symm
      _ = (Subobject.pullback G.source.left).obj (Subobject.mk j) := by rw [hgs]
  have hAimmersion : _root_.AlgebraicGeometry.IsImmersion A.arrow := by
    change _root_.AlgebraicGeometry.IsImmersion (Subobject.mk (Tsite.map iV)).arrow
    rw [← Subobject.underlyingIso_hom_comp_eq_mk (Tsite.map iV)]
    have : _root_.AlgebraicGeometry.IsClosedImmersion (Tsite.map iV) := hfirstV.1
    infer_instance
  let Zinv : AlgebraicGeometry.Space.GroupoidInvariantLocallyClosedSubscheme B S hS
      P.target P.source :=
    ⟨A, hAimmersion, hAinv⟩
  let Y : Subfunctor Q.1 :=
    AlgebraicGeometry.Space.descendedInvariantSubfunctor B S hS P Zinv
  have hqV'Etale : AlgebraicGeometry.Space.IsEtale B S hS qV' :=
    AlgebraicGeometry.Space.isEtale_of_presheaf_etale B S hS hqV'etale
  have hqV'Surj : AlgebraicGeometry.Space.IsSurjective B S hS qV' :=
    (AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda B S hS Q.1 Q.property
      V' qV').mp hqV'surj
  have hYsheaf : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) Y.toFunctor :=
    isSheaf_descendedInvariantSubfunctor B S hS P Zinv
  have hYpre : Y.preimage qV' = Subfunctor.range (yoneda.map iV) := by
    have hp := AlgebraicGeometry.Space.descendedInvariantSubfunctor_preimage B S hS P Zinv
    change Y.preimage qV' = AlgebraicGeometry.Space.subschemePoints B S hS A at hp
    exact hp.trans (bridge_subschemePoints_mk B S hS iV)
  have : Mono iV := Tsite.mono_of_mono_map
    (inferInstance : Mono (Tsite.map iV))
  have : Mono (yoneda.map iV) := inferInstance
  obtain ⟨aV, haVpb⟩ :=
    bridge_isPullback_of_preimage_eq_range Y qV' (yoneda.map iV) hYpre
  have hrangeEq : Subfunctor.range (yoneda.map iV) =
      Subfunctor.range (Limits.pullback.snd Y.ι qV') := by
    have he : haVpb.isoPullback.hom ≫ Limits.pullback.snd Y.ι qV' = yoneda.map iV :=
      haVpb.isoPullback_hom_snd
    have h2 : Limits.pullback.snd Y.ι qV' = haVpb.isoPullback.inv ≫ yoneda.map iV := by
      calc Limits.pullback.snd Y.ι qV'
          = 𝟙 _ ≫ Limits.pullback.snd Y.ι qV' := (Category.id_comp _).symm
        _ = (haVpb.isoPullback.inv ≫ haVpb.isoPullback.hom) ≫
              Limits.pullback.snd Y.ι qV' := by rw [Iso.inv_hom_id]
        _ = haVpb.isoPullback.inv ≫
              (haVpb.isoPullback.hom ≫ Limits.pullback.snd Y.ι qV') := Category.assoc _ _ _
        _ = haVpb.isoPullback.inv ≫ yoneda.map iV := congrArg _ he
    exact le_antisymm
      ((congrArg Subfunctor.range he.symm).trans_le (Subfunctor.range_comp_le _ _))
      ((congrArg Subfunctor.range h2).trans_le (Subfunctor.range_comp_le _ _))
  have hbaseFirstRange : AlgebraicGeometry.Space.IsFirstOrderThickening B S hS
      (AlgebraicGeometry.schemeSpace V')
      (Subfunctor.range (Limits.pullback.snd Y.ι qV')) :=
    hrangeEq ▸ AlgebraicGeometry.Space.isFirstOrderThickening_range_yoneda_map B S hS iV
      ⟨hfirstV.1, hfirstV.2⟩
  have hbaseClosed : AlgebraicGeometry.Space.IsClosedImmersion B S hS
      (Limits.pullback.snd Y.ι qV') := by
    let Pfirst := MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsFirstOrderThickening : MorphismProperty Scheme.{u}) Tsite
    let : Pfirst.IsStableUnderBaseChange :=
      ⟨fun hs hb => Stacks.Thickenings.isFirstOrderThickening_isStableUnderBaseChange.of_isPullback
        (hs.map Tsite) hb⟩
    have hiVfirstP : Pfirst.presheaf (yoneda.map iV) :=
      MorphismProperty.relative_map (P := Pfirst) hfirstV
    have he : haVpb.isoPullback.hom ≫ Limits.pullback.snd Y.ι qV' = yoneda.map iV :=
      haVpb.isoPullback_hom_snd
    have hbaseFirst : Pfirst.presheaf (Limits.pullback.snd Y.ι qV') :=
      (Pfirst.presheaf.arrow_mk_iso_iff
        (Arrow.isoMk haVpb.isoPullback (Iso.refl _) (by
          simpa only [Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right, Iso.refl_hom,
            Category.comp_id] using he))).mp hiVfirstP
    exact MorphismProperty.relative_monotone (P := Pfirst) (fun _ _ _ hi => hi.1) _ hbaseFirst
  obtain ⟨hYclosed, hYfirst⟩ :=
    isClosedSubspace_and_isFirstOrderThickening_of_surjectiveEtaleChart B S hS Y hYsheaf
      qV' hqV'surj hqV'etale hbaseClosed hbaseFirstRange
  let Yalg : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨Y.toFunctor, hYclosed.1⟩
  let aValg : AlgebraicGeometry.schemeSpace D.V ⟶ Yalg :=
    ObjectProperty.homMk aV
  let iValg : AlgebraicGeometry.schemeSpace D.V ⟶
      AlgebraicGeometry.schemeSpace V' := ObjectProperty.homMk (yoneda.map iV)
  let qV'alg : AlgebraicGeometry.schemeSpace V' ⟶ Q :=
    ObjectProperty.homMk qV'
  let yIncl : Yalg ⟶ Q := ObjectProperty.homMk Y.ι
  have haVpbAlg : IsPullback aValg iValg yIncl qV'alg := by
    apply IsPullback.of_map (ObjectProperty.ι _)
    · exact ObjectProperty.hom_ext _ haVpb.w
    · exact haVpb
  have haVEtale : AlgebraicGeometry.Space.IsEtale B S hS aV :=
    AlgebraicGeometry.Space.isEtale_of_isPullback B S hS
      iValg aValg qV'alg yIncl haVpbAlg.flip hqV'Etale
  have haVSurj : AlgebraicGeometry.Space.IsSurjective B S hS aV :=
    AlgebraicGeometry.Space.isSurjective_of_isPullback B S hS haVpbAlg.flip hqV'Surj
  have hKQ : IsPullback (yoneda.map K.source) (yoneda.map K.target)
      (yoneda.map iV ≫ qV') (yoneda.map iV ≫ qV') := by
    apply bridge_restricted_kernelPair
      (yoneda.map K.source) (yoneda.map K.target)
      (yoneda.map s') (yoneda.map t') (yoneda.map iV) (yoneda.map iR) qV'
      (hs'pbSite.map yoneda)
    · simpa only [Functor.map_comp] using congrArg yoneda.map htSite
    · exact hqV'kernel
  have hKA : IsPullback (yoneda.map K.source) (yoneda.map K.target)
      aV aV := by
    have hKQ' : IsPullback (yoneda.map K.source) (yoneda.map K.target)
        (aV ≫ Y.ι) (aV ≫ Y.ι) := by
      simpa only [haVpb.w] using hKQ
    exact CategoryTheory.IsKernelPair.cancel_right_of_mono hKQ'
  obtain ⟨zToY, hzToY⟩ := bridge_descend_map_from_atlas B S hS
    Z.property Yalg.property.isSheaf K.source K.target D.sourceChart
    K.kernelPair D.sourceSurjective D.sourceEtale aV hKA.w
  have haVSurjP : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) Tsite).presheaf aV :=
    (AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda B S hS
      Y.toFunctor Yalg.property D.V aV).mpr haVSurj
  have haVEtaleP : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) Tsite).presheaf aV := by
    let E := MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) Tsite
    let : E.presheaf.IsStableUnderBaseChange := E.relative_isStableUnderBaseChange
    exact E.presheaf.of_isPullback haVpb.flip hqV'etale
  obtain ⟨yToZ, hyToZ⟩ := bridge_descend_map_from_atlas B S hS
    Yalg.property Z.property.isSheaf K.source K.target aV
    hKA haVSurjP haVEtaleP D.sourceChart K.kernelPair.w
  have hzToYInv : zToY ≫ yToZ = 𝟙 Z.1 := by
    apply bridge_maps_equal_of_atlas B S hS Z.property Z.property.isSheaf
      K.source K.target D.sourceChart K.kernelPair
      D.sourceSurjective D.sourceEtale
    calc
      D.sourceChart ≫ (zToY ≫ yToZ) = aV ≫ yToZ := by
        rw [← Category.assoc, hzToY]
      _ = D.sourceChart := hyToZ
      _ = D.sourceChart ≫ 𝟙 Z.1 := (Category.comp_id _).symm
  have hyToZInv : yToZ ≫ zToY = 𝟙 Y.toFunctor := by
    apply bridge_maps_equal_of_atlas B S hS Yalg.property Yalg.property.isSheaf
      K.source K.target aV hKA haVSurjP haVEtaleP
    calc
      aV ≫ (yToZ ≫ zToY) = D.sourceChart ≫ zToY := by
        rw [← Category.assoc, hyToZ]
      _ = aV := hzToY
      _ = aV ≫ 𝟙 Y.toFunctor := (Category.comp_id _).symm
  let sourceIso : Z.1 ≅ Y.toFunctor := ⟨zToY, yToZ, hzToYInv, hyToZInv⟩
  have hsourceIncl : sourceIso.hom ≫ Y.ι = gZ := by
    apply bridge_maps_equal_of_atlas B S hS Z.property Q.property.isSheaf
      K.source K.target D.sourceChart K.kernelPair
      D.sourceSurjective D.sourceEtale
    calc
      D.sourceChart ≫ (sourceIso.hom ≫ Y.ι) = aV ≫ Y.ι := by
        rw [← Category.assoc, hzToY]
      _ = yoneda.map iV ≫ qV' := haVpb.w
      _ = D.sourceChart ≫ gZ := hgZ.symm
  let xAtlas : AlgebraicGeometry.schemeSpace D.U ⟶ X :=
    ObjectProperty.homMk D.targetChart
  have hxAtlasEtale : AlgebraicGeometry.Space.IsEtale B S hS D.targetChart :=
    AlgebraicGeometry.Space.isEtale_of_presheaf_etale B S hS D.targetEtale
  have hxAtlasFormalEtale : AlgebraicGeometry.Space.FormallyEtale D.targetChart :=
    AlgebraicGeometry.Space.formallyEtale_of_isUnramified_of_isFlat B S hS
      (AlgebraicGeometry.schemeSpace D.U).property X.property D.targetChart
      (AlgebraicGeometry.Space.isUnramified_of_isEtale B S hS hxAtlasEtale)
      (AlgebraicGeometry.Space.isFlat_of_isEtale B S hS hxAtlasEtale)
  have hVunivX : AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS
      (Subfunctor.range (yoneda.map iV))
      (AlgebraicGeometry.schemeSpaceMap pV ≫ xAtlas) :=
    AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.comp_formallyEtale
      B S hS (Subfunctor.range (yoneda.map iV))
      (AlgebraicGeometry.schemeSpaceMap pV) xAtlas hVuniv hxAtlasFormalEtale
  have hqVX : qV'alg ≫ gXalg = AlgebraicGeometry.schemeSpaceMap pV ≫ xAtlas :=
    ObjectProperty.hom_ext _ hgX
  let ZV : Subfunctor (AlgebraicGeometry.schemeSpace V').1 :=
    Subfunctor.range (yoneda.map iV)
  have : Mono (yoneda.map iV) := inferInstance
  let eV : yoneda.obj D.V ≅ (Subfunctor.range (yoneda.map iV)).toFunctor :=
    asIso (Subfunctor.toRange (yoneda.map iV))
  let aZV : ZV.toFunctor ⟶ Y.toFunctor := eV.inv ≫ aV
  have heVι : eV.inv ≫ yoneda.map iV = ZV.ι := by
    have h1 : eV.inv ≫ yoneda.map iV = eV.inv ≫ eV.hom ≫ ZV.ι :=
      congrArg (fun z => eV.inv ≫ z) (Subfunctor.toRange_ι (yoneda.map iV)).symm
    exact h1.trans (eV.inv_hom_id_assoc ZV.ι)
  have hZVsquare : IsPullback aZV ZV.ι Y.ι qV' := by
    apply haVpb.of_iso' eV.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · exact (Category.comp_id (eV.inv ≫ aV)).symm
    · exact heVι.trans (Category.comp_id ZV.ι).symm
    · simp
    · simp
  have haZVEtale : AlgebraicGeometry.Space.IsEtale B S hS aZV :=
    AlgebraicGeometry.Space.isEtale_comp B S hS
      (AlgebraicGeometry.Space.isEtale_of_isIso B S hS eV.symm.hom) haVEtale
  have haZVSurj : AlgebraicGeometry.Space.IsSurjective B S hS aZV := by
    change Function.Surjective (AlgebraicGeometry.Space.pointsMap B S hS
      (Subfunctor.range (yoneda.map iV)).toFunctor (eV.inv ≫ aV))
    rw [AlgebraicGeometry.Space.pointsMap_comp B S hS _ eV.inv aV]
    exact haVSurj.comp (AlgebraicGeometry.Space.surjective_pointsMap_of_isIso B S hS eV.symm)
  have hYuniv : AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS Y gXalg := by
    refine AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.of_surjectiveEtale
      B S hS Y ZV gXalg qV'alg hqV'Etale hYfirst aZV hZVsquare.w haZVEtale haZVSurj ?_
    rw [hqVX]
    exact hVunivX
  refine ⟨{ ambient := Q, source := Y, sourceIso := sourceIso, toBase := gXalg },
    ?_, hYuniv⟩
  change sourceIso.hom ≫ Y.ι ≫ gX = h.hom
  rw [← Category.assoc, hsourceIncl]
  exact congrArg (fun f => f.hom) hgZX

end Stacks.Spaces.UniversalThickening

end
