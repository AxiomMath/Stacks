module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChowLemma.ResolveGraph
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChowLemma.GraphClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverDenseOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic
public import StacksFrontier.AlgebraicGeometry.HProjective.QuasiProjectiveOfHQuasiProjective
public import StacksFrontier.AlgebraicGeometry.HProjective.AmpleBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Morphisms.OpenImmersionOfFlatClosure
public import StacksFrontier.AlgebraicGeometry.C1573Port.Blowup.FlattenedGraph
public import StacksFrontier.AlgebraicGeometry.C1573Port.SectionsToProjectiveSpace.DenseOpen
public import StacksFrontier.AlgebraicGeometry.C1573Port.Blowup.ReesAlgebra.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleExtension
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.StandardAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleEnlargementOfOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProjectiveSpaceContracted
public import StacksFrontier.AlgebraicGeometry.SegreProdIso.Main

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573
namespace AlgebraicGeometry.Space.C1573.ChowDatum
end AlgebraicGeometry.Space.C1573.ChowDatum

/-!
# The data Chow's lemma is concluded from

A `ChowDatum` for a morphism `f : X ⟶ Y` of algebraic spaces consists of a dense open `D ⊆ X`
which is a Noetherian affine scheme, an affine étale atlas of `X`, a scheme `T₀ ⟶ X` which is an
isomorphism over `D`, its chart over the atlas, closed in the product of the atlas with a closed
subscheme `Z₂` of a projective space, an ample invertible module on `T₀`, and an immersion of `T₀`
into a projective space over `Y`. From such a datum, Chow's lemma for `f` follows: there is a
`U`-admissible blowup of `X`, for a dense open `U`, which immerses into a projective space over
`Y`.

## Main definitions

* `AlgebraicGeometry.Space.C1573.ChowDatum`: the datum.

## Main results

* `AlgebraicGeometry.Space.C1573.exists_isImmersion_projectiveSpacePresheaf`: a closed subscheme
  of a projective space over a scheme immersed in a projective space over `Y` is immersed in a
  projective space over `Y` (Segre embedding, Stacks 01WD).
* `AlgebraicGeometry.Space.C1573.ChowDatum.exists_isAdmissibleBlowup`: the conclusion of Chow's
  lemma from a datum.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
  _root_.CategoryTheory.Limits.C1573
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- Projective space `ℙⁿ_Y = ℙⁿ_S ×_S Y` over a presheaf `Y` on the big fppf site of `S`. -/
abbrev C1573.projectiveSpacePresheaf (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (n : ℕ) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback ((isTerminal_yoneda_obj_base B S hS).from Y)
    ((isTerminal_yoneda_obj_base B S hS).from (yoneda.obj (projectiveSpaceSiteObject B S hS n)))

/-- A morphism of the site whose underlying morphism of schemes is an immersion is an immersion of
represented presheaves. -/
theorem C1573.isImmersion_yoneda_map_of_isImmersion {A A' : BigFppfOver B S hS} (g : A ⟶ A')
    (hg : _root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map g)) :
    IsImmersion B S hS (yoneda.map g) :=
  (presheaf_yoneda_map_iff B S hS (P := @_root_.AlgebraicGeometry.IsImmersion.{u})
    inferInstance g).2 hg

/-- Immersions of presheaves are stable under base change. -/
theorem C1573.isImmersion_of_isPullback' {A A' C C' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {fst : A ⟶ C} {snd : A ⟶ A'} {f : C ⟶ C'} {g : A' ⟶ C'} (sq : IsPullback fst snd f g)
    (hf : IsImmersion B S hS f) : IsImmersion B S hS snd :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sq hf

/-- **A product with a fixed presheaf is a base change.** Over a terminal object `t`, the map
`Y × A ⟶ Y × B` induced by `g : A ⟶ B` is a base change of `g`. -/
theorem C1573.isPullback_pullbackMap_terminal_presheaf {C : Type*} [Category C] [HasPullbacks C]
    {T Y A A' : C} (hT : IsTerminal T) (g : A ⟶ A') :
    IsPullback (pullback.snd (hT.from Y) (hT.from A))
      (pullback.map (hT.from Y) (hT.from A) (hT.from Y) (hT.from A') (𝟙 Y) g (𝟙 T)
        (hT.hom_ext _ _) (hT.hom_ext _ _)) g (pullback.snd (hT.from Y) (hT.from A')) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback (hT.from Y) (hT.from A')).flip
  rw [pullback.lift_fst, Category.comp_id,
    show g ≫ hT.from A' = hT.from A from hT.hom_ext _ _]
  exact (IsPullback.of_hasPullback (hT.from Y) (hT.from A)).flip

/-- **Projective space over the blowup of a scheme immersed in projective space over `Y`.** Let
`jT : h_{T₀} ⟶ ℙᵏ_Y` be an immersion and `W ⟶ T₀` a morphism with a closed immersion
`W ⟶ ℙᵃ_{T₀}` over `T₀`. Then `h_W` immerses into a projective space over `Y`, compatibly with
`jT` on the projections to `Y`. -/
theorem C1573.exists_isImmersion_projectiveSpacePresheaf {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T₀ W : BigFppfOver B S hS} {k a : ℕ} (jT : yoneda.obj T₀ ⟶ projectiveSpacePresheaf B S hS Y k)
    (hjT : IsImmersion B S hS jT) (πT : W ⟶ T₀)
    (iW : (BigFppfOver.toScheme B S hS).obj W ⟶
      projectiveSpaceOver a ((BigFppfOver.toScheme B S hS).obj T₀))
    [_root_.AlgebraicGeometry.IsClosedImmersion iW]
    (hiW : iW ≫ (projectiveSpaceOver a ((BigFppfOver.toScheme B S hS).obj T₀) ↘
      (BigFppfOver.toScheme B S hS).obj T₀) = (BigFppfOver.toScheme B S hS).map πT) :
    ∃ (N : ℕ) (iN : yoneda.obj W ⟶ projectiveSpacePresheaf B S hS Y N),
      IsImmersion B S hS iN ∧
        iN ≫ pullback.fst _ _ = yoneda.map πT ≫ jT ≫ pullback.fst _ _ := by
  set tS := isTerminal_yoneda_obj_base B S hS
  let toS := BigFppfOver.toScheme B S hS
  have tSo : IsTerminal (Over.mk (𝟙 (B.obj hS))) := Over.mkIdTerminal
  set PA := projectiveSpaceSiteObject B S hS a
  set PK := projectiveSpaceSiteObject B S hS k
  have hcPT : B.Contains (projectiveSpaceOver a (toS.obj T₀)) := by
    have := isProper_projectiveSpaceOver a (toS.obj T₀)
    exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
      (projectiveSpaceOver a (toS.obj T₀) ↘
        toS.obj T₀) T₀.left.property
  set gT : toS.obj T₀ ⟶ S := B.inclusion.map T₀.hom
  set PT := BigFppfOver.mk B S hS hcPT
    ((projectiveSpaceOver a (toS.obj T₀) ↘
      toS.obj T₀) ≫ gT)
  set prT : PT ⟶ T₀ := BigFppfOver.homMk B S hS T₀.left.property _
    (projectiveSpaceOver a (toS.obj T₀) ↘
      toS.obj T₀) rfl
  set mA := pullback.map (terminal.from (toS.obj T₀))
    (terminal.from (projectiveSpaceAtUniverse.{u} a)) (terminal.from S)
    (terminal.from (projectiveSpaceAtUniverse.{u} a)) gT (𝟙 _) (𝟙 _)
    (terminal.hom_ext _ _) (terminal.hom_ext _ _) with hmA
  have hsqA := isPullback_pullbackMap_terminal (P := projectiveSpaceAtUniverse.{u} a) gT
  set prA : PT ⟶ PA := BigFppfOver.homMk B S hS (contains_projectiveSpaceOver B S hS a) _ mA
    (by
      change mA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ gT
      exact hsqA.w)
  have yonedaPullback : ∀ {P A C : BigFppfOver B S hS} (p : P ⟶ A) (q : P ⟶ C)
      (f : A ⟶ Over.mk (𝟙 (B.obj hS))) (g : C ⟶ Over.mk (𝟙 (B.obj hS))),
      IsPullback (toS.map p) (toS.map q) (toS.map f) (toS.map g) →
      IsPullback (yoneda.map p) (yoneda.map q) (tS.from _) (tS.from _) := fun p q f g h => by
    convert (IsPullback.of_map toS (tSo.hom_ext _ _) h).map yoneda
      using 1 <;> exact tS.hom_ext _ _
  have hPT' := yonedaPullback prA prT (Over.homMk PA.hom (by simp)) (Over.homMk T₀.hom (by simp))
    hsqA
  set w : W ⟶ PT := BigFppfOver.homMk B S hS hcPT _ iW (by
    rw [← Category.assoc, hiW]
    change B.inclusion.map πT.left ≫ _ = _
    rw [← B.inclusion.map_comp, Over.w πT])
  have hw : IsImmersion B S hS (yoneda.map w) :=
    isImmersion_yoneda_map_of_isImmersion w (inferInstanceAs
      (_root_.AlgebraicGeometry.IsImmersion iW))
  have hwT : w ≫ prT = πT :=
    toS.map_injective ((Functor.map_comp _ _ _).trans hiW)
  obtain ⟨seg, hsegC, hseg⟩ := Stacks.AlgebraicGeometry.SegreProdIso.exists_segreEmbedding
    (n := a) (m := k) S
  have hcAK : B.Contains (pullback (projectiveSpaceOver a S ↘ S) (projectiveSpaceOver k S ↘ S)) :=
    Scheme.size_pullback_lt _ _ (contains_projectiveSpaceOver B S hS a)
      (contains_projectiveSpaceOver B S hS k)
  set PAK := BigFppfOver.mk B S hS hcAK
    (pullback.fst (projectiveSpaceOver a S ↘ S) (projectiveSpaceOver k S ↘ S) ≫
      (projectiveSpaceOver a S ↘ S))
  set PN := projectiveSpaceSiteObject B S hS (a * k + a + k)
  set q1 : PAK ⟶ PA := BigFppfOver.homMk B S hS (contains_projectiveSpaceOver B S hS a) _
    (pullback.fst _ _) rfl
  set q2 : PAK ⟶ PK := BigFppfOver.homMk B S hS (contains_projectiveSpaceOver B S hS k) _
    (pullback.snd _ _) pullback.condition.symm
  set sg : PAK ⟶ PN := BigFppfOver.homMk B S hS (contains_projectiveSpaceOver B S hS _) _
    seg hseg
  have hQ' := yonedaPullback q1 q2 (Over.homMk PA.hom (by simp)) (Over.homMk PK.hom (by simp))
    (IsPullback.of_hasPullback (projectiveSpaceOver a S ↘ S) (projectiveSpaceOver k S ↘ S))
  have hsg : IsImmersion B S hS (yoneda.map sg) :=
    isImmersion_yoneda_map_of_isImmersion sg (inferInstanceAs
      (_root_.AlgebraicGeometry.IsImmersion seg))
  set lam : yoneda.obj PT ⟶ yoneda.obj PAK :=
    hQ'.lift (yoneda.map prA) (yoneda.map prT ≫ jT ≫ pullback.snd _ _) (tS.hom_ext _ _)
  set L₁ : yoneda.obj PT ⟶ pullback (tS.from Y) (tS.from (yoneda.obj PAK)) :=
    pullback.lift (yoneda.map prT ≫ jT ≫ pullback.fst _ _) lam (tS.hom_ext _ _)
  set M := pullback.map (tS.from Y) (tS.from (yoneda.obj PAK)) (tS.from Y)
    (tS.from (yoneda.obj PK)) (𝟙 Y) (yoneda.map q2) (𝟙 _) (tS.hom_ext _ _) (tS.hom_ext _ _)
  have hM := isPullback_pullbackMap_terminal_presheaf (Y := Y) tS (yoneda.map q2)
  have hright : IsPullback (pullback.snd (tS.from Y) (tS.from (yoneda.obj PAK)) ≫ yoneda.map q1)
      M (tS.from (yoneda.obj PA)) (tS.from (projectiveSpacePresheaf B S hS Y k)) := by
    have := hM.paste_horiz hQ'
    convert this using 1
    exact tS.hom_ext _ _
  have hL₁ : IsPullback (yoneda.map prT) L₁ jT M := by
    refine (IsPullback.of_right ?_ ?_ hright).flip
    · have h1 : L₁ ≫ pullback.snd (tS.from Y) (tS.from (yoneda.obj PAK)) ≫ yoneda.map q1 =
          yoneda.map prA := by
        rw [← Category.assoc, pullback.lift_snd, IsPullback.lift_fst]
      rw [h1, show jT ≫ tS.from (projectiveSpacePresheaf B S hS Y k) =
        tS.from (yoneda.obj T₀) from tS.hom_ext _ _]
      exact hPT'
    · apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.comp_id, pullback.lift_fst,
          Category.assoc]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
          IsPullback.lift_snd, Category.assoc]
  have hiL₁ : IsImmersion B S hS L₁ := isImmersion_of_isPullback' hL₁ hjT
  set L₂ := pullback.map (tS.from Y) (tS.from (yoneda.obj PAK)) (tS.from Y)
    (tS.from (yoneda.obj PN)) (𝟙 Y) (yoneda.map sg) (𝟙 _) (tS.hom_ext _ _) (tS.hom_ext _ _)
  have hiL₂ : IsImmersion B S hS L₂ :=
    isImmersion_of_isPullback' (isPullback_pullbackMap_terminal_presheaf (Y := Y) tS
      (yoneda.map sg)) hsg
  refine ⟨a * k + a + k, yoneda.map w ≫ L₁ ≫ L₂,
    isImmersion_comp B S hS _ _ hw (isImmersion_comp B S hS _ _ hiL₁ hiL₂), ?_⟩
  simp only [Category.assoc]
  rw [pullback.lift_fst, Category.comp_id, pullback.lift_fst, ← yoneda.map_comp_assoc, hwT]

/-- **The data from which Chow's lemma is concluded**, for a morphism `f : X ⟶ Y` of algebraic
spaces: a dense open `u : h_D ⟶ X` from a Noetherian affine scheme, an affine étale atlas
`φ : h_V ⟶ X` with affine relation, a morphism `τ : h_{T₀} ⟶ X` from a Noetherian scheme which is
an isomorphism over `D`, with a chart `TV = T₀ ×_X V` closed in `V ×_S Z₂` for a closed subscheme
`Z₂` of a projective space over `S`, an ample invertible module on `T₀` and an immersion of `T₀`
into a projective space over `Y`. -/
structure C1573.ChowDatum (X : AlgebraicSpaces B S hS) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X.1 ⟶ Y) where
  /-- The dense open. -/
  D : BigFppfOver B S hS
  /-- The atlas. -/
  V : BigFppfOver B S hS
  /-- The scheme isomorphic to `X` over `D`. -/
  T₀ : BigFppfOver B S hS
  /-- The chart `T₀ ×_X V`. -/
  TV : BigFppfOver B S hS
  /-- The closed subscheme of projective space. -/
  Z₂ : BigFppfOver B S hS
  u : yoneda.obj D ⟶ X.1
  hu : IsOpenImmersion B S hS u
  hdense : letI := pointTopology B S hS X.1
    DenseRange (pointsMap B S hS (yoneda.obj D) u)
  φ : yoneda.obj V ⟶ X.1
  hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ
  he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ
  affV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)
  affR : IsAffine ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hs))
  noethV : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)
  noethT₀ : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T₀)
  noethTV : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj TV)
  noethD : _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj D)
  compactT₀ : CompactSpace ((BigFppfOver.toScheme B S hS).obj T₀)
  τ : yoneda.obj T₀ ⟶ X.1
  σ : D ⟶ T₀
  hσ : IsPullback (yoneda.map σ) (𝟙 _) τ u
  pT : TV ⟶ T₀
  tV : TV ⟶ V
  hsq : IsPullback (yoneda.map pT) (yoneda.map tV) τ φ
  o : T₀ ⟶ Z₂
  m : ℕ
  i : (BigFppfOver.toScheme B S hS).obj Z₂ ⟶ projectiveSpaceOver m S
  hiC : _root_.AlgebraicGeometry.IsClosedImmersion i
  hi : i ≫ pullback.fst _ _ = B.inclusion.map Z₂.hom
  cS : (BigFppfOver.toScheme B S hS).obj TV ⟶
    pullback (B.inclusion.map V.hom) (B.inclusion.map Z₂.hom)
  hcC : _root_.AlgebraicGeometry.IsClosedImmersion cS
  hc1 : cS ≫ pullback.fst _ _ = (BigFppfOver.toScheme B S hS).map tV
  hc2 : cS ≫ pullback.snd _ _ = (BigFppfOver.toScheme B S hS).map (pT ≫ o)
  M : ((BigFppfOver.toScheme B S hS).obj T₀).Modules
  hMi : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj T₀) M
  hM : letI := hMi; Stacks.Ample.IsAmple ((BigFppfOver.toScheme B S hS).obj T₀) M
  k : ℕ
  jT : yoneda.obj T₀ ⟶ projectiveSpacePresheaf B S hS Y k
  hjT : IsImmersion B S hS jT
  hjTf : jT ≫ pullback.fst _ _ = τ ≫ f

/-- **Chow's lemma from a Chow datum.** A `ChowDatum` for `f : X ⟶ Y` produces a dense open
subspace `U ⊆ X`, a `U`-admissible blowup `X' ⟶ X` with `X'` a scheme, and an immersion of `X'`
into a projective space over `Y`, over `f`. -/
theorem C1573.ChowDatum.exists_isAdmissibleBlowup {X : AlgebraicSpaces B S hS}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X.1 ⟶ Y} (d : ChowDatum X f) :
    letI := pointTopology B S hS X.1
    ∃ (U : OpenSubspaces B S hS X.1), DenseRange (pointsMap B S hS U.1.toFunctor U.1.ι) ∧
      ∃ (N : ℕ) (W : BigFppfOver B S hS) (π : schemeSpace W ⟶ X)
        (iN : yoneda.obj W ⟶ projectiveSpacePresheaf B S hS Y N),
        IsAdmissibleBlowup B S hS U π ∧ IsImmersion B S hS iN ∧
          iN ≫ pullback.fst _ _ = π.hom ≫ f ∧
          CompactSpace ((BigFppfOver.toScheme B S hS).obj W) := by
  let := BigFppfOver.hasSheafify_type B S hS
  let := pointTopology B S hS X.1
  have := d.affV
  have := d.affR
  have := d.noethV
  have := d.noethT₀
  have := d.noethTV
  have := d.noethD
  have := d.hiC
  have := d.hcC
  have : Finite (irreducibleComponents ((BigFppfOver.toScheme B S hS).obj d.D)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  obtain ⟨U', hdense, ZJ, hdisj, W, π, JT, eW, heW, hb⟩ :=
    exists_isBlowupAlong_resolution X d.u d.hu d.hs d.he d.τ d.σ d.hσ d.pT d.tV d.hsq d.o d.i
      d.hi d.cS d.hc1 d.hc2
  have hu' : IsOpenImmersion B S hS (yoneda.map (openSubHom d.D U') ≫ d.u) :=
    isOpenImmersion_comp B S hS _ _ (isOpenImmersion_yoneda_map_openSubHom d.D U') d.hu
  have : Mono (yoneda.map (openSubHom d.D U') ≫ d.u) := mono_of_presheaf_isOpenImmersion hu'
  set U : OpenSubspaces B S hS X.1 := ⟨Subfunctor.range (yoneda.map (openSubHom d.D U') ≫ d.u),
    isOpenSubspace_range_of_isOpenImmersion _ _ hu'⟩ with hUdef
  have hrangeU : Set.range (pointsMap B S hS U.1.toFunctor U.1.ι) =
      Set.range (pointsMap B S hS _ (yoneda.map (openSubHom d.D U') ≫ d.u)) :=
    range_pointsMap_ι_range B S hS _
  let := pointTopology B S hS (yoneda.obj d.D)
  let := pointTopology B S hS (yoneda.obj (openSub d.D U'))
  have hdenseU : DenseRange (pointsMap B S hS U.1.toFunctor U.1.ι) := by
    change Dense (Set.range _)
    rw [hrangeU, pointsMap_comp]
    have h1 : DenseRange (pointsMap B S hS _ (yoneda.map (openSubHom d.D U'))) := by
      rw [denseRange_pointsMap_yoneda_map_iff, toScheme_map_openSubHom]
      change Dense (Set.range U'.ι.base)
      rw [Scheme.Opens.range_ι]
      exact hdense
    exact d.hdense.comp h1 (continuous_pointsMap B S hS d.u)
  have hfp : IsFinitePresentation B S hS ZJ.1.ι := by
    refine (isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart B S hS
      (Z := ⟨ZJ.1.toFunctor, ZJ.2.1⟩) (X := X) (ObjectProperty.homMk ZJ.1.ι) ZJ.2.2 d.he d.hs).2
      fun A => ?_
    have := IsLocallyNoetherian.component_noetherian A
    exact IsNoetherian.noetherian _
  have hadm : IsAdmissibleBlowup B S hS U
      (schemeSpaceMap π ≫ (ObjectProperty.homMk d.τ : schemeSpace d.T₀ ⟶ X)) := by
    refine ⟨ZJ, hfp, ?_, hb⟩
    change Disjoint (Set.range (pointsMap B S hS U.1.toFunctor U.1.ι)) _
    rw [hrangeU]
    exact hdisj
  have := d.hMi
  have hJT : JT.IsFiniteType := fun A => by
    have := IsLocallyNoetherian.component_noetherian A
    exact IsNoetherian.noetherian _
  obtain ⟨a, iW, hiW, hiWo⟩ := isProjectiveMorphism_blowUpToBase JT hJT d.M d.hM
  have := hiW
  obtain ⟨N, iN, himm, hcomp⟩ := exists_isImmersion_projectiveSpacePresheaf d.jT d.hjT π
    (eW.hom ≫ iW) (by rw [Category.assoc, hiWo, heW])
  refine ⟨U, hdenseU, N, W, schemeSpaceMap π ≫ (ObjectProperty.homMk d.τ : schemeSpace d.T₀ ⟶ X),
    iN, hadm, himm, ?_, ?_⟩
  · rw [hcomp, d.hjTf]
    rfl
  · have := d.compactT₀
    have : _root_.AlgebraicGeometry.IsProper (AlgebraicGeometry.blowUpToBase JT) :=
      isProper_blowUpToBase_of_fg JT hJT
    have : CompactSpace (AlgebraicGeometry.blowUp JT) :=
      (quasiCompact_iff_compactSpace (AlgebraicGeometry.blowUpToBase JT)).1 inferInstance
    exact eW.inv.homeomorph.compactSpace

end AlgebraicGeometry.Space

end
