module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Limits.AffineTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.QuotientLimitAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Affine chart limits of a system of étale quotients are computed in schemes

Let `E` be an inverse system of étale equivalence relations `(V_j, R_j)` on objects of the big
fppf site with cartesian source squares and affine transition morphisms
(`AlgebraicGeometry.Space.EtaleRelationSystem`), whose objects have a limit `V = lim V_j` in
schemes. For an affine object `U₀` of the site mapping to a stage `V_{i₀}/R_{i₀}` of the system
of quotients, the base changes `U₀ ×_{V_{i₀}/R_{i₀}} V_j/R_j` have the base change
`U₀ ×_{V_{i₀}/R_{i₀}} lim_j V_j/R_j` as their limit in schemes, and not merely in the site.
This is `AlgebraicGeometry.Space.AffineChartLimitsInSchemes` for the system of quotients, the
condition under which Stacks 07SK runs without a bound on the index category; it is the first
step of the proof of Stacks 07SU, where the étale neighbourhood `W ⟶ U` of the open part is
descended to a finite stage of the system approximating `U`.

## Main results

* `AlgebraicGeometry.Scheme.isLimit_of_isLimit_of_isPullback`: a cone over a cofiltered diagram
  of schemes over a base `U` is a limit as soon as its base change along a surjective, flat,
  quasi-compact morphism `P ⟶ U` is a limit, provided the diagram has a limit.
* `CategoryTheory.Limits.isLimitOfIsPullbackOverStage`: the base change, along a morphism into a
  stage, of a limiting cone of a cofiltered diagram is a limit of the base changed stages.
* `AlgebraicGeometry.Space.EtaleRelationSystem.affineChartLimitsInSchemes`: the affine chart
  systems of the system of quotients have their limits computed in schemes.

## Implementation notes

The proof base changes the affine chart system along the surjective étale chart
`P = U₀ ×_{V_{i₀}/R_{i₀}} V_{i₀} ⟶ U₀`. After that base change the chart system becomes
`P ×_{V_{i₀}} V_j`, because the squares `V_j ⟶ V_{i₀}` over `V_j/R_j ⟶ V_{i₀}/R_{i₀}` are
cartesian (Stacks 07S3), and the system `P ×_{V_{i₀}} V_j` has `P ×_{V_{i₀}} V` as its limit in
schemes because `V` is the limit of the `V_j` in schemes. Isomorphisms descend along surjective
flat quasi-compact morphisms of schemes (Stacks 02L4), which brings the limit back down to `U₀`.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
* [Stacks Project, Tag 02L4](https://stacks.math.columbia.edu/tag/02L4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Limits

/-- **Base change of a cofiltered limit along a morphism into a stage.** Let `cD` be a limiting
cone of a cofiltered diagram `D`, and `g : T ⟶ D i` a morphism into a stage. A system `E` over
the stages above `i` whose members are the base changes `T ×_{D i} D j`, together with a cone
over it whose apex is the base change `T ×_{D i} cD.pt`, compatibly with the maps to `T` and to
the stages, is a limit. -/
noncomputable def isLimitOfIsPullbackOverStage {C : Type*} [Category* C] [HasPullbacks C]
    {J : Type*} [Category* J] [IsCofiltered J]
    (D : J ⥤ C) (cD : Cone D) (hcD : IsLimit cD) (i : J) (T : C) (g : T ⟶ D.obj i)
    (E : Over i ⥤ C) (c : Cone E)
    (p : E ⟶ Over.forget i ⋙ D) (q : E ⟶ (Functor.const _).obj T)
    (hp : ∀ j, IsPullback (p.app j) (q.app j) (D.map j.hom) g)
    (pL : c.pt ⟶ cD.pt) (qL : c.pt ⟶ T)
    (hL : IsPullback pL qL (cD.π.app i) g)
    (hc₁ : ∀ j, c.π.app j ≫ p.app j = pL ≫ cD.π.app j.left)
    (hc₂ : ∀ j, c.π.app j ≫ q.app j = qL) : IsLimit c := by
  let e : E ≅ (Over.post D) ⋙ Over.pullback g ⋙ Over.forget T :=
    NatIso.ofComponents (fun j => (hp j).isoPullback) (by
      intro j k f
      apply pullback.hom_ext
      · change (E.map f ≫ (hp k).isoPullback.hom) ≫ pullback.fst (D.map k.hom) g =
          ((hp j).isoPullback.hom ≫
            pullback.lift (pullback.fst (D.map j.hom) g ≫ D.map f.left)
              (pullback.snd (D.map j.hom) g)
              (by rw [Category.assoc, ← D.map_comp, Over.w f]; exact pullback.condition)) ≫
            pullback.fst (D.map k.hom) g
        simp only [Category.assoc, IsPullback.isoPullback_hom_fst, pullback.lift_fst,
          IsPullback.isoPullback_hom_fst_assoc]
        exact p.naturality f
      · change (E.map f ≫ (hp k).isoPullback.hom) ≫ pullback.snd (D.map k.hom) g =
          ((hp j).isoPullback.hom ≫
            pullback.lift (pullback.fst (D.map j.hom) g ≫ D.map f.left)
              (pullback.snd (D.map j.hom) g)
              (by rw [Category.assoc, ← D.map_comp, Over.w f]; exact pullback.condition)) ≫
            pullback.snd (D.map k.hom) g
        simp only [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd]
        simp)
  let cP := (Over.forget T).mapCone ((Over.pullback g).mapCone (cD.overPost i))
  have hcP : IsLimit cP := isLimitOfPreserves (Over.forget T)
    (isLimitOfPreserves (Over.pullback g) (hcD.overPost i))
  refine IsLimit.postcomposeHomEquiv e c (hcP.ofIsoLimit (Cone.ext hL.isoPullback fun j ↦ ?_).symm)
  apply pullback.hom_ext
  · change (c.π.app j ≫ (hp j).isoPullback.hom) ≫ pullback.fst _ _ =
      (hL.isoPullback.hom ≫ (pullback.lift (pullback.fst (cD.π.app i) g ≫ cD.π.app j.left)
          (pullback.snd (cD.π.app i) g)
          (by rw [Category.assoc, Cone.w]; exact pullback.condition))) ≫
        pullback.fst (D.map j.hom) g
    simp only [Category.assoc, IsPullback.isoPullback_hom_fst, pullback.lift_fst,
      IsPullback.isoPullback_hom_fst_assoc]
    exact hc₁ j
  · change (c.π.app j ≫ (hp j).isoPullback.hom) ≫ pullback.snd _ _ =
      (hL.isoPullback.hom ≫ (pullback.lift (pullback.fst (cD.π.app i) g ≫ cD.π.app j.left)
          (pullback.snd (cD.π.app i) g)
          (by rw [Category.assoc, Cone.w]; exact pullback.condition))) ≫
        pullback.snd (D.map j.hom) g
    simp only [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd]
    exact hc₂ j

end CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- **Limits of schemes descend along surjective flat quasi-compact base changes.** Let `G` be a
cofiltered diagram of schemes over a quasi-compact quasi-separated base `U` (for instance an
affine one) which has a limit, and let `c` be a
cone over `G` over `U`. Let `g : P ⟶ U` be surjective, flat and locally of finite presentation
(for instance a surjective étale morphism), let `G'` be a diagram of base
changes `G j ×_U P`, and let `c'` be a cone over `G'` whose apex is the base change
`c.pt ×_U P`, compatibly with the projections. If `c'` is a limit, then so is `c`. -/
theorem isLimit_of_isLimit_of_isPullback {K : Type*} [Category* K] [IsCofiltered K]
    {U P : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U] (g : P ⟶ U) [Surjective g] [Flat g]
    [LocallyOfFinitePresentation g]
    (G : K ⥤ Scheme.{u}) [HasLimit G] (π : G ⟶ (Functor.const K).obj U)
    (c : Cone G) (πc : c.pt ⟶ U) (hπc : ∀ j, c.π.app j ≫ π.app j = πc)
    (G' : K ⥤ Scheme.{u}) (α : G' ⟶ G) (β : G' ⟶ (Functor.const K).obj P)
    (hαβ : ∀ j, IsPullback (α.app j) (β.app j) (π.app j) g)
    (c' : Cone G') (hc' : IsLimit c') (αL : c'.pt ⟶ c.pt) (βL : c'.pt ⟶ P)
    (hL : IsPullback αL βL πc g)
    (hα : ∀ j, c'.π.app j ≫ α.app j = αL ≫ c.π.app j)
    (hβ : ∀ j, c'.π.app j ≫ β.app j = βL) :
    Nonempty (IsLimit c) := by
  have : IsConnected K := IsCofiltered.isConnected K
  have hπnat : ∀ {j k : K} (f : j ⟶ k), G.map f ≫ π.app k = π.app j := fun f => by simp
  let Gh : K ⥤ Over U := G.toOver U π.app hπnat
  let ch : Cone Gh :=
    { pt := Over.mk πc
      π := { app := fun j => Over.homMk (c.π.app j) (hπc j)
             naturality := fun j k f => by
               ext
               exact (c.w f).symm } }
  have : HasLimit Gh := by
    have : HasLimit (Gh ⋙ Over.forget U) := inferInstanceAs (HasLimit G)
    exact hasLimit_of_created Gh (Over.forget U)
  -- the base change of `ch` along `g` is a limit, being isomorphic to `c'`
  have hpb : IsLimit ((Over.pullback g).mapCone ch) := by
    apply isLimitOfReflects (Over.forget P)
    let e : G' ≅ Gh ⋙ Over.pullback g ⋙ Over.forget P :=
      NatIso.ofComponents (fun j => (hαβ j).isoPullback) (by
        intro j k f
        apply pullback.hom_ext
        · simp only [Functor.comp_map, Over.forget_map, Over.pullback_map_left, Category.assoc,
            pullback.lift_fst]
          change G'.map f ≫ (hαβ k).isoPullback.hom ≫ pullback.fst (π.app k) g =
            (hαβ j).isoPullback.hom ≫ pullback.fst (π.app j) g ≫ G.map f
          rw [IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc]
          exact α.naturality f
        · simp only [Functor.comp_map, Over.forget_map, Over.pullback_map_left, Category.assoc,
            pullback.lift_snd]
          change G'.map f ≫ (hαβ k).isoPullback.hom ≫ pullback.snd (π.app k) g =
            (hαβ j).isoPullback.hom ≫ pullback.snd (π.app j) g
          rw [IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd]
          simp)
    have h1 : IsLimit ((Cone.postcompose e.hom).obj c') :=
      (IsLimit.postcomposeHomEquiv e c').symm hc'
    refine h1.ofIsoLimit (Cone.ext hL.isoPullback fun j => ?_)
    apply pullback.hom_ext
    · simp only [Functor.mapCone_π_app, Over.forget_map, Over.pullback_map_left, Category.assoc,
        pullback.lift_fst]
      exact (congrArg (c'.π.app j ≫ ·) (hαβ j).isoPullback_hom_fst).trans
        ((hα j).trans (hL.isoPullback_hom_fst_assoc _).symm)
    · simp only [Functor.mapCone_π_app, Over.forget_map, Over.pullback_map_left, Category.assoc,
        pullback.lift_snd]
      exact (congrArg (c'.π.app j ≫ ·) (hαβ j).isoPullback_hom_snd).trans
        ((hβ j).trans hL.isoPullback_hom_snd.symm)
  -- a quasi-compact open of `P` still surjects onto `U`
  obtain ⟨W : P.Opens, hW, hWsurj⟩ :=
    g.isOpenMap.exists_opens_image_eq_of_prespectralSpace g.continuous (by simp) isOpen_univ
      isCompact_univ
  have : CompactSpace (Scheme.Opens.toScheme W) := isCompact_iff_compactSpace.mp hW
  let g' : Scheme.Opens.toScheme W ⟶ U := W.ι ≫ g
  have : Surjective g' := ⟨fun y ↦ by
    obtain ⟨x, hxW, hxy⟩ : y ∈ g.base '' W := by rw [hWsurj]; trivial
    exact ⟨⟨x, hxW⟩, hxy⟩⟩
  have : QuasiCompact g' := quasiCompact_of_compactSpace g'
  have hpb' : IsLimit ((Over.pullback g').mapCone ch) :=
    (IsLimit.mapConeEquiv (Over.pullbackComp W.ι g).symm)
      (isLimitOfPreserves (Over.pullback W.ι) hpb)
  -- the comparison morphism to the limit becomes an isomorphism after base change
  let ψ : ch ⟶ limit.cone Gh := (limit.isLimit Gh).liftConeMorphism ch
  have hiso : IsIso ((Cone.functoriality Gh (Over.pullback g')).map ψ) :=
    IsLimit.hom_isIso hpb' (isLimitOfPreserves (Over.pullback g') (limit.isLimit Gh)) _
  have hisoL : IsIso ((Over.pullback g').map ψ.hom).left := by
    have : IsIso ((Over.pullback g').map ψ.hom) :=
      inferInstanceAs
        (IsIso ((Cone.forget _).map ((Cone.functoriality Gh (Over.pullback g')).map ψ)))
    exact (Over.forget _).map_isIso ((Over.pullback g').map ψ.hom)
  have hsq : IsPullback ((Over.pullback g').map ψ.hom).left (pullback.fst πc g')
      (pullback.fst (limit Gh).hom g') ψ.hom.left := by
    refine (IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback (limit Gh).hom g')).flip
    · have h1 : ((Over.pullback g').map ψ.hom).left ≫ pullback.snd (limit Gh).hom g' =
          pullback.snd πc g' := pullback.lift_snd _ _ _
      have h2 : ψ.hom.left ≫ (limit Gh).hom = πc := Over.w ψ.hom
      rw [h1, h2]
      exact IsPullback.of_hasPullback πc g'
    · exact (pullback.lift_fst _ _ _).symm
  have hψ : IsIso ψ.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme.{u})
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq
      ⟨⟨(inferInstance : Surjective (pullback.fst (limit Gh).hom g')),
        (inferInstance : Flat (pullback.fst (limit Gh).hom g'))⟩,
        (inferInstance : QuasiCompact (pullback.fst (limit Gh).hom g'))⟩ hisoL
  have : IsIso ((Over.forget U).map ψ.hom) := hψ
  have : IsIso ψ.hom := isIso_of_reflects_iso ψ.hom (Over.forget U)
  have : IsIso ψ := Cone.cone_iso_of_hom_iso ψ
  refine ⟨(isLimitOfPreserves (Over.forget U)
    ((limit.isLimit Gh).ofIsoLimit (asIso ψ).symm)).ofIsoLimit
      (Cone.ext (Iso.refl _) fun j => ?_)⟩
  simp [ch]
  rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Space

/-- Pasting cartesian squares in presheaves: a cartesian square `γ, β, s, b` of the site, a
cartesian square `m, yoneda.map s, r, tq` of presheaves, and a cartesian square `ts, yoneda.map h,
r, q₀` give a cartesian square `α, β, h, a` of the site, with `α` compatible with `γ` and `m`. -/
private theorem exists_isPullback_of_paste {C : Type*} [Category C]
    {P' W V₀ X P Y : C} {Q Q₀ : Cᵒᵖ ⥤ Type _} (q₀ : yoneda.obj Y ⟶ Q₀)
    (tq : yoneda.obj V₀ ⟶ Q₀) (b : P ⟶ V₀) (a : P ⟶ Y)
    (hsqP : IsPullback (yoneda.map b) (yoneda.map a) tq q₀)
    (γ : P' ⟶ W) (β : P' ⟶ P) (s : W ⟶ V₀) (hγβ : IsPullback γ β s b)
    (m : yoneda.obj W ⟶ Q) (r : Q ⟶ Q₀) (hmid : IsPullback m (yoneda.map s) r tq)
    (ts : yoneda.obj X ⟶ Q) (h : X ⟶ Y) (hpb : IsPullback ts (yoneda.map h) r q₀) :
    ∃ α : P' ⟶ X, yoneda.map α ≫ ts = yoneda.map γ ≫ m ∧ α ≫ h = β ≫ a ∧
      IsPullback α β h a := by
  have hw : (yoneda.map γ ≫ m) ≫ r = yoneda.map (β ≫ a) ≫ q₀ := by
    rw [Category.assoc, hmid.w, ← Category.assoc, ← yoneda.map_comp, hγβ.w, yoneda.map_comp,
      Category.assoc, hsqP.w, yoneda.map_comp, Category.assoc]
  obtain ⟨α, hα⟩ := yoneda.map_surjective (hpb.lift _ _ hw)
  have h₁ : yoneda.map α ≫ ts = yoneda.map γ ≫ m := by simp [hα]
  have h₂ : α ≫ h = β ≫ a := yoneda.map_injective (by simp [hα])
  refine ⟨α, h₁, h₂, IsPullback.of_map yoneda h₂ (IsPullback.of_right ?_ ?_ hpb)⟩
  · rw [h₁, ← hsqP.w]
    exact (hγβ.map yoneda).paste_horiz hmid
  · rw [← yoneda.map_comp, ← yoneda.map_comp, h₂]

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

namespace EtaleRelationSystem

variable {J : Type u} [Category.{u} J] [IsCofiltered J] (E : EtaleRelationSystem B S hS J)

/-- **The chart systems of a system of étale quotients have their limits computed in schemes.**
Let `E` be an inverse system of étale equivalence relations with affine transition morphisms on
the objects, whose objects have a limit in schemes. Let `q₀ : Y₀ ⟶ V_{i₀}/R_{i₀}` be a morphism
from a quasi-compact quasi-separated object of the site, and let `F` be a system of objects over
`Y₀`, indexed by the stages over `i₀`, whose stages are the base changes `Y₀ ×_{V_{i₀}/R_{i₀}}
V_j/R_j`. Then a cone over `F` whose apex is the base change `Y₀ ×_{V_{i₀}/R_{i₀}} lim_j V_j/R_j`
is a limit in schemes. For an affine `Y₀` this is
`AlgebraicGeometry.Space.EtaleRelationSystem.affineChartLimitsInSchemes`. -/
theorem chartLimitsInSchemes
    (hobj : ∀ {i j : J} (g : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.obj.map g)))
    (cV : Cone E.obj) (hV : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cV))
    (i₀ : J) (U' : BigFppfOver B S hS)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj U')]
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U')]
    (q₀ : yoneda.obj U' ⟶ E.quotient.obj i₀) (F : Over i₀ ⥤ Over U')
    (toStage : ∀ j : Over i₀, yoneda.obj (F.obj j).left ⟶ E.quotient.obj j.left)
    (hnat : ∀ {j k : Over i₀} (e : j ⟶ k),
      yoneda.map (F.map e).left ≫ toStage k = toStage j ≫ E.quotient.map e.left)
    (hpb : ∀ j : Over i₀, IsPullback (toStage j) (yoneda.map (F.obj j).hom)
      (E.quotient.map j.hom) q₀)
    (c : Cone F) (p : yoneda.obj c.pt.left ⟶ limit E.quotient)
    (hp : IsPullback p (yoneda.map c.pt.hom) (limit.π E.quotient i₀) q₀)
    (hcomp : ∀ j : Over i₀, yoneda.map (c.π.app j).left ≫ toStage j =
      p ≫ limit.π E.quotient j.left) :
    Nonempty (IsLimit ((Over.forget U' ⋙ BigFppfOver.toScheme B S hS).mapCone c)) := by
  have : IsConnected J := IsCofiltered.isConnected J
  have hV' : IsLimit cV := BigFppfOver.isLimit_of_isLimit_toScheme B S hS hV
  let T := BigFppfOver.toScheme B S hS
  -- the surjective étale chart `P = U₀ ×_{V_{i₀}/R_{i₀}} V_{i₀} ⟶ U₀`
  have hrep : yoneda.relativelyRepresentable (E.toQuotient.app i₀) :=
    (E.isAlgebraicSpace_quotient_obj i₀).diagonal_representable.of_diag _
  let P := hrep.pullback q₀
  let a : P ⟶ U' := hrep.snd q₀
  let b : P ⟶ E.obj.obj i₀ := yoneda.preimage (hrep.fst q₀)
  have hb : yoneda.map b = hrep.fst q₀ := Functor.map_preimage _ _
  have hsqP : IsPullback (yoneda.map b) (yoneda.map a) (E.toQuotient.app i₀) q₀ :=
    hb ▸ hrep.isPullback q₀
  have hsurj : Surjective (T.map a) :=
    (quotientMap_surjective_unconditional B S hS (E.s.app i₀) (E.t.app i₀)).property q₀ _ a hsqP
  have hetale : Etale (T.map a) :=
    (quotientMap_etale_unconditional B S hS (E.s.app i₀) (E.t.app i₀)).property q₀ _ a hsqP
  -- the base changed chart system `P ×_{V_{i₀}} V_j`, in the site
  let G' : Over i₀ ⥤ BigFppfOver B S hS := Over.post E.obj ⋙ Over.pullback b ⋙ Over.forget P
  let c' : Cone G' := (Over.forget P).mapCone ((Over.pullback b).mapCone (cV.overPost i₀))
  let γ : G' ⟶ Over.forget i₀ ⋙ E.obj :=
    { app := fun j => pullback.fst (E.obj.map j.hom) b
      naturality := fun j k f => pullback.lift_fst _ _ _ }
  let β : G' ⟶ (Functor.const _).obj P :=
    { app := fun j => pullback.snd (E.obj.map j.hom) b
      naturality := fun j k f => (pullback.lift_snd _ _ _).trans (Category.comp_id _).symm }
  have hγβ : ∀ j, IsPullback (γ.app j) (β.app j) (E.obj.map j.hom) b := fun j =>
    IsPullback.of_hasPullback _ _
  -- the comparison maps `P ×_{V_{i₀}} V_j ⟶ F_j`
  choose α hα₁ hα₂ hsiteα using fun j : Over i₀ =>
    exists_isPullback_of_paste q₀ (E.toQuotient.app i₀) b a hsqP (γ.app j) (β.app j)
      (E.obj.map j.hom) (hγβ j) (E.toQuotient.app j.left) (E.quotient.map j.hom)
      (E.isPullback_toQuotient j.hom) (toStage j) (F.obj j).hom (hpb j)
  have hαnat : ∀ {j k : Over i₀} (f : j ⟶ k), G'.map f ≫ α k = α j ≫ (F.map f).left :=
    fun {j k} f => yoneda.map_injective <| by
      refine (hpb k).hom_ext ?_ ?_
      · calc yoneda.map (G'.map f ≫ α k) ≫ toStage k
            = yoneda.map (G'.map f) ≫ yoneda.map (α k) ≫ toStage k := by simp
          _ = yoneda.map (G'.map f ≫ γ.app k) ≫ E.toQuotient.app k.left := by
              rw [hα₁, Functor.map_comp, Category.assoc]
          _ = yoneda.map (γ.app j ≫ E.obj.map f.left) ≫ E.toQuotient.app k.left := by
              rw [γ.naturality f]; rfl
          _ = yoneda.map (γ.app j) ≫ E.toQuotient.app j.left ≫ E.quotient.map f.left := by
              rw [Functor.map_comp, Category.assoc]
              exact congrArg (yoneda.map (γ.app j) ≫ ·) (E.toQuotient.naturality f.left)
          _ = yoneda.map (α j) ≫ toStage j ≫ E.quotient.map f.left := by
              rw [← Category.assoc, ← hα₁, Category.assoc]
          _ = yoneda.map (α j ≫ (F.map f).left) ≫ toStage k := by
              rw [← hnat f, Functor.map_comp, Category.assoc]
      · rw [← yoneda.map_comp, ← yoneda.map_comp]
        congr 1
        simp only [Category.assoc, hα₂, Over.w (F.map f)]
        rw [← Category.assoc, β.naturality f]
        simp
  -- the apex: `P ×_{V_{i₀}} V` and its comparison map to the given cone
  let γL : c'.pt ⟶ cV.pt := pullback.fst (cV.π.app i₀) b
  let βL : c'.pt ⟶ P := pullback.snd (cV.π.app i₀) b
  obtain ⟨αL, hαL₁, hαL₂, hsiteL⟩ := exists_isPullback_of_paste q₀ (E.toQuotient.app i₀) b a hsqP
    γL βL (cV.π.app i₀) (IsPullback.of_hasPullback _ b) (E.limitToQuotient cV)
    (limit.π E.quotient i₀) (E.isPullback_limitToQuotient cV hV' i₀) p c.pt.hom hp
  have hcγ : ∀ j, c'.π.app j ≫ γ.app j = γL ≫ cV.π.app j.left := fun j =>
    pullback.lift_fst _ _ _
  have hcβ : ∀ j, c'.π.app j ≫ β.app j = βL := fun j => pullback.lift_snd _ _ _
  have hcα : ∀ j, c'.π.app j ≫ α j = αL ≫ (c.π.app j).left := fun j =>
    yoneda.map_injective <| by
      refine (hpb j).hom_ext ?_ ?_
      · calc yoneda.map (c'.π.app j ≫ α j) ≫ toStage j
            = yoneda.map (c'.π.app j ≫ γ.app j) ≫ E.toQuotient.app j.left := by
              rw [Functor.map_comp, Category.assoc, hα₁, ← Category.assoc, ← Functor.map_comp]
          _ = yoneda.map γL ≫ E.limitToQuotient cV ≫ limit.π E.quotient j.left := by
              rw [hcγ, limitToQuotient_π, Functor.map_comp, Category.assoc]
          _ = yoneda.map αL ≫ p ≫ limit.π E.quotient j.left := by
              rw [← Category.assoc, ← hαL₁, Category.assoc]
          _ = yoneda.map (αL ≫ (c.π.app j).left) ≫ toStage j := by
              rw [Functor.map_comp, Category.assoc, hcomp j]
      · rw [← yoneda.map_comp, ← yoneda.map_comp]
        congr 1
        rw [Category.assoc, hα₂, ← Category.assoc, hcβ, Category.assoc, Over.w (c.π.app j)]
        exact hαL₂.symm
  -- the chart system is affine over `Y₀`, so it has a limit in schemes
  have hFaff : ∀ j : Over i₀, _root_.AlgebraicGeometry.IsAffineHom (T.map (F.obj j).hom) :=
    fun j => by
      have h := ((isAffineHom_tfae_of_isAlgebraicSpace B S hS (E.quotient.map j.hom)
        (E.isAlgebraicSpace_quotient_obj _) (E.isAlgebraicSpace_quotient_obj _)).out 2 1).mp
          (E.isAffineHom_quotient_map hobj j.hom)
      exact h.2.property q₀ (toStage j) (F.obj j).hom (hpb j)
  let G : Over i₀ ⥤ Scheme.{u} := F ⋙ Over.forget U' ⋙ T
  have : ∀ j, _root_.AlgebraicGeometry.IsAffineHom
      ((fun j : Over i₀ => T.map (F.obj j).hom : ∀ j, G.obj j ⟶ T.obj U') j) := hFaff
  have : HasLimit G := CofilteredLimit.hasLimit_of_isAffineHom_of_isCofiltered
    (F := G) (fun j => T.map (F.obj j).hom) (fun {j k} f => by
      simp only [G, Functor.comp_map, Over.forget_map, ← T.map_comp, Over.w (F.map f)])
  -- the base changed cone is a limit in schemes
  let γT : G' ⋙ T ⟶ Over.forget i₀ ⋙ E.obj ⋙ T := Functor.whiskerRight γ T
  let βT : G' ⋙ T ⟶ (Functor.const _).obj (T.obj P) :=
    { app := fun j => T.map (β.app j)
      naturality := fun j k f => by
        simp only [Functor.comp_map, Functor.const_obj_map, Category.comp_id,
          ← T.map_comp, β.naturality f, Functor.const_obj_obj] }
  have hc' : IsLimit (T.mapCone c') :=
    isLimitOfIsPullbackOverStage (E.obj ⋙ T) (T.mapCone cV) hV i₀ (T.obj P) (T.map b)
      (G' ⋙ T) (T.mapCone c') γT βT (fun j => (hγβ j).map T) (T.map γL) (T.map βL)
      ((IsPullback.of_hasPullback (cV.π.app i₀) b).map T)
      (fun j => (T.map_comp _ _).symm.trans ((congrArg T.map (hcγ j)).trans (T.map_comp _ _)))
      (fun j => (T.map_comp _ _).symm.trans (congrArg T.map (hcβ j)))
  -- descend along the surjective étale chart
  let πT : G ⟶ (Functor.const _).obj (T.obj U') :=
    { app := fun j => T.map (F.obj j).hom
      naturality := fun j k f => by
        simp only [G, Functor.comp_map, Functor.const_obj_map, Category.comp_id,
          Over.forget_map, ← T.map_comp, Over.w (F.map f), Functor.const_obj_obj] }
  let αT : G' ⋙ T ⟶ G :=
    { app := fun j => T.map (α j)
      naturality := fun j k f => by
        simp only [G, Functor.comp_map, Over.forget_map, ← T.map_comp, hαnat f] }
  exact Scheme.isLimit_of_isLimit_of_isPullback (T.map a) G πT
    ((Over.forget U' ⋙ T).mapCone c) (T.map c.pt.hom)
    (fun j => (T.map_comp _ _).symm.trans (congrArg T.map (Over.w (c.π.app j))))
    (G' ⋙ T) αT βT (fun j => (hsiteα j).map T) (T.mapCone c') hc' (T.map αL) (T.map βL)
    (hsiteL.map T)
    (fun j => (T.map_comp _ _).symm.trans ((congrArg T.map (hcα j)).trans (T.map_comp _ _)))
    (fun j => (T.map_comp _ _).symm.trans (congrArg T.map (hcβ j)))

/-- **The affine chart systems of a system of étale quotients have their limits computed in
schemes.** For an inverse system of étale equivalence relations with affine transition morphisms
on the objects, whose objects have a limit in schemes, the system of quotients `V_j / R_j`
satisfies `AlgebraicGeometry.Space.AffineChartLimitsInSchemes`. -/
theorem affineChartLimitsInSchemes
    (hobj : ∀ {i j : J} (g : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.obj.map g)))
    (cV : Cone E.obj) (hV : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cV)) :
    AffineChartLimitsInSchemes B S hS E.quotient := by
  intro i₀ U₀ q₀ F toStage hnat hpb c p hp hcomp
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj U₀)) :=
    U₀.property
  exact E.chartLimitsInSchemes hobj cV hV i₀ _ q₀ F toStage hnat hpb c p hp hcomp

end EtaleRelationSystem

end AlgebraicGeometry.Space

end
