module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteAffineLimitsRealised
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Limits of algebraic spaces whose limit is realised in the site

`AlgebraicGeometry.Space.eventually_eq_of_baseChange_eq` and its companions in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent` carry a hypothesis
`#I < B.cutoff.ord.cof` on the index category of the inverse system. That hypothesis cannot
simply be dropped: without it the statements are **false**. See the module docstring section
"Why the index bound cannot just be deleted" below.

What is true, and what this file proves, is the same statement for a system presented
together with a limit *inside the site*: a diagram `Dsite : I ⥤ BigFppfOver B S hS` and a
cone `cS` on it whose image under the underlying-scheme functor is a limit cone. No
cardinal occurs anywhere in the hypotheses.

## Why the index bound cannot just be deleted

A `BigFppfSite` constrains its cutoff `κ` only by `ℵ₀ < κ`, `Cardinal.IsStrongPrelimit κ`
and `ℵ₀ < κ.ord.cof`; `κ` may be singular. Take `κ = ℶ_{ω₁}`, let `K` be a field of
characteristic zero with `#K = κ` written as an increasing union `⋃_{α < ω₁} A_α` of
subrings with `A_0 = ℤ` and `#A_α < κ`, and let `D α = yoneda (Spec A_α)` over
`S = Spec ℤ`, indexed by `I = ω₁ᵒᵖ`. Every stage is an affine object of the site and every
transition is affine, so all the hypotheses except the index bound hold.

The limit *presheaf* is then invisible to the site. For `T` in the site,
`(limit D)(T) = Hom_Ring(K, Γ(T, ⊤))`, and if `T` is nonempty then `K` embeds into
`Γ(T, V)` for a nonempty affine open `V ⊆ T`, forcing `#Γ(T, V) ≥ κ` against
`AlgebraicGeometry.Scheme.mk_sections_le_size`. So `limit D` is empty on every nonempty
object of the site. Consequently the two base changes of *any* pair of morphisms to the
limit agree vacuously, while for `Yᵢ = Zᵢ = yoneda (Spec ℤ[x])` over `D 0` the identity and
`x ↦ x + 1` differ at every stage. Faithfulness without the index bound therefore fails,
and fullness and essential surjectivity fail a fortiori.

The index bound is thus not proof bookkeeping: it is the only thing in the original
statement that forces the limit to be seen by the site. Requiring the limit to be an object
of the site — the hypothesis used here — is what restores the theorem, and unlike a
cardinality bound on `I` it is available in the intended applications, where the system is
a system of open neighbourhoods of a point and the limit is `Spec` of a local ring.

## Main results

* `AlgebraicGeometry.Space.eventually_eq_of_baseChange_eq_of_isLimit`: faithfulness, with no
  hypothesis on the size of the index category.
* `AlgebraicGeometry.Space.exists_hom_on_chart`: a morphism off the chart of the limit is
  defined on a finite-stage chart, again with no such hypothesis.
* `AlgebraicGeometry.Space.exists_mono_after_baseChange_of_isLimit`: monomorphy descends to a
  finite stage, with no such hypothesis.
* `AlgebraicGeometry.Space.exists_morphism_after_baseChange_of_isLimit`: fullness, with no
  hypothesis on the size of the index category.
* `AlgebraicGeometry.Space.exists_lift_pair_after_baseChange_of_isLimit`: a lift of a pair of
  morphisms over the limit descends to a finite stage, with no such hypothesis.
* `AlgebraicGeometry.Space.exists_model_of_finitePresentation_of_isLimit`: essential
  surjectivity, with no hypothesis on the size of the index category.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

open FinitePresentationDescent

attribute [local instance] AlgebraicGeometry.hasPullbacks_bigFppfOver
attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

section Realised

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (Dsite : I ⥤ AlgebraicGeometry.BigFppfOver B S hS)

/-! ### A cone of cartesian squares over an arbitrary limit cone -/

/-- A cone whose every leg sits in a cartesian square over the legs of a limit cone, and
whose apex sits in the cartesian square over the limit, is itself a limit cone. -/
noncomputable def isLimitOfCartesianCone
    {C : Type*} [Category* C] [HasPullbacks C]
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ C) (cD : Cone D) (hcD : IsLimit cD) (i : J) (T : C) (g : T ⟶ D.obj i)
    (E : Over i ⥤ C) (c : Cone E)
    (p : E ⟶ Over.forget i ⋙ D) (q : E ⟶ (Functor.const _).obj T)
    (hp : ∀ j, IsPullback (p.app j) (q.app j) (D.map j.hom) g)
    (pL : c.pt ⟶ cD.pt) (qL : c.pt ⟶ T)
    (hL : IsPullback pL qL (cD.π.app i) g)
    (hc₁ : ∀ j, c.π.app j ≫ p.app j = pL ≫ cD.π.app j.left)
    (hc₂ : ∀ j, c.π.app j ≫ q.app j = qL) : IsLimit c := by
  let : IsConnected (Over i) := IsCofiltered.isConnected _
  let P := (Over.post D) ⋙ Over.pullback g ⋙ Over.forget T
  let e : E ≅ P := NatIso.ofComponents (fun j => (hp j).isoPullback) (by
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
  apply (IsLimit.postcomposeHomEquiv e c).toFun
  apply hcP.ofIsoLimit
  apply Iso.symm
  refine Cone.ext hL.isoPullback ?_
  intro j
  apply pullback.hom_ext
  · change (c.π.app j ≫ (hp j).isoPullback.hom) ≫ pullback.fst _ _ =
      (hL.isoPullback.hom ≫ (pullback.lift (pullback.fst (cD.π.app i) g ≫ cD.π.app j.left)
          (pullback.snd (cD.π.app i) g)
          (by rw [Category.assoc, cD.w]; exact pullback.condition))) ≫
        pullback.fst (D.map j.hom) g
    simp only [Category.assoc, IsPullback.isoPullback_hom_fst, pullback.lift_fst,
      IsPullback.isoPullback_hom_fst_assoc]
    exact hc₁ j
  · change (c.π.app j ≫ (hp j).isoPullback.hom) ≫ pullback.snd _ _ =
      (hL.isoPullback.hom ≫ (pullback.lift (pullback.fst (cD.π.app i) g ≫ cD.π.app j.left)
          (pullback.snd (cD.π.app i) g)
          (by rw [Category.assoc, cD.w]; exact pullback.condition))) ≫
        pullback.snd (D.map j.hom) g
    simp only [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd]
    exact hc₂ j

/-- The first projection of a fibre product is natural in the object being pulled back. -/
theorem pullback_map_left_comp_fst {C : Type*} [Category* C] [HasPullbacks C] {X Y : C}
    (a₀ : X ⟶ Y) {g h : Over Y} (k : g ⟶ h) :
    ((Over.pullback a₀).map k).left ≫ pullback.fst h.hom a₀ =
      pullback.fst g.hom a₀ ≫ k.left := by
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

/-! ### The chart system of an affine object over a stage -/

/-- The system of fibre products of a fixed object `U₀` over the stage `Dsite i` with the
later stages, indexed by the slice over `i`. When `U₀` is affine and the transition
morphisms are affine this is a cofiltered system of affine objects of the site. -/
noncomputable abbrev chartDiagram (i : I) {U₀ : AlgebraicGeometry.BigFppfOver B S hS}
    (a₀ : U₀ ⟶ Dsite.obj i) : Over i ⥤ Over U₀ :=
  Over.post (X := i) Dsite ⋙ Over.pullback a₀

/-- The cone on the chart system induced by a cone on the system of stages. -/
noncomputable abbrev chartCone (i : I) {U₀ : AlgebraicGeometry.BigFppfOver B S hS}
    (a₀ : U₀ ⟶ Dsite.obj i) (cS : Cone Dsite) :
    Cone (chartDiagram B S hS Dsite i a₀) :=
  (Over.pullback a₀).mapCone (cS.overPost i)

variable {Dsite}

omit [IsCofiltered I] in
/-- Every stage of the chart system is affine, because the transition morphisms are affine
and the object being pulled back is. -/
theorem isAffine_chartDiagram_obj
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    (i : I) {U₀ : AlgebraicGeometry.BigFppfOver B S hS}
    (hU₀ : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀))
    (a₀ : U₀ ⟶ Dsite.obj i) (j : Over i) :
    IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      ((chartDiagram B S hS Dsite i a₀).obj j).left) := by
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hsq : IsPullback (G.map (pullback.fst (Dsite.map j.hom) a₀))
      (G.map (pullback.snd (Dsite.map j.hom) a₀))
      (G.map (Dsite.map j.hom)) (G.map a₀) :=
    (IsPullback.of_hasPullback (Dsite.map j.hom) a₀).map G
  have : _root_.AlgebraicGeometry.IsAffineHom
      (G.map ((chartDiagram B S hS Dsite i a₀).obj j).hom) :=
    MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsAffineHom) hsq
      (hAffine j.hom)
  have : IsAffine (G.obj U₀) := hU₀
  exact AlgebraicGeometry.isAffine_of_isAffineHom
    (G.map ((chartDiagram B S hS Dsite i a₀).obj j).hom)

/-- The apex of the chart cone is affine, because the projection from the limit is an
affine morphism. -/
theorem isAffine_chartCone_pt
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (i : I) {U₀ : AlgebraicGeometry.BigFppfOver B S hS}
    (hU₀ : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀))
    (a₀ : U₀ ⟶ Dsite.obj i) :
    IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (chartCone B S hS Dsite i a₀ cS).pt.left) := by
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have _ : ∀ {j k : I} (f : j ⟶ k),
      _root_.AlgebraicGeometry.IsAffineHom ((Dsite ⋙ G).map f) := fun f => hAffine f
  have hπ : _root_.AlgebraicGeometry.IsAffineHom (G.map (cS.π.app i)) :=
    AlgebraicGeometry.EventualLimit.isAffineHom_π_app (Dsite ⋙ G) (G.mapCone cS) hcS i
  have hsq : IsPullback (G.map (pullback.fst (cS.π.app i) a₀))
      (G.map (pullback.snd (cS.π.app i) a₀))
      (G.map (cS.π.app i)) (G.map a₀) :=
    (IsPullback.of_hasPullback (cS.π.app i) a₀).map G
  have : _root_.AlgebraicGeometry.IsAffineHom
      (G.map (chartCone B S hS Dsite i a₀ cS).pt.hom) :=
    MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsAffineHom) hsq hπ
  have : IsAffine (G.obj U₀) := hU₀
  exact AlgebraicGeometry.isAffine_of_isAffineHom
    (G.map (chartCone B S hS Dsite i a₀ cS).pt.hom)

/-! ### The chart cone's legs -/

omit [IsCofiltered I] in
/-- The chart cone's leg at `j`, followed by the chart's projection to the stage `Dsite j`,
is the projection of the limit chart to the limit followed by the limit cone's leg. -/
theorem chartCone_π_left_comp_fst
    (cS : Cone Dsite) (i : I) {U₀ : AlgebraicGeometry.BigFppfOver B S hS}
    (a₀ : U₀ ⟶ Dsite.obj i) (j : Over i) :
    ((chartCone B S hS Dsite i a₀ cS).π.app j).left ≫
        pullback.fst (Dsite.map j.hom) a₀ =
      pullback.fst (cS.π.app i) a₀ ≫ cS.π.app j.left :=
  pullback_map_left_comp_fst a₀ _

omit [IsCofiltered I] in
/-- The chart cone's leg at `j`, followed by the chart's structure map to `U₀`, is the
structure map of the limit chart. -/
theorem chartCone_π_left_comp_snd
    (cS : Cone Dsite) (i : I) {U₀ : AlgebraicGeometry.BigFppfOver B S hS}
    (a₀ : U₀ ⟶ Dsite.obj i) (j : Over i) :
    ((chartCone B S hS Dsite i a₀ cS).π.app j).left ≫
        pullback.snd (Dsite.map j.hom) a₀ =
      pullback.snd (cS.π.app i) a₀ :=
  Over.w ((chartCone B S hS Dsite i a₀ cS).π.app j)

/-- If the image of `cS` under the underlying-scheme functor is a limit cone, then so is the
image of the chart cone. -/
noncomputable def isLimitChartCone
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (i : I) {U₀ : AlgebraicGeometry.BigFppfOver B S hS} (a₀ : U₀ ⟶ Dsite.obj i) :
    IsLimit ((Over.forget U₀ ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone
      (chartCone B S hS Dsite i a₀ cS)) := by
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let pN : (chartDiagram B S hS Dsite i a₀ ⋙ Over.forget U₀ ⋙ G) ⟶
      Over.forget i ⋙ (Dsite ⋙ G) :=
    { app := fun j => G.map (pullback.fst (Dsite.map j.hom) a₀)
      naturality := fun j k f => by
        have h : ((chartDiagram B S hS Dsite i a₀).map f).left ≫
              pullback.fst (Dsite.map k.hom) a₀ =
            pullback.fst (Dsite.map j.hom) a₀ ≫ Dsite.map f.left :=
          pullback_map_left_comp_fst a₀ _
        exact ((G.map_comp _ _).symm.trans (congrArg G.map h)).trans (G.map_comp _ _) }
  let qN : (chartDiagram B S hS Dsite i a₀ ⋙ Over.forget U₀ ⋙ G) ⟶
      (Functor.const (Over i)).obj (G.obj U₀) :=
    { app := fun j => G.map (pullback.snd (Dsite.map j.hom) a₀)
      naturality := fun j k f => by
        have h : ((chartDiagram B S hS Dsite i a₀).map f).left ≫
              pullback.snd (Dsite.map k.hom) a₀ =
            pullback.snd (Dsite.map j.hom) a₀ :=
          Over.w ((chartDiagram B S hS Dsite i a₀).map f)
        exact ((G.map_comp _ _).symm.trans (congrArg G.map h)).trans
          (Category.comp_id _).symm }
  refine isLimitOfCartesianCone (Dsite ⋙ G) (G.mapCone cS) hcS i (G.obj U₀) (G.map a₀) _ _
    pN qN (fun j => (IsPullback.of_hasPullback (Dsite.map j.hom) a₀).map G)
    (G.map (pullback.fst (cS.π.app i) a₀)) (G.map (pullback.snd (cS.π.app i) a₀))
    ((IsPullback.of_hasPullback (cS.π.app i) a₀).map G) (fun j => ?_) (fun j => ?_)
  · exact ((G.map_comp _ _).symm.trans
      (congrArg G.map (chartCone_π_left_comp_fst B S hS cS i a₀ j))).trans (G.map_comp _ _)
  · exact (G.map_comp _ _).symm.trans
      (congrArg G.map (chartCone_π_left_comp_snd B S hS cS i a₀ j))

/-- The general-target form of `eventually_eq_on_chart`: the two morphisms are compared over
an arbitrary algebraic space `G` receiving the stage, not over the stage itself. -/
theorem eventually_eq_on_chart_over
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (i : I) {U₀ : AlgebraicGeometry.BigFppfOver B S hS}
    (hU₀ : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀))
    (a₀ : U₀ ⟶ Dsite.obj i)
    {G Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (b : yoneda.obj (Dsite.obj i) ⟶ G)
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ G)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f g : yoneda.obj U₀ ⟶ Z)
    (hf : f ≫ a = yoneda.map a₀ ≫ b) (hg : g ≫ a = yoneda.map a₀ ≫ b)
    (hfg : pullback.snd (yoneda.map (cS.π.app i)) (yoneda.map a₀) ≫ f =
      pullback.snd (yoneda.map (cS.π.app i)) (yoneda.map a₀) ≫ g) :
    ∃ j : Over i,
      yoneda.map ((chartDiagram B S hS Dsite i a₀).obj j).hom ≫ f =
        yoneda.map ((chartDiagram B S hS Dsite i a₀).obj j).hom ≫ g := by
  have hsq : IsPullback
      (yoneda.map ((pullback.fst (cS.π.app i) a₀ :
        (chartCone B S hS Dsite i a₀ cS).pt.left ⟶ cS.pt)))
      (yoneda.map (chartCone B S hS Dsite i a₀ cS).pt.hom)
      (yoneda.map (cS.π.app i)) (yoneda.map a₀) :=
    (IsPullback.of_hasPullback (cS.π.app i) a₀).map yoneda
  have hh : yoneda.map (chartCone B S hS Dsite i a₀ cS).pt.hom ≫ f =
      yoneda.map (chartCone B S hS Dsite i a₀ cS).pt.hom ≫ g := by
    have h2 := congrArg (fun k => hsq.isoPullback.hom ≫ k) hfg
    simp only [← Category.assoc, IsPullback.isoPullback_hom_snd] at h2
    exact h2
  exact eventually_eq_homs_of_locallyOfFinitePresentation B S hS hZalg hG a ha U₀
    (yoneda.map a₀ ≫ b)
    (chartDiagram B S hS Dsite i a₀) (chartCone B S hS Dsite i a₀ cS)
    (isLimitChartCone B S hS hcS i a₀)
    (isAffine_chartDiagram_obj B S hS hAffine i hU₀ a₀)
    (isAffine_chartCone_pt B S hS hAffine hcS i hU₀ a₀) f g hf hg hh

/-- The base change of a surjective étale morphism of presheaves is surjective and étale. -/
private theorem surjective_etale_presheaf_of_isPullback
    {X Y Z W : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf b ∧
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf b := by
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  exact ⟨P.presheaf.of_isPullback h hs, Q.presheaf.of_isPullback h he⟩

/-- A chart of the base change of `Dj` to a cover `q₀` of `Y` is the pullback of `q₀` along
the induced map to the base change of `Y`. -/
private theorem isPullback_lift_of_isPullback_comp
    {C : Type*} [Category* C] [HasPullbacks C] {Xi Xj Y Uo Cl : C}
    (r : Y ⟶ Xi) (Dj : Xj ⟶ Xi) (q₀ : Uo ⟶ Y) {cproj : Cl ⟶ Xj} {cchart : Cl ⟶ Uo}
    (hC : IsPullback cproj cchart Dj (q₀ ≫ r)) :
    IsPullback cchart
      (pullback.lift (cchart ≫ q₀) cproj (by simpa only [Category.assoc] using hC.w.symm))
      q₀ (pullback.fst r Dj) := by
  apply IsPullback.of_bot _ ((pullback.lift_fst _ _ _).symm)
    (IsPullback.of_hasPullback r Dj)
  simpa only [pullback.lift_snd] using hC.flip

/-- **Two morphisms out of a quasi-compact algebraic space over a stage, into a space
locally of finite presentation, which agree after base change to the limit agree already
after base change to a later stage.** No hypothesis on the size of the index category. -/
theorem eventually_eq_on_quasiCompact_source_of_isLimit
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (i : I) {Y Z G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (hYqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS Y)
    (r : Y ⟶ yoneda.obj (Dsite.obj i)) (a : Z ⟶ G)
    (b : yoneda.obj (Dsite.obj i) ⟶ G)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f g : Y ⟶ Z) (hf : f ≫ a = r ≫ b) (hg : g ≫ a = r ≫ b)
    (hfg : pullback.fst r (yoneda.map (cS.π.app i)) ≫ f =
      pullback.fst r (yoneda.map (cS.π.app i)) ≫ g) :
    ∃ (j : I) (e : j ⟶ i),
      pullback.fst r (yoneda.map (Dsite.map e)) ≫ f =
        pullback.fst r (yoneda.map (Dsite.map e)) ≫ g := by
  classical
  obtain ⟨U₀, q₀, hU₀, hsurj, het⟩ := exists_affine_etale_atlas B S hS Y hY hYqc
  let a₀ : U₀ ⟶ Dsite.obj i := yoneda.preimage (q₀ ≫ r)
  have ha₀ : yoneda.map a₀ = q₀ ≫ r := Functor.map_preimage _ _
  have hh : pullback.snd (yoneda.map (cS.π.app i)) (yoneda.map a₀) ≫ q₀ ≫ f =
      pullback.snd (yoneda.map (cS.π.app i)) (yoneda.map a₀) ≫ q₀ ≫ g := by
    rw [ha₀]
    let k : pullback (yoneda.map (cS.π.app i)) (q₀ ≫ r) ⟶
        pullback r (yoneda.map (cS.π.app i)) :=
      pullback.lift (pullback.snd (yoneda.map (cS.π.app i)) (q₀ ≫ r) ≫ q₀)
        (pullback.fst (yoneda.map (cS.π.app i)) (q₀ ≫ r))
        (by simp only [Category.assoc, pullback.condition])
    have hk : k ≫ pullback.fst r (yoneda.map (cS.π.app i)) =
        pullback.snd (yoneda.map (cS.π.app i)) (q₀ ≫ r) ≫ q₀ := pullback.lift_fst _ _ _
    rw [← reassoc_of% hk, ← reassoc_of% hk, hfg]
  obtain ⟨j, hj⟩ := eventually_eq_on_chart_over B S hS hAffine hcS i hU₀ a₀ hG b hZalg a ha
    (q₀ ≫ f) (q₀ ≫ g) (by rw [ha₀]; simp [hf]) (by rw [ha₀]; simp [hg]) hh
  refine ⟨j.left, j.hom, ?_⟩
  let C := (chartDiagram B S hS Dsite i a₀).obj j
  let Cproj : C.left ⟶ Dsite.obj j.left := pullback.fst (Dsite.map j.hom) a₀
  have hC : IsPullback (yoneda.map Cproj) (yoneda.map C.hom)
      (yoneda.map (Dsite.map j.hom)) (q₀ ≫ r) := by
    rw [← ha₀]
    exact (IsPullback.of_hasPullback (Dsite.map j.hom) a₀).map yoneda
  let p : yoneda.obj C.left ⟶ pullback r (yoneda.map (Dsite.map j.hom)) :=
    pullback.lift (yoneda.map C.hom ≫ q₀) (yoneda.map Cproj)
      (by simpa only [Category.assoc] using hC.w.symm)
  have hp := isPullback_lift_of_isPullback_comp r (yoneda.map (Dsite.map j.hom)) q₀ hC
  obtain ⟨hs, he⟩ := surjective_etale_presheaf_of_isPullback B S hS hp hsurj
    (represented_etale_of_isEtale B S hS q₀ het)
  apply hom_ext_of_surjective_etale_atlas B S hS
    (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS r (yoneda.map (Dsite.map j.hom)) hY
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj j.left))
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj i)))
    hZalg.isSheaf p hs he
  have hlift : p ≫ pullback.fst r (yoneda.map (Dsite.map j.hom)) =
      yoneda.map C.hom ≫ q₀ := pullback.lift_fst _ _ _
  rw [reassoc_of% hlift, reassoc_of% hlift]
  exact hj

/-! ### The limit projections are affine, and the limit is an algebraic space -/

/-- **The projections from the limit are affine morphisms**, with no hypothesis on the size of
the index category.

This is the analogue of `AlgebraicGeometry.Space.isAffineHom_limitπ` (Stacks 07SF part (1)),
which assumes `#I < B.cutoff.ord.cof`. -/
theorem isAffineHom_yoneda_map_π
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (i : I) :
    AlgebraicGeometry.Space.IsAffineHom B S hS (yoneda.map (cS.π.app i)) := by
  intro Z g
  classical
  let a₀ : (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj Z ⟶ Dsite.obj i :=
    yoneda.preimage g
  have ha₀ : yoneda.map a₀ = g := Functor.map_preimage _ _
  refine ⟨⟨(chartCone B S hS Dsite i a₀ cS).pt.left,
      isAffine_chartCone_pt B S hS hAffine hcS i Z.property a₀⟩,
    yoneda.map ((pullback.fst (cS.π.app i) a₀ :
      (chartCone B S hS Dsite i a₀ cS).pt.left ⟶ cS.pt)),
    (chartCone B S hS Dsite i a₀ cS).pt.hom, ?_⟩
  rw [← ha₀]
  exact (IsPullback.of_hasPullback (cS.π.app i) a₀).map yoneda

omit [IsCofiltered I] in
/-- The apex of `cS`, an object of the site, is an algebraic space. -/
theorem isAlgebraicSpace_yoneda_cone_pt (cS : Cone Dsite) :
    AlgebraicGeometry.IsAlgebraicSpace B S hS (yoneda.obj cS.pt) :=
  AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS cS.pt

/-! ### Lifting a morphism off the limit -/

/-- A morphism defined on the chart of the limit, into an algebraic space locally of finite
presentation over the stage, is already defined on one of the finite-stage charts,
compatibly. -/
theorem exists_hom_on_chart
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (i : I) {U₀ : AlgebraicGeometry.BigFppfOver B S hS}
    (hU₀ : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀))
    (a₀ : U₀ ⟶ Dsite.obj i)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    (a : Z ⟶ yoneda.obj (Dsite.obj i))
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f : yoneda.obj (chartCone B S hS Dsite i a₀ cS).pt.left ⟶ Z)
    (hf : f ≫ a =
      yoneda.map (chartCone B S hS Dsite i a₀ cS).pt.hom ≫ yoneda.map a₀) :
    ∃ (j : Over i) (g : yoneda.obj ((chartDiagram B S hS Dsite i a₀).obj j).left ⟶ Z),
      g ≫ a = yoneda.map ((chartDiagram B S hS Dsite i a₀).obj j).hom ≫ yoneda.map a₀ ∧
        yoneda.map ((chartCone B S hS Dsite i a₀ cS).π.app j).left ≫ g = f :=
  exists_hom_of_locallyOfFinitePresentation B S hS hZalg
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj i)) a ha U₀ (yoneda.map a₀)
    (chartDiagram B S hS Dsite i a₀) (chartCone B S hS Dsite i a₀ cS)
    (isLimitChartCone B S hS hcS i a₀)
    (isAffine_chartDiagram_obj B S hS hAffine i hU₀ a₀)
    (isAffine_chartCone_pt B S hS hAffine hcS i hU₀ a₀) f hf

/-! ### Descending a finite-presentation object from the limit chart -/

/-- The schemes of the chart system are affine over each other, compact and quasi-separated. -/
private theorem affineHom_compact_quasiSeparated_chartDiagram
    {J : Type u} [Category.{u} J] {D : J ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    (hAffine : ∀ {i j : J} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (D.map f)))
    (i : J) {U₀ : AlgebraicGeometry.BigFppfOver B S hS}
    (hU₀ : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀))
    (a₀ : U₀ ⟶ D.obj i) :
    let E := chartDiagram B S hS D i a₀ ⋙ Over.forget U₀ ⋙
      AlgebraicGeometry.BigFppfOver.toScheme B S hS
    (∀ {j k : Over i} (f : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (E.map f)) ∧
    (∀ j : Over i, CompactSpace (E.obj j)) ∧ (∀ j : Over i, QuasiSeparatedSpace (E.obj j)) := by
  intro E
  have hAff : ∀ j : Over i, IsAffine (E.obj j) := fun j =>
    isAffine_chartDiagram_obj B S hS hAffine i hU₀ a₀ j
  refine ⟨fun {j k} f => ?_, fun j => ?_, fun j => ?_⟩
  · have := hAff j
    have := hAff k
    exact AlgebraicGeometry.isAffineHom_of_isAffine _
  · have := hAff j; infer_instance
  · have := hAff j; infer_instance

/-- **A finite-presentation object over the limit of the chart system descends to a finite
stage.** No hypothesis on the size of the index category. -/
@[sga "3 VIB 10.0" "(ii), special case"]
theorem chartScheme_model_of_finitePresentation
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    (i : I) {U₀ : AlgebraicGeometry.BigFppfOver B S hS}
    (hU₀ : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀))
    (a₀ : U₀ ⟶ Dsite.obj i)
    (c : Cone (chartDiagram B S hS Dsite i a₀ ⋙ Over.forget U₀ ⋙
      AlgebraicGeometry.BigFppfOver.toScheme B S hS))
    (hc : IsLimit c) (X : Over c.pt)
    (hFp : _root_.AlgebraicGeometry.FinitePresentation X.hom) :
    ∃ (j : Over i) (Xⱼ : Over ((chartDiagram B S hS Dsite i a₀ ⋙ Over.forget U₀ ⋙
        AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj j)),
      _root_.AlgebraicGeometry.FinitePresentation Xⱼ.hom ∧
        Nonempty (X ≅ (Over.pullback (c.π.app j)).obj Xⱼ) := by
  let E := chartDiagram B S hS Dsite i a₀ ⋙ Over.forget U₀ ⋙
    AlgebraicGeometry.BigFppfOver.toScheme B S hS
  obtain ⟨_, _, _⟩ := affineHom_compact_quasiSeparated_chartDiagram B S hS hAffine i hU₀ a₀
  exact AlgebraicGeometry.Space.FinitePresentationDescent.scheme_model_of_finitePresentation
    E c hc X hFp

/-- `chartScheme_model_of_finitePresentation` at the canonical chart cone, which
`isLimitChartCone` exhibits as a limit. -/
theorem chartScheme_model_of_finitePresentation_chartCone
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (i : I) {U₀ : AlgebraicGeometry.BigFppfOver B S hS}
    (hU₀ : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀))
    (a₀ : U₀ ⟶ Dsite.obj i)
    (X : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (chartCone B S hS Dsite i a₀ cS).pt.left))
    (hFp : _root_.AlgebraicGeometry.FinitePresentation X.hom) :
    ∃ (j : Over i) (Xⱼ : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
        ((chartDiagram B S hS Dsite i a₀).obj j).left)),
      _root_.AlgebraicGeometry.FinitePresentation Xⱼ.hom ∧
        Nonempty (X ≅ (Over.pullback ((Over.forget U₀ ⋙
          AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
            ((chartCone B S hS Dsite i a₀ cS).π.app j))).obj Xⱼ) :=
  chartScheme_model_of_finitePresentation B S hS hAffine i hU₀ a₀ _
    (isLimitChartCone B S hS hcS i a₀) X hFp

/-- The affine refinement of `chartScheme_model_of_finitePresentation`: an affine
finite-presentation object over the limit of the chart system descends to an affine
finite-presentation object over a finite-stage chart. No hypothesis on the size of the index
category. -/
theorem chartScheme_affine_model_of_finitePresentation
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    (i : I) {U₀ : AlgebraicGeometry.BigFppfOver B S hS}
    (hU₀ : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀))
    (a₀ : U₀ ⟶ Dsite.obj i)
    (c : Cone (chartDiagram B S hS Dsite i a₀ ⋙ Over.forget U₀ ⋙
      AlgebraicGeometry.BigFppfOver.toScheme B S hS))
    (hc : IsLimit c) (X : Over c.pt)
    (hFp : _root_.AlgebraicGeometry.FinitePresentation X.hom)
    (hXaff : IsAffine X.left) :
    ∃ (j : Over i) (Xⱼ : Over ((chartDiagram B S hS Dsite i a₀ ⋙ Over.forget U₀ ⋙
        AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj j)),
      _root_.AlgebraicGeometry.FinitePresentation Xⱼ.hom ∧ IsAffine Xⱼ.left ∧
        Nonempty (X ≅ (Over.pullback (c.π.app j)).obj Xⱼ) := by
  let E := chartDiagram B S hS Dsite i a₀ ⋙ Over.forget U₀ ⋙
    AlgebraicGeometry.BigFppfOver.toScheme B S hS
  obtain ⟨_, _, _⟩ := affineHom_compact_quasiSeparated_chartDiagram B S hS hAffine i hU₀ a₀
  exact AlgebraicGeometry.Space.FinitePresentationDescent.scheme_affine_model_of_finitePresentation
    E c hc X hFp hXaff

/-! ### Etaleness spreads from the limit chart to a finite-stage chart -/

/-- A finite-presentation object over an affine chart which becomes etale after base change to
the chart of the limit is already etale over one of the finite-stage charts. No hypothesis on
the size of the index category. -/
theorem eventually_etale_on_chart
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (i : I) {U₀ : AlgebraicGeometry.BigFppfOver B S hS}
    (hU₀ : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀))
    (a₀ : U₀ ⟶ Dsite.obj i)
    (X : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀))
    (hX : _root_.AlgebraicGeometry.FinitePresentation X.hom)
    [Etale ((Over.pullback ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (chartCone B S hS Dsite i a₀ cS).pt.hom)).obj X).hom] :
    ∃ j : Over i, Etale ((Over.pullback
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        ((chartDiagram B S hS Dsite i a₀).obj j).hom)).obj X).hom := by
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let : IsConnected (Over i) := IsCofiltered.isConnected _
  let E' := chartDiagram B S hS Dsite i a₀ ⋙ Over.post Q
  let sc := (Over.post Q).mapCone (chartCone B S hS Dsite i a₀ cS)
  have hAff : ∀ j : Over i, IsAffine (E'.obj j).left := fun j =>
    isAffine_chartDiagram_obj B S hS hAffine i hU₀ a₀ j
  have : ∀ {j k : Over i} (a : j ⟶ k),
      _root_.AlgebraicGeometry.IsAffineHom (E'.map a).left := by
    intro j k a
    have := hAff j
    have := hAff k
    exact AlgebraicGeometry.isAffineHom_of_isAffine _
  have hsc : IsLimit ((Over.forget (Q.obj U₀)).mapCone sc) :=
    isLimitChartCone B S hS hcS i a₀
  let : Etale ((Over.pullback sc.pt.hom).obj X).hom :=
    ‹Etale ((Over.pullback (Q.map (chartCone B S hS Dsite i a₀ cS).pt.hom)).obj X).hom›
  exact AlgebraicGeometry.Space.FinitePresentationDescent.scheme_eventually_etale_pullback
    E' sc hsc X hX

/-! ### A finite-presentation chart descends to an object of the site over a stage -/

/-- A finitely presented model `f` of the limit chart over a finite-stage chart, cartesian over
the chart's projection to the stage, gives a finitely presented morphism to the stage whose
pullback along the limit's projection is `g`. -/
private theorem isFinitePresentation_and_isPullback_of_chart_model
    {J : Type u} [Category.{u} J] {D : J ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    (hAffine : ∀ {i j : J} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (D.map f)))
    (hQs : ∀ i, AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ
      (yoneda.obj (D.obj i)))
    {cS : Cone D}
    (i : J) {U₀ : AlgebraicGeometry.BigFppfOver B S hS}
    (hU₀ : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀))
    (a₀ : U₀ ⟶ D.obj i)
    (ha₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (yoneda.map a₀))
    (j : Over i) {W V : AlgebraicGeometry.BigFppfOver B S hS}
    (g : W ⟶ (chartCone B S hS D i a₀ cS).pt.left)
    (f : V ⟶ ((chartDiagram B S hS D i a₀).obj j).left) (a : W ⟶ V)
    (hf : _root_.AlgebraicGeometry.FinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f))
    (ha : IsPullback a g f ((chartCone B S hS D i a₀ cS).π.app j).left) :
    AlgebraicGeometry.Space.IsFinitePresentation B S hS
      (yoneda.map f ≫ yoneda.map (pullback.fst (D.map j.hom) a₀)) ∧
    IsPullback (yoneda.map a)
      (yoneda.map g ≫ yoneda.map (pullback.fst (cS.π.app i) a₀))
      (yoneda.map f ≫ yoneda.map (pullback.fst (D.map j.hom) a₀))
      (yoneda.map (cS.π.app j.left)) := by
  classical
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let b : (chartCone B S hS D i a₀ cS).pt.left ⟶
      ((chartDiagram B S hS D i a₀).obj j).left :=
    ((chartCone B S hS D i a₀ cS).π.app j).left
  let cproj : ((chartDiagram B S hS D i a₀).obj j).left ⟶ D.obj j.left :=
    pullback.fst (D.map j.hom) a₀
  let lproj : (chartCone B S hS D i a₀ cS).pt.left ⟶ cS.pt :=
    pullback.fst (cS.π.app i) a₀
  have hCj : IsPullback (yoneda.map cproj)
      (yoneda.map ((chartDiagram B S hS D i a₀).obj j).hom)
      (yoneda.map (D.map j.hom)) (yoneda.map a₀) :=
    (IsPullback.of_hasPullback (D.map j.hom) a₀).map yoneda
  have hbp : yoneda.map b ≫ yoneda.map cproj =
      yoneda.map lproj ≫ yoneda.map (cS.π.app j.left) :=
    ((yoneda.map_comp _ _).symm.trans
      (congrArg yoneda.map (chartCone_π_left_comp_fst B S hS cS i a₀ j))).trans
      (yoneda.map_comp _ _)
  have hbq : yoneda.map b ≫
      yoneda.map ((chartDiagram B S hS D i a₀).obj j).hom =
      yoneda.map (chartCone B S hS D i a₀ cS).pt.hom :=
    (yoneda.map_comp _ _).symm.trans
      (congrArg yoneda.map (chartCone_π_left_comp_snd B S hS cS i a₀ j))
  have hU : IsPullback (yoneda.map b) (yoneda.map lproj)
      (yoneda.map cproj)
      (yoneda.map (cS.π.app j.left)) := by
    apply IsPullback.of_right (h₂₂ := yoneda.map (D.map j.hom)) _ hbp hCj.flip
    rw [hbq, ← yoneda.map_comp, cS.w j.hom]
    exact ((IsPullback.of_hasPullback (cS.π.app i) a₀).map yoneda).flip
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Q
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (etaleInverseImageIsStableUnderComposition _)
  have hpc : P.presheaf (yoneda.map cproj) :=
    P.presheaf.of_isPullback hCj.flip ha₀
  have : IsAffine (Q.obj ((chartDiagram B S hS D i a₀).obj j).left) :=
    isAffine_chartDiagram_obj B S hS hAffine i hU₀ a₀ j
  have : LocallyOfFinitePresentation (Q.map f) := hf.1
  have : QuasiCompact (Q.map f) := hf.2.1
  have : QuasiSeparated (Q.map f) := hf.2.2
  have hVqc : CompactSpace (Q.obj V) := QuasiCompact.compactSpace_of_compactSpace (Q.map f)
  have hVqs : QuasiSeparatedSpace (Q.obj V) :=
    quasiSeparatedSpace_of_quasiSeparated (Q.map f)
  refine ⟨isFinitePresentation_of_scheme_chart B S hS hZ
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (D.obj j.left)) (hQs j.left)
      V ((chartDiagram B S hS D i a₀).obj j).left hVqc hVqs f
      (yoneda.map cproj) hpc hf.1, (ha.map yoneda).paste_vert hU⟩

/-- **A finite-presentation object over the limit chart descends to an object of the site,
finitely presented over a finite stage, cartesianly.** No hypothesis on the size of the index
category. -/
theorem exists_site_model_on_chart
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    (hQs : ∀ i, AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ
      (yoneda.obj (Dsite.obj i)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (i : I) {U₀ : AlgebraicGeometry.BigFppfOver B S hS}
    (hU₀ : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀))
    (a₀ : U₀ ⟶ Dsite.obj i)
    (ha₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (yoneda.map a₀))
    (W : AlgebraicGeometry.BigFppfOver B S hS)
    (g : W ⟶ (chartCone B S hS Dsite i a₀ cS).pt.left)
    (hg : _root_.AlgebraicGeometry.FinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) :
    ∃ (j : Over i) (V : AlgebraicGeometry.BigFppfOver B S hS)
      (v : yoneda.obj V ⟶ yoneda.obj (Dsite.obj j.left)) (a : W ⟶ V),
      AlgebraicGeometry.Space.IsFinitePresentation B S hS v ∧
      IsPullback (yoneda.map a)
        (yoneda.map g ≫ yoneda.map (pullback.fst (cS.π.app i) a₀))
        v (yoneda.map (cS.π.app j.left)) := by
  classical
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  obtain ⟨j, V₀, hV₀, ⟨e⟩⟩ :=
    chartScheme_model_of_finitePresentation_chartCone B S hS hAffine hcS i hU₀ a₀
      (Over.mk (Q.map g)) hg
  let b : (chartCone B S hS Dsite i a₀ cS).pt.left ⟶
      ((chartDiagram B S hS Dsite i a₀).obj j).left :=
    ((chartCone B S hS Dsite i a₀ cS).π.app j).left
  obtain ⟨V, f, a, hf, _, ha⟩ := exists_site_pullback_model B S hS b g V₀ hV₀ e
  obtain ⟨hfp, hpb⟩ := isFinitePresentation_and_isPullback_of_chart_model B S hS hZ hAffine hQs
    i hU₀ a₀ ha₀ j g f a hf ha
  exact ⟨j, V, _, a, hfp, hpb⟩

/-- The affine refinement of `exists_site_model_on_chart`: an affine finite-presentation
object over the limit chart descends to an affine object of the site, finitely presented over
a finite stage. No hypothesis on the size of the index category. -/
theorem exists_affine_site_model_on_chart
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    (hQs : ∀ i, AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ
      (yoneda.obj (Dsite.obj i)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (i : I) {U₀ : AlgebraicGeometry.BigFppfOver B S hS}
    (hU₀ : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀))
    (a₀ : U₀ ⟶ Dsite.obj i)
    (ha₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (yoneda.map a₀))
    (W : AlgebraicGeometry.BigFppfOver B S hS)
    (g : W ⟶ (chartCone B S hS Dsite i a₀ cS).pt.left)
    (hg : _root_.AlgebraicGeometry.FinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g))
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)] :
    ∃ (j : Over i) (V : AlgebraicGeometry.BigFppfOver B S hS)
      (v : yoneda.obj V ⟶ yoneda.obj (Dsite.obj j.left)) (a : W ⟶ V),
      AlgebraicGeometry.Space.IsFinitePresentation B S hS v ∧
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V) ∧
      IsPullback (yoneda.map a)
        (yoneda.map g ≫ yoneda.map (pullback.fst (cS.π.app i) a₀))
        v (yoneda.map (cS.π.app j.left)) := by
  classical
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  obtain ⟨j, V₀, hV₀, hV₀aff, ⟨e⟩⟩ :=
    chartScheme_affine_model_of_finitePresentation B S hS hAffine i hU₀ a₀ _
      (isLimitChartCone B S hS hcS i a₀) (Over.mk (Q.map g)) hg
      ‹IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)›
  let b : (chartCone B S hS Dsite i a₀ cS).pt.left ⟶
      ((chartDiagram B S hS Dsite i a₀).obj j).left :=
    ((chartCone B S hS Dsite i a₀ cS).π.app j).left
  obtain ⟨V, f, a, hf, ⟨eV⟩, ha⟩ := exists_site_pullback_model B S hS b g V₀ hV₀ e
  obtain ⟨hfp, hpb⟩ := isFinitePresentation_and_isPullback_of_chart_model B S hS hZ hAffine hQs
    i hU₀ a₀ ha₀ j g f a hf ha
  refine ⟨j, V, _, a, hfp, ?_, hpb⟩
  have : IsAffine V₀.left := hV₀aff
  have : IsIso eV.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (Q.obj
      ((chartDiagram B S hS Dsite i a₀).obj j).left)).map eV.hom))
  exact IsAffine.of_isIso eV.hom.left

/-! ### Faithfulness -/

/-- Two morphisms out of an affine object over a stage, into an algebraic space locally of
finite presentation over that stage, which agree after base change to the limit already
agree on one of the charts. -/
theorem eventually_eq_on_chart
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (i : I) {U₀ : AlgebraicGeometry.BigFppfOver B S hS}
    (hU₀ : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀))
    (a₀ : U₀ ⟶ Dsite.obj i)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    (a : Z ⟶ yoneda.obj (Dsite.obj i))
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f g : yoneda.obj U₀ ⟶ Z)
    (hf : f ≫ a = yoneda.map a₀) (hg : g ≫ a = yoneda.map a₀)
    (hfg : pullback.snd (yoneda.map (cS.π.app i)) (yoneda.map a₀) ≫ f =
      pullback.snd (yoneda.map (cS.π.app i)) (yoneda.map a₀) ≫ g) :
    ∃ j : Over i,
      yoneda.map ((chartDiagram B S hS Dsite i a₀).obj j).hom ≫ f =
        yoneda.map ((chartDiagram B S hS Dsite i a₀).obj j).hom ≫ g := by
  exact eventually_eq_on_chart_over B S hS hAffine hcS i hU₀ a₀
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj i)) (𝟙 _) hZalg a ha f g
    (hf.trans (Category.comp_id _).symm) (hg.trans (Category.comp_id _).symm) hfg

/-- **Stacks 07SK, faithfulness, with no hypothesis on the size of the index category.**

Two morphisms of algebraic spaces of finite presentation over a stage of a cofiltered
inverse system with affine transition morphisms, whose base changes to the limit agree,
agree already at a later stage.

The system is given as a diagram `Dsite` in the big fppf site together with a cone `cS` on
it whose image under the underlying-scheme functor is a limit cone. That the limit is an
object of the site is what replaces the hypothesis `#I < B.cutoff.ord.cof` of
`AlgebraicGeometry.Space.eventually_eq_of_baseChange_eq`; the statement is false without
some such hypothesis, as the module docstring explains. The stages are *not* assumed
affine, only quasi-compact. -/
theorem eventually_eq_of_baseChange_eq_of_isLimit
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (hQc : ∀ i, AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS
      (yoneda.obj (Dsite.obj i)))
    (i : I) (Yᵢ Zᵢ : Over (yoneda.obj (Dsite.obj i)))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zᵢ.hom)
    (f g : Yᵢ ⟶ Zᵢ)
    (hfg : (Over.pullback (yoneda.map (cS.π.app i))).map f =
      (Over.pullback (yoneda.map (cS.π.app i))).map g) :
    ∃ (j : I) (e : j ⟶ i),
      (Over.pullback (yoneda.map (Dsite.map e))).map f =
        (Over.pullback (yoneda.map (Dsite.map e))).map g := by
  classical
  have hDi := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj i)
  have hYqc := AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation B S hS
    Yᵢ.hom hDi (hQc i) hYfp
  obtain ⟨j, e, hj⟩ := eventually_eq_on_quasiCompact_source_of_isLimit B S hS hAffine hcS i
    hY hZ' hDi hYqc Yᵢ.hom Zᵢ.hom (𝟙 _) hZfp.1 f.left g.left
    (by rw [Over.w f, Category.comp_id]) (by rw [Over.w g, Category.comp_id])
    (by rw [← pullback_map_left_comp_fst _ f, ← pullback_map_left_comp_fst _ g, hfg])
  refine ⟨j, e, ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact ((pullback_map_left_comp_fst _ f).trans hj).trans (pullback_map_left_comp_fst _ g).symm
  · exact (Over.w _).trans (Over.w _).symm

/-! ### Monomorphy descends to a finite stage -/

/-- **A morphism of finite-presentation algebraic spaces over a stage which becomes a
monomorphism after base change to the limit is already a monomorphism after base change to a
later stage.** No hypothesis on the size of the index category. -/
theorem exists_mono_after_baseChange_of_isLimit
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    (hQc : ∀ i, AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS
      (yoneda.obj (Dsite.obj i)))
    (hQs : ∀ i, AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ
      (yoneda.obj (Dsite.obj i)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (i : I) (Y Z : Over (yoneda.obj (Dsite.obj i)))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Z.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Z.hom)
    (f : Y ⟶ Z) [Mono ((Over.pullback (yoneda.map (cS.π.app i))).map f)] :
    ∃ (j : I) (e : j ⟶ i),
      Mono ((Over.pullback (yoneda.map (Dsite.map e))).map f) := by
  let c := overPullbackCone f f
  have hc := overPullbackCone_isPullback f f
  have hDi := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj i)
  have hf := isFinitePresentation_overHom B S hS hZ hDi (hQc i) (hQs i)
    Y Z hY hZ' hYfp hZfp f
  have hR : AlgebraicGeometry.IsAlgebraicSpace B S hS c.pt.left :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS f.left f.left hY hY hZ'
  have hRfst := isFinitePresentation_of_isPullback B S hS hR hY hY hZ'
    (IsPullback.of_hasPullback f.left f.left).flip hf
  have hRfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS c.pt.hom :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hR hY hDi
      (pullback.fst f.left f.left) Y.hom hRfst hYfp
  have heq : (Over.pullback (yoneda.map (cS.π.app i))).map c.fst =
      (Over.pullback (yoneda.map (cS.π.app i))).map c.snd := by
    apply (cancel_mono ((Over.pullback (yoneda.map (cS.π.app i))).map f)).mp
    rw [← Functor.map_comp, ← Functor.map_comp, c.condition]
  obtain ⟨j, e, hj⟩ := eventually_eq_of_baseChange_eq_of_isLimit B S hS hAffine hcS hQc
    i c.pt Y hR hY hRfp hYfp c.fst c.snd heq
  exact ⟨j, e, IsKernelPair.mono_of_eq_fst_snd
    (hc.map (Over.pullback (yoneda.map (Dsite.map e)))) hj⟩

/-! ### Fullness -/

omit [IsCofiltered I] in
/-- The compatibility `Cone.w` of the cone `cS`, read through `yoneda`. -/
theorem yoneda_map_cone_w {cS : Cone Dsite} {j i : I} (e : j ⟶ i) :
    yoneda.map (cS.π.app j) ≫ yoneda.map (Dsite.map e) = yoneda.map (cS.π.app i) :=
  (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map (cS.w e))

omit [IsCofiltered I] in
/-- Functoriality of `Dsite`, read through `yoneda`. -/
theorem yoneda_map_Dsite_comp {k j i : I} (e : k ⟶ j) (d : j ⟶ i) :
    yoneda.map (Dsite.map e) ≫ yoneda.map (Dsite.map d) =
      yoneda.map (Dsite.map (e ≫ d)) :=
  (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map (Dsite.map_comp e d).symm)

/-- Two squares over `Y` are given: `hC`, exhibiting the chart `Cl` of a later stage, and `hW`,
exhibiting the chart `Wl` of the limit; `cl` is the comparison between them, `p` and `k` are
the induced maps to the two base changes of `Y`, and `lift` compares the iterated base change
with the single one. A morphism `g` on the later-stage chart that agrees with `f` after base
change to the limit then agrees with `f` on the whole base change of the stage. -/
theorem fst_comp_eq_lift_comp_iteratedBaseChangeIso
    {C : Type*} [Category* C] [HasPullbacks C]
    {Xi Xj L Uo Cl Wl T Zl : C} (Y : Over Xi)
    (Dj : Xj ⟶ Xi) (πi : L ⟶ Xi) (πj : L ⟶ Xj) (hπ : πj ≫ Dj = πi)
    (q₀ : Uo ⟶ Y.left)
    {cproj : Cl ⟶ Xj} {cchart : Cl ⟶ Uo}
    (hC : IsPullback cproj cchart Dj (q₀ ≫ Y.hom))
    {wproj : Wl ⟶ L} {wchart : Wl ⟶ Uo}
    (hW : IsPullback wproj wchart πi (q₀ ≫ Y.hom))
    (cl : Wl ⟶ Cl) (hcl₁ : cl ≫ cproj = wproj ≫ πj) (hcl₂ : cl ≫ cchart = wchart)
    (p : Cl ⟶ pullback Y.hom Dj)
    (hp₁ : p ≫ pullback.fst Y.hom Dj = cchart ≫ q₀)
    (hp₂ : p ≫ pullback.snd Y.hom Dj = cproj)
    (k : Wl ⟶ pullback Y.hom πi)
    (hk₁ : k ≫ pullback.fst Y.hom πi = wchart ≫ q₀)
    (hk₂ : k ≫ pullback.snd Y.hom πi = wproj)
    (tF : T ⟶ Cl) (tG : T ⟶ L)
    (htc : tF ≫ p ≫ pullback.snd Y.hom Dj = tG ≫ πj)
    (lift : T ⟶ pullback (pullback.snd Y.hom Dj) πj)
    (hlift₁ : lift ≫ pullback.fst (pullback.snd Y.hom Dj) πj = tF ≫ p)
    (hlift₂ : lift ≫ pullback.snd (pullback.snd Y.hom Dj) πj = tG)
    (g : Cl ⟶ Zl) (f : pullback Y.hom πi ⟶ Zl) (hgf : cl ≫ g = k ≫ f) :
    tF ≫ g = lift ≫ (iteratedBaseChangeIso Dj πj πi hπ Y).hom.left ≫ f := by
  have hR : (p ≫ pullback.snd Y.hom Dj) ≫ Dj = cchart ≫ q₀ ≫ Y.hom := by
    rw [hp₂, hC.w]
  have hv₁ : tG ≫ πi = (tF ≫ cchart) ≫ q₀ ≫ Y.hom := by
    rw [← hπ, ← Category.assoc, ← htc, Category.assoc, hR, Category.assoc]
  let v : T ⟶ Wl := hW.lift tG (tF ≫ cchart) hv₁
  have hvfst : v ≫ wproj = tG := hW.lift_fst _ _ _
  have hvsnd : v ≫ wchart = tF ≫ cchart := hW.lift_snd _ _ _
  have hvcl : v ≫ cl = tF := by
    apply hC.hom_ext
    · rw [Category.assoc, hcl₁, ← Category.assoc, hvfst, ← htc, hp₂]
    · rw [Category.assoc, hcl₂, hvsnd]
  have hvk : v ≫ k = lift ≫ (iteratedBaseChangeIso Dj πj πi hπ Y).hom.left := by
    apply pullback.hom_ext
    · rw [Category.assoc, hk₁, ← Category.assoc, hvsnd, Category.assoc, ← hp₁,
        Category.assoc, iteratedBaseChangeIso_hom_fst, ← Category.assoc, ← Category.assoc,
        hlift₁]
    · rw [Category.assoc, hk₂, hvfst, Category.assoc, iteratedBaseChangeIso_hom_left,
        pullback.lift_snd, hlift₂]
  rw [← hvcl, Category.assoc, hgf, reassoc_of% hvk]

/-- **A morphism defined on the base change of a stage to the limit is defined, on an affine
étale chart, already at a later stage.** No hypothesis on the size of the index category.

The affine chart `U` of a later stage and its surjective étale map `p` to the base change of
`Y` along that stage come with the factorization `g` of `f`, and the last conjunct records
that `g` recovers `f` after base change to the limit. -/
theorem exists_stage_atlas_factorization_of_isLimit
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (i : I) (Y : Over (yoneda.obj (Dsite.obj i)))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hYqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS Y.left)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    (a : Z ⟶ yoneda.obj (Dsite.obj i))
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f : pullback Y.hom (yoneda.map (cS.π.app i)) ⟶ Z)
    (hf : f ≫ a = pullback.fst Y.hom (yoneda.map (cS.π.app i)) ≫ Y.hom) :
    ∃ (j : Over i) (U : AlgebraicGeometry.BigAffineFppf B S hS)
      (p : yoneda.obj U.obj ⟶ pullback Y.hom (yoneda.map (Dsite.map j.hom)))
      (g : yoneda.obj U.obj ⟶ Z),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p ∧
      g ≫ a = p ≫ pullback.snd Y.hom (yoneda.map (Dsite.map j.hom)) ≫
        yoneda.map (Dsite.map j.hom) ∧
      pullback.fst (p ≫ pullback.snd Y.hom (yoneda.map (Dsite.map j.hom)))
          (yoneda.map (cS.π.app j.left)) ≫ g =
        pullback.lift
          (pullback.fst (p ≫ pullback.snd Y.hom (yoneda.map (Dsite.map j.hom)))
            (yoneda.map (cS.π.app j.left)) ≫ p)
          (pullback.snd (p ≫ pullback.snd Y.hom (yoneda.map (Dsite.map j.hom)))
            (yoneda.map (cS.π.app j.left)))
          (by simpa only [Over.pullback_obj_hom, Category.assoc] using
            (pullback.condition
              (f := p ≫ pullback.snd Y.hom (yoneda.map (Dsite.map j.hom)))
              (g := yoneda.map (cS.π.app j.left)))) ≫
        (iteratedBaseChangeIso (yoneda.map (Dsite.map j.hom))
          (yoneda.map (cS.π.app j.left)) (yoneda.map (cS.π.app i))
          (yoneda_map_cone_w B S hS j.hom) Y).hom.left ≫ f := by
  classical
  obtain ⟨U₀, q₀, hU₀, hs, he⟩ := exists_affine_etale_atlas B S hS Y.left hY hYqc
  let a₀ : U₀ ⟶ Dsite.obj i := yoneda.preimage (q₀ ≫ Y.hom)
  have ha₀ : yoneda.map a₀ = q₀ ≫ Y.hom := Functor.map_preimage _ _
  have hsq : IsPullback
      (yoneda.map ((pullback.fst (cS.π.app i) a₀ :
        (chartCone B S hS Dsite i a₀ cS).pt.left ⟶ cS.pt)))
      (yoneda.map (chartCone B S hS Dsite i a₀ cS).pt.hom)
      (yoneda.map (cS.π.app i)) (q₀ ≫ Y.hom) := by
    rw [← ha₀]
    exact (IsPullback.of_hasPullback (cS.π.app i) a₀).map yoneda
  let k : yoneda.obj (chartCone B S hS Dsite i a₀ cS).pt.left ⟶
      pullback Y.hom (yoneda.map (cS.π.app i)) :=
    pullback.lift (yoneda.map (chartCone B S hS Dsite i a₀ cS).pt.hom ≫ q₀)
      (yoneda.map ((pullback.fst (cS.π.app i) a₀ :
        (chartCone B S hS Dsite i a₀ cS).pt.left ⟶ cS.pt)))
      ((Category.assoc _ _ _).trans hsq.w.symm)
  have hkfst : k ≫ pullback.fst Y.hom (yoneda.map (cS.π.app i)) =
      yoneda.map (chartCone B S hS Dsite i a₀ cS).pt.hom ≫ q₀ := pullback.lift_fst _ _ _
  have hksnd : k ≫ pullback.snd Y.hom (yoneda.map (cS.π.app i)) =
      yoneda.map ((pullback.fst (cS.π.app i) a₀ :
        (chartCone B S hS Dsite i a₀ cS).pt.left ⟶ cS.pt)) := pullback.lift_snd _ _ _
  obtain ⟨j, g, hg, hgf⟩ := exists_hom_on_chart B S hS hAffine hcS i hU₀ a₀ hZalg a ha
    (k ≫ f) (by rw [Category.assoc, hf, reassoc_of% hkfst, ha₀])
  let C := (chartDiagram B S hS Dsite i a₀).obj j
  let Cproj : C.left ⟶ Dsite.obj j.left := pullback.fst (Dsite.map j.hom) a₀
  have hC : IsPullback (yoneda.map Cproj) (yoneda.map C.hom)
      (yoneda.map (Dsite.map j.hom)) (q₀ ≫ Y.hom) := by
    rw [← ha₀]
    exact (IsPullback.of_hasPullback (Dsite.map j.hom) a₀).map yoneda
  let U : AlgebraicGeometry.BigAffineFppf B S hS :=
    ⟨C.left, isAffine_chartDiagram_obj B S hS hAffine i hU₀ a₀ j⟩
  let p : yoneda.obj U.obj ⟶ pullback Y.hom (yoneda.map (Dsite.map j.hom)) :=
    pullback.lift (yoneda.map C.hom ≫ q₀) (yoneda.map Cproj)
      (by simpa only [Category.assoc] using hC.w.symm)
  have hpfst : p ≫ pullback.fst Y.hom (yoneda.map (Dsite.map j.hom)) =
      yoneda.map C.hom ≫ q₀ := pullback.lift_fst _ _ _
  have hpsnd : p ≫ pullback.snd Y.hom (yoneda.map (Dsite.map j.hom)) =
      yoneda.map Cproj := pullback.lift_snd _ _ _
  have hp := isPullback_lift_of_isPullback_comp Y.hom (yoneda.map (Dsite.map j.hom)) q₀ hC
  obtain ⟨hps, hpe⟩ := surjective_etale_presheaf_of_isPullback B S hS hp hs
    (represented_etale_of_isEtale B S hS q₀ he)
  refine ⟨j, U, p, g, hps, hpe, ?_, ?_⟩
  · rw [hg, ha₀, reassoc_of% hpsnd]
    exact hC.w.symm
  · refine fst_comp_eq_lift_comp_iteratedBaseChangeIso Y
      (yoneda.map (Dsite.map j.hom)) (yoneda.map (cS.π.app i))
      (yoneda.map (cS.π.app j.left)) (yoneda_map_cone_w B S hS j.hom) q₀ hC hsq
      (yoneda.map ((((chartCone B S hS Dsite i a₀ cS).π.app j).left :
        (chartCone B S hS Dsite i a₀ cS).pt.left ⟶ C.left))) ?_ ?_
      p hpfst hpsnd k hkfst hksnd
      (pullback.fst (p ≫ pullback.snd Y.hom (yoneda.map (Dsite.map j.hom)))
        (yoneda.map (cS.π.app j.left)))
      (pullback.snd (p ≫ pullback.snd Y.hom (yoneda.map (Dsite.map j.hom)))
        (yoneda.map (cS.π.app j.left)))
      pullback.condition _
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) g f hgf
    · have h : ((chartCone B S hS Dsite i a₀ cS).π.app j).left ≫ Cproj =
          pullback.fst (cS.π.app i) a₀ ≫ cS.π.app j.left :=
        pullback_map_left_comp_fst a₀ _
      exact ((yoneda.map_comp _ _).symm.trans (congrArg yoneda.map h)).trans
        (yoneda.map_comp _ _)
    · have h : ((chartCone B S hS Dsite i a₀ cS).π.app j).left ≫ C.hom =
          (chartCone B S hS Dsite i a₀ cS).pt.hom :=
        Over.w ((chartCone B S hS Dsite i a₀ cS).π.app j)
      exact (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map h)

/-- The chart `Kl` of a later stage, mapped into the base change of the stage by `pK`, is
what the chart of the limit becomes after the two comparison isomorphisms of iterated base
changes. -/
theorem lift_comp_iteratedBaseChangeIso_hom_comp_inv
    {C : Type*} [Category* C] [HasPullbacks C]
    {Xi Xj Xk L Up Kl : C} (Y : Over Xi)
    (Dj : Xj ⟶ Xi) (De : Xk ⟶ Xj) (Dd : Xk ⟶ Xi) (hDd : De ≫ Dj = Dd)
    (πi : L ⟶ Xi) (πj : L ⟶ Xj) (πk : L ⟶ Xk)
    (hπj : πj ≫ Dj = πi) (hπk : πk ≫ De = πj)
    (p : Up ⟶ pullback Y.hom Dj) (Kproj : Kl ⟶ Xk) (Kchart : Kl ⟶ Up)
    (q : pullback (p ≫ ((Over.pullback Dj).obj Y).hom) πj ⟶
      pullback (((Over.pullback Dj).obj Y).hom) πj)
    (hq₁ : q ≫ pullback.fst (((Over.pullback Dj).obj Y).hom) πj =
      pullback.fst (p ≫ ((Over.pullback Dj).obj Y).hom) πj ≫ p)
    (hq₂ : q ≫ pullback.snd (((Over.pullback Dj).obj Y).hom) πj =
      pullback.snd (p ≫ ((Over.pullback Dj).obj Y).hom) πj)
    (m : pullback Y.hom πi ⟶ pullback Y.hom Dd)
    (hm₁ : m ≫ pullback.fst Y.hom Dd = pullback.fst Y.hom πi)
    (hm₂ : m ≫ pullback.snd Y.hom Dd = pullback.snd Y.hom πi ≫ πk)
    (l : pullback (p ≫ ((Over.pullback Dj).obj Y).hom) πj ⟶ Kl)
    (hl₁ : l ≫ Kproj = pullback.snd (p ≫ ((Over.pullback Dj).obj Y).hom) πj ≫ πk)
    (hl₂ : l ≫ Kchart = pullback.fst (p ≫ ((Over.pullback Dj).obj Y).hom) πj)
    (pK : Kl ⟶ pullback (((Over.pullback Dj).obj Y).hom) De)
    (hpK₁ : pK ≫ pullback.fst (((Over.pullback Dj).obj Y).hom) De = Kchart ≫ p)
    (hpK₂ : pK ≫ pullback.snd (((Over.pullback Dj).obj Y).hom) De = Kproj) :
    q ≫ (iteratedBaseChangeIso Dj πj πi hπj Y).hom.left ≫ m ≫
        (iteratedBaseChangeIso Dj De Dd hDd Y).inv.left =
      l ≫ pK := by
  have hA₁ : (iteratedBaseChangeIso Dj πj πi hπj Y).hom.left ≫ pullback.fst Y.hom πi =
      pullback.fst (((Over.pullback Dj).obj Y).hom) πj ≫ pullback.fst Y.hom Dj :=
    iteratedBaseChangeIso_hom_fst _ _ _ _ _
  have hA₂ : (iteratedBaseChangeIso Dj πj πi hπj Y).hom.left ≫ pullback.snd Y.hom πi =
      pullback.snd (((Over.pullback Dj).obj Y).hom) πj :=
    Over.w (iteratedBaseChangeIso Dj πj πi hπj Y).hom
  have hη₀ := iteratedBaseChangeIso_inv_fst Dj De Dd hDd Y
  have hη₁ : (iteratedBaseChangeIso Dj De Dd hDd Y).inv.left ≫
      pullback.fst (((Over.pullback Dj).obj Y).hom) De ≫ pullback.fst Y.hom Dj =
      pullback.fst Y.hom Dd :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ pullback.fst Y.hom Dj) hη₀).trans (pullback.lift_fst _ _ _))
  have hη₂ : (iteratedBaseChangeIso Dj De Dd hDd Y).inv.left ≫
      pullback.fst (((Over.pullback Dj).obj Y).hom) De ≫ pullback.snd Y.hom Dj =
      pullback.snd Y.hom Dd ≫ De :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ pullback.snd Y.hom Dj) hη₀).trans
        (pullback.lift_snd _ _ _))
  have hη₃ : (iteratedBaseChangeIso Dj De Dd hDd Y).inv.left ≫
      pullback.snd (((Over.pullback Dj).obj Y).hom) De = pullback.snd Y.hom Dd :=
    Over.w (iteratedBaseChangeIso Dj De Dd hDd Y).inv
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hη₁, hm₁, hA₁, ← Category.assoc q, hq₁, ← Category.assoc pK, hpK₁]
      simp only [Category.assoc]
      rw [← Category.assoc l Kchart, hl₂]
    · simp only [Category.assoc]
      rw [hη₂, ← Category.assoc m, hm₂]
      simp only [Category.assoc]
      rw [hπk, ← Category.assoc (iteratedBaseChangeIso Dj πj πi hπj Y).hom.left, hA₂,
        ← Category.assoc q, hq₂, ← Category.assoc pK, hpK₁]
      simp only [Category.assoc]
      rw [← Category.assoc l Kchart, hl₂]
      exact pullback.condition.symm
  · simp only [Category.assoc]
    rw [hη₃, hm₂, ← Category.assoc (iteratedBaseChangeIso Dj πj πi hπj Y).hom.left, hA₂,
      ← Category.assoc q, hq₂, hpK₂, hl₁]

/-- There is a later stage at which the kernel pair of the atlas `p` is equalized by the
chart-level factorization `g`. -/
theorem exists_stage_equalizing_kernelPair
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (i : I) (j : Over i) (Yᵢ Zᵢ : Over (yoneda.obj (Dsite.obj i)))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS
      (AlgebraicGeometry.BigFppfSite.contains_terminal B) Yᵢ.left)
    (hQsj : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS
      (AlgebraicGeometry.BigFppfSite.contains_terminal B) (yoneda.obj (Dsite.obj j.left)))
    (hZfp : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS Zᵢ.hom)
    (U : AlgebraicGeometry.BigAffineFppf B S hS)
    (p : yoneda.obj U.obj ⟶ pullback Yᵢ.hom (yoneda.map (Dsite.map j.hom)))
    (g : yoneda.obj U.obj ⟶ Zᵢ.left)
    (f₀ : pullback Yᵢ.hom (yoneda.map (cS.π.app i)) ⟶ Zᵢ.left)
    (hg : g ≫ Zᵢ.hom = p ≫ pullback.snd Yᵢ.hom (yoneda.map (Dsite.map j.hom)) ≫
      yoneda.map (Dsite.map j.hom))
    (hgf : pullback.fst (p ≫ pullback.snd Yᵢ.hom (yoneda.map (Dsite.map j.hom)))
          (yoneda.map (cS.π.app j.left)) ≫ g =
        pullback.lift
          (pullback.fst (p ≫ pullback.snd Yᵢ.hom (yoneda.map (Dsite.map j.hom)))
            (yoneda.map (cS.π.app j.left)) ≫ p)
          (pullback.snd (p ≫ pullback.snd Yᵢ.hom (yoneda.map (Dsite.map j.hom)))
            (yoneda.map (cS.π.app j.left)))
          (by simpa only [Over.pullback_obj_hom, Category.assoc] using
            (pullback.condition
              (f := p ≫ pullback.snd Yᵢ.hom (yoneda.map (Dsite.map j.hom)))
              (g := yoneda.map (cS.π.app j.left)))) ≫
        (iteratedBaseChangeIso (yoneda.map (Dsite.map j.hom))
          (yoneda.map (cS.π.app j.left)) (yoneda.map (cS.π.app i))
          (yoneda_map_cone_w B S hS j.hom) Yᵢ).hom.left ≫ f₀)
    :
    ∃ (k : I) (e : k ⟶ j.left),
      pullback.fst (pullback.fst p p ≫ p ≫
            pullback.snd Yᵢ.hom (yoneda.map (Dsite.map j.hom)))
          (yoneda.map (Dsite.map e)) ≫ pullback.fst p p ≫ g =
        pullback.fst (pullback.fst p p ≫ p ≫
            pullback.snd Yᵢ.hom (yoneda.map (Dsite.map j.hom)))
          (yoneda.map (Dsite.map e)) ≫ pullback.snd p p ≫ g := by
  classical
  have hDi := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj i)
  let Yj := (Over.pullback (yoneda.map (Dsite.map j.hom))).obj Yᵢ
  have hYj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yᵢ.hom
    (yoneda.map (Dsite.map j.hom)) hY
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj j.left)) hDi
  have hYjqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_pullback
    B S hS (AlgebraicGeometry.BigFppfSite.contains_terminal B) Yᵢ.hom
    (yoneda.map (Dsite.map j.hom)) hY
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj j.left)) hDi hYqs
    hQsj
  have hU := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U.obj
  have hUqc := AlgebraicGeometry.Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS U.obj
    U.property
  have hR := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS p p hU hU hYj
  have hRqc := AlgebraicGeometry.Space.isQuasiCompactSpace_pullback
    B S hS (AlgebraicGeometry.BigFppfSite.contains_terminal B) p p hU hYj hUqc hUqc
    hYjqs
  have hlim := equalizes_kernelPair_after_baseChange p Yj.hom
    (yoneda.map (cS.π.app j.left))
    ((iteratedBaseChangeIso (yoneda.map (Dsite.map j.hom))
      (yoneda.map (cS.π.app j.left)) (yoneda.map (cS.π.app i))
      (yoneda_map_cone_w B S hS j.hom) Yᵢ).hom.left ≫ f₀) g hgf
  exact eventually_eq_on_quasiCompact_source_of_isLimit B S hS hAffine hcS
    j.left hR hZ' hDi hRqc
    (pullback.fst p p ≫ p ≫ Yj.hom) Zᵢ.hom (yoneda.map (Dsite.map j.hom)) hZfp
    (pullback.fst p p ≫ g) (pullback.snd p p ≫ g)
    (by simpa only [Yj, Over.pullback_obj_hom, Category.assoc] using
      congrArg (fun t => pullback.fst p p ≫ t) hg)
    (by
      simpa only [Yj, Over.pullback_obj_hom, Category.assoc, pullback.condition_assoc] using
        congrArg (fun t => pullback.snd p p ≫ t) hg) hlim

/-- Base changing the atlas `p` of a stage along the projection from the limit again gives a
surjective étale atlas, so two morphisms out of the base change of the stage to the limit
that agree on it are equal. -/
theorem hom_ext_of_baseChange_atlas
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (i : I) (j : Over i) (Yᵢ : Over (yoneda.obj (Dsite.obj i)))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (U : AlgebraicGeometry.BigAffineFppf B S hS)
    (p : yoneda.obj U.obj ⟶ pullback Yᵢ.hom (yoneda.map (Dsite.map j.hom)))
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZsh : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) Z)
    (q : pullback (p ≫ ((Over.pullback (yoneda.map (Dsite.map j.hom))).obj Yᵢ).hom)
        (yoneda.map (cS.π.app j.left)) ⟶
      pullback ((Over.pullback (yoneda.map (Dsite.map j.hom))).obj Yᵢ).hom
        (yoneda.map (cS.π.app j.left)))
    (hq : IsPullback
      (pullback.fst (p ≫ ((Over.pullback (yoneda.map (Dsite.map j.hom))).obj Yᵢ).hom)
        (yoneda.map (cS.π.app j.left))) q p
      (pullback.fst ((Over.pullback (yoneda.map (Dsite.map j.hom))).obj Yᵢ).hom
        (yoneda.map (cS.π.app j.left))))
    (x y : pullback ((Over.pullback (yoneda.map (Dsite.map j.hom))).obj Yᵢ).hom
      (yoneda.map (cS.π.app j.left)) ⟶ Z)
    (hxy : q ≫ x = q ≫ y) : x = y := by
  classical
  have hDi := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj i)
  let Yj := (Over.pullback (yoneda.map (Dsite.map j.hom))).obj Yᵢ
  have hYj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yᵢ.hom
    (yoneda.map (Dsite.map j.hom)) hY
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj j.left)) hDi
  obtain ⟨hqs, hqe⟩ := surjective_etale_presheaf_of_isPullback B S hS hq hs he
  obtain ⟨V, v, w, hV⟩ :=
    isAffineHom_yoneda_map_π B S hS hAffine hcS j.left U (p ≫ Yj.hom)
  exact hom_ext_of_surjective_etale_atlas B S hS
    (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yj.hom
      (yoneda.map (cS.π.app j.left)) hYj
      (isAlgebraicSpace_yoneda_cone_pt B S hS cS)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj j.left)))
    hZsh (hV.flip.isoPullback.hom ≫ q)
    (MorphismProperty.RespectsIso.precomp _ hV.flip.isoPullback.hom q
      hqs)
    (MorphismProperty.RespectsIso.precomp _ hV.flip.isoPullback.hom q hqe)
    x y (by
      simpa only [Category.assoc] using congrArg (fun t => hV.flip.isoPullback.hom ≫ t) hxy)

/-- The limit chart of the stage sees the descended morphism `gK` as the given `f₀`. -/
theorem comp_eq_of_stage_hom
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (i : I) (j : Over i) (k : I) (e : k ⟶ j.left)
    (Yᵢ Zᵢ : Over (yoneda.obj (Dsite.obj i)))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (U : AlgebraicGeometry.BigAffineFppf B S hS)
    (p : yoneda.obj U.obj ⟶ pullback Yᵢ.hom (yoneda.map (Dsite.map j.hom)))
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (g : yoneda.obj U.obj ⟶ Zᵢ.left)
    (f₀ : pullback Yᵢ.hom (yoneda.map (cS.π.app i)) ⟶ Zᵢ.left)
    (hgf : pullback.fst
          (p ≫ ((Over.pullback (yoneda.map (Dsite.map j.hom))).obj Yᵢ).hom)
          (yoneda.map (cS.π.app j.left)) ≫ g =
        pullback.lift
          (pullback.fst
            (p ≫ ((Over.pullback (yoneda.map (Dsite.map j.hom))).obj Yᵢ).hom)
            (yoneda.map (cS.π.app j.left)) ≫ p)
          (pullback.snd
            (p ≫ ((Over.pullback (yoneda.map (Dsite.map j.hom))).obj Yᵢ).hom)
            (yoneda.map (cS.π.app j.left)))
          (by simp only [Category.assoc, pullback.condition]) ≫
        (iteratedBaseChangeIso (yoneda.map (Dsite.map j.hom))
          (yoneda.map (cS.π.app j.left)) (yoneda.map (cS.π.app i))
          (yoneda_map_cone_w B S hS j.hom) Yᵢ).hom.left ≫ f₀)
    {Kl : AlgebraicGeometry.BigFppfOver B S hS} (Kproj : Kl ⟶ Dsite.obj k)
    (Kchart : Kl ⟶ U.obj)
    (hK : IsPullback (yoneda.map Kproj) (yoneda.map Kchart) (yoneda.map (Dsite.map e))
      (p ≫ ((Over.pullback (yoneda.map (Dsite.map j.hom))).obj Yᵢ).hom))
    (gK : ((Over.pullback (yoneda.map (Dsite.map e))).obj
      ((Over.pullback (yoneda.map (Dsite.map j.hom))).obj Yᵢ)).left ⟶ Zᵢ.left)
    (hgK : pullback.lift (yoneda.map Kchart ≫ p) (yoneda.map Kproj)
        ((Category.assoc _ _ _).trans hK.w.symm) ≫ gK = yoneda.map Kchart ≫ g) :
    pullback.lift (pullback.fst Yᵢ.hom (yoneda.map (cS.π.app i)))
        (pullback.snd Yᵢ.hom (yoneda.map (cS.π.app i)) ≫ yoneda.map (cS.π.app k))
        (by
          rw [Category.assoc, yoneda_map_cone_w B S hS (e ≫ j.hom)]
          exact pullback.condition) ≫
      (iteratedBaseChangeIso (yoneda.map (Dsite.map j.hom)) (yoneda.map (Dsite.map e))
        (yoneda.map (Dsite.map (e ≫ j.hom))) (yoneda_map_Dsite_comp B S hS e j.hom)
        Yᵢ).inv.left ≫ gK = f₀ := by
  classical
  have hDi := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj i)
  let Yj := (Over.pullback (yoneda.map (Dsite.map j.hom))).obj Yᵢ
  have hYj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yᵢ.hom
    (yoneda.map (Dsite.map j.hom)) hY
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj j.left)) hDi
  let A := iteratedBaseChangeIso (yoneda.map (Dsite.map j.hom))
    (yoneda.map (cS.π.app j.left)) (yoneda.map (cS.π.app i))
    (yoneda_map_cone_w B S hS j.hom) Yᵢ
  let d := e ≫ j.hom
  let η := iteratedBaseChangeIso (yoneda.map (Dsite.map j.hom)) (yoneda.map (Dsite.map e))
    (yoneda.map (Dsite.map d)) (yoneda_map_Dsite_comp B S hS e j.hom) Yᵢ
  let raw : pullback Yᵢ.hom (yoneda.map (Dsite.map d)) ⟶ Zᵢ.left := η.inv.left ≫ gK
  let m : pullback Yᵢ.hom (yoneda.map (cS.π.app i)) ⟶
      pullback Yᵢ.hom (yoneda.map (Dsite.map d)) :=
    pullback.lift (pullback.fst Yᵢ.hom (yoneda.map (cS.π.app i)))
      (pullback.snd Yᵢ.hom (yoneda.map (cS.π.app i)) ≫ yoneda.map (cS.π.app k))
      (by rw [Category.assoc, yoneda_map_cone_w B S hS d]; exact pullback.condition)
  let pK : yoneda.obj Kl ⟶ ((Over.pullback (yoneda.map (Dsite.map e))).obj Yj).left :=
    pullback.lift (yoneda.map Kchart ≫ p) (yoneda.map Kproj)
      ((Category.assoc _ _ _).trans hK.w.symm)
  have hpKfst : pK ≫ pullback.fst Yj.hom (yoneda.map (Dsite.map e)) =
      yoneda.map Kchart ≫ p := pullback.lift_fst _ _ _
  have hpKsnd : pK ≫ pullback.snd Yj.hom (yoneda.map (Dsite.map e)) =
      yoneda.map Kproj := pullback.lift_snd _ _ _
  have hpKg : pK ≫ gK = yoneda.map Kchart ≫ g := hgK
  change m ≫ raw = f₀
  let q : pullback (p ≫ Yj.hom) (yoneda.map (cS.π.app j.left)) ⟶
      pullback Yj.hom (yoneda.map (cS.π.app j.left)) :=
    pullback.lift
      (pullback.fst (p ≫ Yj.hom) (yoneda.map (cS.π.app j.left)) ≫ p)
      (pullback.snd (p ≫ Yj.hom) (yoneda.map (cS.π.app j.left)))
      (by simp only [Category.assoc, pullback.condition])
  have hq : IsPullback (pullback.fst (p ≫ Yj.hom) (yoneda.map (cS.π.app j.left))) q p
      (pullback.fst Yj.hom (yoneda.map (cS.π.app j.left))) := by
    apply IsPullback.of_bot _ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback Yj.hom (yoneda.map (cS.π.app j.left)))
    simpa only [q, pullback.lift_snd] using
      IsPullback.of_hasPullback (p ≫ Yj.hom) (yoneda.map (cS.π.app j.left))
  let l : pullback (p ≫ Yj.hom) (yoneda.map (cS.π.app j.left)) ⟶ yoneda.obj Kl :=
    hK.lift
      (pullback.snd (p ≫ Yj.hom) (yoneda.map (cS.π.app j.left)) ≫
        yoneda.map (cS.π.app k))
      (pullback.fst (p ≫ Yj.hom) (yoneda.map (cS.π.app j.left)))
      (by rw [Category.assoc, yoneda_map_cone_w B S hS e]; exact pullback.condition.symm)
  have hqfst : q ≫ pullback.fst Yj.hom (yoneda.map (cS.π.app j.left)) =
      pullback.fst (p ≫ Yj.hom) (yoneda.map (cS.π.app j.left)) ≫ p :=
    pullback.lift_fst _ _ _
  have hqsnd : q ≫ pullback.snd Yj.hom (yoneda.map (cS.π.app j.left)) =
      pullback.snd (p ≫ Yj.hom) (yoneda.map (cS.π.app j.left)) :=
    pullback.lift_snd _ _ _
  have hmfst : m ≫ pullback.fst Yᵢ.hom (yoneda.map (Dsite.map d)) =
      pullback.fst Yᵢ.hom (yoneda.map (cS.π.app i)) := pullback.lift_fst _ _ _
  have hmsnd : m ≫ pullback.snd Yᵢ.hom (yoneda.map (Dsite.map d)) =
      pullback.snd Yᵢ.hom (yoneda.map (cS.π.app i)) ≫ yoneda.map (cS.π.app k) :=
    pullback.lift_snd _ _ _
  have hlfst : l ≫ yoneda.map Kproj =
      pullback.snd (p ≫ Yj.hom) (yoneda.map (cS.π.app j.left)) ≫
        yoneda.map (cS.π.app k) := hK.lift_fst _ _ _
  have hlsnd : l ≫ yoneda.map Kchart =
      pullback.fst (p ≫ Yj.hom) (yoneda.map (cS.π.app j.left)) := hK.lift_snd _ _ _
  have hl : q ≫ A.hom.left ≫ m ≫ η.inv.left = l ≫ pK :=
    lift_comp_iteratedBaseChangeIso_hom_comp_inv Yᵢ (yoneda.map (Dsite.map j.hom))
      (yoneda.map (Dsite.map e)) (yoneda.map (Dsite.map d))
      (yoneda_map_Dsite_comp B S hS e j.hom) (yoneda.map (cS.π.app i))
      (yoneda.map (cS.π.app j.left)) (yoneda.map (cS.π.app k))
      (yoneda_map_cone_w B S hS j.hom) (yoneda_map_cone_w B S hS e)
      p (yoneda.map Kproj) (yoneda.map Kchart)
      q hqfst hqsnd m hmfst hmsnd l hlfst hlsnd pK hpKfst hpKsnd
  have hEq : q ≫ A.hom.left ≫ (m ≫ raw) = q ≫ A.hom.left ≫ f₀ := by
    change q ≫ A.hom.left ≫ m ≫ η.inv.left ≫ gK = _
    have hh := congrArg (fun t => t ≫ gK) hl
    simp only [Category.assoc, hpKg] at hh
    rw [hh, reassoc_of% hlsnd]
    exact hgf
  have hEq' : A.hom.left ≫ (m ≫ raw) = A.hom.left ≫ f₀ :=
    hom_ext_of_baseChange_atlas B S hS hAffine hcS i j Yᵢ hY U p hs he hZ'.isSheaf q hq
      _ _ hEq
  let : IsIso A.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (yoneda.obj cS.pt)).map A.hom))
  exact (cancel_epi A.hom.left).mp hEq'

/-- Given an atlas factorization as produced by `exists_stage_atlas_factorization_of_isLimit`,
there is a morphism defined on the whole base change of `Yᵢ` to a later stage that agrees with
`f₀` over the limit. -/
theorem exists_stage_hom_of_atlas_factorization
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (i : I) (j : Over i) (Yᵢ Zᵢ : Over (yoneda.obj (Dsite.obj i)))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS
      (AlgebraicGeometry.BigFppfSite.contains_terminal B) Yᵢ.left)
    (hQsj : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS
      (AlgebraicGeometry.BigFppfSite.contains_terminal B) (yoneda.obj (Dsite.obj j.left)))
    (hZfp : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS Zᵢ.hom)
    (U : AlgebraicGeometry.BigAffineFppf B S hS)
    (p : yoneda.obj U.obj ⟶ pullback Yᵢ.hom (yoneda.map (Dsite.map j.hom)))
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (g : yoneda.obj U.obj ⟶ Zᵢ.left)
    (f₀ : pullback Yᵢ.hom (yoneda.map (cS.π.app i)) ⟶ Zᵢ.left)
    (hg : g ≫ Zᵢ.hom = p ≫ pullback.snd Yᵢ.hom (yoneda.map (Dsite.map j.hom)) ≫
      yoneda.map (Dsite.map j.hom))
    (hgf : pullback.fst (p ≫ pullback.snd Yᵢ.hom (yoneda.map (Dsite.map j.hom)))
          (yoneda.map (cS.π.app j.left)) ≫ g =
        pullback.lift
          (pullback.fst (p ≫ pullback.snd Yᵢ.hom (yoneda.map (Dsite.map j.hom)))
            (yoneda.map (cS.π.app j.left)) ≫ p)
          (pullback.snd (p ≫ pullback.snd Yᵢ.hom (yoneda.map (Dsite.map j.hom)))
            (yoneda.map (cS.π.app j.left)))
          (by simpa only [Over.pullback_obj_hom, Category.assoc] using
            (pullback.condition
              (f := p ≫ pullback.snd Yᵢ.hom (yoneda.map (Dsite.map j.hom)))
              (g := yoneda.map (cS.π.app j.left)))) ≫
        (iteratedBaseChangeIso (yoneda.map (Dsite.map j.hom))
          (yoneda.map (cS.π.app j.left)) (yoneda.map (cS.π.app i))
          (yoneda_map_cone_w B S hS j.hom) Yᵢ).hom.left ≫ f₀) :
    ∃ (k : I) (e : k ⟶ j.left)
      (raw : pullback Yᵢ.hom (yoneda.map (Dsite.map (e ≫ j.hom))) ⟶ Zᵢ.left),
      raw ≫ Zᵢ.hom = pullback.snd Yᵢ.hom (yoneda.map (Dsite.map (e ≫ j.hom))) ≫
          yoneda.map (Dsite.map (e ≫ j.hom)) ∧
        pullback.lift (pullback.fst Yᵢ.hom (yoneda.map (cS.π.app i)))
            (pullback.snd Yᵢ.hom (yoneda.map (cS.π.app i)) ≫ yoneda.map (cS.π.app k))
            (by
              rw [Category.assoc, yoneda_map_cone_w B S hS (e ≫ j.hom)]
              exact pullback.condition) ≫
          raw = f₀ := by
  classical
  have hDi := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj i)
  let Yj := (Over.pullback (yoneda.map (Dsite.map j.hom))).obj Yᵢ
  have hYj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yᵢ.hom
    (yoneda.map (Dsite.map j.hom)) hY
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj j.left)) hDi
  let A := iteratedBaseChangeIso (yoneda.map (Dsite.map j.hom))
    (yoneda.map (cS.π.app j.left)) (yoneda.map (cS.π.app i))
    (yoneda_map_cone_w B S hS j.hom) Yᵢ
  obtain ⟨k, e, hkg⟩ := exists_stage_equalizing_kernelPair B S hS hAffine hcS i j Yᵢ Zᵢ
    hY hZ' hYqs hQsj hZfp U p g f₀ hg hgf
  let a₁ : U.obj ⟶ Dsite.obj j.left := yoneda.preimage (p ≫ Yj.hom)
  have ha₁ : yoneda.map a₁ = p ≫ Yj.hom := Functor.map_preimage _ _
  let K := (chartDiagram B S hS Dsite j.left a₁).obj (Over.mk e)
  let Kproj : K.left ⟶ Dsite.obj k := pullback.fst (Dsite.map e) a₁
  have hK : IsPullback (yoneda.map Kproj) (yoneda.map K.hom)
      (yoneda.map (Dsite.map e)) (p ≫ Yj.hom) := by
    rw [← ha₁]
    exact (IsPullback.of_hasPullback (Dsite.map e) a₁).map yoneda
  let Yk := (Over.pullback (yoneda.map (Dsite.map e))).obj Yj
  let pK : yoneda.obj K.left ⟶ Yk.left :=
    pullback.lift (yoneda.map K.hom ≫ p) (yoneda.map Kproj)
      ((Category.assoc _ _ _).trans hK.w.symm)
  have hpKfst : pK ≫ pullback.fst Yj.hom (yoneda.map (Dsite.map e)) =
      yoneda.map K.hom ≫ p := pullback.lift_fst _ _ _
  have hpKsnd : pK ≫ pullback.snd Yj.hom (yoneda.map (Dsite.map e)) =
      yoneda.map Kproj := pullback.lift_snd _ _ _
  have hpK := isPullback_lift_of_isPullback_comp Yj.hom (yoneda.map (Dsite.map e)) p hK
  obtain ⟨hKs, hKe⟩ := surjective_etale_presheaf_of_isPullback B S hS hpK hs he
  have hYk := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yj.hom
    (yoneda.map (Dsite.map e)) hYj
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj k))
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj j.left))
  obtain ⟨gK, hgK⟩ := exists_hom_of_equalizes_atlas B S hS hYk hZ'.isSheaf pK hKs hKe
    (yoneda.map K.hom ≫ g)
    (equalizes_kernelPair_of_baseChange_eq p Yj.hom (yoneda.map (Dsite.map e))
      (pullback.fst Yj.hom (yoneda.map (Dsite.map e)))
      (pullback.snd Yj.hom (yoneda.map (Dsite.map e))) pullback.condition
      (yoneda.map K.hom) pK hpKfst.symm g hkg)
  have hgKa : gK ≫ Zᵢ.hom =
      Yk.hom ≫ yoneda.map (Dsite.map e) ≫ yoneda.map (Dsite.map j.hom) := by
    apply hom_ext_of_surjective_etale_atlas B S hS hYk hDi.isSheaf pK hKs hKe
    calc pK ≫ gK ≫ Zᵢ.hom = (pK ≫ gK) ≫ Zᵢ.hom := (Category.assoc _ _ _).symm
      _ = (yoneda.map K.hom ≫ g) ≫ Zᵢ.hom := by rw [hgK]
      _ = yoneda.map K.hom ≫ g ≫ Zᵢ.hom := Category.assoc _ _ _
      _ = yoneda.map K.hom ≫ p ≫ pullback.snd Yᵢ.hom (yoneda.map (Dsite.map j.hom)) ≫
            yoneda.map (Dsite.map j.hom) := by rw [hg]
      _ = (yoneda.map K.hom ≫ p ≫ Yj.hom) ≫ yoneda.map (Dsite.map j.hom) := by
          simp only [Yj, Over.pullback_obj_hom, Category.assoc]
      _ = (yoneda.map Kproj ≫ yoneda.map (Dsite.map e)) ≫
            yoneda.map (Dsite.map j.hom) := by rw [hK.w]
      _ = ((pK ≫ pullback.snd Yj.hom (yoneda.map (Dsite.map e))) ≫
            yoneda.map (Dsite.map e)) ≫ yoneda.map (Dsite.map j.hom) := by rw [hpKsnd]
      _ = pK ≫ Yk.hom ≫ yoneda.map (Dsite.map e) ≫ yoneda.map (Dsite.map j.hom) := by
          simp only [Yk, Over.pullback_obj_hom, Category.assoc]
  let d := e ≫ j.hom
  let η := iteratedBaseChangeIso (yoneda.map (Dsite.map j.hom)) (yoneda.map (Dsite.map e))
    (yoneda.map (Dsite.map d)) (yoneda_map_Dsite_comp B S hS e j.hom) Yᵢ
  let raw : pullback Yᵢ.hom (yoneda.map (Dsite.map d)) ⟶ Zᵢ.left := η.inv.left ≫ gK
  let m : pullback Yᵢ.hom (yoneda.map (cS.π.app i)) ⟶
      pullback Yᵢ.hom (yoneda.map (Dsite.map d)) :=
    pullback.lift (pullback.fst Yᵢ.hom (yoneda.map (cS.π.app i)))
      (pullback.snd Yᵢ.hom (yoneda.map (cS.π.app i)) ≫ yoneda.map (cS.π.app k))
      (by rw [Category.assoc, yoneda_map_cone_w B S hS d]; exact pullback.condition)
  refine ⟨k, e, raw, ?_, ?_⟩
  · have hw : η.inv.left ≫ Yk.hom =
        pullback.snd Yᵢ.hom (yoneda.map (Dsite.map d)) := Over.w η.inv
    calc raw ≫ Zᵢ.hom = η.inv.left ≫ gK ≫ Zᵢ.hom := Category.assoc _ _ _
      _ = η.inv.left ≫ Yk.hom ≫ yoneda.map (Dsite.map e) ≫
            yoneda.map (Dsite.map j.hom) := by rw [hgKa]
      _ = η.inv.left ≫ Yk.hom ≫ yoneda.map (Dsite.map d) := by
          rw [yoneda_map_Dsite_comp B S hS e j.hom]
      _ = (η.inv.left ≫ Yk.hom) ≫ yoneda.map (Dsite.map d) := (Category.assoc _ _ _).symm
      _ = pullback.snd Yᵢ.hom (yoneda.map (Dsite.map d)) ≫
            yoneda.map (Dsite.map d) := by rw [hw]
  · exact comp_eq_of_stage_hom B S hS hAffine hcS i j k e Yᵢ Zᵢ hY hZ' U p hs he g f₀ hgf
      Kproj K.hom hK gK hgK

/-- **Stacks 07SK, fullness, with no hypothesis on the size of the index category.**

A morphism between the base changes to the limit of two algebraic spaces of finite
presentation over a stage comes from a morphism at a later stage, compatibly with the
canonical comparison isomorphisms of the iterated base changes.

As for `AlgebraicGeometry.Space.eventually_eq_of_baseChange_eq_of_isLimit`, the system is
given as a diagram `Dsite` in the big fppf site together with a cone `cS` on it whose image
under the underlying-scheme functor is a limit cone; that the limit is an object of the site
is what replaces the hypothesis `#I < B.cutoff.ord.cof` of
`AlgebraicGeometry.Space.exists_morphism_after_baseChange`. -/
theorem exists_morphism_after_baseChange_of_isLimit
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (hQc : ∀ i, AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS
      (yoneda.obj (Dsite.obj i)))
    (hQs : ∀ i, AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS
      (AlgebraicGeometry.BigFppfSite.contains_terminal B) (yoneda.obj (Dsite.obj i)))
    (i : I) (Yᵢ Zᵢ : Over (yoneda.obj (Dsite.obj i)))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zᵢ.hom)
    (f : (Over.pullback (yoneda.map (cS.π.app i))).obj Yᵢ ⟶
      (Over.pullback (yoneda.map (cS.π.app i))).obj Zᵢ) :
    ∃ (j : I) (e : j ⟶ i)
      (g : (Over.pullback (yoneda.map (Dsite.map e))).obj Yᵢ ⟶
        (Over.pullback (yoneda.map (Dsite.map e))).obj Zᵢ)
      (α : (Over.pullback (yoneda.map (cS.π.app j))).obj
          ((Over.pullback (yoneda.map (Dsite.map e))).obj Yᵢ) ≅
        (Over.pullback (yoneda.map (cS.π.app i))).obj Yᵢ)
      (β : (Over.pullback (yoneda.map (cS.π.app j))).obj
          ((Over.pullback (yoneda.map (Dsite.map e))).obj Zᵢ) ≅
        (Over.pullback (yoneda.map (cS.π.app i))).obj Zᵢ),
      (α.hom.left ≫ pullback.fst Yᵢ.hom (yoneda.map (cS.π.app i)) =
        pullback.fst ((Over.pullback (yoneda.map (Dsite.map e))).obj Yᵢ).hom
            (yoneda.map (cS.π.app j)) ≫
          pullback.fst Yᵢ.hom (yoneda.map (Dsite.map e))) ∧
      (β.hom.left ≫ pullback.fst Zᵢ.hom (yoneda.map (cS.π.app i)) =
        pullback.fst ((Over.pullback (yoneda.map (Dsite.map e))).obj Zᵢ).hom
            (yoneda.map (cS.π.app j)) ≫
          pullback.fst Zᵢ.hom (yoneda.map (Dsite.map e))) ∧
      α.hom ≫ f = (Over.pullback (yoneda.map (cS.π.app j))).map g ≫ β.hom := by
  classical
  have hDi := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj i)
  have hYqc := AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation B S hS
    Yᵢ.hom hDi (hQc i) hYfp
  have hYqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated
    B S hS (AlgebraicGeometry.BigFppfSite.contains_terminal B) hY (hQs i) hYfp.2.2
  let f₀ := f.left ≫ pullback.fst Zᵢ.hom (yoneda.map (cS.π.app i))
  have hf₀ : f₀ ≫ Zᵢ.hom =
      pullback.fst Yᵢ.hom (yoneda.map (cS.π.app i)) ≫ Yᵢ.hom := by
    simp only [f₀, Category.assoc, pullback.condition]
    have hw : f.left ≫ pullback.snd Zᵢ.hom (yoneda.map (cS.π.app i)) =
        pullback.snd Yᵢ.hom (yoneda.map (cS.π.app i)) := f.w
    rw [← Category.assoc, hw]
  obtain ⟨j, U, p, g, hs, he, hg, hgf⟩ := exists_stage_atlas_factorization_of_isLimit
    B S hS hAffine hcS i Yᵢ hY hYqc hZ' Zᵢ.hom hZfp.1 f₀ hf₀
  obtain ⟨k, e, raw, hrawa, hraw⟩ := exists_stage_hom_of_atlas_factorization B S hS
    hAffine hcS i j Yᵢ Zᵢ hY hZ' hYqs (hQs j.left) hZfp.1 U p hs he g f₀ hg hgf
  let d := e ≫ j.hom
  let Yd := (Over.pullback (yoneda.map (Dsite.map d))).obj Yᵢ
  let Zd := (Over.pullback (yoneda.map (Dsite.map d))).obj Zᵢ
  let g' : Yd ⟶ Zd :=
    Over.homMk (pullback.lift raw (pullback.snd Yᵢ.hom (yoneda.map (Dsite.map d))) hrawa)
      (pullback.lift_snd _ _ _)
  let α := iteratedBaseChangeIso (yoneda.map (Dsite.map d)) (yoneda.map (cS.π.app k))
    (yoneda.map (cS.π.app i)) (yoneda_map_cone_w B S hS d) Yᵢ
  let β := iteratedBaseChangeIso (yoneda.map (Dsite.map d)) (yoneda.map (cS.π.app k))
    (yoneda.map (cS.π.app i)) (yoneda_map_cone_w B S hS d) Zᵢ
  let m : pullback Yᵢ.hom (yoneda.map (cS.π.app i)) ⟶
      pullback Yᵢ.hom (yoneda.map (Dsite.map d)) :=
    pullback.lift (pullback.fst Yᵢ.hom (yoneda.map (cS.π.app i)))
      (pullback.snd Yᵢ.hom (yoneda.map (cS.π.app i)) ≫ yoneda.map (cS.π.app k))
      (by rw [Category.assoc, yoneda_map_cone_w B S hS d]; exact pullback.condition)
  have hraw' : m ≫ raw = f₀ := hraw
  refine ⟨k, d, g', α, β, iteratedBaseChangeIso_hom_fst _ _ _ _ _,
    iteratedBaseChangeIso_hom_fst _ _ _ _ _, ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hmfst : m ≫ pullback.fst Yᵢ.hom (yoneda.map (Dsite.map d)) =
        pullback.fst Yᵢ.hom (yoneda.map (cS.π.app i)) := pullback.lift_fst _ _ _
    have hmsnd : m ≫ pullback.snd Yᵢ.hom (yoneda.map (Dsite.map d)) =
        pullback.snd Yᵢ.hom (yoneda.map (cS.π.app i)) ≫ yoneda.map (cS.π.app k) :=
      pullback.lift_snd _ _ _
    have hαfst : α.hom.left ≫ pullback.fst Yᵢ.hom (yoneda.map (cS.π.app i)) =
        pullback.fst Yd.hom (yoneda.map (cS.π.app k)) ≫
          pullback.fst Yᵢ.hom (yoneda.map (Dsite.map d)) :=
      iteratedBaseChangeIso_hom_fst _ _ _ _ _
    have hαsnd : α.hom.left ≫ pullback.snd Yᵢ.hom (yoneda.map (cS.π.app i)) =
        pullback.snd Yd.hom (yoneda.map (cS.π.app k)) := Over.w α.hom
    have hm : α.hom.left ≫ m = pullback.fst Yd.hom (yoneda.map (cS.π.app k)) := by
      apply pullback.hom_ext
      · rw [Category.assoc, hmfst, hαfst]
      · rw [Category.assoc, hmsnd, ← Category.assoc, hαsnd]
        exact pullback.condition.symm
    have hh : pullback.fst Yd.hom (yoneda.map (cS.π.app k)) ≫ raw =
        α.hom.left ≫ f₀ := by rw [← hm, Category.assoc, hraw']
    have hβfst : β.hom.left ≫ pullback.fst Zᵢ.hom (yoneda.map (cS.π.app i)) =
        pullback.fst Zd.hom (yoneda.map (cS.π.app k)) ≫
          pullback.fst Zᵢ.hom (yoneda.map (Dsite.map d)) :=
      iteratedBaseChangeIso_hom_fst _ _ _ _ _
    have hgl : g'.left ≫ pullback.fst Zᵢ.hom (yoneda.map (Dsite.map d)) = raw :=
      pullback.lift_fst _ _ _
    have hmap : ((Over.pullback (yoneda.map (cS.π.app k))).map g').left ≫
        pullback.fst Zd.hom (yoneda.map (cS.π.app k)) =
        pullback.fst Yd.hom (yoneda.map (cS.π.app k)) ≫ g'.left :=
      pullback_map_left_comp_fst (yoneda.map (cS.π.app k)) g'
    calc (α.hom ≫ f).left ≫ pullback.fst Zᵢ.hom (yoneda.map (cS.π.app i))
        = α.hom.left ≫ f.left ≫ pullback.fst Zᵢ.hom (yoneda.map (cS.π.app i)) := by
          simp only [Over.comp_left, Category.assoc]
      _ = α.hom.left ≫ f₀ := rfl
      _ = pullback.fst Yd.hom (yoneda.map (cS.π.app k)) ≫ raw := hh.symm
      _ = pullback.fst Yd.hom (yoneda.map (cS.π.app k)) ≫
            g'.left ≫ pullback.fst Zᵢ.hom (yoneda.map (Dsite.map d)) := by rw [hgl]
      _ = (pullback.fst Yd.hom (yoneda.map (cS.π.app k)) ≫ g'.left) ≫
            pullback.fst Zᵢ.hom (yoneda.map (Dsite.map d)) := (Category.assoc _ _ _).symm
      _ = (((Over.pullback (yoneda.map (cS.π.app k))).map g').left ≫
            pullback.fst Zd.hom (yoneda.map (cS.π.app k))) ≫
            pullback.fst Zᵢ.hom (yoneda.map (Dsite.map d)) := by rw [hmap]
      _ = ((Over.pullback (yoneda.map (cS.π.app k))).map g').left ≫
            β.hom.left ≫ pullback.fst Zᵢ.hom (yoneda.map (cS.π.app i)) := by
          rw [hβfst, Category.assoc]
      _ = ((Over.pullback (yoneda.map (cS.π.app k))).map g' ≫ β.hom).left ≫
            pullback.fst Zᵢ.hom (yoneda.map (cS.π.app i)) := by
          simp only [Over.comp_left, Category.assoc]
  · exact (Over.w (α.hom ≫ f)).trans
      (Over.w ((Over.pullback (yoneda.map (cS.π.app k))).map g' ≫ β.hom)).symm

/-! ### Lifting a pair of morphisms to a finite stage -/

/-- Given a morphism `g` over `X'` whose base change along `q` is the lift `u` over `X''`
(the compatibility `hg`), the pair `x`, `z` lifted by `u` over `X''` is lifted by `g` after
base change along `q`. -/
theorem baseChange_comp_eq_of_liftPair
    {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X) (h : q ≫ p = r)
    {A R W : Over X}
    (u : (Over.pullback r).obj A ⟶ (Over.pullback r).obj R)
    (g : (Over.pullback p).obj A ⟶ (Over.pullback p).obj R)
    (hg : (iteratedBaseChangeIso p q r h A).hom ≫ u =
      (Over.pullback q).map g ≫ (iteratedBaseChangeIso p q r h R).hom)
    (x : R ⟶ W) (z : A ⟶ W)
    (hz : u ≫ (Over.pullback r).map x = (Over.pullback r).map z) :
    (Over.pullback q).map (g ≫ (Over.pullback p).map x) =
      (Over.pullback q).map ((Over.pullback p).map z) := by
  apply (cancel_mono (iteratedBaseChangeIso p q r h W).hom).mp
  rw [Functor.map_comp, Category.assoc, iteratedBaseChangeIso_naturality p q r h x,
    ← Category.assoc, ← hg, Category.assoc, hz,
    iteratedBaseChangeIso_naturality p q r h z]

/-- A lift `g` over `X'` whose base change along `q` lifts the pair `x`, `z`, transported
across the comparison isomorphisms of the iterated base changes, lifts that pair over the
composite `r`. -/
theorem liftPair_iteratedBaseChangeIso
    {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X) (h : q ≫ p = r)
    {A R W : Over X} (g : (Over.pullback p).obj A ⟶ (Over.pullback p).obj R)
    (x : R ⟶ W) (z : A ⟶ W)
    (hx : (Over.pullback q).map (g ≫ (Over.pullback p).map x) =
      (Over.pullback q).map ((Over.pullback p).map z)) :
    ((iteratedBaseChangeIso p q r h A).inv ≫ (Over.pullback q).map g ≫
        (iteratedBaseChangeIso p q r h R).hom) ≫ (Over.pullback r).map x =
      (Over.pullback r).map z := by
  calc ((iteratedBaseChangeIso p q r h A).inv ≫ (Over.pullback q).map g ≫
        (iteratedBaseChangeIso p q r h R).hom) ≫ (Over.pullback r).map x
      = (iteratedBaseChangeIso p q r h A).inv ≫ (Over.pullback q).map g ≫
          (Over.pullback q).map ((Over.pullback p).map x) ≫
          (iteratedBaseChangeIso p q r h W).hom := by
        simp only [Category.assoc]
        rw [← iteratedBaseChangeIso_naturality p q r h x]
    _ = (iteratedBaseChangeIso p q r h A).inv ≫
          (Over.pullback q).map ((Over.pullback p).map z) ≫
          (iteratedBaseChangeIso p q r h W).hom := by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun y => (iteratedBaseChangeIso p q r h A).inv ≫ y ≫
            (iteratedBaseChangeIso p q r h W).hom) hx
    _ = (Over.pullback r).map z := by
        rw [iteratedBaseChangeIso_naturality p q r h z, Iso.inv_hom_id_assoc]

/-- A morphism whose base change along `q` lifts a pair of morphisms gives a lift of that
pair over the composite base change along `r`. -/
theorem exists_liftPair_of_baseChange_comp
    {C : Type*} [Category* C] [HasPullbacks C]
    {X X' X'' : C} (p : X' ⟶ X) (q : X'' ⟶ X') (r : X'' ⟶ X) (h : q ≫ p = r)
    {A R W : Over X} (s t : R ⟶ W) (a b : A ⟶ W)
    (g : (Over.pullback p).obj A ⟶ (Over.pullback p).obj R)
    (h₁ : (Over.pullback q).map (g ≫ (Over.pullback p).map s) =
      (Over.pullback q).map ((Over.pullback p).map a))
    (h₂ : (Over.pullback q).map (g ≫ (Over.pullback p).map t) =
      (Over.pullback q).map ((Over.pullback p).map b)) :
    ∃ v : (Over.pullback r).obj A ⟶ (Over.pullback r).obj R,
      v ≫ (Over.pullback r).map s = (Over.pullback r).map a ∧
      v ≫ (Over.pullback r).map t = (Over.pullback r).map b :=
  ⟨_, liftPair_iteratedBaseChangeIso p q r h g s a h₁,
    liftPair_iteratedBaseChangeIso p q r h g t b h₂⟩

/-- **A lift of a pair of morphisms over the limit descends to a finite stage.** No hypothesis
on the size of the index category.

If `u` is a morphism over the limit with `u ≫ s = a` and `u ≫ t = b` after base change to the
limit, then already at a later stage `j ⟶ i` there is a `v` with `v ≫ s = a` and `v ≫ t = b`
after base change to that stage.

As for `AlgebraicGeometry.Space.eventually_eq_of_baseChange_eq_of_isLimit`, the system is
given as a diagram `Dsite` in the big fppf site together with a cone `cS` on it whose image
under the underlying-scheme functor is a limit cone; that the limit is an object of the site
is what replaces the hypothesis `#I < B.cutoff.ord.cof` of the index-bounded development. -/
theorem exists_lift_pair_after_baseChange_of_isLimit
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (hQc : ∀ i, AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS
      (yoneda.obj (Dsite.obj i)))
    (hQs : ∀ i, AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ
      (yoneda.obj (Dsite.obj i)))
    (i : I) (A R W : Over (yoneda.obj (Dsite.obj i)))
    (hA : AlgebraicGeometry.IsAlgebraicSpace B S hS A.left)
    (hR : AlgebraicGeometry.IsAlgebraicSpace B S hS R.left)
    (hW : AlgebraicGeometry.IsAlgebraicSpace B S hS W.left)
    (hAfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS A.hom)
    (hRfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS R.hom)
    (hWfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS W.hom)
    (s t : R ⟶ W) (a b : A ⟶ W)
    (u : (Over.pullback (yoneda.map (cS.π.app i))).obj A ⟶
      (Over.pullback (yoneda.map (cS.π.app i))).obj R)
    (hu₁ : u ≫ (Over.pullback (yoneda.map (cS.π.app i))).map s =
      (Over.pullback (yoneda.map (cS.π.app i))).map a)
    (hu₂ : u ≫ (Over.pullback (yoneda.map (cS.π.app i))).map t =
      (Over.pullback (yoneda.map (cS.π.app i))).map b) :
    ∃ (j : I) (e : j ⟶ i)
      (v : (Over.pullback (yoneda.map (Dsite.map e))).obj A ⟶
        (Over.pullback (yoneda.map (Dsite.map e))).obj R),
      v ≫ (Over.pullback (yoneda.map (Dsite.map e))).map s =
        (Over.pullback (yoneda.map (Dsite.map e))).map a ∧
      v ≫ (Over.pullback (yoneda.map (Dsite.map e))).map t =
        (Over.pullback (yoneda.map (Dsite.map e))).map b := by
  classical
  obtain ⟨j, e, g, α, β, hα, hβ, hg⟩ := exists_morphism_after_baseChange_of_isLimit
    B S hS hAffine hcS hQc hQs i A R hA hR hAfp hRfp u
  have hα' := iteratedBaseChangeIso_unique (yoneda.map (Dsite.map e))
    (yoneda.map (cS.π.app j)) (yoneda.map (cS.π.app i)) (yoneda_map_cone_w B S hS e) A α hα
  have hβ' := iteratedBaseChangeIso_unique (yoneda.map (Dsite.map e))
    (yoneda.map (cS.π.app j)) (yoneda.map (cS.π.app i)) (yoneda_map_cone_w B S hS e) R β hβ
  rw [hα', hβ'] at hg
  have hDi := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj i)
  have hDj := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj j)
  have hAj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS A.hom
    (yoneda.map (Dsite.map e)) hA hDj hDi
  have hWj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS W.hom
    (yoneda.map (Dsite.map e)) hW hDj hDi
  have hAjfp := isFinitePresentation_of_isPullback B S hS hAj hA hDj hDi
    (IsPullback.of_hasPullback A.hom (yoneda.map (Dsite.map e))) hAfp
  have hWjfp := isFinitePresentation_of_isPullback B S hS hWj hW hDj hDi
    (IsPullback.of_hasPullback W.hom (yoneda.map (Dsite.map e))) hWfp
  obtain ⟨k₁, e₁, hk₁⟩ := eventually_eq_of_baseChange_eq_of_isLimit B S hS hAffine hcS hQc
    j ((Over.pullback (yoneda.map (Dsite.map e))).obj A)
    ((Over.pullback (yoneda.map (Dsite.map e))).obj W) hAj hWj hAjfp hWjfp
    (g ≫ (Over.pullback (yoneda.map (Dsite.map e))).map s)
    ((Over.pullback (yoneda.map (Dsite.map e))).map a)
    (baseChange_comp_eq_of_liftPair (yoneda.map (Dsite.map e)) (yoneda.map (cS.π.app j))
      (yoneda.map (cS.π.app i)) (yoneda_map_cone_w B S hS e) u g hg s a hu₁)
  obtain ⟨k₂, e₂, hk₂⟩ := eventually_eq_of_baseChange_eq_of_isLimit B S hS hAffine hcS hQc
    j ((Over.pullback (yoneda.map (Dsite.map e))).obj A)
    ((Over.pullback (yoneda.map (Dsite.map e))).obj W) hAj hWj hAjfp hWjfp
    (g ≫ (Over.pullback (yoneda.map (Dsite.map e))).map t)
    ((Over.pullback (yoneda.map (Dsite.map e))).map b)
    (baseChange_comp_eq_of_liftPair (yoneda.map (Dsite.map e)) (yoneda.map (cS.π.app j))
      (yoneda.map (cS.π.app i)) (yoneda_map_cone_w B S hS e) u g hg t b hu₂)
  let k := IsCofiltered.min (Over.mk e₁) (Over.mk e₂)
  let c₁ := IsCofiltered.minToLeft (Over.mk e₁) (Over.mk e₂)
  let c₂ := IsCofiltered.minToRight (Over.mk e₁) (Over.mk e₂)
  have hk₁' := baseChange_eq_of_baseChange_eq (yoneda.map (Dsite.map e₁))
    (yoneda.map (Dsite.map c₁.left)) (yoneda.map (Dsite.map k.hom))
    ((yoneda_map_Dsite_comp B S hS c₁.left e₁).trans
      (congrArg (fun m => yoneda.map (Dsite.map m)) c₁.w)) _ _ hk₁
  have hk₂' := baseChange_eq_of_baseChange_eq (yoneda.map (Dsite.map e₂))
    (yoneda.map (Dsite.map c₂.left)) (yoneda.map (Dsite.map k.hom))
    ((yoneda_map_Dsite_comp B S hS c₂.left e₂).trans
      (congrArg (fun m => yoneda.map (Dsite.map m)) c₂.w)) _ _ hk₂
  obtain ⟨v, hv₁, hv₂⟩ := exists_liftPair_of_baseChange_comp (yoneda.map (Dsite.map e))
    (yoneda.map (Dsite.map k.hom)) (yoneda.map (Dsite.map (k.hom ≫ e)))
    (yoneda_map_Dsite_comp B S hS k.hom e) s t a b g hk₁' hk₂'
  exact ⟨k.left, k.hom ≫ e, v, hv₁, hv₂⟩

/-! ### Essential surjectivity -/

omit [IsCofiltered I] in
/-- A transition morphism of the system is an affine morphism of algebraic spaces. -/
theorem isAffineHom_yoneda_map_Dsite_map
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {i j : I} (f : i ⟶ j) :
    AlgebraicGeometry.Space.IsAffineHom B S hS (yoneda.map (Dsite.map f)) := by
  intro Z g
  classical
  let a₀ : (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj Z ⟶ Dsite.obj j :=
    yoneda.preimage g
  have ha₀ : yoneda.map a₀ = g := Functor.map_preimage _ _
  refine ⟨⟨((chartDiagram B S hS Dsite j a₀).obj (Over.mk f)).left,
      isAffine_chartDiagram_obj B S hS hAffine j Z.property a₀ (Over.mk f)⟩,
    yoneda.map (pullback.fst (Dsite.map f) a₀),
    ((chartDiagram B S hS Dsite j a₀).obj (Over.mk f)).hom, ?_⟩
  rw [← ha₀]
  exact (IsPullback.of_hasPullback (Dsite.map f) a₀).map yoneda

/-- The comparison of two cartesian presentations of one object through the
iterated-base-change isomorphism.

`eA` presents `A` as the base change of `Z` along `ql`, `hB` presents `R` as the base change
of `Z` along `p`, and `am` is the induced map; the claim is that `am`, read into the fibre
product, is the composite of `eA` with the comparison isomorphism. -/
theorem lift_comp_isoPullback_hom
    {C : Type*} [Category* C] [HasPullbacks C]
    {Xl Xm L A R : C} (p : Xm ⟶ Xl) (qm : L ⟶ Xm) (ql : L ⟶ Xl) (h : qm ≫ p = ql)
    (Z : Over Xl) {a : A ⟶ Z.left} {x : A ⟶ L}
    (eA : A ⟶ pullback Z.hom ql) (heA₁ : eA ≫ pullback.fst Z.hom ql = a)
    (heA₂ : eA ≫ pullback.snd Z.hom ql = x)
    {b₁ : R ⟶ Z.left} {b₂ : R ⟶ Xm} (hB : IsPullback b₁ b₂ Z.hom p)
    (am : A ⟶ R) (hfst : am ≫ b₁ = a) (hsnd : am ≫ b₂ = x ≫ qm) :
    am ≫ hB.isoPullback.hom =
      eA ≫ (iteratedBaseChangeIso p qm ql h Z).inv.left ≫
        pullback.fst (pullback.snd Z.hom p) qm := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [hB.isoPullback_hom_fst, hfst,
      reassoc_of% (iteratedBaseChangeIso_inv_fst p qm ql h Z), pullback.lift_fst, heA₁]
  · simp only [Category.assoc]
    rw [hB.isoPullback_hom_snd, hsnd,
      reassoc_of% (iteratedBaseChangeIso_inv_fst p qm ql h Z), pullback.lift_snd,
      ← Category.assoc, heA₂]

/-- **An affine-stage relation whose legs are étale over the atlas of the space descends to
an étale relation at a later stage, and so to a model of the space.** No hypothesis on the
size of the index category.

`sm`, `tm` are the two legs of a relation over the stage `m` whose base changes along the
atlas `awm` of `Y` are étale. -/
theorem exists_model_of_affine_stage_relation_of_isLimit
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (hQc : ∀ i, AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS
      (yoneda.obj (Dsite.obj i)))
    (hQs : ∀ i, AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ
      (yoneda.obj (Dsite.obj i)))
    (m : I)
    (Y : Over (yoneda.obj cS.pt))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    {W KR : AlgebraicGeometry.BigFppfOver B S hS} (w : yoneda.obj W ⟶ Y.left)
    (hws : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (hwe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (kt ks : KR ⟶ W) (hwk : IsPullback (yoneda.map kt) (yoneda.map ks) w w)
    {Wm Rm : AlgebraicGeometry.BigFppfOver B S hS}
    (hWmAff : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Wm))
    (wm : yoneda.obj Wm ⟶ yoneda.obj (Dsite.obj m)) (sm tm : Rm ⟶ Wm)
    (htm : yoneda.map tm ≫ wm = yoneda.map sm ≫ wm)
    (hWmFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wm)
    (hRmFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map sm ≫ wm))
    (hSmFp : _root_.AlgebraicGeometry.FinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sm))
    (hTmFp : _root_.AlgebraicGeometry.FinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map tm))
    (awm : W ⟶ Wm) (arm : KR ⟶ Rm)
    (hWlim : IsPullback (yoneda.map awm) (w ≫ Y.hom) wm (yoneda.map (cS.π.app m)))
    (hRlim : IsPullback (yoneda.map arm) (yoneda.map kt ≫ w ≫ Y.hom)
      (yoneda.map sm ≫ wm) (yoneda.map (cS.π.app m)))
    (hsmSquare : IsPullback arm kt sm awm) (htmSquare : IsPullback arm ks tm awm) :
    ∃ (i : I) (Yᵢ : Over (yoneda.obj (Dsite.obj i))),
      AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left ∧
        AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom ∧
        Nonempty (Y ≅ (Over.pullback (yoneda.map (cS.π.app i))).obj Yᵢ) := by
  classical
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let pW := w ≫ Y.hom
  let pR := yoneda.map kt ≫ w ≫ Y.hom
  let rm := yoneda.map sm ≫ wm
  have hsm : yoneda.map sm ≫ wm = rm := rfl
  have ht : yoneda.map kt ≫ pW = pR := rfl
  have hsK : yoneda.map ks ≫ pW = pR := by
    change yoneda.map ks ≫ w ≫ Y.hom = yoneda.map kt ≫ w ≫ Y.hom
    rw [← Category.assoc, ← hwk.w, Category.assoc]
  have hX := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS cS.pt
  have hRmAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rm
  have hWmAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wm
  let a₀m : Wm ⟶ Dsite.obj m := yoneda.preimage wm
  have ha₀m : yoneda.map a₀m = wm := Functor.map_preimage _ _
  have hWmChart : IsPullback (yoneda.map (pullback.fst (cS.π.app m) a₀m))
      (yoneda.map (pullback.snd (cS.π.app m) a₀m)) (yoneda.map (cS.π.app m)) wm := by
    rw [← ha₀m]
    exact (IsPullback.of_hasPullback (cS.π.app m) a₀m).map yoneda
  let θ : (chartCone B S hS Dsite m a₀m cS).pt.left ⟶ W := yoneda.preimage
    (hWlim.flip.lift (yoneda.map (pullback.fst (cS.π.app m) a₀m))
      (yoneda.map (pullback.snd (cS.π.app m) a₀m)) hWmChart.w)
  have hθ : θ ≫ awm = (chartCone B S hS Dsite m a₀m cS).pt.hom := by
    apply yoneda.map_injective
    simp only [θ, yoneda.map_comp, yoneda.map_preimage]
    exact hWlim.flip.lift_snd _ _ _
  have hθQ : Q.map θ ≫ Q.map awm = Q.map (chartCone B S hS Dsite m a₀m cS).pt.hom := by
    rw [← Q.map_comp]
    exact congrArg Q.map hθ
  let : Etale ((Over.pullback (Q.map awm)).obj (Over.mk (Q.map sm))).hom :=
    (etale_iff_pullback_of_isPullback (hsmSquare.map Q)).mp
      (hwe.property w (yoneda.map ks) kt hwk.flip)
  let : Etale ((Over.pullback (Q.map awm)).obj (Over.mk (Q.map tm))).hom :=
    (etale_iff_pullback_of_isPullback (htmSquare.map Q)).mp
      (hwe.property w (yoneda.map kt) ks hwk)
  let : Etale ((Over.pullback (Q.map (chartCone B S hS Dsite m a₀m cS).pt.hom)).obj
      (Over.mk (Q.map sm))).hom :=
    etale_pullback_of_etale_pullback (Q.map awm) (Q.map θ)
      (Q.map (chartCone B S hS Dsite m a₀m cS).pt.hom) hθQ (Over.mk (Q.map sm))
  let : Etale ((Over.pullback (Q.map (chartCone B S hS Dsite m a₀m cS).pt.hom)).obj
      (Over.mk (Q.map tm))).hom :=
    etale_pullback_of_etale_pullback (Q.map awm) (Q.map θ)
      (Q.map (chartCone B S hS Dsite m a₀m cS).pt.hom) hθQ (Over.mk (Q.map tm))
  obtain ⟨js, hjs⟩ := eventually_etale_on_chart B S hS hAffine hcS m hWmAff a₀m
    (Over.mk (Q.map sm)) hSmFp
  obtain ⟨jt, hjt⟩ := eventually_etale_on_chart B S hS hAffine hcS m hWmAff a₀m
    (Over.mk (Q.map tm)) hTmFp
  let n := IsCofiltered.min js jt
  let as' := IsCofiltered.minToLeft js jt
  let at' := IsCofiltered.minToRight js jt
  let En := chartDiagram B S hS Dsite m a₀m
  let Cn := En.obj n
  have hCnAff : IsAffine (Q.obj Cn.left) :=
    isAffine_chartDiagram_obj B S hS hAffine m hWmAff a₀m n
  let cnStage : yoneda.obj Cn.left ⟶ yoneda.obj (Dsite.obj n.left) :=
    yoneda.map (pullback.fst (Dsite.map n.hom) a₀m)
  have hCn : IsPullback cnStage (yoneda.map Cn.hom) (yoneda.map (Dsite.map n.hom)) wm := by
    rw [← ha₀m]
    exact (IsPullback.of_hasPullback (Dsite.map n.hom) a₀m).map yoneda
  have hsChart : Etale (pullback.snd (Q.map sm) (Q.map Cn.hom)) := by
    let : Etale ((Over.pullback (Q.map (En.obj js).hom)).obj (Over.mk (Q.map sm))).hom := hjs
    exact etale_pullback_of_etale_pullback (Q.map (En.obj js).hom)
      (Q.map (En.map as').left) (Q.map (En.obj n).hom)
      (by rw [← Q.map_comp]; exact congrArg Q.map (En.map as').w) (Over.mk (Q.map sm))
  have htChart : Etale (pullback.snd (Q.map tm) (Q.map Cn.hom)) := by
    let : Etale ((Over.pullback (Q.map (En.obj jt).hom)).obj (Over.mk (Q.map tm))).hom := hjt
    exact etale_pullback_of_etale_pullback (Q.map (En.obj jt).hom)
      (Q.map (En.map at').left) (Q.map (En.obj n).hom)
      (by rw [← Q.map_comp]; exact congrArg Q.map (En.map at').w) (Over.mk (Q.map tm))
  let Wn := Cn.left
  let wn := cnStage
  let Rn := pullback sm Cn.hom
  let sn : Rn ⟶ Wn := pullback.snd sm Cn.hom
  let br : Rn ⟶ Rm := pullback.fst sm Cn.hom
  let rn := yoneda.map sn ≫ wn
  have hRn : IsPullback (yoneda.map br) rn rm (yoneda.map (Dsite.map n.hom)) := by
    have hh := ((IsPullback.of_hasPullback sm Cn.hom).map yoneda).paste_vert hCn.flip
    simpa only [hsm] using hh
  let tn : Rn ⟶ Wn := yoneda.preimage (hCn.lift rn
    (yoneda.map br ≫ yoneda.map tm) (by
      simp only [Category.assoc, htm]
      exact hRn.w.symm))
  have htn : yoneda.map tn ≫ wn = rn := by simp [tn, wn]
  have htnBr : br ≫ tm = tn ≫ Cn.hom := by
    apply yoneda.map_injective
    simp [tn]
  have htnSquare : IsPullback br tn tm Cn.hom := by
    apply IsPullback.of_map yoneda htnBr
    apply IsPullback.of_bot _ (by simpa only [Functor.map_comp] using congrArg yoneda.map htnBr)
      hCn.flip
    simpa only [← show wn = cnStage from rfl, htm, htn] using hRn
  have hsnEtale : Etale (Q.map sn) :=
    (etale_iff_pullback_of_isPullback ((IsPullback.of_hasPullback sm Cn.hom).map Q)).mpr
      hsChart
  have htnEtale : Etale (Q.map tn) :=
    (etale_iff_pullback_of_isPullback (htnSquare.map Q)).mpr htChart
  have hRnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rn
  have hWnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wn
  have hRnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS rn :=
    isFinitePresentation_of_isPullback B S hS hRnAlg hRmAlg
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj n.left))
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj m)) hRn hRmFp
  have hWnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wn :=
    isFinitePresentation_of_isPullback B S hS hWnAlg hWmAlg
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj n.left))
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj m)) hCn.flip hWmFp
  let awn : W ⟶ Wn := yoneda.preimage (hCn.flip.lift (yoneda.map awm)
    (pW ≫ yoneda.map (cS.π.app n.left))
    (by rw [Category.assoc, yoneda_map_cone_w B S hS n.hom]; exact hWlim.w))
  let arn : KR ⟶ Rn := yoneda.preimage (hRn.lift (yoneda.map arm)
    (pR ≫ yoneda.map (cS.π.app n.left))
    (by rw [Category.assoc, yoneda_map_cone_w B S hS n.hom]; exact hRlim.w))
  have hWnlim : IsPullback (yoneda.map awn) pW wn (yoneda.map (cS.π.app n.left)) := by
    have hh : IsPullback (yoneda.map awm) pW wm
        (yoneda.map (cS.π.app n.left) ≫ yoneda.map (Dsite.map n.hom)) := by
      rw [yoneda_map_cone_w B S hS n.hom]
      exact hWlim
    simpa only [awn, yoneda.map_preimage] using hh.of_right' hCn.flip
  have hRnlim : IsPullback (yoneda.map arn) pR rn (yoneda.map (cS.π.app n.left)) := by
    have hh : IsPullback (yoneda.map arm) pR rm
        (yoneda.map (cS.π.app n.left) ≫ yoneda.map (Dsite.map n.hom)) := by
      rw [yoneda_map_cone_w B S hS n.hom]
      exact hRlim
    simpa only [arn, yoneda.map_preimage] using hh.of_right' hRn
  have hArnBr : yoneda.map arn ≫ yoneda.map br = yoneda.map arm := by simp [arn]
  have hAwnBw : yoneda.map awn ≫ yoneda.map Cn.hom = yoneda.map awm := by simp [awn]
  have hsnCompat : arn ≫ sn = kt ≫ awn := by
    apply yoneda.map_injective
    apply hCn.hom_ext
    · simp only [Functor.map_comp, Category.assoc]
      change yoneda.map arn ≫ rn = yoneda.map kt ≫ yoneda.map awn ≫ wn
      rw [hRnlim.w, hWnlim.w, ← Category.assoc, ht]
    · simp only [Functor.map_comp, Category.assoc]
      have hsn : sn ≫ Cn.hom = br ≫ sm := pullback.condition.symm
      rw [← yoneda.map_comp sn Cn.hom, hsn, yoneda.map_comp,
        ← Category.assoc, hArnBr, hAwnBw]
      exact congrArg yoneda.map hsmSquare.w
  have htnCompat : arn ≫ tn = ks ≫ awn := by
    apply yoneda.map_injective
    apply hCn.hom_ext
    · simp only [Functor.map_comp, Category.assoc]
      change yoneda.map arn ≫ yoneda.map tn ≫ wn =
        yoneda.map ks ≫ yoneda.map awn ≫ wn
      rw [htn, hRnlim.w, hWnlim.w, ← Category.assoc, hsK]
    · simp only [Functor.map_comp, Category.assoc]
      rw [← yoneda.map_comp tn Cn.hom, ← htnBr, yoneda.map_comp,
        ← Category.assoc, hArnBr, hAwnBw]
      exact congrArg yoneda.map htmSquare.w
  have hsnSquare : IsPullback arn kt sn awn := by
    apply IsPullback.of_map yoneda hsnCompat
    apply IsPullback.of_bot _ (by
      simpa only [Functor.map_comp] using congrArg yoneda.map hsnCompat) hWnlim
    simpa only [ht] using hRnlim
  have htnLimitSquare : IsPullback arn ks tn awn := by
    apply IsPullback.of_map yoneda htnCompat
    apply IsPullback.of_bot _ (by
      simpa only [Functor.map_comp] using congrArg yoneda.map htnCompat) hWnlim
    simpa only [htn, hsK] using hRnlim
  have hDalg : ∀ x : I, AlgebraicGeometry.IsAlgebraicSpace B S hS ((Dsite ⋙ yoneda).obj x) :=
    fun x => AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj x)
  have hAffSpace : ∀ {x y : I} (e : x ⟶ y),
      AlgebraicGeometry.Space.IsAffineHom B S hS ((Dsite ⋙ yoneda).map e) :=
    fun e => isAffineHom_yoneda_map_Dsite_map B S hS hAffine e
  refine exists_model_of_stage_relation_of_cone B S hS hZ (Dsite ⋙ yoneda) hDalg hAffSpace
    hQc hQs (yoneda.mapCone cS) ?_ ?_ n.left hX Y hY w hws hwe kt ks hwk
    (show IsAffine (Q.obj Wn) from hCnAff) wn sn tn htn hsnEtale htnEtale
    hWnFp hRnFp awn arn hWnlim hRnlim hsnCompat htnCompat
  · intro x A' R' W' hA' hR' hW' hA'fp hR'fp hW'fp s' t' a' b' u' hu₁ hu₂
    exact exists_lift_pair_after_baseChange_of_isLimit B S hS hZ hAffine hcS hQc hQs
      x A' R' W' hA' hR' hW' hA'fp hR'fp hW'fp s' t' a' b' u' hu₁ hu₂
  · intro x Y' Z' hY' hZ'' hY'fp hZ'fp f' hf'
    have : Mono ((Over.pullback (yoneda.map (cS.π.app x))).map f') := hf'
    exact exists_mono_after_baseChange_of_isLimit B S hS hZ hAffine hQc hQs hcS
      x Y' Z' hY' hZ'' hY'fp hZ'fp f'

/-- **Stacks 07SK, essential surjectivity, with no hypothesis on the size of the index
category.**

Every algebraic space of finite presentation over the apex of the cone is the base change of
one over a finite stage.

As for `AlgebraicGeometry.Space.eventually_eq_of_baseChange_eq_of_isLimit`, the system is
given as a diagram `Dsite` in the big fppf site together with a cone `cS` on it whose image
under the underlying-scheme functor is a limit cone; that the limit is an object of the site
is what replaces the hypothesis `#I < B.cutoff.ord.cof` of
`AlgebraicGeometry.Space.exists_model_of_finitePresentation`. -/
theorem exists_model_of_finitePresentation_of_isLimit
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (hQc : ∀ i, AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS
      (yoneda.obj (Dsite.obj i)))
    (hQs : ∀ i, AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ
      (yoneda.obj (Dsite.obj i)))
    (Y : Over (yoneda.obj cS.pt))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom) :
    ∃ (i : I) (Yᵢ : Over (yoneda.obj (Dsite.obj i))),
      AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left ∧
        AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom ∧
        Nonempty (Y ≅ (Over.pullback (yoneda.map (cS.π.app i))).obj Yᵢ) := by
  classical
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨U₀, p₀, hU₀, hs₀, he₀⟩ := exists_affine_etale_atlas B S hS
    (yoneda.obj (Dsite.obj i)) (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj i))
    (hQc i)
  let a₀ : U₀ ⟶ Dsite.obj i := yoneda.preimage p₀
  have ha₀ : yoneda.map a₀ = p₀ := Functor.map_preimage _ _
  have hp₀ := represented_etale_of_isEtale B S hS p₀ he₀
  have ha₀E := show (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (yoneda.map a₀) from by
    rwa [ha₀]
  let U : AlgebraicGeometry.BigAffineFppf B S hS :=
    ⟨(chartCone B S hS Dsite i a₀ cS).pt.left,
      isAffine_chartCone_pt B S hS hAffine hcS i hU₀ a₀⟩
  let p : yoneda.obj U.obj ⟶ yoneda.obj cS.pt :=
    yoneda.map (pullback.fst (cS.π.app i) a₀)
  let q : U.obj ⟶ U₀ := pullback.snd (cS.π.app i) a₀
  have hp : IsPullback p (yoneda.map q) (yoneda.map (cS.π.app i)) p₀ := by
    rw [← ha₀]
    exact (IsPullback.of_hasPullback (cS.π.app i) a₀).map yoneda
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  obtain ⟨hs, he⟩ := surjective_etale_presheaf_of_isPullback B S hS hp.flip hs₀ hp₀
  have hX := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS cS.pt
  have hXqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
    hX (hQs i)
    (isQuasiSeparated_of_isAffineHom B S hS (yoneda.map (cS.π.app i)) hX
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj i))
      (isAffineHom_yoneda_map_π B S hS hAffine hcS i))
  have hYqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated
    B S hS hZ hY hXqs hFp.2.2
  obtain ⟨W, w, g, hws, hwe, hw, hg⟩ :=
    exists_affine_finitePresentation_chart B S hS hX hY Y.hom hFp U p hs he
  let K := atlasKernelPair B S hS w hY.diagonal_representable
  have hKt := atlasKernelPair_target_finitePresentation B S hS hZ hY hYqs W w hwe
  have hKg : AlgebraicGeometry.FinitePresentation (Q.map (K.s ≫ g)) := by
    let : LocallyOfFinitePresentation (Q.map K.s) := hKt.1
    let : QuasiCompact (Q.map K.s) := hKt.2.1
    let : QuasiSeparated (Q.map K.s) := hKt.2.2
    let : LocallyOfFinitePresentation (Q.map g) := hg.1
    let : QuasiCompact (Q.map g) := hg.2.1
    let : QuasiSeparated (Q.map g) := hg.2.2
    rw [Q.map_comp]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W.obj) := W.property
  obtain ⟨j, Wj, wj, aw, hwj, hWjaff, hWmodel⟩ := exists_affine_site_model_on_chart
    B S hS hZ hAffine hQs hcS i hU₀ a₀ ha₀E W.obj g hg
  obtain ⟨k, Rk, rk, ar, hrk, hRmodel⟩ := exists_site_model_on_chart
    B S hS hZ hAffine hQs hcS i hU₀ a₀ ha₀E K.R (K.s ≫ g) hKg
  let l := IsCofiltered.min j.left k.left
  let ej : l ⟶ j.left := IsCofiltered.minToLeft _ _
  let ek : l ⟶ k.left := IsCofiltered.minToRight _ _
  let pW := yoneda.map g ≫ p
  let pR := yoneda.map (K.s ≫ g) ≫ p
  obtain ⟨WlA, wl, bl, hbl⟩ :=
    isAffineHom_yoneda_map_Dsite_map B S hS hAffine ej ⟨Wj, hWjaff⟩ wj
  let Wl := WlA.obj
  have hwl : AlgebraicGeometry.Space.IsFinitePresentation B S hS wl :=
    isFinitePresentation_of_isPullback B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wl)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wj)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj l))
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj j.left)) hbl.flip hwj
  let awl : W.obj ⟶ Wl := yoneda.preimage (hbl.flip.lift (yoneda.map aw)
    (pW ≫ yoneda.map (cS.π.app l))
    (by rw [Category.assoc, yoneda_map_cone_w B S hS ej]; exact hWmodel.w))
  have hWl : IsPullback (yoneda.map awl) pW wl (yoneda.map (cS.π.app l)) := by
    have hh : IsPullback (yoneda.map aw) pW wj
        (yoneda.map (cS.π.app l) ≫ yoneda.map (Dsite.map ej)) := by
      rw [yoneda_map_cone_w B S hS ej]
      exact hWmodel
    simpa only [awl, yoneda.map_preimage] using hh.of_right' hbl.flip
  obtain ⟨Rl, rl, arl, hrl, hRl⟩ := advance_represented_model B S hS
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj l))
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj k.left))
    rk ar pR (yoneda.map (cS.π.app l)) (yoneda.map (Dsite.map ek))
    (yoneda.map (cS.π.app k.left)) (yoneda_map_cone_w B S hS ek)
    (isAffineHom_yoneda_map_Dsite_map B S hS hAffine ek) hrk hRmodel
  let KW := atlasKernelPair B S hS wl
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj l)).diagonal_representable
  have hWlAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wl
  have hKWAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS KW.R
  have hKWt : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map KW.s) :=
    isFinitePresentation_of_isPullback B S hS hKWAlg hWlAlg hWlAlg
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj l))
      KW.kernelPair.flip hwl
  let vKW := yoneda.map KW.s ≫ wl
  have hKWfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS vKW :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hKWAlg hWlAlg
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj l))
      (yoneda.map KW.s) wl hKWt hwl
  have ht : yoneda.map K.s ≫ pW = pR := by
    simp only [pW, pR, Functor.map_comp, Category.assoc]
  have hsK : yoneda.map K.t ≫ pW = pR := by
    rw [← ht]
    simpa only [pW, hw, Category.assoc] using
      congrArg (fun t => t ≫ Y.hom) K.kernelPair.w.symm
  let b : yoneda.obj K.R ⟶ yoneda.obj KW.R := KW.kernelPair.lift
    (yoneda.map K.s ≫ yoneda.map awl) (yoneda.map K.t ≫ yoneda.map awl) (by
      simp only [Category.assoc, hWl.w]
      rw [← Category.assoc, ht, ← Category.assoc, hsK])
  have hb : b ≫ vKW = pR ≫ yoneda.map (cS.π.app l) := by
    simp only [b, vKW, IsPullback.lift_fst_assoc]
    rw [Category.assoc, hWl.w, ← Category.assoc, ht]
  let source := Over.mk rl
  let target := Over.mk vKW
  let er : Over.mk pR ≅ (Over.pullback (yoneda.map (cS.π.app l))).obj source :=
    Over.isoMk hRl.isoPullback hRl.isoPullback_hom_snd
  let f : (Over.pullback (yoneda.map (cS.π.app l))).obj source ⟶
      (Over.pullback (yoneda.map (cS.π.app l))).obj target :=
    Over.homMk (pullback.lift (er.inv.left ≫ b)
      (pullback.snd rl (yoneda.map (cS.π.app l))) (by
        change (er.inv.left ≫ b) ≫ vKW = _
        rw [Category.assoc, hb, ← Category.assoc]
        exact congrArg (fun t => t ≫ yoneda.map (cS.π.app l)) er.inv.w))
      (pullback.lift_snd _ _ _)
  obtain ⟨m, em, gm, αm, βm, hαm, hβm, hgm⟩ := exists_morphism_after_baseChange_of_isLimit
    B S hS hAffine hcS hQc hQs l source target
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rl) hKWAlg hrl hKWfp f
  have hαmEq := iteratedBaseChangeIso_unique (yoneda.map (Dsite.map em))
    (yoneda.map (cS.π.app m)) (yoneda.map (cS.π.app l))
    (yoneda_map_cone_w B S hS em) source αm hαm
  have hβmEq := iteratedBaseChangeIso_unique (yoneda.map (Dsite.map em))
    (yoneda.map (cS.π.app m)) (yoneda.map (cS.π.app l))
    (yoneda_map_cone_w B S hS em) target βm hβm
  rw [hαmEq, hβmEq] at hgm
  have hmAffine := ((AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace B S hS
    (yoneda.map (Dsite.map em))
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj m))
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj l))).out 2 1).mp
    (isAffineHom_yoneda_map_Dsite_map B S hS hAffine em)
  let Rm := hmAffine.1.pullback rl
  let Wm := hmAffine.1.pullback wl
  let rm := hmAffine.1.fst rl
  let wm := hmAffine.1.fst wl
  have hRm : IsPullback rm (yoneda.map (hmAffine.1.snd rl))
      (yoneda.map (Dsite.map em)) rl := hmAffine.1.isPullback rl
  have hWm : IsPullback wm (yoneda.map (hmAffine.1.snd wl))
      (yoneda.map (Dsite.map em)) wl := hmAffine.1.isPullback wl
  have hWmAffineHom : _root_.AlgebraicGeometry.IsAffineHom (Q.map (hmAffine.1.snd wl)) :=
    hmAffine.2.property wl wm (hmAffine.1.snd wl) hWm
  have hWmAffine : IsAffine (Q.obj Wm) := by
    let : IsAffine (Q.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj WlA)) :=
      WlA.property
    let : _root_.AlgebraicGeometry.IsAffineHom (Q.map (hmAffine.1.snd wl)) := hWmAffineHom
    exact AlgebraicGeometry.isAffine_of_isAffineHom (Q.map (hmAffine.1.snd wl))
  have hRmFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS rm :=
    isFinitePresentation_of_isPullback B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rm)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rl)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj m))
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj l)) hRm.flip hrl
  have hWmFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wm :=
    isFinitePresentation_of_isPullback B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wm)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wl)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj m))
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj l)) hWm.flip hwl
  let st : target ⟶ Over.mk wl := Over.homMk (yoneda.map KW.s) rfl
  let tt : target ⟶ Over.mk wl := Over.homMk (yoneda.map KW.t) KW.kernelPair.w.symm
  let sm₀ := gm ≫ (Over.pullback (yoneda.map (Dsite.map em))).map st
  let tm₀ := gm ≫ (Over.pullback (yoneda.map (Dsite.map em))).map tt
  let sm : Rm ⟶ Wm := yoneda.preimage
    (hRm.flip.isoPullback.hom ≫ sm₀.left ≫ hWm.flip.isoPullback.inv)
  let tm : Rm ⟶ Wm := yoneda.preimage
    (hRm.flip.isoPullback.hom ≫ tm₀.left ≫ hWm.flip.isoPullback.inv)
  have hsm : yoneda.map sm ≫ wm = rm := by
    simp only [sm, yoneda.map_preimage, Category.assoc, IsPullback.isoPullback_inv_snd]
    rw [show sm₀.left ≫ pullback.snd wl (yoneda.map (Dsite.map em)) =
      pullback.snd rl (yoneda.map (Dsite.map em)) from sm₀.w,
      hRm.flip.isoPullback_hom_snd]
  have htm : yoneda.map tm ≫ wm = rm := by
    simp only [tm, yoneda.map_preimage, Category.assoc, IsPullback.isoPullback_inv_snd]
    rw [show tm₀.left ≫ pullback.snd wl (yoneda.map (Dsite.map em)) =
      pullback.snd rl (yoneda.map (Dsite.map em)) from tm₀.w,
      hRm.flip.isoPullback_hom_snd]
  let arm : K.R ⟶ Rm := yoneda.preimage (hRm.flip.lift (yoneda.map arl)
    (pR ≫ yoneda.map (cS.π.app m))
    (by rw [Category.assoc, yoneda_map_cone_w B S hS em]; exact hRl.w))
  let awm : W.obj ⟶ Wm := yoneda.preimage (hWm.flip.lift (yoneda.map awl)
    (pW ≫ yoneda.map (cS.π.app m))
    (by rw [Category.assoc, yoneda_map_cone_w B S hS em]; exact hWl.w))
  have hRlim : IsPullback (yoneda.map arm) pR rm (yoneda.map (cS.π.app m)) := by
    have hh : IsPullback (yoneda.map arl) pR rl
        (yoneda.map (cS.π.app m) ≫ yoneda.map (Dsite.map em)) := by
      rw [yoneda_map_cone_w B S hS em]
      exact hRl
    simpa only [arm, yoneda.map_preimage] using hh.of_right' hRm.flip
  have hWlim : IsPullback (yoneda.map awm) pW wm (yoneda.map (cS.π.app m)) := by
    have hh : IsPullback (yoneda.map awl) pW wl
        (yoneda.map (cS.π.app m) ≫ yoneda.map (Dsite.map em)) := by
      rw [yoneda_map_cone_w B S hS em]
      exact hWl
    simpa only [awm, yoneda.map_preimage] using hh.of_right' hWm.flip
  have harm : yoneda.map arm ≫ yoneda.map (hmAffine.1.snd rl) = yoneda.map arl := by
    simp [arm]
  have hawm : yoneda.map awm ≫ yoneda.map (hmAffine.1.snd wl) = yoneda.map awl := by
    simp [awm]
  have harPB := lift_comp_isoPullback_hom (yoneda.map (Dsite.map em))
    (yoneda.map (cS.π.app m)) (yoneda.map (cS.π.app l)) (yoneda_map_cone_w B S hS em)
    source er.hom.left hRl.isoPullback_hom_fst hRl.isoPullback_hom_snd hRm.flip
    (yoneda.map arm) harm hRlim.w
  have hgm' : yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫ gm.left ≫
      pullback.fst vKW (yoneda.map (Dsite.map em)) = b := by
    have hh := congrArg (fun z => er.hom ≫
      (iteratedBaseChangeIso (yoneda.map (Dsite.map em)) (yoneda.map (cS.π.app m))
        (yoneda.map (cS.π.app l)) (yoneda_map_cone_w B S hS em) source).inv ≫ z) hgm
    simp only [Iso.inv_hom_id_assoc] at hh
    have hh' := congrArg
      (fun z => z.left ≫ pullback.fst vKW (yoneda.map (cS.π.app l))) hh
    have her : er.hom.left ≫ er.inv.left = 𝟙 _ :=
      congrArg (fun z => z.left) er.hom_inv_id
    simp only [Over.comp_left, Category.assoc] at hh'
    have hβfst := iteratedBaseChangeIso_hom_fst (yoneda.map (Dsite.map em))
      (yoneda.map (cS.π.app m)) (yoneda.map (cS.π.app l))
      (yoneda_map_cone_w B S hS em) target
    change (iteratedBaseChangeIso (yoneda.map (Dsite.map em)) (yoneda.map (cS.π.app m))
      (yoneda.map (cS.π.app l)) (yoneda_map_cone_w B S hS em) target).hom.left ≫
      pullback.fst vKW (yoneda.map (cS.π.app l)) = _ at hβfst
    rw [hβfst] at hh'
    rw [reassoc_of% harPB]
    simpa only [source, target,
      Over.pullback_map_left, Over.pullback_obj_hom, Over.mk_hom, f,
      Over.homMk_left, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      her, reassoc_of% her, Category.id_comp] using hh'.symm
  have hsmCompat : arm ≫ sm = K.s ≫ awm := by
    apply yoneda.map_injective
    apply hWm.hom_ext
    · simp only [Functor.map_comp, Category.assoc, hsm, hRlim.w, hWlim.w]
      rw [← Category.assoc, ht]
    · simp only [Functor.map_comp, Category.assoc, sm, yoneda.map_preimage,
        IsPullback.isoPullback_inv_fst]
      change yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫
        (gm ≫ (Over.pullback (yoneda.map (Dsite.map em))).map st).left ≫
          pullback.fst wl (yoneda.map (Dsite.map em)) =
        yoneda.map K.s ≫ yoneda.map awm ≫ yoneda.map (hmAffine.1.snd wl)
      simp only [Over.comp_left, Over.pullback_map_left, Category.assoc,
        pullback.lift_fst, hawm, source, target, st, Over.mk_hom, Over.homMk_left]
      change yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫ gm.left ≫
        pullback.fst vKW (yoneda.map (Dsite.map em)) ≫ yoneda.map KW.s = _
      rw [reassoc_of% hgm']
      simp [b]
  have htmCompat : arm ≫ tm = K.t ≫ awm := by
    apply yoneda.map_injective
    apply hWm.hom_ext
    · simp only [Functor.map_comp, Category.assoc, htm, hRlim.w, hWlim.w]
      rw [← Category.assoc, hsK]
    · simp only [Functor.map_comp, Category.assoc, tm, yoneda.map_preimage,
        IsPullback.isoPullback_inv_fst]
      change yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫
        (gm ≫ (Over.pullback (yoneda.map (Dsite.map em))).map tt).left ≫
          pullback.fst wl (yoneda.map (Dsite.map em)) =
        yoneda.map K.t ≫ yoneda.map awm ≫ yoneda.map (hmAffine.1.snd wl)
      simp only [Over.comp_left, Over.pullback_map_left, Category.assoc,
        pullback.lift_fst, hawm, source, target, tt, Over.mk_hom, Over.homMk_left]
      change yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫ gm.left ≫
        pullback.fst vKW (yoneda.map (Dsite.map em)) ≫ yoneda.map KW.t = _
      rw [reassoc_of% hgm']
      simp [b]
  have hsmSquare : IsPullback arm K.s sm awm := by
    apply IsPullback.of_map yoneda hsmCompat
    apply IsPullback.of_bot _ (by
      simpa only [Functor.map_comp] using congrArg yoneda.map hsmCompat) hWlim
    simpa only [hsm, ht] using hRlim
  have htmSquare : IsPullback arm K.t tm awm := by
    apply IsPullback.of_map yoneda htmCompat
    apply IsPullback.of_bot _ (by
      simpa only [Functor.map_comp] using congrArg yoneda.map htmCompat) hWlim
    simpa only [htm, hsK] using hRlim
  have hRmAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rm
  have hWmAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wm
  have hSmFp := finitePresentation_of_yoneda B S hS sm
    (isFinitePresentation_overHom B S hS hZ
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj m)) (hQc m) (hQs m)
      (Over.mk rm) (Over.mk wm) hRmAlg hWmAlg hRmFp hWmFp
      (Over.homMk (yoneda.map sm) hsm))
  have hTmFp := finitePresentation_of_yoneda B S hS tm
    (isFinitePresentation_overHom B S hS hZ
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Dsite.obj m)) (hQc m) (hQs m)
      (Over.mk rm) (Over.mk wm) hRmAlg hWmAlg hRmFp hWmFp
      (Over.homMk (yoneda.map tm) htm))
  have hWlim' : IsPullback (yoneda.map awm) (w ≫ Y.hom) wm (yoneda.map (cS.π.app m)) := by
    rwa [← hw]
  have hRlim' : IsPullback (yoneda.map arm) (yoneda.map K.s ≫ w ≫ Y.hom)
      (yoneda.map sm ≫ wm) (yoneda.map (cS.π.app m)) := by
    rwa [show yoneda.map K.s ≫ w ≫ Y.hom = pR from by rwa [← hw], hsm]
  exact exists_model_of_affine_stage_relation_of_isLimit B S hS hZ hAffine hcS hQc hQs
    m Y hY w hws hwe K.s K.t K.kernelPair hWmAffine wm sm tm (htm.trans hsm.symm)
    hWmFp (by rwa [hsm]) hSmFp hTmFp awm arm hWlim' hRlim'
    hsmSquare htmSquare


end Realised

end AlgebraicGeometry.Space

end
