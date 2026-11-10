module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.SurjectiveCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local finite presentation on every chart from lifting along affine limits

Let `f : X ⟶ Y` be a morphism from a presheaf `X` on the big fppf site of `S`, with values in a
universe `max w u`, to the universe lift of a presheaf `Y` of `Type u`. Assume that `f` lifts
sections along cofiltered limits of affine schemes of the site. That is, if `T = lim T_i`, `x` is
a section of `X` over `T` and `y` is a section of `Y` over a stage `T_i` with `f(x) = y|_T`, then
some later stage `T_j` carries a section `z` of `X` with `f(z) = y|_{T_j}` and `z|_T = x`. Then
every commuting square of étale charts of `f` has its underlying morphism of schemes locally of
finite presentation. This is the condition of Stacks 03MJ for local finite presentation
(Stacks 03XP).

Neither `X` nor `Y` is assumed to be an algebraic space. This is the point of the result: the
criterion of Stacks 0CM6,
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_affineLimit_surjective`, first reduces
to one surjective chart and so needs both sides algebraic. Here each chart square is treated on
its own. This is what allows the conclusion for a presheaf whose algebraicity is not yet known,
such as the Quot functor of Stacks 09TR.

## The argument

Let `a : U ⟶ X` and `b : V ⟶ Y` be étale charts and `h : U ⟶ V` a morphism of the site with
`h ≫ b = a ≫ f`. Form the fibre product `U' = V ×_Y U` of `b` along `h ≫ b`, a scheme of the
site because `b` is representable, with projections `p : U' ⟶ V` and `q : U' ⟶ U`. Then:

* `h` factors as `s ≫ p`, where `s = (h, id) : U ⟶ U'` is a section of `q`. The morphism `q` is a
  base change of `b`, hence étale. So `s` is locally of finite presentation, by cancellation
  against `q`, and it suffices that `p` is.
* `p` is a morphism between representable algebraic spaces. By Stacks 0CM6 it suffices to lift
  a point `x = (v, u)` of `U'` over a limit `T`, with `v` coming from a point `y_i` of `V` at a
  stage. The section `a(u)` of `X` lies over `b(y_i)|_T`, so the hypothesis lifts it to a stage
  `T_j`. Then the representable étale morphism `a` lifts `u` itself to a later stage `T_k`
  (Stacks 04AK for a representable étale morphism). Together with `y_i` this gives a point of
  `U' = V ×_Y U` over `T_k` restricting to `x`.

## Main results

* `Space.exists_stage_lift_of_relative_etale_uliftYoneda`: a section over a cofiltered limit of
  affine schemes of the site, lifting a section over a stage along a morphism which is étale
  relative to `CategoryTheory.uliftYoneda`, lifts over a later stage.
* `Space.holdsOnEveryEtaleChartULift_locallyOfFinitePresentation_of_exists_stage_lift`: the chart
  condition for local finite presentation from lifting along affine limits.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 0CM6](https://stacks.math.columbia.edu/tag/0CM6)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A section over a limit lifting a section over a stage along a relatively étale morphism
lifts over a later stage** (Stacks 04AK for a representable étale morphism, in the value
universe `max w u`). Let `T = lim T_i` be a cofiltered limit of affine schemes of the site, taken
in schemes, and `p : W ⟶ X` a morphism from a scheme of the site which is étale relative to
`CategoryTheory.uliftYoneda`. Let `ξ` be a section of `X` over a stage `T_i` and `a : T ⟶ W`
with `p(a) = ξ|_T`. Then some later stage `T_j` carries `b : T_j ⟶ W` with `b|_T = a` and
`p(b) = ξ|_{T_j}`. -/
theorem exists_stage_lift_of_relative_etale_uliftYoneda
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ BigFppfOver B S hS) (c : Cone D)
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hD : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
    {W : BigFppfOver B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (p : uliftYoneda.{w}.obj W ⟶ X)
    (hp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{w} p)
    (i : I) (ξ : uliftYoneda.{w}.obj (D.obj i) ⟶ X) (a : c.pt ⟶ W)
    (ha : uliftYoneda.{w}.map a ≫ p = uliftYoneda.{w}.map (c.π.app i) ≫ ξ) :
    ∃ (j : I) (g : j ⟶ i) (b : D.obj j ⟶ W),
      c.π.app j ≫ b = a ∧ uliftYoneda.{w}.map b ≫ p = uliftYoneda.{w}.map (D.map g) ≫ ξ := by
  let T := BigFppfOver.toScheme B S hS
  let e := hp.rep
  let E := e.pullback ξ
  let aE : c.pt ⟶ E := e.lift' a (c.π.app i) ha
  have he : Etale (T.map (e.snd ξ)) := hp.property_snd ξ
  let P := Over.forget i
  let D' := P ⋙ D ⋙ T
  let c' := (T.mapCone c).whisker P
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv P (T.mapCone c)).symm hc
  have : ∀ k, IsAffine (D'.obj k) := fun k => hD k.left
  have : ∀ {k l} (g : k ⟶ l), AlgebraicGeometry.IsAffineHom (D'.map g) := fun _ => inferInstance
  have : ∀ k, CompactSpace (D'.obj k) := fun _ => inferInstance
  have : ∀ k, QuasiSeparatedSpace (D'.obj k) := fun _ => inferInstance
  let t : D' ⟶ (Functor.const (Over i)).obj (T.obj (D.obj i)) :=
    { app := fun k => T.map (D.map k.hom)
      naturality := by
        intro k l α
        dsimp [D', P]
        simp only [Category.comp_id, ← Functor.map_comp]
        congr 2
        exact Over.w α }
  have hcompat : c'.π ≫ t = (Functor.const (Over i)).map (T.map aE ≫ T.map (e.snd ξ)) := by
    ext k
    change T.map (c.π.app k.left) ≫ T.map (D.map k.hom) = T.map aE ≫ T.map (e.snd ξ)
    rw [← T.map_comp, ← T.map_comp, c.w k.hom, e.lift'_snd]
  obtain ⟨k, β, hβ, hβ'⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D' t (T.map (e.snd ξ)) c' hc'
      (T.map aE) hcompat
  have hβS : β ≫ B.inclusion.map E.hom = B.inclusion.map (D.obj k.left).hom := by
    calc
      β ≫ B.inclusion.map E.hom =
          β ≫ T.map (e.snd ξ) ≫ B.inclusion.map (D.obj i).hom := by
        congr 1
        exact (congrArg B.inclusion.map (e.snd ξ).w).symm
      _ = T.map (D.map k.hom) ≫ B.inclusion.map (D.obj i).hom := by
        rw [← Category.assoc, hβ']
      _ = B.inclusion.map (D.obj k.left).hom :=
        congrArg B.inclusion.map (D.map k.hom).w
  let β' : D.obj k.left ⟶ E :=
    Over.homMk (ObjectProperty.homMk β) (by apply ObjectProperty.hom_ext; exact hβS)
  have hβ₁ : c.π.app k.left ≫ β' = aE := T.map_injective hβ
  have hβ₂ : β' ≫ e.snd ξ = D.map k.hom := T.map_injective hβ'
  refine ⟨k.left, k.hom, β' ≫ e.fst' ξ, ?_, ?_⟩
  · rw [← Category.assoc, hβ₁]
    exact e.lift'_fst a (c.π.app i) ha
  · rw [Functor.map_comp, Category.assoc, (e.isPullback' ξ).w, ← Category.assoc,
      ← Functor.map_comp, hβ₂]

/-- **Local finite presentation on every étale chart from lifting along affine limits.** Let
`f : X ⟶ Y ⋙ uliftFunctor` be a morphism from a presheaf of `Type (max w u)` to the universe
lift of a presheaf of `Type u` on the big fppf site of `S`. Assume `f` lifts sections along
cofiltered limits of affine schemes of the site: whenever `T = lim T_i`, `x` is a section of `X`
over `T` and `y` a section of `Y` over a stage `T_i` with `f(x) = y|_T`, some later stage `T_j`
carries a section `z` of `X` with `f(z) = y|_{T_j}` and `z|_T = x`. Then the morphism of schemes
underlying every commuting square of étale charts of `f` is locally of finite presentation.

No algebraicity is assumed of `X` or of `Y`; see the module documentation. -/
@[sga "3 XI 3.2" "Representable case"]
theorem holdsOnEveryEtaleChartULift_locallyOfFinitePresentation_of_exists_stage_lift
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y ⋙ uliftFunctor.{w})
    (hlift : ∀ (I : Type u) [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ BigFppfOver B S hS) (c : Cone D),
      IsLimit ((BigFppfOver.toScheme B S hS).mapCone c) →
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i))) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) →
      ∀ (x : X.obj (op c.pt)) (i : I) (y : Y.obj (op (D.obj i))),
        (f.app (op c.pt) x).down = Y.map (c.π.app i).op y →
        ∃ (j : I) (g : j ⟶ i) (z : X.obj (op (D.obj j))),
          (f.app (op (D.obj j)) z).down = Y.map (D.map g).op y ∧
            X.map (c.π.app j).op z = x) :
    HoldsOnEveryEtaleChartULift.{w} B S hS
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) f := by
  intro U V a b h ha hb hw
  obtain ⟨b₀, rfl⟩ := exists_whiskerRight_eq B S hS (F := yoneda.obj V) b
  have hb₀ := (relative_uliftYoneda_whiskerRight_iff' B S hS _ b₀).mp hb
  let T := BigFppfOver.toScheme B S hS
  let φ₀ : yoneda.obj U ⟶ Y := yoneda.map h ≫ b₀
  let e := hb₀.rep
  let p : e.pullback φ₀ ⟶ V := e.fst' φ₀
  let q : e.pullback φ₀ ⟶ U := e.snd φ₀
  have hq : Etale (T.map q) := hb₀.property_snd φ₀
  let s : U ⟶ e.pullback φ₀ := e.lift' h (𝟙 U) (by simp [φ₀])
  have hsq : s ≫ q = 𝟙 U := e.lift'_snd _ _ _
  have hsp : s ≫ p = h := e.lift'_fst _ _ _
  -- the value of `f ∘ a` at a point `u` of `U` is `b₀(h ∘ u)`
  have hfa : ∀ (Z : BigFppfOver B S hS) (u : Z ⟶ U),
      (f.app (op Z) (a.app (op Z) ⟨u⟩)).down = b₀.app (op Z) (u ≫ h) := fun Z u =>
    (congrArg (fun k => (k.app (op Z) ⟨u⟩).down) hw).symm
  have hpq : ∀ (Z : BigFppfOver B S hS) (x : Z ⟶ e.pullback φ₀),
      b₀.app (op Z) (x ≫ p) = b₀.app (op Z) ((x ≫ q) ≫ h) := fun Z x => by
    exact congrArg (fun k => k.app (op Z) x) (e.isPullback' φ₀).w
  have hp : LocallyOfFinitePresentation (T.map p) := by
    refine (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget p).1 ?_
    refine isLocallyOfFinitePresentation_of_affineLimit_surjective B S hS
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS V) (yoneda.map p) ?_
    intro I _ _ D c hc hD hpt x y hxy
    obtain ⟨⟨i⟩, yi, rfl⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit _) y
    have hxy' : x ≫ p = c.π.app i ≫ yi := by
      have h₁ := hxy
      change x ≫ p = colimit.desc (D.op ⋙ yoneda.obj V) ((yoneda.obj V).mapCocone c.op)
        (colimit.ι (D.op ⋙ yoneda.obj V) (op i) yi) at h₁
      rw [colimit.ι_desc_apply] at h₁
      exact h₁
    have hX : (f.app (op c.pt) (a.app (op c.pt) ⟨x ≫ q⟩)).down =
        Y.map (c.π.app i).op (b₀.app (op (D.obj i)) yi) := by
      rw [hfa, ← hpq, hxy']
      exact NatTrans.naturality_apply b₀ (c.π.app i).op yi
    obtain ⟨j, g, ζ, hζ₁, hζ₂⟩ := hlift I D c hc hD hpt (a.app (op c.pt) ⟨x ≫ q⟩) i
      (b₀.app (op (D.obj i)) yi) hX
    let ξ : uliftYoneda.{w}.obj (D.obj j) ⟶ X := uliftYonedaEquiv.symm ζ
    have ha' : uliftYoneda.{w}.map (x ≫ q) ≫ a = uliftYoneda.{w}.map (c.π.app j) ≫ ξ := by
      apply uliftYonedaEquiv.injective
      simp only [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]
      exact hζ₂.symm
    obtain ⟨k, g', wk, hwk₁, hwk₂⟩ :=
      exists_stage_lift_of_relative_etale_uliftYoneda B S hS D c hc hD a ha j ξ (x ≫ q) ha'
    have hlift' : yoneda.map (D.map (g' ≫ g) ≫ yi) ≫ b₀ = yoneda.map wk ≫ φ₀ := by
      apply yonedaEquiv.injective
      change b₀.app (op (D.obj k)) (D.map (g' ≫ g) ≫ yi) = b₀.app (op (D.obj k)) (wk ≫ h)
      have h₁ : a.app (op (D.obj k)) ⟨wk⟩ = X.map (D.map g').op ζ := by
        have := congrArg uliftYonedaEquiv.{w} hwk₂
        simp only [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map] at this
        exact this
      rw [← hfa, h₁, NatTrans.naturality_apply f (D.map g').op ζ]
      change b₀.app (op (D.obj k)) (D.map (g' ≫ g) ≫ yi) =
        Y.map (D.map g').op (f.app (op (D.obj j)) ζ).down
      rw [hζ₁, ← NatTrans.naturality_apply b₀ (D.map g).op yi,
        ← NatTrans.naturality_apply b₀ (D.map g').op, Functor.map_comp, Category.assoc]
      rfl
    let z' : D.obj k ⟶ e.pullback φ₀ := e.lift' (D.map (g' ≫ g) ≫ yi) wk hlift'
    refine ⟨colimit.ι (D.op ⋙ yoneda.obj (e.pullback φ₀)) (op k) z', ?_, ?_⟩
    · rw [colimit.ι_desc_apply]
      change c.π.app k ≫ z' = x
      apply e.hom_ext'
      · rw [Category.assoc, e.lift'_fst, ← Category.assoc, c.w]
        exact hxy'.symm
      · rw [Category.assoc, e.lift'_snd]
        exact hwk₁
    · rw [colimit.ι_map_apply]
      change colimit.ι (D.op ⋙ yoneda.obj V) (op k) (z' ≫ p) = _
      rw [e.lift'_fst]
      exact colimit.w_apply (D.op ⋙ yoneda.obj V) (g' ≫ g).op yi
  have hs : LocallyOfFinitePresentation (T.map s) := by
    have : LocallyOfFinitePresentation (T.map s ≫ T.map q) := by
      rw [← T.map_comp, hsq, T.map_id]
      infer_instance
    exact locallyOfFinitePresentation_of_comp (T.map s) (T.map q)
  change LocallyOfFinitePresentation (T.map h)
  rw [← hsp, T.map_comp]
  infer_instance

end AlgebraicGeometry.Space

end
