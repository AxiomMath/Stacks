module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomDescentCocycle
public import StacksFrontier.AlgebraicGeometry.Descent.CandidateEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityComparison
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.MorphismDescent
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescendedScheme
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentDataBridge

/-!
# Stacks 03I2 with the hypotheses the source places on the property

Stacks 03I2 asks of its property `P` of morphisms of schemes exactly three things: that `P` be
preserved by arbitrary base change, that `P` be fppf local on the base, and that morphisms with
`P` satisfy descent for fppf coverings (Descent, Definition 35.36.1, Tag 02W2). This file derives
from those three the one geometric input of the proof as
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleDescent` isolates it,
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`, and states Stacks 03I2 itself
with the source's hypotheses.

The three hypotheses are, in order, `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`,
`CategoryTheory.MorphismProperty.IsLocalAtTarget` at
`AlgebraicGeometry.Scheme.fppfPrecoverage`, and `AlgebraicGeometry.SatisfiesDescent` at that
precoverage.

## Main results

* `AlgebraicGeometry.exists_descended_of_actionAssoc`: the step which spends fppf descent. A
  descent datum of schemes relative to a surjective flat morphism locally of finite presentation,
  presented by the isomorphism of its two literal fibre products together with the associativity
  of the resulting action, descends: there are a scheme over the base, a Cartesian square
  exhibiting the datum as its base change, the property of the descended morphism, and the
  invariance of the projection.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_satisfiesDescent`: the
  derivation. A property stable under base change, fppf local on the base and satisfying fppf
  descent descends effectively along the surjective étale morphisms of the big fppf site of `S`.
* `AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart`: **Stacks
  03I2**, with those three hypotheses on `P` in place of the repackaged one. Its conditional
  form, which carries effective descent along a surjective étale chart as a hypothesis, is
  `AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent`.

## Implementation notes

**Why associativity is a hypothesis of the scheme-level step.** The cocycle condition is forced
by the fact that two morphisms into `v` which agree over `c` and over `X` are equal — and "over
`X`" makes sense only for test objects *of the site*, since `X` is a presheaf on the site. So
the associativity of the action is established between morphisms of the site out of
`c ×_a (c ×_a v)`, by `AlgebraicGeometry.Space.descentAction_unique`, and handed to the
scheme-level step as a hypothesis quantified over arbitrary test schemes; the scheme-level step
knows nothing of the site, and no test object outside the site has to be placed inside it.

**The index universe of hypothesis (3).** `AlgebraicGeometry.SatisfiesDescent` quantifies over
covering families indexed by an arbitrary type; the hypothesis below is taken for index types in
`Type`, which is all the one-member covering `{q}` needs. It is therefore implied by the
source's hypothesis for arbitrary index sets, so the statement proved is at least as strong as
the source's.

## References

* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 02W2](https://stacks.math.columbia.edu/tag/02W2)
* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
* [Stacks Project, Tag 02W5](https://stacks.math.columbia.edu/tag/02W5)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The scheme-level descent step -/

/-- **Effective fppf descent, from an isomorphism of fibre products and the associativity of its
action.** Let `g : C ⟶ T` be a surjective flat morphism locally of finite presentation, let
`p : V ⟶ C`, and let `φ : V ×_T C ≅ C ×_T V` be an isomorphism over `C ×_T C`, presented through
two Cartesian squares. Write `ψ` for the composite of `φ` with the projection to `V`: on
generalized points `ψ` is the action of the groupoid `C ×_T C` on `V`. If the action is
associative — `hassoc` — then `(V, φ)` is a descent datum relative to `g`, and the effective
descent of morphisms with a property `Pr` which `p` has makes it effective: there are a scheme
`W` over `T` with `Pr`, a Cartesian square exhibiting `V` as `C ×_T W`, and the invariance of the
projection `V ⟶ W` for the action: two generalized points of `V` lying over the same point of
`T` and related by the action have the same image in `W`. -/
theorem exists_descended_of_actionAssoc {T C V W₁ W₂ : Scheme.{u}}
    {g : C ⟶ T} {p : V ⟶ C} {pi1 : W₁ ⟶ V} {pi2 : W₁ ⟶ C} {ρ1 : W₂ ⟶ C} {ρ2 : W₂ ⟶ V}
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    (φ : W₁ ≅ W₂) (sq1 : IsPullback pi1 pi2 (p ≫ g) g) (sq2 : IsPullback ρ1 ρ2 g (p ≫ g))
    (hφ1 : φ.hom ≫ ρ1 = pi1 ≫ p) (hφ2 : (φ.hom ≫ ρ2) ≫ p = pi2)
    (hassoc : ∀ ⦃Z : Scheme.{u}⦄ (ξ : Z ⟶ W₁) (y : Z ⟶ C)
      (h₁ : (ξ ≫ φ.hom ≫ ρ2) ≫ p ≫ g = y ≫ g) (h₂ : (ξ ≫ pi1) ≫ p ≫ g = y ≫ g),
      sq1.lift (ξ ≫ φ.hom ≫ ρ2) y h₁ ≫ φ.hom ≫ ρ2 =
        sq1.lift (ξ ≫ pi1) y h₂ ≫ φ.hom ≫ ρ2)
    {Pr : MorphismProperty Scheme.{u}} [Pr.IsLocalAtTarget Scheme.fppfPrecoverage] (hPp : Pr p)
    (hdesc : SatisfiesDescent.{u, 0} Pr Scheme.fppfPrecoverage) :
    ∃ (W : Scheme.{u}) (i : W ⟶ T) (k : V ⟶ W),
      IsPullback p k g i ∧ Pr i ∧
      ∀ ⦃Z : Scheme.{u}⦄ (z₁ z₂ : Z ⟶ V) (hz : z₁ ≫ p ≫ g = (z₂ ≫ p) ≫ g),
        sq1.lift z₁ (z₂ ≫ p) hz ≫ φ.hom ≫ ρ2 = z₂ → z₁ ≫ k = z₂ ≫ k := by
  have hi1 : sq1.isoPullback.inv ≫ pi1 = pullback.fst (p ≫ g) g := by
    rw [Iso.inv_comp_eq, sq1.isoPullback_hom_fst]
  have hi2 : sq1.isoPullback.inv ≫ pi2 = pullback.snd (p ≫ g) g := by
    rw [Iso.inv_comp_eq, sq1.isoPullback_hom_snd]
  obtain ⟨Θ, hΘ1, hΘψ⟩ :
      ∃ Θ : pullback (p ≫ g) g ≅ pullback g (p ≫ g),
        Θ.hom ≫ pullback.fst g (p ≫ g) = pullback.fst (p ≫ g) g ≫ p ∧
        Θ.hom ≫ pullback.snd g (p ≫ g) = sq1.isoPullback.inv ≫ φ.hom ≫ ρ2 := by
    refine ⟨sq1.isoPullback.symm ≪≫ φ ≪≫ sq2.isoPullback, ?_, ?_⟩
    · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, sq2.isoPullback_hom_fst]
      rw [hφ1, ← Category.assoc sq1.isoPullback.inv pi1 p, hi1]
    · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, sq2.isoPullback_hom_snd]
  have hΘ2 : Θ.hom ≫ pullback.snd g (p ≫ g) ≫ p = pullback.snd (p ≫ g) g := by
    rw [← Category.assoc Θ.hom (pullback.snd g (p ≫ g)) p, hΘψ, Category.assoc, hφ2, hi2]
  obtain ⟨Φ, h1, h2, hactl⟩ := exists_gluingIso_of_pullbackIso g p Θ hΘ1 hΘ2
  have hex : ∀ {Z : Scheme.{u}} (a : Z ⟶ V) (b : Z ⟶ C) (h : a ≫ p ≫ g = b ≫ g),
      ∃ L : Z ⟶ pullback (p ≫ g) g, L ≫ pullback.fst (p ≫ g) g = a ∧
        L ≫ pullback.snd (p ≫ g) g = b ∧ L ≫ sq1.isoPullback.inv = sq1.lift a b h := fun a b h ↦
    ⟨pullback.lift a b h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
      sq1.hom_ext (by rw [Category.assoc, hi1, pullback.lift_fst, sq1.lift_fst])
        (by rw [Category.assoc, hi2, pullback.lift_snd, sq1.lift_snd])⟩
  have hlift : ∀ {Z : Over T} (v' : Z ⟶ (Over.map g).obj (Over.mk p)) (x : Z ⟶ Over.mk g),
      v'.left ≫ p ≫ g = x.left ≫ g := by
    intro Z v' x
    rw [← Category.assoc v'.left p g]
    exact (Over.w v').trans (Over.w x).symm
  have hact : ∀ {Z : Over T} (v' : Z ⟶ (Over.map g).obj (Over.mk p)) (x : Z ⟶ Over.mk g)
      (l : Z.left ⟶ pullback (p ≫ g) g), l ≫ pullback.fst (p ≫ g) g = v'.left →
      l ≫ pullback.snd (p ≫ g) g = x.left →
      (gluingAction (Over.mk p) Φ.hom.left v' x).left =
        l ≫ sq1.isoPullback.inv ≫ φ.hom ≫ ρ2 := by
    intro Z v' x l hl1 hl2
    rw [hactl v' x l hl1 hl2, hΘψ]
  have hcocycle : prod.map Φ.hom.left (𝟙 (Over.mk g)) ≫ prodMapLastTwo Φ.hom.left =
      prodMapFirstThird Φ.hom.left := by
    refine (cocycle_iff_gluingAction_act_act (Over.mk p) Φ.hom.left h1 h2).mpr ?_
    intro Z v' x y
    refine Over.OverMorphism.ext ?_
    obtain ⟨L₁, hL₁f, hL₁s, -⟩ := hex v'.left x.left (hlift v' x)
    have hξ1 : (L₁ ≫ sq1.isoPullback.inv) ≫ pi1 = v'.left := by
      rw [Category.assoc, hi1, hL₁f]
    have hξ2 : (L₁ ≫ sq1.isoPullback.inv) ≫ pi2 = x.left := by
      rw [Category.assoc, hi2, hL₁s]
    have hxy : x.left ≫ g = y.left ≫ g := (Over.w x).trans (Over.w y).symm
    have hcond₁ : ((L₁ ≫ sq1.isoPullback.inv) ≫ φ.hom ≫ ρ2) ≫ p ≫ g = y.left ≫ g := by
      have h0 : ((L₁ ≫ sq1.isoPullback.inv) ≫ φ.hom ≫ ρ2) ≫ p = x.left := by
        rw [Category.assoc (L₁ ≫ sq1.isoPullback.inv) (φ.hom ≫ ρ2) p, hφ2, hξ2]
      rw [← Category.assoc ((L₁ ≫ sq1.isoPullback.inv) ≫ φ.hom ≫ ρ2) p g, h0]
      exact hxy
    have hcond₂ : ((L₁ ≫ sq1.isoPullback.inv) ≫ pi1) ≫ p ≫ g = y.left ≫ g := by
      rw [hξ1]
      exact hlift v' y
    obtain ⟨L₂, hL₂f, hL₂s, hL₂eq⟩ := hex _ y.left hcond₁
    obtain ⟨L₃, hL₃f, hL₃s, hL₃eq⟩ := hex _ y.left hcond₂
    rw [hξ1] at hL₃f
    have hL₂f' : L₂ ≫ pullback.fst (p ≫ g) g =
        (gluingAction (Over.mk p) Φ.hom.left v' x).left := by
      rw [hL₂f, hact v' x L₁ hL₁f hL₁s, Category.assoc]
    rw [hact (gluingAction (Over.mk p) Φ.hom.left v' x) y L₂ hL₂f' hL₂s,
      hact v' y L₃ hL₃f hL₃s,
      ← Category.assoc L₂ sq1.isoPullback.inv (φ.hom ≫ ρ2),
      ← Category.assoc L₃ sq1.isoPullback.inv (φ.hom ≫ ρ2), hL₂eq, hL₃eq]
    exact hassoc (L₁ ≫ sq1.isoPullback.inv) y.left hcond₁ hcond₂
  have hcov : Presieve.ofArrows (fun _ : Unit ↦ C) (fun _ ↦ g) ∈ Scheme.fppfPrecoverage T := by
    rw [Presieve.ofArrows_pUnit]
    exact g.singleton_mem_fppfPrecoverage
  obtain ⟨Q⟩ := DescentDatum.nonempty_descended_of_isEffective
    (DescentData.isEffective_of_isFamilyEffective
      (hdesc (fun _ : Unit ↦ g) hcov (DescentDatum.mk' (Over.mk p) Φ hcocycle) fun _ ↦ hPp))
  have hQpb : IsPullback p Q.proj g Q.base.hom := Q.isPullback
  have hactD : ∀ {Z : Over T} (v' : Z ⟶ (Over.map g).obj (Over.mk p)) (x : Z ⟶ Over.mk g)
      (l : Z.left ⟶ pullback (p ≫ g) g), l ≫ pullback.fst (p ≫ g) g = v'.left →
      l ≫ pullback.snd (p ≫ g) g = x.left →
      ((DescentDatum.mk' (f := g) (Over.mk p) Φ hcocycle).act v' x).left =
        l ≫ sq1.isoPullback.inv ≫ φ.hom ≫ ρ2 := hact
  refine ⟨Q.base.left, Q.base.hom, Q.proj, hQpb, ?_, ?_⟩
  · refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (K := Scheme.fppfPrecoverage) (R := Presieve.singleton g)
      g.singleton_mem_fppfPrecoverage ?_
    intro U g' _ hg'
    cases hg'
    have h' : Pr (hQpb.flip.isoPullback.hom ≫ pullback.snd Q.base.hom g) := by
      rw [hQpb.flip.isoPullback_hom_snd]
      exact hPp
    exact (MorphismProperty.cancel_left_of_respectsIso Pr _ _).1 h'
  · intro Z z₁ z₂ hz hzψ
    have hx' : (z₂ ≫ p) ≫ g = (Over.mk (z₁ ≫ p ≫ g) : Over T).hom := hz.symm
    have hv' : z₁ ≫ ((Over.map g).obj (Over.mk p)).hom =
        (Over.mk (z₁ ≫ p ≫ g) : Over T).hom := rfl
    obtain ⟨L, hLf, hLs, hL'⟩ := hex z₁ (z₂ ≫ p) hz
    have hLψ : L ≫ sq1.isoPullback.inv ≫ φ.hom ≫ ρ2 = z₂ := by
      rw [← Category.assoc L sq1.isoPullback.inv (φ.hom ≫ ρ2), hL', hzψ]
    have hinv := DescentDatum.act_left_comp_of_transitionPullbackIso
      (DescentDatum.mk' (f := g) (Over.mk p) Φ hcocycle) Q.proj Q.proj_invariant
      (Z := Over.mk (z₁ ≫ p ≫ g)) (Over.homMk z₁ hv') (Over.homMk (z₂ ≫ p) hx')
    have hLf' : L ≫ pullback.fst (p ≫ g) g =
        (Over.homMk z₁ hv' :
          Over.mk (z₁ ≫ p ≫ g) ⟶ (Over.map g).obj (Over.mk p)).left := hLf
    have hLs' : L ≫ pullback.snd (p ≫ g) g =
        (Over.homMk (z₂ ≫ p) hx' : Over.mk (z₁ ≫ p ≫ g) ⟶ Over.mk g).left := hLs
    rw [hactD (Z := Over.mk (z₁ ≫ p ≫ g))
      (Over.homMk z₁ hv' : Over.mk (z₁ ≫ p ≫ g) ⟶ (Over.map g).obj (Over.mk p))
      (Over.homMk (z₂ ≫ p) hx' : Over.mk (z₁ ≫ p ≫ g) ⟶ Over.mk g) L hLf' hLs',
      hLψ] at hinv
    exact hinv.symm

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of schemes between the underlying schemes of two objects of the big fppf category
over `S` which is compatible with the structure morphisms is a morphism of that category.
Compatibility means that the morphism `z` composed with the image of some `n : t' ⟶ t''` is the
image of some `y : t ⟶ t''`. -/
private theorem exists_toScheme_map_eq {t t' t'' : BigFppfOver B S hS} {n : t' ⟶ t''}
    {y : t ⟶ t''}
    (z : (BigFppfOver.toScheme B S hS).obj t ⟶ (BigFppfOver.toScheme B S hS).obj t')
    (hz : z ≫ (BigFppfOver.toScheme B S hS).map n = (BigFppfOver.toScheme B S hS).map y) :
    ∃ ζ : t ⟶ t', (BigFppfOver.toScheme B S hS).map ζ = z := by
  refine ⟨Over.homMk (ObjectProperty.homMk z) ?_, rfl⟩
  apply ObjectProperty.hom_ext
  show z ≫ B.inclusion.map t'.hom = B.inclusion.map t.hom
  have hn : B.inclusion.map t'.hom =
      (BigFppfOver.toScheme B S hS).map n ≫ B.inclusion.map t''.hom := by
    show B.inclusion.map t'.hom = B.inclusion.map n.left ≫ B.inclusion.map t''.hom
    rw [← B.inclusion.map_comp, Over.w n]
  have hy : (BigFppfOver.toScheme B S hS).map y ≫ B.inclusion.map t''.hom =
      B.inclusion.map t.hom := by
    show B.inclusion.map y.left ≫ B.inclusion.map t''.hom = B.inclusion.map t.hom
    rw [← B.inclusion.map_comp, Over.w y]
  rw [hn, ← Category.assoc z ((BigFppfOver.toScheme B S hS).map n)
    (B.inclusion.map t''.hom), hz, hy]

/-- **Stacks 03I2, hypothesis (1) discharged.** Let `P` be a property of morphisms of schemes
which is preserved by arbitrary base change, is fppf local on the base, and is such that
morphisms with `P` satisfy descent for fppf coverings. Then morphisms with `P` descend
effectively along the surjective étale morphisms of the big fppf site of `S`.

This is the geometric content of the proof of Stacks 03I2, and the three hypotheses are exactly
hypothesis (1) of that tag. -/
theorem isEffectiveDescentAlongSurjectiveEtale_of_satisfiesDescent
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    (hP : SatisfiesDescent.{u, 0} P Scheme.fppfPrecoverage) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS P := by
  refine isEffectiveDescentAlongSurjectiveEtale_of_exists_isPullback_of_invariant ?_
  intro X Y f _hX _hY a c h q hqs hqe A m r sq hr
  obtain ⟨v, w, e, hwP, hew, P₁, P₂, π₁, π₂, ρ₁, ρ₂, s, φ, sq₁, sq₂, hsw, hsX, hφ₃, hφ₄⟩ :=
    exists_descentAction_of_isPullback sq hr
  have vsq : IsPullback (e.inv ≫ m) (yoneda.map w) f (yoneda.map q ≫ h) := by
    refine sq.of_iso e (Iso.refl X) (Iso.refl (yoneda.obj c)) (Iso.refl Y) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id, hew]
    · simp
    · simp
  have hπ₁ : φ.hom ≫ s = π₁ := by rw [← hφ₃, Iso.hom_inv_id_assoc]
  have hψwR : φ.hom ≫ ρ₂ ≫ w = π₂ := by rw [← hφ₄, Iso.hom_inv_id_assoc]
  have hψw : (φ.hom ≫ ρ₂) ≫ w = π₂ := by rw [Category.assoc, hψwR]
  have hψc : φ.hom ≫ ρ₁ = π₁ ≫ w := by rw [← hsw, ← hπ₁, Category.assoc]
  have hψX : ∀ {d : BigFppfOver B S hS} (ξ : d ⟶ P₁),
      yoneda.map (ξ ≫ φ.hom ≫ ρ₂) ≫ e.inv ≫ m = yoneda.map (ξ ≫ π₁) ≫ e.inv ≫ m := by
    intro d ξ
    rw [← hπ₁]
    simp only [Functor.map_comp, Category.assoc]
    rw [← hsX]
  have : Surjective ((BigFppfOver.toScheme B S hS).map q) := hqs
  have : Etale ((BigFppfOver.toScheme B S hS).map q) := hqe
  have sq₁S : IsPullback ((BigFppfOver.toScheme B S hS).map π₁)
      ((BigFppfOver.toScheme B S hS).map π₂)
      ((BigFppfOver.toScheme B S hS).map w ≫ (BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map q) := by
    simpa only [Functor.map_comp] using sq₁.map _
  have sq₂S : IsPullback ((BigFppfOver.toScheme B S hS).map ρ₁)
      ((BigFppfOver.toScheme B S hS).map ρ₂) ((BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map w ≫ (BigFppfOver.toScheme B S hS).map q) := by
    simpa only [Functor.map_comp] using sq₂.map _
  have hψS : ((BigFppfOver.toScheme B S hS).mapIso φ).hom ≫
      (BigFppfOver.toScheme B S hS).map ρ₂ =
        (BigFppfOver.toScheme B S hS).map (φ.hom ≫ ρ₂) := by
    show (BigFppfOver.toScheme B S hS).map φ.hom ≫ _ = _
    rw [← Functor.map_comp]
  have hφ1S : ((BigFppfOver.toScheme B S hS).mapIso φ).hom ≫
      (BigFppfOver.toScheme B S hS).map ρ₁ =
        (BigFppfOver.toScheme B S hS).map π₁ ≫ (BigFppfOver.toScheme B S hS).map w := by
    show (BigFppfOver.toScheme B S hS).map φ.hom ≫ _ = _
    rw [← Functor.map_comp, hψc, Functor.map_comp]
  have hφ2S : (((BigFppfOver.toScheme B S hS).mapIso φ).hom ≫
      (BigFppfOver.toScheme B S hS).map ρ₂) ≫ (BigFppfOver.toScheme B S hS).map w =
        (BigFppfOver.toScheme B S hS).map π₂ := by
    rw [hψS, ← Functor.map_comp, hψw]
  have hassoc : ∀ ⦃Z : Scheme.{u}⦄ (ξ : Z ⟶ (BigFppfOver.toScheme B S hS).obj P₁)
      (y : Z ⟶ (BigFppfOver.toScheme B S hS).obj c)
      (h₁ : (ξ ≫ ((BigFppfOver.toScheme B S hS).mapIso φ).hom ≫
          (BigFppfOver.toScheme B S hS).map ρ₂) ≫
        (BigFppfOver.toScheme B S hS).map w ≫ (BigFppfOver.toScheme B S hS).map q =
          y ≫ (BigFppfOver.toScheme B S hS).map q)
      (h₂ : (ξ ≫ (BigFppfOver.toScheme B S hS).map π₁) ≫
        (BigFppfOver.toScheme B S hS).map w ≫ (BigFppfOver.toScheme B S hS).map q =
          y ≫ (BigFppfOver.toScheme B S hS).map q),
      sq₁S.lift (ξ ≫ ((BigFppfOver.toScheme B S hS).mapIso φ).hom ≫
          (BigFppfOver.toScheme B S hS).map ρ₂) y h₁ ≫
          ((BigFppfOver.toScheme B S hS).mapIso φ).hom ≫
          (BigFppfOver.toScheme B S hS).map ρ₂ =
        sq₁S.lift (ξ ≫ (BigFppfOver.toScheme B S hS).map π₁) y h₂ ≫
          ((BigFppfOver.toScheme B S hS).mapIso φ).hom ≫
          (BigFppfOver.toScheme B S hS).map ρ₂ := by
    have sq₃ : IsPullback (pullback.fst (π₂ ≫ q) q) (pullback.snd (π₂ ≫ q) q) (π₂ ≫ q) q :=
      IsPullback.of_hasPullback _ _
    have sq₃S : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst (π₂ ≫ q) q))
        ((BigFppfOver.toScheme B S hS).map (pullback.snd (π₂ ≫ q) q))
        ((BigFppfOver.toScheme B S hS).map π₂ ≫ (BigFppfOver.toScheme B S hS).map q)
        ((BigFppfOver.toScheme B S hS).map q) := by
      simpa only [Functor.map_comp] using sq₃.map _
    intro Z ξ y h₁ h₂
    have hc : ξ ≫ (BigFppfOver.toScheme B S hS).map π₂ ≫
        (BigFppfOver.toScheme B S hS).map q = y ≫ (BigFppfOver.toScheme B S hS).map q := by
      rw [← hφ2S]
      simpa only [Category.assoc] using h₁
    obtain ⟨ξ₃, hξ₃1, hξ₃2⟩ : ∃ ξ₃ : Z ⟶ (BigFppfOver.toScheme B S hS).obj
        (Limits.pullback (π₂ ≫ q) q),
        ξ₃ ≫ (BigFppfOver.toScheme B S hS).map (pullback.fst (π₂ ≫ q) q) = ξ ∧
          ξ₃ ≫ (BigFppfOver.toScheme B S hS).map (pullback.snd (π₂ ≫ q) q) = y :=
      ⟨sq₃S.lift ξ y hc, sq₃S.lift_fst _ _ hc, sq₃S.lift_snd _ _ hc⟩
    have key : ∀ (α : P₁ ⟶ v)
        (hα : (pullback.fst (π₂ ≫ q) q ≫ α) ≫ w ≫ q = pullback.snd (π₂ ≫ q) q ≫ q)
        (h : (ξ ≫ (BigFppfOver.toScheme B S hS).map α) ≫ (BigFppfOver.toScheme B S hS).map w ≫
          (BigFppfOver.toScheme B S hS).map q = y ≫ (BigFppfOver.toScheme B S hS).map q),
        ∃ ll : Limits.pullback (π₂ ≫ q) q ⟶ P₁, ll ≫ π₁ = pullback.fst (π₂ ≫ q) q ≫ α ∧
          ll ≫ π₂ = pullback.snd (π₂ ≫ q) q ∧
          sq₁S.lift (ξ ≫ (BigFppfOver.toScheme B S hS).map α) y h =
            ξ₃ ≫ (BigFppfOver.toScheme B S hS).map ll := by
      intro α hα h
      refine ⟨sq₁.lift _ _ hα, sq₁.lift_fst _ _ hα, sq₁.lift_snd _ _ hα, sq₁S.hom_ext ?_ ?_⟩
      · rw [sq₁S.lift_fst, Category.assoc, ← Functor.map_comp, sq₁.lift_fst, Functor.map_comp,
          ← Category.assoc ξ₃, hξ₃1]
      · rw [sq₁S.lift_snd, Category.assoc, ← Functor.map_comp, sq₁.lift_snd, hξ₃2]
    obtain ⟨ll, hlπ₁, hlπ₂, hA⟩ := key (φ.hom ≫ ρ₂)
      (by rw [Category.assoc _ (φ.hom ≫ ρ₂) (w ≫ q), ← Category.assoc (φ.hom ≫ ρ₂) w q, hψw]
          exact sq₃.w) h₁
    obtain ⟨ll', hl'π₁, hl'π₂, hBb⟩ := key π₁
      (by rw [Category.assoc, sq₁.w]; exact sq₃.w) h₂
    have hll' : ll ≫ φ.hom ≫ ρ₂ = ll' ≫ φ.hom ≫ ρ₂ := by
      refine descentAction_unique vsq ?_ ?_
      · simp only [Category.assoc, hψwR]
        rw [hlπ₂, hl'π₂]
      · rw [hψX ll, hψX ll', hlπ₁, hl'π₁]
        exact hψX (pullback.fst (π₂ ≫ q) q)
    erw [hA, hBb]
    rw [hψS, Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      hll']
  obtain ⟨W₀, i₀, k₀, hpb, hPi₀, hinv₀⟩ := exists_descended_of_actionAssoc
    ((BigFppfOver.toScheme B S hS).mapIso φ) sq₁S sq₂S hφ1S hφ2S hassoc hwP hP
  have : Surjective k₀ := MorphismProperty.of_isPullback hpb inferInstance
  have : Flat k₀ := MorphismProperty.of_isPullback hpb inferInstance
  have hQc : B.Contains W₀ := B.contains_of_flat_surjective k₀ v.left.property
  have hkover : k₀ ≫ i₀ ≫ B.inclusion.map a.hom = B.inclusion.map v.hom := by
    rw [← Category.assoc k₀ i₀ (B.inclusion.map a.hom), ← hpb.w]
    show B.inclusion.map w.left ≫ B.inclusion.map q.left ≫ B.inclusion.map a.hom = _
    rw [← B.inclusion.map_comp, Over.w q, ← B.inclusion.map_comp]
    exact congrArg B.inclusion.map (Over.w w)
  refine ⟨Over.mk (ObjectProperty.homMk (X := B.obj hQc) (i₀ ≫ B.inclusion.map a.hom)), v,
    Over.homMk (ObjectProperty.homMk (X := B.obj hQc) i₀)
      (by apply ObjectProperty.hom_ext; rfl),
    Over.homMk (ObjectProperty.homMk (Y := B.obj hQc) k₀)
      (by apply ObjectProperty.hom_ext; exact hkover), w, hPi₀, ?_, e, hew, ?_⟩
  · exact IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) hpb.flip
  · intro W' ζ₁ ζ₂ hζX hζa
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp]
    show (BigFppfOver.toScheme B S hS).map ζ₁ ≫ k₀ =
      (BigFppfOver.toScheme B S hS).map ζ₂ ≫ k₀
    have hzo : (BigFppfOver.toScheme B S hS).map ζ₁ ≫
        (BigFppfOver.toScheme B S hS).map w ≫ (BigFppfOver.toScheme B S hS).map q =
        ((BigFppfOver.toScheme B S hS).map ζ₂ ≫
          (BigFppfOver.toScheme B S hS).map w) ≫ (BigFppfOver.toScheme B S hS).map q := by
      rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (BigFppfOver.toScheme B S hS).map hζa
    refine hinv₀ _ _ hzo ?_
    obtain ⟨ξ, hξ⟩ := exists_toScheme_map_eq (n := π₂) (y := ζ₂ ≫ w)
      (sq₁S.lift ((BigFppfOver.toScheme B S hS).map ζ₁)
        ((BigFppfOver.toScheme B S hS).map ζ₂ ≫ (BigFppfOver.toScheme B S hS).map w) hzo)
      (by rw [sq₁S.lift_snd, Functor.map_comp])
    have hξπ₁ : ξ ≫ π₁ = ζ₁ := by
      refine (BigFppfOver.toScheme B S hS).map_injective ?_
      rw [Functor.map_comp, hξ, sq₁S.lift_fst]
    have hξπ₂ : ξ ≫ π₂ = ζ₂ ≫ w := by
      refine (BigFppfOver.toScheme B S hS).map_injective ?_
      rw [Functor.map_comp, hξ, sq₁S.lift_snd, Functor.map_comp]
    have hξψ : ξ ≫ φ.hom ≫ ρ₂ = ζ₂ := by
      refine descentAction_unique vsq ?_ ?_
      · rw [Category.assoc ξ (φ.hom ≫ ρ₂) w, Category.assoc φ.hom ρ₂ w, hψwR]
        exact hξπ₂
      · rw [hψX ξ, hξπ₁]
        exact hζX
    rw [← hξ, hψS, ← Functor.map_comp, hξψ]

/-- **Stacks 03I2.** Let `S` be a scheme contained in a big fppf site and let `P` be a property
of morphisms of schemes which is preserved by arbitrary base change, is fppf local on the base,
and is such that morphisms with `P` satisfy descent for fppf coverings. Let `f : X ⟶ Y` be a
morphism of presheaves on the big fppf site of `S` with `X` a sheaf and `Y` an algebraic space
over `S`, and suppose some surjective étale chart `g : yoneda.obj U ⟶ Y` of `Y` makes the base
change of `f` representable with `P`. Then `X` is an algebraic space over `S`, and `f` is
representable and has `P`.

The three conclusions of the source are the two conjuncts: the second,
`(P.inverseImage _).presheaf f`, is representability of `f` together with `P` for every
represented base change of it. -/
@[stacks 03I2]
theorem isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    (hP : SatisfiesDescent.{u, 0} P Scheme.fppfPrecoverage)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ Y}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hV : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g)) :
    IsAlgebraicSpace B S hS X ∧
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f :=
  isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent
    (isEffectiveDescentAlongSurjectiveEtale_of_satisfiesDescent hP) hX hY hs he hV

end Space

end AlgebraicGeometry
