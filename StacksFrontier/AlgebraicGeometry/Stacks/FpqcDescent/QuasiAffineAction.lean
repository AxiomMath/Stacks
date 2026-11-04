module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleDescentFromFppfDescent
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFpqcDescent

/-!
# Effective fpqc descent of a quasi-affine morphism presented by an associative action

A quasi-affine morphism `p : V ⟶ C` together with an
isomorphism `V ×_T C ≅ C ×_T V` over `C ×_T C` whose action is associative descends along a
surjective, flat, quasi-compact `g : C ⟶ T`.

## Main results

* `AlgebraicGeometry.exists_descended_of_actionAssoc_of_isQuasiAffineHom`: a quasi-affine morphism
  with an associative action descends along a surjective, flat, quasi-compact morphism.

## References

* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 0GRH](https://stacks.math.columbia.edu/tag/0GRH)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Effective fpqc descent of a quasi-affine morphism, from an isomorphism of fibre products
and the associativity of its action.** Let `g : C ⟶ T` be surjective, flat and quasi-compact,
let `p : V ⟶ C` be quasi-affine, and let `φ : V ×_T C ≅ C ×_T V` be an isomorphism over
`C ×_T C` whose action is associative. Then there are a scheme `W` over `T` and a Cartesian square
exhibiting `V` as `C ×_T W` whose projection `V ⟶ W` is invariant under the action. -/
theorem exists_descended_of_actionAssoc_of_isQuasiAffineHom {T C V W₁ W₂ : Scheme.{u}}
    {g : C ⟶ T} {p : V ⟶ C} {pi1 : W₁ ⟶ V} {pi2 : W₁ ⟶ C} {ρ1 : W₂ ⟶ C} {ρ2 : W₂ ⟶ V}
    [Surjective g] [Flat g] [QuasiCompact g]
    (φ : W₁ ≅ W₂) (sq1 : IsPullback pi1 pi2 (p ≫ g) g) (sq2 : IsPullback ρ1 ρ2 g (p ≫ g))
    (hφ1 : φ.hom ≫ ρ1 = pi1 ≫ p) (hφ2 : (φ.hom ≫ ρ2) ≫ p = pi2)
    (hassoc : ∀ ⦃Z : Scheme.{u}⦄ (ξ : Z ⟶ W₁) (y : Z ⟶ C)
      (h₁ : (ξ ≫ φ.hom ≫ ρ2) ≫ p ≫ g = y ≫ g) (h₂ : (ξ ≫ pi1) ≫ p ≫ g = y ≫ g),
      sq1.lift (ξ ≫ φ.hom ≫ ρ2) y h₁ ≫ φ.hom ≫ ρ2 =
        sq1.lift (ξ ≫ pi1) y h₂ ≫ φ.hom ≫ ρ2)
    (hp : IsQuasiAffineHom p) :
    ∃ (W : Scheme.{u}) (i : W ⟶ T) (k : V ⟶ W),
      IsPullback p k g i ∧
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
  have hlift : ∀ {Z : Over T} (v' : Z ⟶ (Over.map g).obj (Over.mk p)) (x : Z ⟶ Over.mk g),
      v'.left ≫ p ≫ g = x.left ≫ g := by
    intro Z v' x
    rw [← Category.assoc v'.left p g]
    exact (Over.w v').trans (Over.w x).symm
  have hact : ∀ {Z : Over T} (v' : Z ⟶ (Over.map g).obj (Over.mk p)) (x : Z ⟶ Over.mk g),
      (gluingAction (Over.mk p) Φ.hom.left v' x).left =
        sq1.lift v'.left x.left (hlift v' x) ≫ φ.hom ≫ ρ2 := by
    intro Z v' x
    have hL : pullback.lift v'.left x.left (hlift v' x) ≫ sq1.isoPullback.inv =
        sq1.lift v'.left x.left (hlift v' x) := by
      refine sq1.hom_ext ?_ ?_
      · rw [Category.assoc, hi1, pullback.lift_fst, sq1.lift_fst]
      · rw [Category.assoc, hi2, pullback.lift_snd, sq1.lift_snd]
    rw [hactl v' x _ (pullback.lift_fst _ _ (hlift v' x))
      (pullback.lift_snd _ _ (hlift v' x)), hΘψ,
      ← Category.assoc, hL]
  have hcocycle : prod.map Φ.hom.left (𝟙 (Over.mk g)) ≫ prodMapLastTwo Φ.hom.left =
      prodMapFirstThird Φ.hom.left := by
    refine (cocycle_iff_gluingAction_act_act (Over.mk p) Φ.hom.left h1 h2).mpr ?_
    intro Z v' x y
    refine Over.OverMorphism.ext ?_
    have hcond₁ : (sq1.lift v'.left x.left (hlift v' x) ≫ φ.hom ≫ ρ2) ≫ p ≫ g =
        y.left ≫ g := by
      rw [← hact v' x]
      exact hlift (gluingAction (Over.mk p) Φ.hom.left v' x) y
    have hcond₂ : (sq1.lift v'.left x.left (hlift v' x) ≫ pi1) ≫ p ≫ g = y.left ≫ g := by
      rw [sq1.lift_fst]
      exact hlift v' y
    rw [hact (gluingAction (Over.mk p) Φ.hom.left v' x) y, hact v' y]
    have hc : ∀ {Z : Scheme} {a a' : Z ⟶ V} {b : Z ⟶ C} (h : a ≫ p ≫ g = b ≫ g)
        (h' : a' ≫ p ≫ g = b ≫ g), a = a' → sq1.lift a b h = sq1.lift a' b h' := by
      rintro _ _ _ _ _ _ rfl
      rfl
    exact (congrArg (· ≫ φ.hom ≫ ρ2) (hc _ _ (hact v' x))).trans
      ((hassoc _ y.left hcond₁ hcond₂).trans
        (congrArg (· ≫ φ.hom ≫ ρ2) (hc _ _ (sq1.lift_fst _ _ _))))
  have hcov : Presieve.ofArrows (fun _ : Unit ↦ C) (fun _ ↦ g) ∈ Scheme.fpqcPrecoverage T := by
    rw [Presieve.ofArrows_pUnit]
    exact g.singleton_mem_fpqcPrecoverage
  obtain ⟨Q⟩ := DescentDatum.nonempty_descended_of_isEffective
    (DescentData.isEffective_of_isFamilyEffective
      (DescentData.isFamilyEffective_of_isQuasiAffineHom (fun _ : Unit ↦ g) hcov
        (DescentDatum.mk' (Over.mk p) Φ hcocycle) fun _ ↦ hp))
  have hactD : ∀ {Z : Over T} (v' : Z ⟶ (Over.map g).obj (Over.mk p)) (x : Z ⟶ Over.mk g),
      ((DescentDatum.mk' (f := g) (Over.mk p) Φ hcocycle).act v' x).left =
        sq1.lift v'.left x.left (hlift v' x) ≫ φ.hom ≫ ρ2 := hact
  refine ⟨Q.base.left, Q.base.hom, Q.proj, Q.isPullback, ?_⟩
  intro Z z₁ z₂ hz hzψ
  have hx' : (z₂ ≫ p) ≫ g = (Over.mk (z₁ ≫ p ≫ g) : Over T).hom := hz.symm
  have hv' : z₁ ≫ ((Over.map g).obj (Over.mk p)).hom =
      (Over.mk (z₁ ≫ p ≫ g) : Over T).hom := rfl
  have hinv := DescentDatum.act_left_comp_of_transitionPullbackIso
    (DescentDatum.mk' (f := g) (Over.mk p) Φ hcocycle) Q.proj Q.proj_invariant
    (Z := Over.mk (z₁ ≫ p ≫ g)) (Over.homMk z₁ hv') (Over.homMk (z₂ ≫ p) hx')
  rw [hactD (Over.homMk z₁ hv' : Over.mk (z₁ ≫ p ≫ g) ⟶ (Over.map g).obj (Over.mk p))
    (Over.homMk (z₂ ≫ p) hx' : Over.mk (z₁ ≫ p ≫ g) ⟶ Over.mk g)] at hinv
  erw [hzψ] at hinv
  exact hinv.symm

end AlgebraicGeometry

end
