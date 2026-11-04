module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PointTransitionComp

/-!
# The transitions along points at identity arrows

For a quasi-coherent module `(ℱ, α)` on a groupoid in algebraic spaces (Stacks 0441), `α` read
along an arrow which is an identity arrow, `r = e ∘ a`, is the identification of the two equal
endpoints: this is the unit condition of Stacks 0441 reindexed along `a`. Consequently the
transition along points at an identity arrow is the comparison of Stacks 03LU followed by a
transport, which is the remark of the proof of Stacks 06WT that along a special morphism the
restriction map is just pullback.

## Main results

* `AlgebraicGeometry.Space.transitionTwist_of_eq_comp_identityArrow`: `α` along an identity arrow
  is a transport.
* `AlgebraicGeometry.Space.pointTransition_of_eq_comp_identityArrow`: the transition along points
  at an identity arrow.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
-/

@[expose] public noncomputable section

open CategoryTheory

open Stacks.AlgebraicGeometry.EquivariantQuasicoherentPullback

universe u

namespace AlgebraicGeometry.Space

open GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

section Shapes

variable {D : Type*} [Category D]

/-- The shape of the unit law along a factored arrow. -/
theorem comp₃_eq_of_sandwich {P₀ P₁ P₂ P₃ Q₀ Q₃ : D} (u₁ : P₀ ⟶ P₁) (X : P₁ ⟶ P₂) (u₂ : P₂ ⟶ P₃)
    (v₁ : Q₀ ⟶ P₁) (v₂ : P₂ ⟶ Q₃) (w : Q₀ ⟶ Q₃) (a₁ : P₀ ⟶ Q₀) (b₂ : Q₃ ⟶ P₃) {z : P₀ ⟶ P₃}
    (h : comp₃ v₁ X v₂ = w) (ha : a₁ ≫ v₁ = u₁) (hb : v₂ ≫ b₂ = u₂) (hz : a₁ ≫ w ≫ b₂ = z) :
    comp₃ u₁ X u₂ = z := by
  rw [← hz, ← h, ← ha, ← hb]
  simp [comp₃]

end Shapes

/-- Twisted transitions along equal arrows agree. -/
theorem transitionTwist_congr {U V W : AlgebraicSpaces C S hS}
    (F : Modules.{u, u} C S hS U.1 U.2) {a b : V ⟶ U}
    (α : (modulePullback C S hS a).obj F ⟶ (modulePullback C S hS b).obj F)
    {x y : W ⟶ U} {r r' : W ⟶ V} (hr : r = r') (hx : r ≫ b = x) (hy : r ≫ a = y)
    (hx' : r' ≫ b = x) (hy' : r' ≫ a = y) :
    transitionTwist F α r hx hy = transitionTwist F α r' hx' hy' := by
  subst hr
  rfl

/-- **A transition read along an arrow factoring through a unit is a transport**, for any
transition satisfying the unit law at that unit. -/
theorem transitionTwist_comp_of_unit {U V W Y : AlgebraicSpaces C S hS}
    (F : Modules.{u, u} C S hS U.1 U.2) {a b : V ⟶ U}
    (α : (modulePullback C S hS a).obj F ⟶ (modulePullback C S hS b).obj F)
    (e : Y ⟶ V) (h₀ : e ≫ a = e ≫ b)
    (hunit : transitionReindex C S hS F α e = pullbackTransport F h₀)
    (c : W ⟶ Y) {x y : W ⟶ U} (hx : (c ≫ e) ≫ b = x) (hy : (c ≫ e) ≫ a = y) (hyx : y = x) :
    transitionTwist F α (c ≫ e) hx hy = pullbackTransport F hyx := by
  have t : transitionTwist F α (c ≫ e) hx hy = comp₃ (pullbackTransport F hy.symm)
      (transitionReindex C S hS F α (c ≫ e)) (pullbackTransport F hx) := rfl
  have h₁ := transitionReindex_comp_transport F α c e
  have h₂ : transitionReindex C S hS F (transitionReindex C S hS F α e) c =
      pullbackTransport F (congrArg (c ≫ ·) h₀) :=
    (congrArg (fun φ => transitionReindex C S hS F φ c) hunit).trans
      (transitionReindex_pullbackTransport C S hS F h₀ c)
  have hy₁ : y = c ≫ e ≫ a := hy.symm.trans (Category.assoc c e a)
  have hx₁ : c ≫ e ≫ b = x := (Category.assoc c e b).symm.trans hx
  refine t.trans (comp₃_eq_of_sandwich _ _ _ _ _ _ (pullbackTransport F hy₁)
    (pullbackTransport F hx₁) (h₁.symm.trans h₂)
    (pullbackTransport_comp F hy₁ (Category.assoc c e a).symm hy.symm)
    (pullbackTransport_comp F (Category.assoc c e b) hx₁ hx) ?_)
  rw [pullbackTransport_comp F (congrArg (c ≫ ·) h₀) hx₁ (h₀ ▸ hx₁ :),
    pullbackTransport_comp F hy₁ _ hyx]

variable {A : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS A}
  (M : QuasicoherentModule C S hS G)

/-- **`α` along an identity arrow is a transport**: the unit condition of Stacks 0441. -/
theorem transitionTwist_of_eq_comp_identityArrow {W : AlgebraicSpaces C S hS}
    {x y : W ⟶ G.objects} (c : W ⟶ G.objects) (r : W ⟶ G.arrows)
    (hr : r = c ≫ identityArrow G) (hx : r ≫ G.source = x) (hy : r ≫ G.target = y)
    (hyx : y = x) :
    transitionTwist M.F.obj M.alpha r hx hy = pullbackTransport M.F.obj hyx :=
  have hx' : (c ≫ identityArrow G) ≫ G.source = x := hr ▸ hx
  have hy' : (c ≫ identityArrow G) ≫ G.target = y := hr ▸ hy
  (transitionTwist_congr M.F.obj M.alpha hr hx hy hx' hy').trans
    (transitionTwist_comp_of_unit M.F.obj M.alpha (identityArrow G)
      ((identityArrow_comp_target G).trans (identityArrow_comp_source G).symm) M.unit c hx' hy' hyx)

/-- **The transition along points at an identity arrow** is the comparison of Stacks 03LU
followed by the identification of the two equal endpoints. -/
theorem pointTransition_of_eq_comp_identityArrow {X X' : AlgebraicSpaces C S hS} (f : X' ⟶ X)
    (a : X ⟶ G.objects) {a' : X' ⟶ G.objects} (r : X' ⟶ G.arrows) (hs : r ≫ G.source = a')
    (ht : r ≫ G.target = f ≫ a) (hr : r = a' ≫ identityArrow G) (hfa : f ≫ a = a') :
    pointTransition M f a r hs ht =
      comp₃ ((modulePullbackCompIso C S hS f a).app M.F.obj).hom
        (pullbackTransport M.F.obj hfa) (𝟙 _) := by
  have t : pointTransition M f a r hs ht =
      comp₃ ((modulePullbackCompIso C S hS f a).app M.F.obj).hom
        (transitionTwist M.F.obj M.alpha r hs ht) (𝟙 _) := rfl
  rw [t, transitionTwist_of_eq_comp_identityArrow M a' r hr hs ht hfa]

end AlgebraicGeometry.Space

end
