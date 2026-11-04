module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TransitionReindexComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantQuasicoherentPullback

/-!
# Transition morphisms of a quasi-coherent module on a groupoid along points

Let `(ℱ, α)` be a quasi-coherent module on a groupoid `(U, R, s, t, c)` in algebraic spaces
(Stacks 0441). A morphism `r : X ⟶ R` of algebraic spaces with `s ∘ r = a` and `t ∘ r = b` is an
`X`-valued arrow from `a` to `b`, and `α` read along it is a morphism `b^*ℱ ⟶ a^*ℱ`
(`AlgebraicGeometry.Space.transitionTwist`, defined for any transition morphism between two
inverse images). Combined with the comparison of Stacks 03LU it gives, for
an arrow `r` from `a'` to `f ∘ a` over a morphism `f : X' ⟶ X`, the morphism
`f^*(a^*ℱ) ⟶ a'^*ℱ` (`AlgebraicGeometry.Space.pointTransition`). These are the restriction maps
of the module that `(ℱ, α)` defines on the points of `U`, which is the module of the proof of
Stacks 06WT on the pointwise quotient `[U/_pR]`, and the main result of this file is their
cocycle law: along a composite of arrows the transition is the composite of the transitions
(`AlgebraicGeometry.Space.transitionReindex_transitionTwist_comp_groupoid`). It is the cocycle
condition of Stacks 0441 reindexed along the classifying map of the pair of arrows into
`R ×_{s, U, t} R`.

## Main definitions

* `AlgebraicGeometry.Space.transitionTwist`: `α` read along an `X`-valued arrow.
* `AlgebraicGeometry.Space.pointTransition`: the transition `f^*(a^*ℱ) ⟶ a'^*ℱ`.

## Main results

* `AlgebraicGeometry.Space.transitionReindex_transitionTwist_comp`: the cocycle law for
  `transitionTwist`, for any transition morphism satisfying the cocycle law at a triple.
* `AlgebraicGeometry.Space.transitionReindex_transitionTwist_comp_groupoid`: the same for the
  transition morphism of a quasi-coherent module on a groupoid, at any pair of composable arrows.

## Implementation notes

Every equation between composites of morphisms of algebraic spaces underneath an inverse image
is kept out of definitional unfolding: closing such a goal by `simp` or by a substituted generic
lemma makes the kernel reconcile `f ≫ g ≫ a` with `(f ≫ g) ≫ a` inside `modulePullback` and
time out. The proofs instead normalise both sides with the category-generic lemmas of the
section `Shapes`, whose hypotheses are instances of
`Stacks.AlgebraicGeometry.EquivariantQuasicoherentPullback.pullbackTransport_comp`, and conclude
by `Eq.trans` between syntactically equal terms.

## References

* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
-/

@[expose] public noncomputable section

open CategoryTheory

open Stacks.AlgebraicGeometry.EquivariantQuasicoherentPullback

universe u

namespace AlgebraicGeometry.Space

open GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- Reindexing along `f` and then along `k` is reindexing along `k ≫ f`, with the two inverse
images identified along the associativity of composition, so that both sides have the same
type on the nose. -/
theorem transitionReindex_comp_transport {U V W W' : AlgebraicSpaces C S hS}
    (F : Modules.{u, u} C S hS U.1 U.2) {a b : V ⟶ U}
    (α : (modulePullback C S hS a).obj F ⟶ (modulePullback C S hS b).obj F)
    (k : W' ⟶ W) (f : W ⟶ V) :
    transitionReindex C S hS F (transitionReindex C S hS F α f) k =
      comp₃ (pullbackTransport F (Category.assoc k f a).symm)
        (transitionReindex C S hS F α (k ≫ f)) (pullbackTransport F (Category.assoc k f b)) := by
  rw [transitionReindex_comp]
  simp [comp₃, pullbackTransport]

section Shapes

variable {D : Type*} [Category D]

/-- Two runs of morphisms around a morphism merge. -/
theorem comp₃_merge {X₁ X₂ X₃ X₄ X₅ X₆ : D} (h₁ : X₁ ⟶ X₂) (h₂ : X₂ ⟶ X₃) (φ : X₃ ⟶ X₄)
    (h₃ : X₄ ⟶ X₅) (h₄ : X₅ ⟶ X₆) {h₅ : X₁ ⟶ X₃} {h₆ : X₄ ⟶ X₆} (e : h₁ ≫ h₂ = h₅)
    (e' : h₃ ≫ h₄ = h₆) :
    comp₃ h₁ (comp₃ h₂ φ h₃) h₄ = comp₃ h₅ φ h₆ := by
  rw [← e, ← e']
  simp [comp₃]

/-- The left-hand side of the cocycle law, in normal form. -/
theorem comp₃_comp_comp₃_shape {X₁ X₂ X₃ X₄ X₅ X₆ X₇ : D} (A : X₁ ⟶ X₂) (φ : X₂ ⟶ X₃)
    (Bh : X₃ ⟶ X₄) (Ch : X₄ ⟶ X₅) (ψ : X₅ ⟶ X₆) (Dh : X₆ ⟶ X₇) {BC : X₃ ⟶ X₅}
    (e : Bh ≫ Ch = BC) :
    comp₃ A φ Bh ≫ comp₃ Ch ψ Dh = A ≫ φ ≫ BC ≫ ψ ≫ Dh := by
  rw [← e]
  simp [comp₃]

/-- The right-hand side of the cocycle law, in normal form. -/
theorem comp₃_nested_shape {Y₀ Y₁ X₂ X₃ X₅ X₆ Y₆ X₇ : D} (h₀ : Y₀ ⟶ Y₁) (h₁ : Y₁ ⟶ X₂)
    (φ : X₂ ⟶ X₃) (m : X₃ ⟶ X₅) (ψ : X₅ ⟶ X₆) (h₂ : X₆ ⟶ Y₆) (h₃ : Y₆ ⟶ X₇)
    {h₀₁ : Y₀ ⟶ X₂} {h₂₃ : X₆ ⟶ X₇} (e : h₀ ≫ h₁ = h₀₁) (e' : h₂ ≫ h₃ = h₂₃) :
    comp₃ h₀ (comp₃ h₁ (comp₃ φ m ψ) h₂) h₃ = h₀₁ ≫ φ ≫ m ≫ ψ ≫ h₂₃ := by
  rw [← e, ← e']
  simp [comp₃]

end Shapes

section Generic

variable {U V : AlgebraicSpaces C S hS} (F : Modules.{u, u} C S hS U.1 U.2) {a b : V ⟶ U}
  (α : (modulePullback C S hS a).obj F ⟶ (modulePullback C S hS b).obj F)

/-- A transition morphism `α : a^*ℱ ⟶ b^*ℱ` read along `r : W ⟶ V`, with the endpoints `r ≫ a`
and `r ≫ b` renamed. -/
def transitionTwist {W : AlgebraicSpaces C S hS} {x y : W ⟶ U} (r : W ⟶ V)
    (hx : r ≫ b = x) (hy : r ≫ a = y) :
    (modulePullback C S hS y).obj F ⟶ (modulePullback C S hS x).obj F :=
  comp₃ (pullbackTransport F hy.symm) (transitionReindex C S hS F α r) (pullbackTransport F hx)

/-- A twisted transition unfolds to its `comp₃` of transports around the reindexed one. -/
private theorem transitionTwist_eq_comp₃ {W : AlgebraicSpaces C S hS} {x y : W ⟶ U} (r : W ⟶ V)
    (hx : r ≫ b = x) (hy : r ≫ a = y) :
    transitionTwist F α r hx hy = comp₃ (pullbackTransport F hy.symm)
      (transitionReindex C S hS F α r) (pullbackTransport F hx) := rfl

/-- Reindexing a twisted transition along `f₁`. -/
theorem transitionReindex_transitionTwist {W W' : AlgebraicSpaces C S hS} (f₁ : W' ⟶ W)
    {x₂ y₂ : W ⟶ U} (r₂ : W ⟶ V) (hx₂ : r₂ ≫ b = x₂) (hy₂ : r₂ ≫ a = y₂)
    (e₁ : f₁ ≫ y₂ = (f₁ ≫ r₂) ≫ a) (e₂ : (f₁ ≫ r₂) ≫ b = f₁ ≫ x₂) :
    transitionReindex C S hS F (transitionTwist F α r₂ hx₂ hy₂) f₁ =
      comp₃ (pullbackTransport F e₁) (transitionReindex C S hS F α (f₁ ≫ r₂))
        (pullbackTransport F e₂) := by
  rw [transitionTwist, transitionReindex_comp₃, transitionReindex_pullbackTransport,
    transitionReindex_pullbackTransport, transitionReindex_comp_transport]
  exact comp₃_merge _ _ _ _ _ (pullbackTransport_comp F _ _ e₁) (pullbackTransport_comp F _ _ e₂)

/-- **The cocycle law for twisted transitions**, generically. -/
theorem transitionReindex_transitionTwist_comp {W W' : AlgebraicSpaces C S hS} (f₁ : W' ⟶ W)
    {x₂ y₂ : W ⟶ U} {x₁ : W' ⟶ U} (r₂ : W ⟶ V) (hx₂ : r₂ ≫ b = x₂) (hy₂ : r₂ ≫ a = y₂)
    (r₁ : W' ⟶ V) (hx₁ : r₁ ≫ b = x₁) (hy₁ : r₁ ≫ a = f₁ ≫ x₂)
    (r : W' ⟶ V) (hx : r ≫ b = x₁) (hy : r ≫ a = f₁ ≫ y₂)
    (hcoc : TransitionCocycle C S hS F α (f₁ ≫ r₂) r₁ r) :
    transitionReindex C S hS F (transitionTwist F α r₂ hx₂ hy₂) f₁ ≫
        transitionTwist F α r₁ hx₁ hy₁ =
      transitionTwist F α r hx hy := by
  have ht' : r ≫ a = (f₁ ≫ r₂) ≫ a := by
    rw [hy, ← hy₂]; exact (Category.assoc _ _ _).symm
  have hm' : (f₁ ≫ r₂) ≫ b = r₁ ≫ a := by
    rw [hy₁, ← hx₂]; exact Category.assoc _ _ _
  have hs' : r ≫ b = r₁ ≫ b := hx.trans hx₁.symm
  have e₁ : f₁ ≫ y₂ = (f₁ ≫ r₂) ≫ a := hy.symm.trans ht'
  have e₂ : (f₁ ≫ r₂) ≫ b = f₁ ≫ x₂ := hm'.trans hy₁
  have h₁ := congrArg (· ≫ transitionTwist F α r₁ hx₁ hy₁)
    (transitionReindex_transitionTwist F α f₁ r₂ hx₂ hy₂ e₁ e₂)
  have h₂ := congrArg (comp₃ (pullbackTransport F e₁) (transitionReindex C S hS F α (f₁ ≫ r₂))
    (pullbackTransport F e₂) ≫ ·) (transitionTwist_eq_comp₃ F α r₁ hx₁ hy₁)
  have h₃ := comp₃_comp_comp₃_shape (pullbackTransport F e₁)
    (transitionReindex C S hS F α (f₁ ≫ r₂)) (pullbackTransport F e₂)
    (pullbackTransport F hy₁.symm) (transitionReindex C S hS F α r₁)
    (pullbackTransport F hx₁) (pullbackTransport_comp F e₂ hy₁.symm hm')
  have hc : transitionReindex C S hS F α r =
      comp₃ (pullbackTransport F ht')
        (comp₃ (transitionReindex C S hS F α (f₁ ≫ r₂)) (pullbackTransport F hm')
          (transitionReindex C S hS F α r₁)) (pullbackTransport F hs'.symm) :=
    hcoc ht' hm' hs'
  have h₄ := congrArg (fun z => comp₃ (pullbackTransport F hy.symm) z (pullbackTransport F hx)) hc
  have h₅ := comp₃_nested_shape (pullbackTransport F hy.symm) (pullbackTransport F ht')
    (transitionReindex C S hS F α (f₁ ≫ r₂)) (pullbackTransport F hm')
    (transitionReindex C S hS F α r₁) (pullbackTransport F hs'.symm) (pullbackTransport F hx)
    (pullbackTransport_comp F hy.symm ht' e₁) (pullbackTransport_comp F hs'.symm hx hx₁)
  exact h₁.trans (h₂.trans (h₃.trans (h₅.symm.trans
    (h₄.symm.trans (transitionTwist_eq_comp₃ F α r hx hy).symm))))


/-- Precomposing a twisted transition with a transport changes the endpoint it starts from. -/
theorem pullbackTransport_comp_transitionTwist {W : AlgebraicSpaces C S hS} {x y y' : W ⟶ U}
    (r : W ⟶ V) (hx : r ≫ b = x) (hy : r ≫ a = y) (e : y' = y) (hy' : r ≫ a = y') :
    pullbackTransport F e ≫ transitionTwist F α r hx hy = transitionTwist F α r hx hy' := by
  have h := pullbackTransport_comp F e hy.symm hy'.symm
  rw [transitionTwist_eq_comp₃, transitionTwist_eq_comp₃, comp₃, comp₃, ← h, Category.assoc]

end Generic


section Groupoid

variable {A : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS A}
  (M : QuasicoherentModule C S hS G)

/-- The transition `f^*(a^*ℱ) ⟶ a'^*ℱ` along an `X'`-valued arrow `r` from `a'` to `f ∘ a`. -/
def pointTransition {X X' : AlgebraicSpaces C S hS} (f : X' ⟶ X) (a : X ⟶ G.objects)
    {a' : X' ⟶ G.objects} (r : X' ⟶ G.arrows) (hs : r ≫ G.source = a')
    (ht : r ≫ G.target = f ≫ a) :
    (modulePullback C S hS f).obj ((modulePullback C S hS a).obj M.F.obj) ⟶
      (modulePullback C S hS a').obj M.F.obj :=
  comp₃ ((modulePullbackCompIso C S hS f a).app M.F.obj).hom
    (transitionTwist M.F.obj M.alpha r hs ht) (𝟙 _)

/-- The cocycle condition of Stacks 0441, as a `TransitionCocycle` at the two projections and
the composition of the space of composable pairs. -/
theorem transitionCocycle :
    TransitionCocycle C S hS M.F.obj M.alpha (firstArrow G) (secondArrow G) G.comp :=
  fun _ _ _ =>
    (show groupoidPullbackTransition C S hS G M.F.obj M.alpha G.comp =
      transitionReindex C S hS M.F.obj M.alpha G.comp from rfl).symm.trans
      (M.cocycle.trans (groupoidTransitionComposite_eq C S hS G M.F.obj M.alpha))

/-- **The cocycle law for transitions along arrows.** For an arrow `r₂` from `a'` to `b₂` and an
arrow `r₁` from `a''` to `f₁ ∘ a'` whose composite `r` is classified by `k`, reading `α` along
`r₂`, reindexing along `f₁`, and then reading `α` along `r₁` is reading `α` along `r`. -/
theorem transitionReindex_transitionTwist_comp_groupoid {X' X'' : AlgebraicSpaces C S hS}
    (f₁ : X'' ⟶ X')
    {a' b₂ : X' ⟶ G.objects} {a'' : X'' ⟶ G.objects}
    (r₂ : X' ⟶ G.arrows) (hs₂ : r₂ ≫ G.source = a') (ht₂ : r₂ ≫ G.target = b₂)
    (r₁ : X'' ⟶ G.arrows) (hs₁ : r₁ ≫ G.source = a'') (ht₁ : r₁ ≫ G.target = f₁ ≫ a')
    (r : X'' ⟶ G.arrows) (hs : r ≫ G.source = a'') (ht : r ≫ G.target = f₁ ≫ b₂)
    (k : X'' ⟶ AlgebraicSpaces.fiberProduct C S hS G.source G.target)
    (hk₁ : k ≫ firstArrow G = f₁ ≫ r₂) (hk₂ : k ≫ secondArrow G = r₁) (hk : k ≫ G.comp = r) :
    transitionReindex C S hS M.F.obj (transitionTwist M.F.obj M.alpha r₂ hs₂ ht₂) f₁ ≫
        transitionTwist M.F.obj M.alpha r₁ hs₁ ht₁ =
      transitionTwist M.F.obj M.alpha r hs ht := by
  have hcoc : TransitionCocycle C S hS M.F.obj M.alpha (f₁ ≫ r₂) r₁ r :=
    TransitionCocycle.comp C S hS M.F.obj M.alpha (comp_comp_target G)
      (firstArrow_comp_source G) (comp_comp_source G) (transitionCocycle M) k hk₁ hk₂ hk
  exact transitionReindex_transitionTwist_comp M.F.obj M.alpha f₁ r₂ hs₂ ht₂ r₁ hs₁ ht₁ r hs ht
    hcoc

end Groupoid

end AlgebraicGeometry.Space

end
