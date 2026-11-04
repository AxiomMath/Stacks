module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TransitionTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc

/-!
# Reindexing a transition morphism along a composite

A transition morphism `α : a^*ℱ ⟶ b^*ℱ` between the inverse images of a module along two
parallel morphisms is reindexed along a morphism `f` into the common source of `a` and `b` by
`AlgebraicGeometry.Space.transitionReindex`. This file proves that reindexing is functorial in
`f`, reindexing along `f` and then along `k` being reindexing along `k ≫ f`, and deduces that the
cocycle and unit laws of a transition morphism, stated at a triple and at a single morphism into
the common source, hold at every precomposition of that triple and of that morphism.

## Main results

* `AlgebraicGeometry.Space.transitionReindex_comp`: **reindexing is functorial**.
* `AlgebraicGeometry.Space.transitionReindex_transitionPair` and
  `AlgebraicGeometry.Space.transitionReindex_transitionComposite`: the two composites that make
  up the right-hand side of a cocycle law are carried to the corresponding composites at the
  precomposed morphisms.
* `AlgebraicGeometry.Space.TransitionCocycle.comp` and
  `AlgebraicGeometry.Space.TransitionUnit.comp`: **the cocycle and unit laws are stable under
  precomposition**.

## Implementation notes

Row composites are kept at `CategoryTheory.comp₃`, never unfolded to `≫`: since
`AlgebraicGeometry.Space.pullbackTransport` is an `eqToHom`, rewriting a row composite into `≫`
reduces it to its `Eq.rec`, and the kernel then times out on an object of
`AlgebraicGeometry.Space.Modules`. Proofs go through
`AlgebraicGeometry.Space.transitionReindex_comp₃` instead of `CategoryTheory.comp₃_eq`.

The precomposed laws take the equations of the original triple as explicit hypotheses:
`(k ≫ r) ≫ a = (k ≫ p) ≫ a` does not imply `r ≫ a = p ≫ a`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 043T](https://stacks.math.columbia.edu/tag/043T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U V W W' : AlgebraicSpaces B S hS}

/-- **Reindexing a transition morphism is functorial.** Reindexing along `f` and then along
`k` is reindexing along `k ≫ f`. -/
theorem transitionReindex_comp (F : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F)
    (k : W' ⟶ W) (f : W ⟶ V) :
    transitionReindex B S hS F (transitionReindex B S hS F α f) k =
      transitionReindex B S hS F α (k ≫ f) :=
  (modulePullbackCompIsoAssoc B S hS).modulePullbackReindex_comp k f α

/-- Reindexing the identification of the inverse images along two equal morphisms is the
identification along the two composites. -/
theorem transitionReindex_pullbackTransport (F : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (h : a = b) (f : W ⟶ V) :
    transitionReindex B S hS F (pullbackTransport F h) f =
      pullbackTransport F (congrArg (f ≫ ·) h) := by
  subst h
  simp [transitionReindex, pullbackTransport]

/-- Reindexing a composite of transition morphisms is the composite of the reindexings. -/
theorem transitionReindex_comp_morphism (F : Modules.{u, u} B S hS U.1 U.2) {a b c : V ⟶ U}
    (α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F)
    (β : (modulePullback B S hS b).obj F ⟶ (modulePullback B S hS c).obj F) (f : W ⟶ V) :
    transitionReindex B S hS F (α ≫ β) f =
      transitionReindex B S hS F α f ≫ transitionReindex B S hS F β f :=
  modulePullbackReindex_comp_morphism f α β

/-- Reindexing a row `CategoryTheory.comp₃` of three morphisms is the row of the three
reindexings. -/
theorem transitionReindex_comp₃ (F : Modules.{u, u} B S hS U.1 U.2) {a₁ a₂ a₃ a₄ : V ⟶ U}
    (x : (modulePullback B S hS a₁).obj F ⟶ (modulePullback B S hS a₂).obj F)
    (y : (modulePullback B S hS a₂).obj F ⟶ (modulePullback B S hS a₃).obj F)
    (z : (modulePullback B S hS a₃).obj F ⟶ (modulePullback B S hS a₄).obj F) (f : W ⟶ V) :
    transitionReindex B S hS F (comp₃ x y z) f =
      comp₃ (transitionReindex B S hS F x f) (transitionReindex B S hS F y f)
        (transitionReindex B S hS F z f) := by
  rw [comp₃, comp₃, transitionReindex_comp_morphism, transitionReindex_comp_morphism]

/-- Reindexing the two-step composite of reindexings along a matching pair is the two-step
composite along the precomposed pair. -/
theorem transitionReindex_transitionPair (F : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F) (p q : W ⟶ V)
    (hm : p ≫ b = q ≫ a) (k : W' ⟶ W) (hm' : (k ≫ p) ≫ b = (k ≫ q) ≫ a) :
    transitionReindex B S hS F (transitionPair B S hS F α p q hm) k =
      transitionPair B S hS F α (k ≫ p) (k ≫ q) hm' := by
  rw [transitionPair, transitionReindex_comp₃, transitionReindex_pullbackTransport,
    transitionReindex_comp, transitionReindex_comp, transitionPair]

/-- Reindexing the right-hand side of a cocycle law is the right-hand side of the cocycle law
at the precomposed triple. -/
theorem transitionReindex_transitionComposite (F : Modules.{u, u} B S hS U.1 U.2)
    {a b : V ⟶ U}
    (α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F) (p q r : W ⟶ V)
    (ht : r ≫ a = p ≫ a) (hm : p ≫ b = q ≫ a) (hs : r ≫ b = q ≫ b) (k : W' ⟶ W)
    (ht' : (k ≫ r) ≫ a = (k ≫ p) ≫ a) (hm' : (k ≫ p) ≫ b = (k ≫ q) ≫ a)
    (hs' : (k ≫ r) ≫ b = (k ≫ q) ≫ b) :
    transitionReindex B S hS F (transitionComposite B S hS F α p q r ht hm hs) k =
      transitionComposite B S hS F α (k ≫ p) (k ≫ q) (k ≫ r) ht' hm' hs' := by
  rw [transitionComposite, transitionReindex_comp₃, transitionReindex_pullbackTransport,
    transitionReindex_pullbackTransport,
    transitionReindex_transitionPair B S hS F α p q hm k hm', transitionComposite]

/-- **The cocycle law is stable under precomposition.** If a transition morphism satisfies the
cocycle law at a triple `p`, `q`, `r` of morphisms into the common source of the two morphisms
it compares, then it satisfies it at any precomposition of that triple. -/
theorem TransitionCocycle.comp (F : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F) {p q r : W ⟶ V}
    (ht : r ≫ a = p ≫ a) (hm : p ≫ b = q ≫ a) (hs : r ≫ b = q ≫ b)
    (h : TransitionCocycle B S hS F α p q r) (k : W' ⟶ W) {p' q' r' : W' ⟶ V}
    (hp : k ≫ p = p') (hq : k ≫ q = q') (hr : k ≫ r = r') :
    TransitionCocycle B S hS F α p' q' r' := by
  subst hp hq hr
  intro ht' hm' hs'
  rw [← transitionReindex_comp B S hS F α k r, h ht hm hs,
    transitionReindex_transitionComposite B S hS F α p q r ht hm hs k ht' hm' hs']

/-- **The unit law is stable under precomposition.** If a transition morphism satisfies the
unit law at a morphism `f` into the common source of the two morphisms it compares, then it
satisfies it at any precomposition of `f`. -/
theorem TransitionUnit.comp (F : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F) {f : W ⟶ V}
    (hf : f ≫ a = f ≫ b) (h : TransitionUnit B S hS F α f) (k : W' ⟶ W) {f' : W' ⟶ V}
    (hk : k ≫ f = f') : TransitionUnit B S hS F α f' := by
  subst hk
  intro h'
  rw [← transitionReindex_comp B S hS F α k f, h hf,
    transitionReindex_pullbackTransport B S hS F hf k]

end AlgebraicGeometry.Space

end
