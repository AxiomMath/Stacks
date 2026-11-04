module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseArrowLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TransitionReindexComp

/-!
# Reading a groupoid transition morphism along a pair of legs of a kernel pair

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces and let `φ : U ⟶ X` be a morphism with
`R = U ×_X U` and `t`, `s` the two projections — the situation of Stacks 03M3.  A quasi-coherent
module `(ℱ, α)` on the groupoid, in the sense of Stacks 0441, then assigns to a pair of morphisms
`a, b : P ⟶ U` with `a ≫ φ = b ≫ φ` a morphism `a^*ℱ ⟶ b^*ℱ`: reindex the transition morphism
`α : t^*ℱ ⟶ s^*ℱ` along the unique arrow `P ⟶ R` with target `a` and source `b`, and identify the
two endpoints of the result with `a^*ℱ` and `b^*ℱ`.  That assignment is the content of this file.

## Main definitions

* `AlgebraicGeometry.Space.legTransition`: the transition morphism of a quasi-coherent module on
  the groupoid, read along a pair of morphisms into the space of objects with equal composites to
  `X`.

## Main results

* `AlgebraicGeometry.Space.transitionCocycle_alpha` and
  `AlgebraicGeometry.Space.transitionUnit_alpha`: the cocycle and unit laws of a quasi-coherent
  module on a groupoid in algebraic spaces, read as the general conditions
  `AlgebraicGeometry.Space.TransitionCocycle` and `AlgebraicGeometry.Space.TransitionUnit`.
* `AlgebraicGeometry.Space.legTransition_self`: **a pair of equal morphisms is read as the
  identity.**
* `AlgebraicGeometry.Space.legTransition_comp`: **the reading is multiplicative along a triple of
  morphisms.**
* `AlgebraicGeometry.Space.transitionReindex_legTransition`: **the reading is natural in the test
  space.**

## Implementation notes

Every composite here is written at `CategoryTheory.comp₃`, never as a chain of `≫`: a
`AlgebraicGeometry.Space.pullbackTransport` factor is a `CategoryTheory.eqToHom`, and unfolding a
row composite into `≫` drives it down to its `Eq.rec`, where the kernel exhausts its budget on an
object of `AlgebraicGeometry.Space.Modules`.  Each of `legTransition_eq`,
`comp₃_transitionReindex_congr` and `transitionComposite_eq₃` is a kernel timeout when its row
composites are spelled with `≫`, and immediate at `comp₃`.  The private row lemmas
`CategoryTheory.comp₃_comp_comp₃` and `CategoryTheory.comp₃_comp₃_merge` take the merged
transport as a hypothesis and are proved generically, where nothing can unfold.

The hypothesis `a ≫ φ = b ≫ φ` occupies a proof position of `AlgebraicGeometry.Space.arrowLift`,
so none of the morphisms below depends on which proof is supplied.

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

universe v₁ u₁

/-- The composite of two row composites whose adjacent factors are given a merged name. -/
private theorem comp₃_comp_comp₃ {C : Type u₁} [Category.{v₁} C] {X₁ X₂ X₃ X₄ Y₂ Y₃ Y₄ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃} {f₃ : X₃ ⟶ X₄} {g₁ : X₄ ⟶ Y₂} {g₂ : Y₂ ⟶ Y₃} {g₃ : Y₃ ⟶ Y₄}
    {k : X₃ ⟶ Y₂} (hk : f₃ ≫ g₁ = k) :
    comp₃ f₁ f₂ f₃ ≫ comp₃ g₁ g₂ g₃ = comp₃ f₁ (comp₃ f₂ k g₂) g₃ := by
  subst hk
  simp [comp₃]

/-- A row composite whose middle factor is itself a row composite, with the two outer pairs of
factors given merged names. -/
private theorem comp₃_comp₃_merge {C : Type u₁} [Category.{v₁} C]
    {X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ : C} {t₁ : X₁ ⟶ X₂} {t₂ : X₂ ⟶ X₃} {x : X₃ ⟶ X₄} {y : X₄ ⟶ X₅}
    {z : X₅ ⟶ X₆} {t₃ : X₆ ⟶ X₇} {t₄ : X₇ ⟶ X₈} {k₁ : X₁ ⟶ X₃} {k₂ : X₆ ⟶ X₈}
    (h₁ : t₁ ≫ t₂ = k₁) (h₂ : t₃ ≫ t₄ = k₂) :
    comp₃ t₁ (comp₃ t₂ (comp₃ x y z) t₃) t₄ = comp₃ k₁ (comp₃ x y z) k₂ := by
  subst h₁ h₂
  simp [comp₃]

end CategoryTheory

namespace AlgebraicGeometry.Space

open GroupoidInAlgebraicSpaces

section Transport

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T U V W X : AlgebraicSpaces B S hS}

/-- A row of three identifications of inverse images which returns to its starting point is the
identity. -/
private theorem comp₃_pullbackTransport_id (F : Modules.{u, u} B S hS X.1 X.2)
    {f g h : T ⟶ X} (h₁ : f = g) (h₂ : g = h) (h₃ : h = f) :
    comp₃ (pullbackTransport F h₁) (pullbackTransport F h₂) (pullbackTransport F h₃) =
      𝟙 ((modulePullback B S hS f).obj F) := by
  subst h₁ h₂
  simp [comp₃, pullbackTransport]

/-- A reindexing of a transition morphism, read between two identifications of its endpoints,
depends on the morphism it is reindexed along only up to equality of that morphism. -/
private theorem comp₃_transitionReindex_congr (F : Modules.{u, u} B S hS U.1 U.2)
    {t s : V ⟶ U} (α : (modulePullback B S hS t).obj F ⟶ (modulePullback B S hS s).obj F)
    {m m' : W ⟶ V} (hm : m = m') {x y : W ⟶ U} (h₁ : x = m ≫ t) (h₂ : m ≫ s = y)
    (h₁' : x = m' ≫ t) (h₂' : m' ≫ s = y) :
    comp₃ (pullbackTransport F h₁) (transitionReindex B S hS F α m) (pullbackTransport F h₂) =
      comp₃ (pullbackTransport F h₁') (transitionReindex B S hS F α m')
        (pullbackTransport F h₂') := by
  subst hm
  rfl

/-- `AlgebraicGeometry.Space.transitionComposite` with its inner row composite unfolded, so that
the two reindexings it is made of are visible. -/
private theorem transitionComposite_eq₃ (F : Modules.{u, u} B S hS U.1 U.2) {t s : V ⟶ U}
    (α : (modulePullback B S hS t).obj F ⟶ (modulePullback B S hS s).obj F) (p q r : W ⟶ V)
    (ht : r ≫ t = p ≫ t) (hm : p ≫ s = q ≫ t) (hs : r ≫ s = q ≫ s) :
    transitionComposite B S hS F α p q r ht hm hs =
      comp₃ (pullbackTransport F ht)
        (comp₃ (transitionReindex B S hS F α p) (pullbackTransport F hm)
          (transitionReindex B S hS F α q))
        (pullbackTransport F hs.symm) :=
  rfl

end Transport

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)

/-- **The cocycle law of a quasi-coherent module on a groupoid in algebraic spaces, read as the
general cocycle condition** at the two projections and the composition of the space of composable
pairs of arrows. -/
theorem transitionCocycle_alpha (Z : QuasicoherentModule B S hS G) :
    TransitionCocycle B S hS (U := G.objects) (V := G.arrows) Z.F.obj Z.alpha
      (firstArrow G) (secondArrow G) G.comp :=
  fun _ _ _ => Z.cocycle.trans (groupoidTransitionComposite_eq B S hS G Z.F.obj Z.alpha)

/-- **The unit law of a quasi-coherent module on a groupoid in algebraic spaces, read as the
general unit condition** at the unit arrow. -/
theorem transitionUnit_alpha (Z : QuasicoherentModule B S hS G) :
    TransitionUnit B S hS (U := G.objects) (V := G.arrows) Z.F.obj Z.alpha (identityArrow G) :=
  fun _ => Z.unit

variable {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X)
  (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom)
  {P Q : AlgebraicSpaces B S hS}

/-- **The transition morphism of a quasi-coherent module on a kernel-pair groupoid, read along a
pair of morphisms into the space of objects with equal composites to `X`.**  It is the transition
morphism `α : t^*ℱ ⟶ s^*ℱ` reindexed along the unique arrow with target `a` and source `b`, with
its two endpoints identified with `a^*ℱ` and `b^*ℱ`. -/
def legTransition (Z : QuasicoherentModule B S hS G) (a b : P ⟶ G.objects)
    (hab : a ≫ φ = b ≫ φ) :
    (modulePullback B S hS a).obj Z.F.obj ⟶ (modulePullback B S hS b).obj Z.F.obj :=
  comp₃ (pullbackTransport Z.F.obj (arrowLift_comp_target B S hS G φ hpb a b hab).symm)
    (transitionReindex B S hS Z.F.obj Z.alpha (arrowLift B S hS G φ hpb a b hab))
    (pullbackTransport Z.F.obj (arrowLift_comp_source B S hS G φ hpb a b hab))

/-- The definition of `AlgebraicGeometry.Space.legTransition`, as an equation. -/
private theorem legTransition_eq (Z : QuasicoherentModule B S hS G) (a b : P ⟶ G.objects)
    (hab : a ≫ φ = b ≫ φ) :
    legTransition B S hS G φ hpb Z a b hab =
      comp₃ (pullbackTransport Z.F.obj (arrowLift_comp_target B S hS G φ hpb a b hab).symm)
        (transitionReindex B S hS Z.F.obj Z.alpha (arrowLift B S hS G φ hpb a b hab))
        (pullbackTransport Z.F.obj (arrowLift_comp_source B S hS G φ hpb a b hab)) :=
  rfl

/-- **A pair of equal morphisms is read as the identity.** -/
theorem legTransition_self (Z : QuasicoherentModule B S hS G) (a : P ⟶ G.objects) :
    legTransition B S hS G φ hpb Z a a rfl = 𝟙 ((modulePullback B S hS a).obj Z.F.obj) := by
  have hu : TransitionUnit B S hS (U := G.objects) (V := G.arrows) Z.F.obj Z.alpha
      (arrowLift B S hS G φ hpb a a rfl) :=
    TransitionUnit.comp B S hS Z.F.obj Z.alpha
      (by rw [identityArrow_comp_target, identityArrow_comp_source])
      (transitionUnit_alpha B S hS G Z) a (arrowLift_self B S hS G φ hpb a).symm
  have h : arrowLift B S hS G φ hpb a a rfl ≫ G.target =
      arrowLift B S hS G φ hpb a a rfl ≫ G.source := by
    rw [arrowLift_comp_target, arrowLift_comp_source]
  rw [legTransition_eq, hu h, comp₃_pullbackTransport_id]

/-- **The reading is multiplicative along a triple of morphisms**: the reading along `a, b`
followed by the reading along `b, c` is the reading along `a, c`. -/
theorem legTransition_comp (Z : QuasicoherentModule B S hS G) (a b c : P ⟶ G.objects)
    (hab : a ≫ φ = b ≫ φ) (hbc : b ≫ φ = c ≫ φ) (hac : a ≫ φ = c ≫ φ) :
    legTransition B S hS G φ hpb Z a b hab ≫ legTransition B S hS G φ hpb Z b c hbc =
      legTransition B S hS G φ hpb Z a c hac := by
  have ht' : arrowLift B S hS G φ hpb a c hac ≫ G.target =
      arrowLift B S hS G φ hpb a b hab ≫ G.target := by
    rw [arrowLift_comp_target, arrowLift_comp_target]
  have hm' : arrowLift B S hS G φ hpb a b hab ≫ G.source =
      arrowLift B S hS G φ hpb b c hbc ≫ G.target := by
    rw [arrowLift_comp_source, arrowLift_comp_target]
  have hs' : arrowLift B S hS G φ hpb a c hac ≫ G.source =
      arrowLift B S hS G φ hpb b c hbc ≫ G.source := by
    rw [arrowLift_comp_source, arrowLift_comp_source]
  have hcoc : TransitionCocycle B S hS (U := G.objects) (V := G.arrows) Z.F.obj Z.alpha
      (arrowLift B S hS G φ hpb a b hab) (arrowLift B S hS G φ hpb b c hbc)
      (arrowLift B S hS G φ hpb a c hac) :=
    TransitionCocycle.comp B S hS Z.F.obj Z.alpha (comp_comp_target G)
      (firstArrow_comp_source G) (comp_comp_source G) (transitionCocycle_alpha B S hS G Z)
      (composablePairLift B S hS G φ hpb a b c hab hbc)
      (composablePairLift_comp_firstArrow B S hS G φ hpb a b c hab hbc)
      (composablePairLift_comp_secondArrow B S hS G φ hpb a b c hab hbc)
      (composablePairLift_comp_comp B S hS G φ hpb a b c hab hbc hac)
  rw [legTransition_eq B S hS G φ hpb Z a b hab, legTransition_eq B S hS G φ hpb Z b c hbc,
    legTransition_eq B S hS G φ hpb Z a c hac, hcoc ht' hm' hs', transitionComposite_eq₃,
    comp₃_comp_comp₃ (pullbackTransport_comp Z.F.obj
      (arrowLift_comp_source B S hS G φ hpb a b hab)
      (arrowLift_comp_target B S hS G φ hpb b c hbc).symm hm'),
    comp₃_comp₃_merge
      (pullbackTransport_comp Z.F.obj
        (arrowLift_comp_target B S hS G φ hpb a c hac).symm ht'
        (arrowLift_comp_target B S hS G φ hpb a b hab).symm)
      (pullbackTransport_comp Z.F.obj hs'.symm
        (arrowLift_comp_source B S hS G φ hpb a c hac)
        (arrowLift_comp_source B S hS G φ hpb b c hbc))]

/-- **The reading is natural in the test space.**  Reindexing the reading of a pair along a
morphism of test spaces is the reading of the precomposed pair. -/
theorem transitionReindex_legTransition (Z : QuasicoherentModule B S hS G) (q : Q ⟶ P)
    (a b : P ⟶ G.objects) (hab : a ≫ φ = b ≫ φ) (hab' : (q ≫ a) ≫ φ = (q ≫ b) ≫ φ) :
    transitionReindex B S hS Z.F.obj (legTransition B S hS G φ hpb Z a b hab) q =
      legTransition B S hS G φ hpb Z (q ≫ a) (q ≫ b) hab' := by
  rw [legTransition_eq B S hS G φ hpb Z a b hab,
    legTransition_eq B S hS G φ hpb Z (q ≫ a) (q ≫ b) hab', transitionReindex_comp₃,
    transitionReindex_pullbackTransport, transitionReindex_pullbackTransport,
    transitionReindex_comp]
  exact comp₃_transitionReindex_congr B S hS Z.F.obj Z.alpha
    (comp_arrowLift B S hS G φ hpb q a b hab hab') _ _ _ _

end AlgebraicGeometry.Space

end
