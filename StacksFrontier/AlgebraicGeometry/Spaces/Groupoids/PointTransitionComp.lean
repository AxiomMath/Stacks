module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PointTransition

/-!
# Functoriality of the transitions along points

Let `(ℱ, α)` be a quasi-coherent module on a groupoid `(U, R, s, t, c)` in algebraic spaces
(Stacks 0441). For an arrow `r` from `a'` to `f ∘ a` the transition
`AlgebraicGeometry.Space.pointTransition` is a morphism `f^*(a^*ℱ) ⟶ a'^*ℱ`. This file proves
that these transitions compose: along `f₁ ≫ f₂` and the composite `r` of two arrows `r₂`, `r₁`
the transition is the pullback along `f₁` of the transition along `r₂`, followed by the
transition along `r₁`, read through the comparison `(f₁ ≫ f₂)^* ≅ f₁^* f₂^*` of Stacks 03LU.
These are the restriction maps of the module of the proof of Stacks 06WT on the pointwise
quotient, and this is their functoriality.

## Main results

* `AlgebraicGeometry.Space.pointTransition_comp`: the composition law.
* `AlgebraicGeometry.Space.modulePullbackCompIso_assoc_transport`: the associativity coherence
  of Stacks 03LU with the two bracketings identified by a transport.

## Implementation notes

Every equation about inverse images of modules is proved for abstract morphisms and then
instantiated: an equation proved in place about a named morphism such as
`AlgebraicGeometry.Space.transitionTwist` makes the kernel compare `(F ⋙ G).obj M` with
`G.obj (F.obj M)` by unfolding the inverse image functors, which exhausts its budget.

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

/-- The shape of the functoriality law of point transitions. -/
theorem comp_comp_eq_of_five {P₀ P₁ P₂ P₃ P₄ P₅ P₆ Q : D} (i : P₀ ⟶ P₁) (m₁ : P₁ ⟶ P₂)
    (m₂ : P₂ ⟶ P₃) (c₁ : P₃ ⟶ P₅) (w₁ : P₅ ⟶ P₆) (c' : P₂ ⟶ P₄) (ρ : P₄ ⟶ P₅) (w' : P₄ ⟶ P₆)
    (c₁₂ : P₀ ⟶ Q) (τ : Q ⟶ P₄) (w : Q ⟶ P₆) {x : P₁ ⟶ P₃} {y : P₃ ⟶ P₆} {z : P₀ ⟶ P₆}
    (hx : x = m₁ ≫ m₂) (hy : y = c₁ ≫ w₁) (hz : z = c₁₂ ≫ w) (e₂ : m₂ ≫ c₁ = c' ≫ ρ)
    (e₃ : ρ ≫ w₁ = w') (e₄ : i ≫ m₁ ≫ c' = c₁₂ ≫ τ) (e₅ : τ ≫ w' = w) :
    i ≫ x ≫ y = z := by
  rw [hx, hy, hz, ← e₅, ← e₃]
  simp only [Category.assoc, reassoc_of% e₂, reassoc_of% e₄]

/-- A row of three morphisms ending in an identity is a composite of two. -/
theorem comp₃_id_right {X₁ X₂ X₃ : D} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) :
    comp₃ f g (𝟙 X₃) = f ≫ g := by
  simp [comp₃]

/-- A functor applied to a morphism written as a composite. -/
theorem _root_.CategoryTheory.Functor.map_eq_comp_of_eq {E : Type*} [Category E] (Φ : D ⥤ E)
    {X₁ X₂ X₃ : D} {φ : X₁ ⟶ X₃} {ψ : X₁ ⟶ X₂} {χ : X₂ ⟶ X₃} (h : φ = ψ ≫ χ) :
    Φ.map φ = Φ.map ψ ≫ Φ.map χ := by
  rw [h, Functor.map_comp]

end Shapes

/-- The associativity coherence of Stacks 03LU with the two composites `(f ≫ g) ≫ h` and
`f ≫ g ≫ h` identified by a transport, so that both sides have the same type on the nose. -/
theorem modulePullbackCompIso_assoc_transport {W X Y Z : AlgebraicSpaces C S hS} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) (M : Modules.{u, u} C S hS Z.1 Z.2) :
    (modulePullbackCompIso C S hS f g).inv.app ((modulePullback C S hS h).obj M) ≫
        (modulePullback C S hS f).map ((modulePullbackCompIso C S hS g h).hom.app M) ≫
          (modulePullbackCompIso C S hS f (g ≫ h)).hom.app M =
      (modulePullbackCompIso C S hS (f ≫ g) h).hom.app M ≫
        pullbackTransport M (Category.assoc f g h) := by
  rw [(modulePullbackCompIsoAssoc C S hS).hom_app f g h M, Iso.inv_hom_id_app_assoc]
  simp [pullbackTransport]

/-- Pulling back a morphism along `f` and then comparing is comparing and then reindexing. -/
theorem modulePullback_map_comp_compIso_hom {U W W' : AlgebraicSpaces C S hS}
    {F : Modules.{u, u} C S hS U.1 U.2} {x y : W ⟶ U}
    (f : W' ⟶ W) (φ : (modulePullback C S hS y).obj F ⟶ (modulePullback C S hS x).obj F) :
    (modulePullback C S hS f).map φ ≫ ((modulePullbackCompIso C S hS f x).app F).hom =
      ((modulePullbackCompIso C S hS f y).app F).hom ≫ transitionReindex C S hS F φ f := by
  simp only [transitionReindex, Iso.hom_inv_id_assoc]

section Groupoid

variable {A : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS A}
  (M : QuasicoherentModule C S hS G)

/-- A point transition is the comparison isomorphism followed by the twist. -/
private theorem pointTransition_eq_compIso_hom_comp {X X' : AlgebraicSpaces C S hS}
    (f : X' ⟶ X) (a : X ⟶ G.objects) {a' : X' ⟶ G.objects} (r : X' ⟶ G.arrows)
    (hs : r ≫ G.source = a') (ht : r ≫ G.target = f ≫ a) :
    pointTransition M f a r hs ht =
      ((modulePullbackCompIso C S hS f a).app M.F.obj).hom ≫
        transitionTwist M.F.obj M.alpha r hs ht :=
  comp₃_id_right ((modulePullbackCompIso C S hS f a).app M.F.obj).hom
    (transitionTwist M.F.obj M.alpha r hs ht)

/-- **The transitions along points compose.** For arrows `r₂` from `a'` to `f₂ ∘ a` and `r₁`
from `a''` to `f₁ ∘ a'` whose composite `r` is classified by `k`, the transition along `r₂`
pulled back along `f₁`, followed by the transition along `r₁`, is the transition along `r`. -/
theorem pointTransition_comp {X X' X'' : AlgebraicSpaces C S hS} (f₁ : X'' ⟶ X') (f₂ : X' ⟶ X)
    (a : X ⟶ G.objects) {a' : X' ⟶ G.objects} {a'' : X'' ⟶ G.objects}
    (r₂ : X' ⟶ G.arrows) (hs₂ : r₂ ≫ G.source = a') (ht₂ : r₂ ≫ G.target = f₂ ≫ a)
    (r₁ : X'' ⟶ G.arrows) (hs₁ : r₁ ≫ G.source = a'') (ht₁ : r₁ ≫ G.target = f₁ ≫ a')
    (r : X'' ⟶ G.arrows) (hs : r ≫ G.source = a'') (ht : r ≫ G.target = (f₁ ≫ f₂) ≫ a)
    (k : X'' ⟶ AlgebraicSpaces.fiberProduct C S hS G.source G.target)
    (hk₁ : k ≫ firstArrow G = f₁ ≫ r₂) (hk₂ : k ≫ secondArrow G = r₁) (hk : k ≫ G.comp = r) :
    (modulePullbackCompIso C S hS f₁ f₂).inv.app ((modulePullback C S hS a).obj M.F.obj) ≫
        (modulePullback C S hS f₁).map (pointTransition M f₂ a r₂ hs₂ ht₂) ≫
          pointTransition M f₁ a' r₁ hs₁ ht₁ =
      pointTransition M (f₁ ≫ f₂) a r hs ht := by
  have ht' : r ≫ G.target = f₁ ≫ f₂ ≫ a := ht.trans (Category.assoc f₁ f₂ a)
  have e₁ := Functor.map_eq_comp_of_eq (modulePullback C S hS f₁)
    (pointTransition_eq_compIso_hom_comp M f₂ a r₂ hs₂ ht₂)
  have e₂ := modulePullback_map_comp_compIso_hom f₁
    (transitionTwist M.F.obj M.alpha r₂ hs₂ ht₂)
  have e₃ : transitionReindex C S hS M.F.obj (transitionTwist M.F.obj M.alpha r₂ hs₂ ht₂) f₁ ≫
        transitionTwist M.F.obj M.alpha r₁ hs₁ ht₁ =
      transitionTwist M.F.obj M.alpha r hs ht' :=
    transitionReindex_transitionTwist_comp_groupoid M f₁ r₂ hs₂ ht₂ r₁ hs₁ ht₁ r hs ht' k hk₁
      hk₂ hk
  have e₄ := modulePullbackCompIso_assoc_transport f₁ f₂ a M.F.obj
  have e₅ : pullbackTransport M.F.obj (Category.assoc f₁ f₂ a) ≫
        transitionTwist M.F.obj M.alpha r hs ht' =
      transitionTwist M.F.obj M.alpha r hs ht :=
    pullbackTransport_comp_transitionTwist M.F.obj M.alpha r hs ht' (Category.assoc f₁ f₂ a) ht
  exact comp_comp_eq_of_five _ _ _ _ _ _ _ _ _ _ _ e₁
    (pointTransition_eq_compIso_hom_comp M f₁ a' r₁ hs₁ ht₁)
    (pointTransition_eq_compIso_hom_comp M (f₁ ≫ f₂) a r hs ht) e₂ e₃ e₄ e₅

end Groupoid

end AlgebraicGeometry.Space

end
