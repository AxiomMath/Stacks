module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Checking an exact pairing on a jointly faithful family of monoidal functors

Let `C` be a monoidal category, let `Fᵢ : C ⥤ Dᵢ` be a family of monoidal functors which is
jointly faithful (`CategoryTheory.JointlyFaithful`: a morphism of `C` is determined by its images
under the `Fᵢ`), and let `X, Y` be objects of `C` equipped with candidate data

`η : 𝟙 ⟶ X ⊗ Y`,  `ε : Y ⊗ X ⟶ 𝟙`

for an exact pairing. If each `Fᵢ` carries that data to the coevaluation and the evaluation of an
exact pairing of `Fᵢ X` and `Fᵢ Y`, then `(X, Y, η, ε)` is itself an exact pairing. This is the
formal content of "the two triangle identities are a local question": each identity is a single
equation between morphisms of `C`, so a family of functors which detects equality of morphisms
detects it.

Mathlib has the case of a single faithful functor, `CategoryTheory.ExactPairing.ofFaithful`, and
the direct image along a monoidal functor is
`CategoryTheory.ExactPairing.map` of `StacksFrontier.CategoryTheory.Monoidal.Rigid`. The family
version below is what a proof that is local on a covering family needs, the family being the
restrictions to the members of the covering: those are monoidal by
`Stacks.SheafOfModules.SliceRestriction.overFunctorStrictMonoidal` and jointly faithful by
`Stacks.SheafOfModules.SliceRestriction.overFunctor_map_injective`, both of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal`, whose notes name this
lemma as what consumes them.

## Main definitions

* `CategoryTheory.ExactPairing.ofJointlyFaithful`: the exact pairing obtained from candidate
  data whose image under every member of a jointly faithful family of monoidal functors is an
  exact pairing.

## Implementation notes

The two hypotheses `map_coevaluation` and `map_evaluation` are stated exactly as Mathlib's
`CategoryTheory.ExactPairing.ofFaithful` states them for one functor: the image of the candidate
datum is the coevaluation, respectively the evaluation, of the given pairing on the images,
conjugated by the unit and tensor structure maps of the functor. They are *not* automatic — they
are the identification of the given pairing on `Fᵢ X, Fᵢ Y` with the image of the candidate
data, and a consumer that constructs the pairings on the images by some other route (a local
dual basis, a retract) owes exactly that identification.

The proof is Mathlib's proof of `ExactPairing.ofFaithful`, with joint faithfulness in place of
faithfulness: each triangle identity is checked after applying a single `Fᵢ`, where it follows
from the corresponding identity of the pairing on the images and the monoidal coherence of `Fᵢ`.

Nothing here is a Stacks Project statement, so no tag is attached; it is Mathlib coverage for
Categories, Section 43 (Tag 0FFP), in the same place as
`StacksFrontier.CategoryTheory.Monoidal.Rigid`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory

universe v₁ v₂ u₁ u₂ w

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {I : Type w} {D : I → Type u₂} [∀ i, Category.{v₂} (D i)] [∀ i, MonoidalCategory (D i)]

/-- **An exact pairing may be checked on a jointly faithful family of monoidal functors.** Let
`Fᵢ : C ⥤ Dᵢ` be a jointly faithful family of monoidal functors out of a monoidal category, let
`X, Y` be objects of `C`, and let

`η : 𝟙 ⟶ X ⊗ Y`,  `ε : Y ⊗ X ⟶ 𝟙`

be candidate data for an exact pairing. Suppose each `Fᵢ X, Fᵢ Y` carries an exact pairing whose
coevaluation and evaluation are the images of `η` and `ε` under `Fᵢ`, conjugated by the unit and
tensor structure maps of `Fᵢ`. Then `η` and `ε` satisfy the two triangle identities, so they
make `Y` a left dual of `X`.

This is `CategoryTheory.ExactPairing.ofFaithful` for a family of functors rather than for a
single faithful one, which is the form a proof that is local on a covering family takes: the
family of restrictions to the members of a covering is jointly faithful, and no single one of
them is faithful. -/
@[instance_reducible]
def ExactPairing.ofJointlyFaithful (F : ∀ i, C ⥤ D i) [∀ i, (F i).Monoidal]
    (hF : JointlyFaithful F) {X Y : C}
    (coeval : 𝟙_ C ⟶ X ⊗ Y) (eval : Y ⊗ X ⟶ 𝟙_ C)
    [pairs : ∀ i, ExactPairing ((F i).obj X) ((F i).obj Y)]
    (map_coevaluation : ∀ i, (F i).map coeval =
      η (F i) ≫ η_ ((F i).obj X) ((F i).obj Y) ≫ μ (F i) X Y)
    (map_evaluation : ∀ i, (F i).map eval =
      δ (F i) Y X ≫ ε_ ((F i).obj X) ((F i).obj Y) ≫ ε (F i)) :
    ExactPairing X Y where
  coevaluation' := coeval
  evaluation' := eval
  evaluation_coevaluation' :=
    hF.map_injective fun i => by
      simp [map_evaluation i, map_coevaluation i, Functor.Monoidal.map_whiskerLeft,
        Functor.Monoidal.map_whiskerRight]
  coevaluation_evaluation' :=
    hF.map_injective fun i => by
      simp [map_evaluation i, map_coevaluation i, Functor.Monoidal.map_whiskerLeft,
        Functor.Monoidal.map_whiskerRight]

/-- The coevaluation of `CategoryTheory.ExactPairing.ofJointlyFaithful` is the given candidate
datum, so the pairing it produces is a pairing *for that* coevaluation and not for some other
morphism of the same type. -/
theorem ExactPairing.ofJointlyFaithful_coevaluation (F : ∀ i, C ⥤ D i) [∀ i, (F i).Monoidal]
    (hF : JointlyFaithful F) {X Y : C}
    (coeval : 𝟙_ C ⟶ X ⊗ Y) (eval : Y ⊗ X ⟶ 𝟙_ C)
    [pairs : ∀ i, ExactPairing ((F i).obj X) ((F i).obj Y)]
    (map_coevaluation : ∀ i, (F i).map coeval =
      η (F i) ≫ η_ ((F i).obj X) ((F i).obj Y) ≫ μ (F i) X Y)
    (map_evaluation : ∀ i, (F i).map eval =
      δ (F i) Y X ≫ ε_ ((F i).obj X) ((F i).obj Y) ≫ ε (F i)) :
    letI := ExactPairing.ofJointlyFaithful F hF coeval eval map_coevaluation map_evaluation
    η_ X Y = coeval :=
  rfl

/-- The evaluation of `CategoryTheory.ExactPairing.ofJointlyFaithful` is the given candidate
datum. -/
theorem ExactPairing.ofJointlyFaithful_evaluation (F : ∀ i, C ⥤ D i) [∀ i, (F i).Monoidal]
    (hF : JointlyFaithful F) {X Y : C}
    (coeval : 𝟙_ C ⟶ X ⊗ Y) (eval : Y ⊗ X ⟶ 𝟙_ C)
    [pairs : ∀ i, ExactPairing ((F i).obj X) ((F i).obj Y)]
    (map_coevaluation : ∀ i, (F i).map coeval =
      η (F i) ≫ η_ ((F i).obj X) ((F i).obj Y) ≫ μ (F i) X Y)
    (map_evaluation : ∀ i, (F i).map eval =
      δ (F i) Y X ≫ ε_ ((F i).obj X) ((F i).obj Y) ≫ ε (F i)) :
    letI := ExactPairing.ofJointlyFaithful F hF coeval eval map_coevaluation map_evaluation
    ε_ X Y = eval :=
  rfl

section OneTriangle

variable {X Y : C} (coev : 𝟙_ C ⟶ X ⊗ Y) (ev : Y ⊗ X ⟶ 𝟙_ C)
  (h : coev ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ev = (λ_ X).hom ≫ (ρ_ X).inv)

include h

/-- The triangle identity `(η ▷ X) ≫ α ≫ (X ◁ ε) = λ ≫ ρ⁻¹` in the `⊗≫` spelling of
`CategoryTheory.ExactPairing.evaluation_coevaluation''`, for candidate data rather than for the
coevaluation and the evaluation of a pairing. -/
private theorem evaluation_coevaluation_monoidalComp :
    coev ▷ X ⊗≫ X ◁ ev = ⊗𝟙.hom := by
  convert! h <;> simp [monoidalComp]

/-- **Transposing across candidate duality data and back is the identity, from one triangle
identity alone.** Given `η : 𝟙 ⟶ X ⊗ Y` and `ε : Y ⊗ X ⟶ 𝟙` satisfying only the triangle
identity `(η ▷ X) ≫ α ≫ (X ◁ ε) = λ ≫ ρ⁻¹`, a morphism `f : W ⊗ X ⟶ T` is recovered from its
transpose `W ⟶ T ⊗ Y`.

This is the `left_inv` field of Mathlib's `CategoryTheory.tensorRightHomEquiv`, which is where
the observation that it uses only one of the two triangle identities comes from, restated for
candidate data: the inverse field of that equivalence uses the *other* identity, and is the half
that is unavailable here. -/
theorem whiskerRight_transpose_comp_evaluation {W T : C} (f : W ⊗ X ⟶ T) :
    ((ρ_ W).inv ≫ W ◁ coev ≫ (α_ W X Y).inv ≫ f ▷ Y) ▷ X ≫
        (α_ T Y X).hom ≫ T ◁ ev ≫ (ρ_ T).hom = f := by
  calc
    _ = 𝟙 _ ⊗≫ W ◁ coev ▷ X ⊗≫ (f ▷ (Y ⊗ X) ≫ T ◁ ev) ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫ W ◁ (coev ▷ X ⊗≫ X ◁ ev) ⊗≫ f := by rw [← whisker_exchange]; monoidal
    _ = f := by rw [evaluation_coevaluation_monoidalComp coev ev h]; monoidal

/-- **The second triangle identity, from the first one and a detection hypothesis.** The snake
composite `Y ⟶ Y` which the second triangle identity asserts to be the identity becomes the
identity after being whiskered with `X` and evaluated, *as a consequence of the first identity
alone*. So if the evaluation detects endomorphisms of `Y` — if `c ▷ X ≫ ε = ε` forces
`c = 𝟙 Y` — the second identity follows from the first. -/
theorem whiskerRight_snake_comp_evaluation :
    ((ρ_ Y).inv ≫ Y ◁ coev ≫ (α_ Y X Y).inv ≫ ev ▷ Y ≫ (λ_ Y).hom) ▷ X ≫ ev = ev := by
  calc
    _ = ((ρ_ Y).inv ≫ Y ◁ coev ≫ (α_ Y X Y).inv ≫ ev ▷ Y) ▷ X ≫
          ((λ_ Y).hom ▷ X ≫ ev) := by rw [comp_whiskerRight]; simp
    _ = ((ρ_ Y).inv ≫ Y ◁ coev ≫ (α_ Y X Y).inv ≫ ev ▷ Y) ▷ X ≫
          ((α_ (𝟙_ C) Y X).hom ≫ (𝟙_ C) ◁ ev ≫ (ρ_ (𝟙_ C)).hom) := by
      congr 1
      rw [← unitors_equal, leftUnitor_whiskerRight, Category.assoc,
        leftUnitor_naturality]
    _ = ev := whiskerRight_transpose_comp_evaluation coev ev h (W := Y) (T := 𝟙_ C) ev

/-- **An exact pairing from one triangle identity and a detection hypothesis.** Let `C` be a
monoidal category, let `X, Y` be objects and let

`η : 𝟙 ⟶ X ⊗ Y`,  `ε : Y ⊗ X ⟶ 𝟙`

satisfy the single triangle identity `(η ▷ X) ≫ α ≫ (X ◁ ε) = λ ≫ ρ⁻¹`. If moreover `ε`
detects endomorphisms of `Y`, in the sense that `c ▷ X ≫ ε = ε` holds only for `c = 𝟙 Y`, then
the *second* triangle identity holds as well, so `(η, ε)` is an exact pairing and `Y` is a left
dual of `X`.

The detection hypothesis is what a closed structure supplies: if `c ↦ c ▷ X ≫ ε` is the
bijection `Hom(Y, Hom(X, 𝟙)) ≃ Hom(Y ⊗ X, 𝟙)` of an internal Hom at `Y = Hom(X, 𝟙)` and `ε` is
the image of the identity, then it is injective, and this hypothesis holds. So in a closed
monoidal category *one* triangle identity suffices for the dual object `Hom(X, 𝟙)` — which is
the reason the second identity need not be checked separately on `D(O_X)`; see
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectCoevaluation`. -/
@[instance_reducible]
def ExactPairing.ofEvaluationCoevaluation
    (hdetect : ∀ c : Y ⟶ Y, c ▷ X ≫ ev = ev → c = 𝟙 Y) :
    ExactPairing X Y where
  coevaluation' := coev
  evaluation' := ev
  evaluation_coevaluation' := h
  coevaluation_evaluation' := by
    have hc := hdetect _ (whiskerRight_snake_comp_evaluation coev ev h)
    rw [Iso.eq_comp_inv _]
    simpa using (Iso.inv_comp_eq _).mp hc

end OneTriangle

end CategoryTheory

end
